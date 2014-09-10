/*
 * libjingle
 * Copyright 2004--2005, Google Inc.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 *  1. Redistributions of source code must retain the above copyright notice,
 *     this list of conditions and the following disclaimer.
 *  2. Redistributions in binary form must reproduce the above copyright notice,
 *     this list of conditions and the following disclaimer in the documentation
 *     and/or other materials provided with the distribution.
 *  3. The name of the author may not be used to endorse or promote products
 *     derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO
 * EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS;
 * OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
 * WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR
 * OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF
 * ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#include "network.h"

#ifdef POSIX
#include <sys/socket.h>
#include <sys/utsname.h>
#include <sys/ioctl.h>
#include <net/if.h>
#include <unistd.h>
#include <errno.h>
#ifdef ANDROID
#include "ifaddrs-android.h"
#else
#include <ifaddrs.h>
#endif
#endif  // POSIX

#ifdef RAYCOM_ANDROID
#include "../media_core/MediaCore.h"
#include "logtotal.h"
#endif

#ifdef WIN32
#include "win32.h"
#include <Iphlpapi.h>
#endif

#include <algorithm>
#include <cstdio>

#include "logging.h"
#include "scoped_ptr.h"
#include "socket.h"  // includes something that makes windows happy
#include "stream.h"
#include "stringencode.h"
#include "thread.h"

#ifdef WIN32
#pragma comment(lib, "IPHLPAPI.lib")
#pragma comment(lib,"ws2_32.lib")
#endif
namespace Utils {
namespace {

#define MALLOC(x) HeapAlloc(GetProcessHeap(), 0, (x))
#define FREE(x) HeapFree(GetProcessHeap(), 0, (x))

const uint32 kUpdateNetworksMessage = 1;
const uint32 kSignalNetworksMessage = 2;

// Fetch list of networks every two seconds.
const int kNetworksUpdateIntervalMs = 2000;


// Makes a string key for this network. Used in the network manager's maps.
// Network objects are keyed on interface name, network prefix and the
// length of that prefix.
std::string MakeNetworkKey(const std::string& name, const IPAddress& prefix,
                           int prefix_length) {
  std::ostringstream ost;
  ost << name << "%" << prefix.ToString() << "/" << prefix_length;
  return ost.str();
}

bool CompareNetworks(const Network* a, const Network* b) {
  if (a->prefix_length() == b->prefix_length()) {
    if (a->name() == b->name()) {
      return a->prefix() < b->prefix();
    }
  }
  return a->name() < b->name();
}


}  // namespace

NetworkManager::NetworkManager() {
}

NetworkManager::~NetworkManager() {
}

NetworkManagerBase::NetworkManagerBase() : ipv6_enabled_(true) {
}

NetworkManagerBase::~NetworkManagerBase() {
  for (NetworkMap::iterator i = networks_map_.begin();
       i != networks_map_.end(); ++i) {
    delete i->second;
  }
}

void NetworkManagerBase::GetNetworks(NetworkList* result) const {
  *result = networks_;
}

void NetworkManagerBase::MergeNetworkList(const NetworkList& new_networks,
                                          bool* changed) {
  // Sort the list so that we can detect when it changes.
  typedef std::pair<Network*, std::vector<IPAddress> > address_list;
  std::map<std::string, address_list> address_map;
  NetworkList list(new_networks);
  NetworkList merged_list;
  std::sort(list.begin(), list.end(), CompareNetworks);

  *changed = false;

  if (networks_.size() != list.size())
    *changed = true;

  // First, build a set of network-keys to the ipaddresses.
  for (uint32 i = 0; i < list.size(); ++i) {
    bool might_add_to_merged_list = false;
    std::string key = MakeNetworkKey(list[i]->name(),
                                     list[i]->prefix(),
                                     list[i]->prefix_length());
    if (address_map.find(key) == address_map.end()) {
      address_map[key] = address_list(list[i], std::vector<IPAddress>());
      might_add_to_merged_list = true;
    }
    const std::vector<IPAddress>& addresses = list[i]->GetIPs();
    address_list& current_list = address_map[key];
    for (std::vector<IPAddress>::const_iterator it = addresses.begin();
         it != addresses.end();
         ++it) {
      current_list.second.push_back(*it);
    }
    if (!might_add_to_merged_list) {
      delete list[i];
    }
  }

  // Next, look for existing network objects to re-use.
  for (std::map<std::string, address_list >::iterator it = address_map.begin();
       it != address_map.end();
       ++it) {
    const std::string& key = it->first;
    Network* net = it->second.first;
    NetworkMap::iterator existing = networks_map_.find(key);
    if (existing == networks_map_.end()) {
      // This network is new. Place it in the network map.
      merged_list.push_back(net);
      networks_map_[key] = net;
      *changed = true;
    } else {
      // This network exists in the map already. Reset its IP addresses.
      *changed = existing->second->SetIPs(it->second.second, *changed);
      merged_list.push_back(existing->second);
      if (existing->second != net) {
        delete net;
      }
    }
  }
  networks_ = merged_list;
}

BasicNetworkManager::BasicNetworkManager()
    : thread_(NULL),
      start_count_(0) {
	GetBestNetWork();
}

BasicNetworkManager::~BasicNetworkManager() {
}

#if defined(POSIX)
void BasicNetworkManager::ConvertIfAddrs(struct ifaddrs* interfaces,
                                         bool include_ignored,
                                         NetworkList* networks) const {
  NetworkMap current_networks;
  for (struct ifaddrs* cursor = interfaces;
       cursor != NULL; cursor = cursor->ifa_next) {
    IPAddress prefix;
    IPAddress mask;
    IPAddress ip;
    int scope_id = 0;

    // Some interfaces may not have address assigned.
    if (!cursor->ifa_addr || !cursor->ifa_netmask)
      continue;

    switch (cursor->ifa_addr->sa_family) {
      case AF_INET: {
        ip = IPAddress(
            reinterpret_cast<sockaddr_in*>(cursor->ifa_addr)->sin_addr);
        mask = IPAddress(
            reinterpret_cast<sockaddr_in*>(cursor->ifa_netmask)->sin_addr);
        break;
      }
      case AF_INET6: {
        if (ipv6_enabled()) {
          ip = IPAddress(
              reinterpret_cast<sockaddr_in6*>(cursor->ifa_addr)->sin6_addr);
          mask = IPAddress(
              reinterpret_cast<sockaddr_in6*>(cursor->ifa_netmask)->sin6_addr);
          scope_id =
              reinterpret_cast<sockaddr_in6*>(cursor->ifa_addr)->sin6_scope_id;
          break;
        } else {
          continue;
        }
      }
      default: {
        continue;
      }
    }
#ifdef RAYCOM_ANDROID
    //char* iptmp = inet_ntoa(ip.ipv4_address());
    //total_log("clzhan %s %d iptmp= %s",__func__,__LINE__,iptmp);
    if(ip != best_ip_)
    {
	    continue;
    }
#endif
    int prefix_length = CountIPMaskBits(mask);
    prefix = TruncateIP(ip, prefix_length);
    std::string key = MakeNetworkKey(std::string(cursor->ifa_name),
                                     prefix, prefix_length);
    NetworkMap::iterator existing_network = current_networks.find(key);
    if (existing_network == current_networks.end()) {
      scoped_ptr<Network> network(new Network(cursor->ifa_name,
                                              cursor->ifa_name,
                                              prefix,
                                              prefix_length));
      network->set_scope_id(scope_id);
      network->AddIP(ip);
      bool ignored = ((cursor->ifa_flags & IFF_LOOPBACK) ||
                      IsIgnoredNetwork(*network));
      network->set_ignored(ignored);
      if (include_ignored || !network->ignored()) {
        networks->push_back(network.release());
      }
    } else {
      (*existing_network).second->AddIP(ip);
    }
  }
}

bool BasicNetworkManager::CreateNetworks(bool include_ignored,
                                         NetworkList* networks) const {
  struct ifaddrs* interfaces;
  int error = getifaddrs(&interfaces);
  if (error != 0) {
    LOG_ERR(LERROR) << "getifaddrs failed to gather interface data: " << error;
    return false;
  }

  ConvertIfAddrs(interfaces, include_ignored, networks);

  freeifaddrs(interfaces);
  return true;
}

#elif defined(WIN32)

unsigned int GetPrefix(PIP_ADAPTER_PREFIX prefixlist,
              const IPAddress& ip, IPAddress* prefix) {
  IPAddress current_prefix;
  IPAddress best_prefix;
  unsigned int best_length = 0;
  while (prefixlist) {
    // Look for the longest matching prefix in the prefixlist.
    if (prefixlist->Address.lpSockaddr == NULL ||
        prefixlist->Address.lpSockaddr->sa_family != ip.family()) {
      prefixlist = prefixlist->Next;
      continue;
    }
    switch (prefixlist->Address.lpSockaddr->sa_family) {
      case AF_INET: {
        sockaddr_in* v4_addr =
            reinterpret_cast<sockaddr_in*>(prefixlist->Address.lpSockaddr);
        current_prefix = IPAddress(v4_addr->sin_addr);
        break;
      }
      case AF_INET6: {
          sockaddr_in6* v6_addr =
              reinterpret_cast<sockaddr_in6*>(prefixlist->Address.lpSockaddr);
          current_prefix = IPAddress(v6_addr->sin6_addr);
          break;
      }
      default: {
        prefixlist = prefixlist->Next;
        continue;
      }
    }
    if (TruncateIP(ip, prefixlist->PrefixLength) == current_prefix &&
        prefixlist->PrefixLength > best_length) {
      best_prefix = current_prefix;
      best_length = prefixlist->PrefixLength;
    }
    prefixlist = prefixlist->Next;
  }
  *prefix = best_prefix;
  return best_length;
}


bool TheSameNetSegment(const char *ip1, const char *ip2)
{
	char tmp_ip1[12] = {0};
	char tmp_ip2[12] = {0};

	const char *ptr = strrchr(ip1, '.');
	if(ptr != NULL){
		strncpy(tmp_ip1, ip1, ptr-ip1);
	}
	ptr = strrchr(ip2, '.');
	if(ptr != NULL){
		strncpy(tmp_ip2, ip2, ptr-ip2);
	}

	if(strcmp(tmp_ip1, tmp_ip2)){
		return false;
	}

	return true;
}

bool BasicNetworkManager::CreateNetworks(bool include_ignored,
                                         NetworkList* networks) const {
  NetworkMap current_networks;
  // MSDN recommends a 15KB buffer for the first try at GetAdaptersAddresses.
  size_t buffer_size = 16384;
  scoped_array<char> adapter_info(new char[buffer_size]);
  PIP_ADAPTER_ADDRESSES adapter_addrs =
      reinterpret_cast<PIP_ADAPTER_ADDRESSES>(adapter_info.get());
  int adapter_flags = (GAA_FLAG_SKIP_DNS_SERVER | GAA_FLAG_SKIP_ANYCAST |
                       GAA_FLAG_SKIP_MULTICAST | GAA_FLAG_INCLUDE_PREFIX);
  int ret = 0;
  do {
    adapter_info.reset(new char[buffer_size]);
    adapter_addrs = reinterpret_cast<PIP_ADAPTER_ADDRESSES>(adapter_info.get());
    ret = GetAdaptersAddresses(AF_UNSPEC, adapter_flags,
                               0, adapter_addrs,
                               reinterpret_cast<PULONG>(&buffer_size));
  } while (ret == ERROR_BUFFER_OVERFLOW);
  if (ret != ERROR_SUCCESS) {
    return false;
  }
  int count = 0;
  while (adapter_addrs) {
    if (adapter_addrs->OperStatus == IfOperStatusUp) {
      PIP_ADAPTER_UNICAST_ADDRESS address = adapter_addrs->FirstUnicastAddress;
      PIP_ADAPTER_PREFIX prefixlist = adapter_addrs->FirstPrefix;
      std::string name;
      std::string description;
#ifdef _DEBUG
      name = ToUtf8(adapter_addrs->FriendlyName,
                    wcslen(adapter_addrs->FriendlyName));
#endif
      description = ToUtf8(adapter_addrs->Description,
                           wcslen(adapter_addrs->Description));
      for (; address; address = address->Next) {
#ifndef _DEBUG
        name = Utils::ToString(count);
#endif

        IPAddress ip;
        int scope_id = 0;
        scoped_ptr<Network> network;
        switch (address->Address.lpSockaddr->sa_family) {
          case AF_INET: {
            sockaddr_in* v4_addr =
                reinterpret_cast<sockaddr_in*>(address->Address.lpSockaddr);
            ip = IPAddress(v4_addr->sin_addr);
            break;
          }
          case AF_INET6: {
            if (ipv6_enabled()) {
              sockaddr_in6* v6_addr =
                  reinterpret_cast<sockaddr_in6*>(address->Address.lpSockaddr);
              scope_id = v6_addr->sin6_scope_id;
              ip = IPAddress(v6_addr->sin6_addr);
              break;
            } else {
              continue;
            }
          }
          default: {
            continue;
          }
        }
        IPAddress prefix;
        int prefix_length = GetPrefix(prefixlist, ip, &prefix);
        std::string key = MakeNetworkKey(name, prefix, prefix_length);
        NetworkMap::iterator existing_network = current_networks.find(key);
        if (existing_network == current_networks.end()) {
          scoped_ptr<Network> network(new Network(name,
                                                  description,
                                                  prefix,
                                                  prefix_length));
          network->set_scope_id(scope_id);
          network->AddIP(ip);
          bool ignore = ((adapter_addrs->IfType == IF_TYPE_SOFTWARE_LOOPBACK) ||
                         IsIgnoredNetwork(*network));
          network->set_ignored(ignore);
          if (include_ignored || !network->ignored()) {
            networks->push_back(network.release());
          }
        } else {
          (*existing_network).second->AddIP(ip);
        }
      }
      // Count is per-adapter - all 'Networks' created from the same
      // adapter need to have the same name.
      ++count;
    }
    adapter_addrs = adapter_addrs->Next;
  }
  return true;
}
#endif  // WIN32

bool BasicNetworkManager::IsIgnoredNetwork(const Network& network) {
#ifdef POSIX
  // Ignore local networks (lo, lo0, etc)
  // Also filter out VMware interfaces, typically named vmnet1 and vmnet8
  if (strncmp(network.name().c_str(), "vmnet", 5) == 0 ||
      strncmp(network.name().c_str(), "vnic", 4) == 0) {
    return true;
  }
#elif defined(WIN32)
  // Ignore any HOST side vmware adapters with a description like:
  // VMware Virtual Ethernet Adapter for VMnet1
  // but don't ignore any GUEST side adapters with a description like:
  // VMware Accelerated AMD PCNet Adapter #2
  if (strstr(network.description().c_str(), "VMnet") != NULL) {
    return true;
  }
#endif

  // Ignore any networks with a 0.x.y.z IP
  if (network.prefix().family() == AF_INET) {
    return (network.prefix().v4AddressAsHostOrderInteger() < 0x01000000);
  }
  return false;
}

void BasicNetworkManager::StartUpdating() {
  thread_ = Thread::Current();
  if (start_count_) {
    // If network interfaces are already discovered and signal is sent,
    // we should trigger network signal immediately for the new clients
    // to start allocating ports.
    if (sent_first_update_)
      thread_->Post(this, kSignalNetworksMessage);
  } else {
    thread_->Post(this, kUpdateNetworksMessage);
  }
  ++start_count_;
}

void BasicNetworkManager::StopUpdating() {
  ASSERT(Thread::Current() == thread_);
  if (!start_count_)
    return;

  --start_count_;
  if (!start_count_) {
    thread_->Clear(this);
    sent_first_update_ = false;
  }
}

void BasicNetworkManager::OnMessage(Message* msg) {
  switch (msg->message_id) {
    case kUpdateNetworksMessage:  {
      DoUpdateNetworks();
      break;
    }
    case kSignalNetworksMessage:  {
      SignalNetworksChanged();
      break;
    }
    default:
      ASSERT(false);
  }
}

void BasicNetworkManager::DoUpdateNetworks() {
  if (!start_count_)
    return;

  ASSERT(Thread::Current() == thread_);

  NetworkList list;
  if (!CreateNetworks(false, &list)) {
    SignalError();
  } else {
    bool changed;
    MergeNetworkList(list, &changed);
    if (changed || !sent_first_update_) {
      SignalNetworksChanged();
      sent_first_update_ = true;
    }
  }

  thread_->PostDelayed(kNetworksUpdateIntervalMs, this, kUpdateNetworksMessage);
}

void BasicNetworkManager::DumpNetworks(bool include_ignored) {
  NetworkList list;
  CreateNetworks(include_ignored, &list);
  LOG(LS_INFO) << "NetworkManager detected " << list.size() << " networks:";
  for (size_t i = 0; i < list.size(); ++i) {
    const Network* network = list[i];
    if (!network->ignored() || include_ignored) {
      LOG(LS_INFO) << network->ToString() << ": " << network->description()
                   << ((network->ignored()) ? ", Ignored" : "");
    }
  }
}
#ifdef WIN32
/* 获取最佳网络地址 yan.zhuang*/  
typedef DWORD (WINAPI *GETADAPTERSINFO)( PIP_ADAPTER_INFO, PULONG );
typedef DWORD (WINAPI *GETBESTINTERFACE)( IPAddr, PDWORD );

// GETADAPTERSINFO GetAdaptersInfo = NULL;
// GETBESTINTERFACE GetBestInterface = NULL;

static HINSTANCE	hDll;			// ICMP library handle

static int _GetIpFromAdapterVPN(char *ip)
{
	PIP_ADAPTER_INFO pAdapterInfo;
	PIP_ADAPTER_INFO pAdapter = NULL;
	bool find_vpn_ip = false;
	DWORD dwRetVal = 0;

	if (ip == NULL) {
		return -1;
	}

	ULONG ulOutBufLen = sizeof (IP_ADAPTER_INFO);
	pAdapterInfo = (IP_ADAPTER_INFO *) MALLOC(sizeof (IP_ADAPTER_INFO));
	if (pAdapterInfo == NULL) {
		printf("Error allocating memory needed to call GetAdaptersinfo\n");
		return 1;
	}
	// Make an initial call to GetAdaptersInfo to get
	// the necessary size into the ulOutBufLen variable
	if (GetAdaptersInfo(pAdapterInfo, &ulOutBufLen) == ERROR_BUFFER_OVERFLOW) {
		FREE(pAdapterInfo);
		pAdapterInfo = (IP_ADAPTER_INFO *) MALLOC(ulOutBufLen);
		if (pAdapterInfo == NULL) {
			printf("Error allocating memory needed to call GetAdaptersinfo\n");
			return 1;
		}
	}

	if ((dwRetVal = GetAdaptersInfo(pAdapterInfo, &ulOutBufLen)) == NO_ERROR) {
		pAdapter = pAdapterInfo;
		while (pAdapter) {

			if (pAdapter->Type == MIB_IF_TYPE_PPP ||
				strstr(pAdapter->Description,"VPN") != NULL ||
				strstr(pAdapter->Description,"vpn") != NULL) {
					if (pAdapter->IpAddressList.IpAddress.String != NULL && 
						strlen(pAdapter->IpAddressList.IpAddress.String)>0) {
							if(strcmp(pAdapter->IpAddressList.IpAddress.String, "0.0.0.0")){
								strcpy(ip,pAdapter->IpAddressList.IpAddress.String);
								find_vpn_ip = true;
								break;
							}
					}
			}
			pAdapter = pAdapter->Next;
		}
	}
	if (pAdapterInfo)
		FREE(pAdapterInfo);
	return (find_vpn_ip ? 0 : -1);
}

static char *_GetIpAddrTabletFromIterface(int index)
{
	int i;
	static char local_ip[128] = {0};
	PMIB_IPADDRTABLE pIPAddrTable;
	DWORD dwSize = 0;
	DWORD dwRetVal = 0;
	IN_ADDR IPAddr;

	LPVOID lpMsgBuf;

	pIPAddrTable = (MIB_IPADDRTABLE *) MALLOC(sizeof (MIB_IPADDRTABLE));

	if (pIPAddrTable) {
		if (GetIpAddrTable(pIPAddrTable, &dwSize, 0) ==
			ERROR_INSUFFICIENT_BUFFER) {
				FREE(pIPAddrTable);
				pIPAddrTable = (MIB_IPADDRTABLE *) MALLOC(dwSize);

		}
		if (pIPAddrTable == NULL) {
			return NULL;
		}
	}
	if ( (dwRetVal = GetIpAddrTable( pIPAddrTable, &dwSize, 0 )) != NO_ERROR ) { 
		if (FormatMessage(FORMAT_MESSAGE_ALLOCATE_BUFFER | FORMAT_MESSAGE_FROM_SYSTEM | FORMAT_MESSAGE_IGNORE_INSERTS, NULL, dwRetVal, MAKELANGID(LANG_NEUTRAL, SUBLANG_DEFAULT),       // Default language
			(LPTSTR) & lpMsgBuf, 0, NULL)) {
				LocalFree(lpMsgBuf);
		}
	}

	memset(local_ip,'\0',strlen(local_ip));
	for (i=0; i < (int) pIPAddrTable->dwNumEntries; i++) {
		if (pIPAddrTable->table[i].dwIndex == index) {
			IPAddr.S_un.S_addr = (u_long) pIPAddrTable->table[i].dwAddr;
			strcpy(local_ip,inet_ntoa(IPAddr));
			break;
		}
	}

	if (pIPAddrTable) {
		FREE(pIPAddrTable);
		pIPAddrTable = NULL;
	}

	return local_ip;
}

#endif
/* yan.zhuang */
void BasicNetworkManager::GetBestNetWork()
{
#ifdef WIN32
	int ret = -1;
	static char buf[50] = {0};
	static char local_ip[256];
	char *ipaddr = NULL;
	memset(buf, 0, sizeof(buf));
	memset(local_ip, 0, sizeof(local_ip));
	
	ret = _GetIpFromAdapterVPN(local_ip);
	if (ret != 0) {
		IPAddr dwDestAddr = inet_addr("0.0.0.0");
		DWORD dwBestIfIndex = -1;
		DWORD dwRes = GetBestInterface(dwDestAddr,&dwBestIfIndex);
		if (dwRes != ERROR_SUCCESS) {
			return;
		}
		ipaddr =  _GetIpAddrTabletFromIterface(dwBestIfIndex);
		strcpy(local_ip, ipaddr);
	}

	IN_ADDR ia;
	ia.S_un.S_addr = inet_addr(local_ip);
	
	best_ip_ = IPAddress(ia);
#else
	//static char buf[50] = {0};
	static char local_ip[20] = {0};
	//memset(buf, 0, sizeof(buf));
	memset(local_ip, 0, sizeof(local_ip));


    MediaCoreGetIP(local_ip);
	total_log("libjingle_total", "clzhan %s %d local_ip= %s",__func__,__LINE__,local_ip);
	//IN_ADDR ia;
	//ia.S_un.S_addr = inet_addr(local_ip);

    struct   in_addr   my_addr;      
    my_addr.s_addr   =   inet_addr(local_ip);  
   

    best_ip_ = IPAddress(my_addr);
#endif


#if 0
	static char buf[50] = {0};
	static char local_ip[256];
	memset(buf, 0, sizeof(buf));
	memset(local_ip, 0, sizeof(local_ip));
	DWORD	iAddr;
	
	if( hDll == NULL )
	{
		hDll = LoadLibrary( TEXT("iphlpapi.dll") );
	}

	if( hDll )
	{
		if( GetBestInterface == NULL )
		{
			GetBestInterface = (GETBESTINTERFACE) GetProcAddress( hDll, "GetBestInterface" );
			if( GetBestInterface == NULL ){
				return;
			}
		}

		FILE *test_network_fp = fopen("test_network_addr.txt", "r");
		if(test_network_fp != NULL){
			fgets(buf, 50, test_network_fp);
			fclose(test_network_fp);
		}
		if(buf[0] == 0){
			strcpy(buf, "211.100.47.87");
		}

		iAddr = inet_addr(buf);
		DWORD	iIndex;
		bool	fisFound = false;

		DWORD dwRes = GetBestInterface(iAddr, &iIndex);
		if (dwRes != ERROR_SUCCESS) {
			return;
		}
		
		int i;

		PMIB_IPADDRTABLE pIPAddrTable;
		DWORD dwSize = 0;
		DWORD dwRetVal = 0;
		IN_ADDR IPAddr;

		LPVOID lpMsgBuf;

		pIPAddrTable = (MIB_IPADDRTABLE *) MALLOC(sizeof (MIB_IPADDRTABLE));

		if (pIPAddrTable) {
			if (GetIpAddrTable(pIPAddrTable, &dwSize, 0) ==
				ERROR_INSUFFICIENT_BUFFER) {
					FREE(pIPAddrTable);
					pIPAddrTable = (MIB_IPADDRTABLE *) MALLOC(dwSize);

			}
			if (pIPAddrTable == NULL) {
				return;
			}
		}
		if ( (dwRetVal = GetIpAddrTable( pIPAddrTable, &dwSize, 0 )) != NO_ERROR ) { 
			if (FormatMessage(FORMAT_MESSAGE_ALLOCATE_BUFFER | FORMAT_MESSAGE_FROM_SYSTEM | FORMAT_MESSAGE_IGNORE_INSERTS, NULL, dwRetVal, MAKELANGID(LANG_NEUTRAL, SUBLANG_DEFAULT),       // Default language
				(LPTSTR) & lpMsgBuf, 0, NULL)) {
					LocalFree(lpMsgBuf);
			}
		}

		memset(local_ip,'\0',strlen(local_ip));
		for (i=0; i < (int) pIPAddrTable->dwNumEntries; i++) {
			if (pIPAddrTable->table[i].dwIndex == iIndex) {
				IPAddr.S_un.S_addr = (u_long) pIPAddrTable->table[i].dwAddr;
				strcpy(local_ip,inet_ntoa(IPAddr));
				break;
			}
		}

		if (pIPAddrTable) {
			FREE(pIPAddrTable);
			pIPAddrTable = NULL;
		}

		IN_ADDR ia;
		ia.S_un.S_addr = inet_addr(local_ip);

		best_ip_ = IPAddress(ia);
	}	
#endif


#if 0
	if( hDll == NULL )
	{
		hDll = LoadLibrary( TEXT("iphlpapi.dll") );
	}

	if( hDll )
	{
		if( GetBestInterface == NULL )
		{
			GetBestInterface = (GETBESTINTERFACE) GetProcAddress( hDll, "GetBestInterface" );
			if( GetBestInterface == NULL ) goto NORMAL_CASE;
		}
		char buf[50] = {0};
		FILE *test_network_fp = fopen("test_network_addr.txt", "r");
		if(test_network_fp != NULL){
			fgets(buf, 50, test_network_fp);
			fclose(test_network_fp);
		}
		if(buf[0] == 0){
			strcpy(buf, "211.100.47.87");
		}

		DWORD	iAddr = inet_addr(buf);
		DWORD	iIndex;
		bool	fisFound = false;

		GetBestInterface( iAddr, &iIndex );

		printf( "interface index = %d\n", iIndex );

		DWORD dwErr, dwAdapterInfoSize = 0;
		PIP_ADAPTER_INFO	pAdapterInfo, pAdapt;
		PIP_ADDR_STRING		pAddrStr;

		if( GetAdaptersInfo == NULL )
		{
			GetAdaptersInfo = (GETADAPTERSINFO) GetProcAddress( hDll, "GetAdaptersInfo" );
			if( GetAdaptersInfo == NULL ) goto NORMAL_CASE;
		}

		if( ( dwErr = GetAdaptersInfo( NULL, &dwAdapterInfoSize ) ) != 0 )
		{
			if( dwErr != ERROR_BUFFER_OVERFLOW )
			{
				goto NORMAL_CASE;
			}
		}

		// Allocate memory from sizing information
		if( ( pAdapterInfo = (PIP_ADAPTER_INFO) GlobalAlloc( GPTR, dwAdapterInfoSize )) == NULL )
		{
			goto NORMAL_CASE;
		}

		// Get actual adapter information
		if( ( dwErr = GetAdaptersInfo( pAdapterInfo, &dwAdapterInfoSize ) ) != 0 )
		{
			GlobalFree( pAdapterInfo );
			goto NORMAL_CASE;
		}

		for( pAdapt = pAdapterInfo; pAdapt; pAdapt = pAdapt->Next )
		{
			printf( "pAdapt->index = %d\n", pAdapt->Index );

			if( pAdapt->Index != iIndex ) continue;

			switch ( pAdapt->Type )
			{
			case MIB_IF_TYPE_ETHERNET:
			case MIB_IF_TYPE_PPP:
			case 71:
				if( strlen( pAdapt->GatewayList.IpAddress.String ) > 0 )
				{
					DWORD	dwGwIp, dwMask, dwIp, dwGwNetwork, dwNetwork;

					dwGwIp = inet_addr( pAdapt->GatewayList.IpAddress.String );

					printf( "Gateway address = [%s]\n", pAdapt->GatewayList.IpAddress.String );
					printf( "Gateway mask = [%s]\n", pAdapt->GatewayList.IpMask.String );

					for( pAddrStr = &(pAdapt->IpAddressList); pAddrStr; pAddrStr = pAddrStr->Next )
					{
						if( strlen(pAddrStr->IpAddress.String) > 0 )
						{
							dwIp = inet_addr( pAddrStr->IpAddress.String );
							dwMask = inet_addr( pAddrStr->IpMask.String );
							dwNetwork = dwIp & dwMask;
							dwGwNetwork = dwGwIp & dwMask;

							printf( "IP address = [%s], network = %08x\n", pAddrStr->IpAddress.String, dwNetwork );

							if( dwGwNetwork == dwNetwork )
							{
								IN_ADDR ia;
								ia.S_un.S_addr = inet_addr(pAddrStr->IpAddress.String);
// 								UCHAR tmp;
// 								tmp = ia.S_un.S_un_b.s_b1;
// 								ia.S_un.S_un_b.s_b1 = ia.S_un.S_un_b.s_b4;
// 								ia.S_un.S_un_b.s_b4 = tmp;
// 								tmp = ia.S_un.S_un_b.s_b2;
// 								ia.S_un.S_un_b.s_b2 = ia.S_un.S_un_b.s_b3;
// 								ia.S_un.S_un_b.s_b3 = tmp;

								best_ip_ = IPAddress(ia);
								printf( "ip address = %s\n", pAddrStr->IpAddress.String );
								fisFound = true;
								break;
							}
						}
					}
				}
				break;
			default:
				break;
			}

			if( fisFound == true ) break;
		}

		GlobalFree( pAdapterInfo );

		if( fisFound == false ) goto NORMAL_CASE;
	}
	else
	{
		printf( "iphlpapi.dll is not loaded\n" );
NORMAL_CASE:
		printf( "normal local host ip lookup\n" );
		//PrintIP();
	}
#endif
}


Network::Network(const std::string& name, const std::string& desc,
                 const IPAddress& prefix, int prefix_length)
    : name_(name), description_(desc), prefix_(prefix),
      prefix_length_(prefix_length), scope_id_(0), ignored_(false),
      uniform_numerator_(0), uniform_denominator_(0), exponential_numerator_(0),
      exponential_denominator_(0) {
}

std::string Network::ToString() const {
  std::stringstream ss;
  // Print out the first space-terminated token of the network desc, plus
  // the IP address.
  ss << "Net[" << description_.substr(0, description_.find(' '))
     << ":" << prefix_ << "/" << prefix_length_ << "]";
  return ss.str();
}

// Sets the addresses of this network. Returns true if the address set changed.
// Change detection is short circuited if the changed argument is true.
bool Network::SetIPs(const std::vector<IPAddress>& ips, bool changed) {
  changed = changed || ips.size() != ips_.size();
  // Detect changes with a nested loop; n-squared but we expect on the order
  // of 2-3 addresses per network.
  for (std::vector<IPAddress>::const_iterator it = ips.begin();
      !changed && it != ips.end();
      ++it) {
    bool found = false;
    for (std::vector<IPAddress>::iterator inner_it = ips_.begin();
         !found && inner_it != ips_.end();
         ++inner_it) {
      if (*it == *inner_it) {
        found = true;
      }
    }
    changed = !found;
  }
  ips_ = ips;
  return changed;
}
}  // namespace Utils
