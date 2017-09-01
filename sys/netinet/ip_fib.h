/*
 * Copyright (c) 2005-2012 University of Zagreb
 * Copyright (c) 2005 International Computer Science Institute
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 */


#ifndef _NETINET_IP_FIB_H_
#define	_NETINET_IP_FIB_H_

#ifndef DXR_DIRECT_BITS
#define	DXR_DIRECT_BITS 16
#endif

#define	DXR_RANGE_MASK (0xffffffff >> DXR_DIRECT_BITS)
#define	DXR_RANGE_SHIFT (32 - DXR_DIRECT_BITS)

#define	DIRECT_TBL_SIZE (1 << DXR_DIRECT_BITS)

#if !defined(DXR_VPORTS_MAX) || (DXR_VPORTS_MAX > DIRECT_TBL_SIZE)
#undef DXR_VPORTS_MAX
#define	DXR_VPORTS_MAX DIRECT_TBL_SIZE
#endif
#define ETHER_ADDR_LEN 6
#define DXR_HDR_CACHE_CLEARED(a)	(a[0] & 1)
#define DXR_HDR_CACHE_CLEAR(a)		(a[0] = 1)

extern uint8_t 	dxr_cache_index;
extern int nexthops;

#include <net/ethernet.h>
#include <netinet/in_fib.h>

struct dxr_nexthop {
	struct	ifnet *ifp;
	struct	in_addr gw;
	int32_t refcount;
	int16_t ll_next;
	int16_t ll_prev;
	struct ether_header hdr;
};

struct range_entry_long {
#if (DXR_DIRECT_BITS < 16)
	uint32_t
		 nexthop:DXR_DIRECT_BITS,
		 start:DXR_RANGE_SHIFT;
#else
	uint16_t nexthop;
	uint16_t start;
#endif
};

struct range_entry_short {
	uint8_t nexthop;
	uint8_t start;
};

#define	DESC_BASE_BITS 19
#define	BASE_MAX ((1 << DESC_BASE_BITS) - 1)
struct direct_entry {
	uint32_t
		 fragments:(31 - DESC_BASE_BITS),
		 long_format:1,
		 base:DESC_BASE_BITS;
};

struct dxr_heap_entry {
	uint32_t start;
	uint32_t end;
	int preflen;
	int nexthop;
};

struct chunk_desc {
	LIST_ENTRY(chunk_desc)	cd_all_le;
	LIST_ENTRY(chunk_desc)	cd_hash_le;
	uint32_t		cd_hash;
	uint32_t		cd_refcount;
	uint32_t		cd_base;
	int32_t			cd_cur_size;
	int32_t			cd_max_size;
	int32_t			cd_chunk_first;
};

struct chunk_ptr {
	struct chunk_desc	*cp_cdp;
	int32_t			cp_chunk_next;
};

struct dxr_stats {
	uint64_t local;
	uint64_t slowpath;
	uint64_t fastpath;
	uint64_t no_route;
	uint64_t input_errs;
	uint64_t output_errs;
};


struct mbuf * dxr_input(struct nhop4_basic *, struct in_addr, struct mbuf *, struct dxr_nexthop *);
void dxr_request(struct rtentry *, int);
struct dxr_nexthop * get_nexthop_tbl(void);

#endif /* _NETINET_IP_FIB_H_ */
