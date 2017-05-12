#define	DXR_DIRECT_BITS 18
#define	ALLOW_OOO_EXEC
#define	DXR_LOOKUP_TIMING
//#define	DIR_24_8
//#define	RADIX_TIMING
//#define	DXR_ITER_TIMING
//#define	REPEAT_SAME_KEY
#define	DXR_LOOKUP_CONSISTENCY_CHECK

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
#define ND(format, ...)
#define D(format, ...)						\
	do {							\
		struct timeval __xxts;				\
		microtime(&__xxts);				\
		printf("%03d.%06d [%4d] %-25s " format "\n",	\
		(int)__xxts.tv_sec % 1000, (int)__xxts.tv_usec,	\
		__LINE__, __func__, ##__VA_ARGS__);		\
	} while (0)

/* rate limited, lps indicates how many per second */
#define RD(lps, format, ...)					\
	do {							\
		static int t0, __cnt;				\
		if (t0 != time_second) {			\
			t0 = time_second;			\
			__cnt = 0;				\
		}						\
		if (__cnt++ < lps)				\
			D(format, ##__VA_ARGS__);		\
	} while (0)

/* Compile-time tunables, overriding defaults from ip_fib.h */
#define	DXR_VPORTS_MAX 1024

/* Debugging options */
#define	DXR_BUILD_TIMING
#define	DXR_BUILD_PARANOIC
//#define	DXR_BUILD_DEBUG

#if defined(DXR_ITER_TIMING) && defined(DXR_LOOKUP_TIMING)
#error DXR_ITER_TIMING and DXR_LOOKUP_TIMING are mutualy exclusive
#endif

#ifdef RADIX_MPATH
#error RADIX_MPATH is not compatible with DXR lookups
#endif

#include <sys/param.h>
#include <sys/malloc.h>
#include <sys/mbuf.h>
#include <sys/kernel.h>
#include <sys/kthread.h>
#include <sys/proc.h>
#include <sys/protosw.h>
#include <sys/sched.h>
#include <sys/smp.h>
#include <sys/socket.h>
#include <sys/sysctl.h>
#include <sys/unistd.h>

#include <net/vnet.h>
#include <net/if.h>
#include <net/if_var.h>
#include <net/netisr.h>
#include <net/if_dl.h>
#include <net/route.h>
#include <net/route_var.h>
#include <net/ethernet.h>

#include <netinet/in.h>
#include <netinet/in_systm.h>
#include <netinet/ip.h>
#include <netinet/in_var.h>
#include <netinet/ip_var.h>
#include <netinet/ip_fib.h>
#include <netinet/ip_icmp.h>

#include <machine/clock.h>
#include <machine/in_cksum.h>

#include <vm/vm.h>
#include <vm/pmap.h>
#include <vm/vm_map.h>

static uint16_t nexthop_ref(struct in_addr, struct ifnet *);
static int nexthop_unref(uint16_t);
static void schedule_update(struct rtentry *);
static void update_chunk(int);
static void update_chunk_long(int);
static int dxr_walk(struct radix_node *, void *);
static int dxr_walk_long(struct radix_node *, void *);
static void dxr_initheap(uint32_t, uint32_t);
static void dxr_heap_inject(uint32_t, uint32_t, int, int);
static int dxr_parse(struct rtentry *rt, int, uint32_t, uint32_t, int, int);
static int dxr_parse_long(struct rtentry *rt, int, uint32_t, uint32_t,
    int, int);
static int dxr_lookup(uint32_t);
static void dxr_output(struct mbuf *, struct dxr_nexthop *);
static void prune_empty_chunks(void);
static void chunk_ref(int);
static void chunk_unref(int);
static void apply_pending(void);
static void dxr_init(void);
static void dxr_check_tables(void);
static void addr_print(uint32_t s_addr);
//static void ethhdr_print(struct ether_header *eh);

#ifdef DIR_24_8
#if (DXR_DIRECT_BITS != 24)
#error DXR_DIRECT_BITS must be set to 24 when DIR_24_8 is configured
#endif
static void dir_24_8_rebuild(void);
static int dir_24_8_lookup(uint32_t);
#endif

#if defined(DXR_LOOKUP_TIMING) || defined(DXR_ITER_TIMING) || defined(RADIX_TIMING)
static void dxr_lookup_exercise(void *arg);
#endif

#ifdef DXR_BUILD_DEBUG
static void dxr_heap_dump(void);
static void dxr_chunk_dump(int);
static void print_in_route(struct rtentry *, const char *);
#endif

static struct ifqueue dxr_intrq;

static int	dxr_enable;
static int	async_updates;
static int	updates_pending;
static int	routes;
int	nexthops;
static int	range_tbl_free;
static int	nexthop_tbl_size;
static int	nexthop_head;
static int	nexthop_empty_head;
static int	heap_index;
static struct	dxr_stats dxr_stats;
static int	chunks_short;
static int	chunks_long;
static int	fragments_short;
static int	fragments_long;
static int	aggr_chunks_short;
static int	aggr_chunks_long;
static int	aggr_fragments_short;
static int	aggr_fragments_long;
static struct	dxr_heap_entry dxr_heap[33];
static uint32_t	pending_bitmask[DIRECT_TBL_SIZE >> 5];
static int	pending_start;
static int	pending_end;

static int	rdtsc_latency;

uint8_t dxr_cache_index;

#if defined(DXR_LOOKUP_TIMING) || defined(DXR_ITER_TIMING) || defined(RADIX_TIMING)
static DPCPU_DEFINE(int, valid_timing);
static int	ex_preload;
static int	ex_threads;
static int	ex_iters = 100000;

struct iter_stat {
	uint64_t cnt;
	uint64_t cycles;
} static iter_stats[MAXCPU][32];

static uint32_t *dlp;
static int reduce;

#define	DUMMY_MEM_SIZE (1 << 28)	/* 256 M elements, 1 Gbyte of kmem */
#define	DUMMY_MEM_MASK (DUMMY_MEM_SIZE - 1)

#endif /* DXR_LOOKUP_TIMING ... */

#ifdef DXR_BUILD_TIMING
struct update_stat {
	uint64_t cnt;
	uint64_t cycles;
} static update_stats[34];
#endif /* DXR_BUILD_TIMING */


static struct direct_entry	*direct_tbl;
static struct range_entry_long	*range_tbl;
static struct dxr_nexthop	*nexthop_tbl;

#ifdef DIR_24_8
static uint16_t *tbl_0_23;
static uint16_t *tbl_24_31;
#endif

#define	CHUNK_HASH_BITS 16
#define	CHUNK_HASH_SIZE (CHUNK_HASH_BITS << 1)
#define	CHUNK_HASH_MASK (CHUNK_HASH_SIZE - 1)

static struct chunk_ptr		cptbl[DIRECT_TBL_SIZE];
static LIST_HEAD(, chunk_desc)	chunk_hashtbl[CHUNK_HASH_SIZE];
static LIST_HEAD(, chunk_desc)	all_chunks;
static LIST_HEAD(, chunk_desc)	unused_chunks;	/* abuses hash link entry */
static uma_zone_t chunk_zone;


#define	SIN(s) ((struct sockaddr_in *)s)
#define	SDL(s) ((struct sockaddr_dl *)s)


/*
 * Forwarding plane functions: dxr_input() is called from link-layer
 * demultiplexors, replacing calls to now obsoleted ipflow_fastforward().
 * If a packet for whatever reason cannot be directly forwarded without
 * too much of a hassle, such as in cases of failed ARP resolutions,
 * requirements for ICMP message generation or fragmentation, we return
 * the packet unmodified to the standard lower half of the BSD IP
 * network stack.
 *
 * A significant portion of dxr_input() and dxr_output() skeleton was
 * borrowed from the ip_flow implementation, i.e. from ipflow_fastforward().
 */
struct dxr_nexthop *
get_nexthop_tbl(void)
{
	//printf("get_nexthop_tbl nexthop_tbl = %p\n", nexthop_tbl);
	return nexthop_tbl;
}

void addr_print(uint32_t s_addr)
{
	unsigned char *p;
	p = (unsigned char *)&s_addr;
	printf("%u.%u.%u.%u\n", p[0], p[1], p[2], p[3]);
}

/*
void ethhdr_print(struct ether_header *eh) 
{
	printf("Dst_mac %02x:%02x:%02x:%02x:%02x:%02x\n",
			eh->ether_dhost[0], eh->ether_dhost[1], eh->ether_dhost[2],
			eh->ether_dhost[3], eh->ether_dhost[4], eh->ether_dhost[5]);
	printf("Src_mac %02x:%02x:%02x:%02x:%02x:%02x\n",
			eh->ether_shost[0], eh->ether_shost[1], eh->ether_shost[2],
			eh->ether_shost[3], eh->ether_shost[4], eh->ether_shost[5]);
	printf("Ether_type %04x\n", eh->ether_type);
}
*/

struct mbuf *
dxr_input(struct mbuf *m)
{
	struct ip *ip = mtod(m, struct ip *);
	struct dxr_nexthop *nh;
	struct ifnet *dst_ifp;
	uint32_t dst;
	uint8_t index;

	dst = ntohl(ip->ip_dst.s_addr);

	/*
	 * Find the nexthop.
	 *
	 * XXX Lookup structures should be protected somehow...
	 */
	nh = &nexthop_tbl[(index = dxr_lookup(dst))];
	/*
	printf("in dxr, index = %d, nexthop_tbl = %p, &nexthop_tbl[index] = %p\n", index, nexthop_tbl, nh);
	for (i = 0; i < 10; i++)
		printf("in dxr, i = %d, nexthop_tbl[%d].gw = %d\n", i, i, ntohl(nexthop_tbl[i].gw.s_addr)); 
	*/
	dst_ifp = nh->ifp;
	if (dst_ifp == NULL) {
		/*
		 * Don't just drop the packet, need to send an ICMP unreachable
		 */
		dxr_stats.no_route++;
		dxr_stats.slowpath++;
		return m;
	}
	dxr_cache_index = index;

	/*
	 * We are done - dispatch the mbuf and inform the caller that
	 * our packet was consumed.
	 */
	dxr_output(m, nh);
	return NULL;
}

static void
dxr_output(struct mbuf *m, struct dxr_nexthop *nh)
{
	struct ifnet *dst_ifp = nh->ifp;
	struct ip *ip = mtod(m, struct ip *);
	struct sockaddr_in dst_sin;
	uint32_t dst;
	struct ether_header *hdr = NULL;

	if (nh->gw.s_addr) {
		dst = ntohl(nh->gw.s_addr);
		dst_sin.sin_addr.s_addr = nh->gw.s_addr;
	} else {
		dst = ntohl(ip->ip_dst.s_addr);
		dst_sin.sin_addr.s_addr = ip->ip_dst.s_addr;
	}
	dst_sin.sin_family = AF_INET;
	dst_sin.sin_len = sizeof(dst);

	if (m->m_flags & M_VALE) {
		m->m_pkthdr.PH_loc.ptr = dst_ifp; /* save destination */
	}
	/*
	 * Check if media link state of interface is not down
	 */
	if (dst_ifp->if_link_state == LINK_STATE_DOWN) {
		if (!(m->m_flags & M_VALE)) 
			icmp_error(m, ICMP_UNREACH, ICMP_UNREACH_HOST, 0, 0);
		return;
	}

	/* bypass ethernet_output routine */
	
	/* printf("print cache info \n");
	ethhdr_print((struct ether_header *)&nh->hdr);
	*/

	if ((m->m_flags & M_VALE) && !(DXR_HDR_CACHE_CLEARED(nh->hdr.ether_dhost))) {
		//printf("replace ethernet header\n");
		hdr = (struct ether_header *)(m->m_data - ETHER_HDR_LEN);
		*hdr = nh->hdr;
		m->m_data -= ETHER_HDR_LEN;
		//printf("if_output skip returning...\n");
		return;
	}

	//printf("no cache and go to if_output\n");

	/*
	 * Send the packet on its way.
	 */
	if ((dst_ifp->if_output)(dst_ifp, m,
	    (struct sockaddr *) &dst_sin, NULL) != 0) {
		dxr_stats.output_errs++;
		if (m->m_flags & M_VALE)
			m->m_pkthdr.PH_loc.ptr = NULL; /* reset destination */
	} else
		dxr_stats.fastpath++;
}


#if defined(RADIX_TIMING) || defined(DXR_LOOKUP_CONSISTENCY_CHECK)
#ifdef PROPERLY_LOCKED_AND_REFCOUNTED_RADIX_LOOKUPS
static int
radix_lookup(uint32_t dst)
{
	struct route ro;
	struct rtentry *rt;
	struct sockaddr_in *sin = (struct sockaddr_in *) &ro.ro_dst;
	int nh = 0;

	ro.ro_rt = NULL;
	sin->sin_family = AF_INET;
	sin->sin_len = sizeof(*sin);
	sin->sin_addr.s_addr = htonl(dst);

	rtalloc_ign(&ro, 0);
	if ((rt = ro.ro_rt) != NULL) {
		nh = rt->rt_dxr_nexthop;
		RTFREE(ro.ro_rt);
	} else
		nh = 0; /* Discard port (or default route) */

	return (nh);
}
#else
static int
radix_lookup(uint32_t dst)
{
	struct rib_head *rnh = rt_tables_get_rnh(0, AF_INET);
	struct radix_node *rn;
	struct rtentry *rt;
	struct sockaddr_in sin;

	sin.sin_family = AF_INET;
	sin.sin_len = sizeof(sin);
	sin.sin_addr.s_addr = htonl(dst);

	rn = rnh->rnh_matchaddr(&sin, &rnh->head);
        if (rn && ((rn->rn_flags & RNF_ROOT) == 0)) {
                rt = (struct rtentry *) rn;
		return (rt->rt_dxr_nexthop);
        } else
		return (0); /* Discard port (or default route) */
}
#endif
#endif /* RADIX_TIMING || DXR_LOOKUP_CONSISTENCY_CHECK */


static int
dxr_lookup(uint32_t dst)
{
	register uint32_t *fdescp;
	register int32_t nh;
	register uint32_t masked_dst;
	register uint32_t upperbound;
	register uint32_t middle;
	register uint32_t lowerbound;
#ifdef DXR_ITER_TIMING
	uint32_t iters = 0;
	uint64_t timer = rdtsc();
#define	INCR_ITERS()	iters++;
#else
#define	INCR_ITERS()
#endif

	masked_dst = dst & DXR_RANGE_MASK;
	fdescp = (uint32_t *) &direct_tbl[dst >> DXR_RANGE_SHIFT];

	lowerbound = *fdescp;
	nh = lowerbound >> (32 - DESC_BASE_BITS); /* nh == .base */
	if (nh != BASE_MAX) {
		/*
		 * Binary search for a matching range - the magic
		 * happens here in this simple loop (unrolling is
		 * just an optimization).
		 */
		#define	DXR_LOOKUP_STAGE				 \
			INCR_ITERS();					 \
			if (masked_dst < range[middle].start) {		 \
				upperbound = middle;			 \
				middle = (middle + lowerbound) / 2;	 \
			} else if (masked_dst < range[middle + 1].start) { \
				lowerbound = middle;			 \
				break;					 \
			} else {					 \
				lowerbound = middle + 1;		 \
				middle = (upperbound + middle + 1) / 2;	\
			}						 \
			if (upperbound == lowerbound)			 \
				break;

		if (lowerbound & 0x1000) { /* .long_format set? */
			register struct range_entry_long *range;

			upperbound = lowerbound & 0xfff; /* .fragments */
			range = &range_tbl[nh]; /* nh == .base */
			middle = upperbound / 2;
			lowerbound = 0;

			do {
				DXR_LOOKUP_STAGE
				DXR_LOOKUP_STAGE
				DXR_LOOKUP_STAGE
				DXR_LOOKUP_STAGE
				DXR_LOOKUP_STAGE
				DXR_LOOKUP_STAGE
				DXR_LOOKUP_STAGE
				DXR_LOOKUP_STAGE
				DXR_LOOKUP_STAGE
				DXR_LOOKUP_STAGE
				DXR_LOOKUP_STAGE
				DXR_LOOKUP_STAGE
			} while (1);
			nh = range[lowerbound].nexthop;
		} else {
			register struct range_entry_short *range;

			middle = lowerbound & 0xfff; /* .fragments */
			masked_dst >>= 8;
			range = (struct range_entry_short *) &range_tbl[nh];
			upperbound = middle * 2 + 1;
			lowerbound = 0;

			do {
				DXR_LOOKUP_STAGE
				DXR_LOOKUP_STAGE
				DXR_LOOKUP_STAGE
				DXR_LOOKUP_STAGE
				DXR_LOOKUP_STAGE
				DXR_LOOKUP_STAGE
				DXR_LOOKUP_STAGE
				DXR_LOOKUP_STAGE
			} while (1);
			nh = range[lowerbound].nexthop;
		}

		#undef DXR_LOOKUP_STAGE
	} else {
		/* nexthop is encoded in the fragments field */
		nh = lowerbound & 0xfff; /* XXX hardcoded - revisit this!!! */
	}

#ifdef DXR_ITER_TIMING
	timer = rdtsc() - timer;
	if (DPCPU_GET(valid_timing)) {
		int cpuid = PCPU_GET(cpuid);
		iter_stats[cpuid][iters].cnt++;
		iter_stats[cpuid][iters].cycles += timer - rdtsc_latency;
	}
#endif
	return (nh);
}


/*
 * Control plane interface / support.
 *
 * XXX should we catch RTM_CHANGE messages here?
 */
void
dxr_request(struct rtentry *rt, int req)
{
	struct sockaddr *dst = rt_key(rt);
	struct sockaddr *mask = rt_mask(rt);
	struct sockaddr_in *in_gw = SIN(rt->rt_gateway);
	int rt_flags = rt->rt_flags;
	int refs;
#ifdef DXR_BUILD_TIMING
	uint64_t timer;
	int preflen;

	if (mask) {
		preflen = ffs(ntohl(SIN(mask)->sin_addr.s_addr));
		if (preflen)
			preflen = 33-preflen;
	} else
		preflen = 32;
	timer = rdtsc();
#endif

	/* Fast-path DXR available only in vnet0 */
	if (!IS_DEFAULT_VNET(curvnet))
		return;

	/* Fast-path DXR available only for table #0 */
	if (rt->rt_fibnum != 0)
		panic("rt->rt_fibnum = %d", rt->rt_fibnum);

	if (dst->sa_family != AF_INET)
		return;

	RIB_LOCK_ASSERT(rt_tables_get_rnh(0, AF_INET));

	switch(req) {
	case RTM_DELETE:
		if (rt_flags & RTF_LLINFO)
			panic("RTM_DELETE with RTF_LLINFO");

		routes--;

		if (mask && SIN(mask)->sin_addr.s_addr == 0) {
			/* Default route removal */
			nexthop_tbl[0].ifp = NULL;
			nexthop_tbl[0].gw.s_addr = 0;
			break;
		}

#ifdef DXR_BUILD_DEBUG
		print_in_route(rt, "RTM_DELETE");
#endif

		refs = nexthop_unref(rt->rt_dxr_nexthop);
		schedule_update(rt);
		/*
		 * If we have deleted the last reference to a nexthop,
		 * we have to forcibly apply all pending changes to the
		 * FIB, otherwise we might leave a stale pointer there
		 * to a now nonexisting nexthop.
		 */
		if (refs == 0 || async_updates == 0)
			apply_pending();
#ifdef DXR_BUILD_TIMING
		timer = rdtsc() - timer;
		if (async_updates == 0) {
			update_stats[preflen].cnt++;
			update_stats[preflen].cycles += timer;
		}
#endif
		break;

	case RTM_ADD:
		if (rt_flags & RTF_LLINFO)
			panic("RTM_ADD with RTF_LLINFO");

		routes++;

		if (mask && SIN(mask)->sin_addr.s_addr == 0) {
			/* Default route insertion */
			nexthop_tbl[0].ifp = rt->rt_ifp;
			nexthop_tbl[0].gw = in_gw->sin_addr;
			break;
		}

		if (in_gw->sin_family != AF_INET )
			rt->rt_dxr_nexthop = nexthop_ref((struct in_addr) {0},
							rt->rt_ifp);
		else
			rt->rt_dxr_nexthop = nexthop_ref(in_gw->sin_addr,
							rt->rt_ifp);

#ifdef DXR_BUILD_DEBUG
		print_in_route(rt, "RTM_ADD");
#endif

		schedule_update(rt);
		if (async_updates == 0) {
			apply_pending();
			if (!LIST_EMPTY(&unused_chunks))
				prune_empty_chunks();
		}
#ifdef DXR_BUILD_TIMING
		timer = rdtsc() - timer;
		if (async_updates == 0) {
			update_stats[preflen].cnt++;
			update_stats[preflen].cycles += timer;
		}
#endif
		break;
	default:
#ifdef DXR_BUILD_DEBUG
		print_in_route(rt, "unsupported!");
#endif
		panic("don't know how to handle request %d", req);
	}
}


static void
dxr_initheap(dst, chunk)
	uint32_t dst;
	uint32_t chunk;
{
	struct route start_ro;
	struct rtentry *rt;
	struct sockaddr_in *sin = (struct sockaddr_in *) &start_ro.ro_dst;
	struct dxr_heap_entry *fhp = &dxr_heap[0];

	heap_index = 0;

	start_ro.ro_rt = NULL;
	sin->sin_family = AF_INET;
	sin->sin_len = sizeof(*sin);
	sin->sin_addr.s_addr = htonl(dst);

	RIB_LOCK_ASSERT(rt_tables_get_rnh(0, AF_INET));
	in_rtalloc_ign(&start_ro, RTF_RNH_LOCKED, 0);

	if ((rt = start_ro.ro_rt)) {
		struct sockaddr_in *dst = (struct sockaddr_in *)rt_key(rt);
		struct sockaddr_in *mask = (struct sockaddr_in *)rt_mask(rt);

		fhp->start = ntohl(dst->sin_addr.s_addr);

		if (mask) {
			fhp->preflen = ffs(ntohl(mask->sin_addr.s_addr));
			if (fhp->preflen)
				fhp->preflen = 33 - fhp->preflen;
			fhp->end = fhp->start | ~ntohl(mask->sin_addr.s_addr);
		} else {
			fhp->preflen = 32;
			fhp->end = fhp->start;
		}
		fhp->nexthop = rt->rt_dxr_nexthop;
		RTFREE(start_ro.ro_rt);
#ifdef DXR_BUILD_DEBUG
		print_in_route(rt, "  initheap");
#endif
	} else {
		fhp->start = 0;
		fhp->end = 0xffffffff;
		fhp->preflen = 0;
		fhp->nexthop = 0;
#ifdef DXR_BUILD_DEBUG
		printf("  initheap: DEFAULT\n");
#endif
	}
}


static void
schedule_update(struct rtentry *rt)
{
	struct sockaddr_in *dst = (struct sockaddr_in *)rt_key(rt);
	struct sockaddr_in *mask = (struct sockaddr_in *)rt_mask(rt);
	uint32_t start, end;
	int preflen, chunk;

	if (!dxr_enable)
		return;

	start = ntohl(dst->sin_addr.s_addr);
	if (mask) {
		preflen = ffs(ntohl(mask->sin_addr.s_addr));
		if (preflen)
			preflen = 33 - preflen;
		end = start | ~ntohl(mask->sin_addr.s_addr);
	} else {
		preflen = 32;
		end = start;
	}

	start = start >> DXR_RANGE_SHIFT;
	end = end >> DXR_RANGE_SHIFT;
	for (chunk = start; chunk <= end; chunk++)
		pending_bitmask[chunk >> 5] |= (1 << (chunk & 0x1f));
	if (start < pending_start)
		pending_start = start;
	if (end > pending_end)
		pending_end = end;
	updates_pending++;
}


static void
dxr_check_tables()
{
	int i, nh;
	int error;

	for (i = 0; i < DIRECT_TBL_SIZE; i++) {
		error = 0;
		nh = -1;
		if (direct_tbl[i].base == BASE_MAX) {
			/* Nexthop is directly resolvable */
			nh = direct_tbl[i].fragments;
			if (nh >= nexthop_tbl_size) {
				/* Nexthop index out of range */
				error = 1;
				goto report_err;
			}
			continue;
		}
report_err:
		if (error)
			printf("i = %d nh = %d err = %d\n", i, nh, error);
	}
}


static void
dxr_updater(void *arg)
{
	int last_pending = 0;
#ifdef DXR_BUILD_TIMING
	uint64_t timer;
	int i, j;
#endif

	/* DXR works always and only in vnet0 */
	CURVNET_SET(vnet0);

	for (;;) {
		pause("-", hz / 4);

#if defined(DXR_LOOKUP_TIMING) || defined(DXR_ITER_TIMING) || defined(RADIX_TIMING)
		/* Reduce random keys to those resolvable by binary search */
		if (dlp != NULL && updates_pending == 0 &&
		    routes > 400000 && reduce) {
			uint32_t dst;
			for (i = 0; i < DUMMY_MEM_SIZE; i++) {
				for (dst = dlp[i];
				    direct_tbl[dst >> DXR_RANGE_SHIFT
				      ].base == BASE_MAX ||
				    dst >> 24 == 0 || dst >> 24 == 10 || 
				    dst >> 24 == 127 || dst >> 24 >= 224;
				    dlp[i] = dst) {
					dst = arc4random();
				}
			}
			reduce = 0;
		}
#endif

		if (async_updates) {
			RIB_RLOCK(rt_tables_get_rnh(0, AF_INET));
			if (updates_pending &&
			    updates_pending == last_pending) {
#ifdef DXR_BUILD_TIMING
				timer = rdtsc();
#endif
				apply_pending();
				if (!LIST_EMPTY(&unused_chunks))
					prune_empty_chunks();
#ifdef DXR_BUILD_TIMING
				timer = rdtsc() - timer;
				timer = timer * 1000000 / tsc_freq;
				printf("FIB updated: %u prefixes in %u.%03u"
				    " ms\n", updates_pending,
				    (int) (timer / 1000), (int) (timer % 1000));
				j = 0;
				for (i = 0; i < DIRECT_TBL_SIZE; i++)
					if (direct_tbl[i].base == BASE_MAX)
						j++;
				printf("FIB rebuilt, %d descriptors,"
				    " %d directly resolvable\n",
				    DIRECT_TBL_SIZE, j);
#endif
				dxr_check_tables();
				updates_pending = 0;
#ifdef DIR_24_8
				dir_24_8_rebuild();
#endif
			} 
			last_pending = updates_pending;
			RIB_RUNLOCK(rt_tables_get_rnh(0, AF_INET));
		}
	}

	/* Notreached */
}


static void
prune_empty_chunks(void)
{
	struct chunk_desc *cdp1, *cdp2;
	int chunk, from, to, len;

	for (cdp1 = LIST_FIRST(&unused_chunks); cdp1 != NULL;
	    cdp1 = LIST_FIRST(&unused_chunks)) {
		from = cdp1->cd_base + cdp1->cd_max_size;
		to = cdp1->cd_base;
		cdp2 = LIST_NEXT(cdp1, cd_hash_le);
		if (cdp2 != NULL) {
	 		/* Case A: more than one chunk */
			len = cdp2->cd_base - from;
			cdp2->cd_max_size += cdp1->cd_max_size;
		} else {
			/* Single empty chunk found */
			cdp2 = LIST_FIRST(&all_chunks);
			if (cdp1 != cdp2) {
	 			/* Case B: not the last chunk on the heap */
				len = range_tbl_free - from;
				range_tbl_free -= cdp1->cd_max_size;
			} else {
				/* Case C: is the last chunk on the heap */
				range_tbl_free -= cdp1->cd_max_size;
				LIST_REMOVE(cdp1, cd_all_le);
				LIST_REMOVE(cdp1, cd_hash_le);
				uma_zfree(chunk_zone, cdp1);
				break;
			}
		}
		bcopy(&range_tbl[from], &range_tbl[to],
		    len * sizeof(*range_tbl));
		do  {
			cdp2->cd_base -= cdp1->cd_max_size;
			for (chunk = cdp2->cd_chunk_first; chunk >= 0;
			    chunk = cptbl[chunk].cp_chunk_next)
				if (direct_tbl[chunk].base != BASE_MAX)
					direct_tbl[chunk].base -=
					    cdp1->cd_max_size;
			cdp2 = LIST_NEXT(cdp2, cd_all_le);
		} while (cdp2 != cdp1);
		LIST_REMOVE(cdp1, cd_all_le);
		LIST_REMOVE(cdp1, cd_hash_le);
		uma_zfree(chunk_zone, cdp1);
	}
}


static uint32_t
chunk_hash(struct direct_entry *fdesc)
{
	uint32_t *p = (uint32_t *) &range_tbl[fdesc->base];
	uint32_t *l =
	    (uint32_t *) &range_tbl[fdesc->base + fdesc->fragments];
	uint32_t hash = fdesc->fragments;

	for (; p <= l; p++)
		hash = (hash << 1) + (hash >> 1) + *p;

	return (hash + (hash >> 16));
}


static void
chunk_ref(int chunk)
{
	struct direct_entry *fdesc = &direct_tbl[chunk];
	struct chunk_desc *cdp, *empty_cdp;
	uint32_t hash = chunk_hash(fdesc);
	int base = fdesc->base;
	int size = fdesc->fragments + 1;

	/* Find an already existing chunk descriptor */
	LIST_FOREACH(cdp, &chunk_hashtbl[hash & CHUNK_HASH_MASK], cd_hash_le) {
		if (cdp->cd_hash == hash && cdp->cd_cur_size == size &&
		    memcmp(&range_tbl[base], &range_tbl[cdp->cd_base],
		    sizeof(struct range_entry_long) * size) == 0) {
			cdp->cd_refcount++;
			fdesc->base = cdp->cd_base;
			if (fdesc->long_format) {
				aggr_chunks_long++;
				aggr_fragments_long += size;
				chunks_long--;
				fragments_long -= size;
			} else {
				aggr_chunks_short++;
				aggr_fragments_short += (size << 1);
				chunks_short--;
				fragments_short -= (size << 1);
			}
			range_tbl_free -= size;
			/* Link in the chunk */
			cptbl[chunk].cp_cdp = cdp;
			cptbl[chunk].cp_chunk_next = cdp->cd_chunk_first;
			cdp->cd_chunk_first = chunk;
			return;
		}
	}

	/* No matching chunks found. Recycle an empty or allocate a new one */
	cdp = NULL;
	LIST_FOREACH(empty_cdp, &unused_chunks, cd_hash_le) {
		if (empty_cdp->cd_max_size >= size &&
		    (cdp == NULL ||
		    empty_cdp->cd_max_size < cdp->cd_max_size)) {
			cdp = empty_cdp;
			if (empty_cdp->cd_max_size == size)
				break;
		}
	}

	if (cdp != NULL) {
		/* Copy from heap into the recycled chunk */
		bcopy(&range_tbl[fdesc->base], &range_tbl[cdp->cd_base],
		    size * sizeof(struct range_entry_long));
		fdesc->base = cdp->cd_base;
		range_tbl_free -= size;
		if (cdp->cd_max_size > size + 0) { /* XXX hardcoded const! */
			/* Alloc a new (empty) descriptor */
			empty_cdp = uma_zalloc(chunk_zone, M_NOWAIT);
			if (empty_cdp == NULL)
				panic("%s %d\n", __func__, __LINE__);
			empty_cdp->cd_max_size = cdp->cd_max_size - size;
			empty_cdp->cd_base = cdp->cd_base + size;
			empty_cdp->cd_chunk_first = -1;
			empty_cdp->cd_cur_size = 0;
			LIST_INSERT_BEFORE(cdp, empty_cdp, cd_all_le);
			LIST_INSERT_AFTER(cdp, empty_cdp, cd_hash_le);
			cdp->cd_max_size = size;
		}
		LIST_REMOVE(cdp, cd_hash_le);
	} else {
		/* Alloc a new descriptor */
		cdp = uma_zalloc(chunk_zone, M_NOWAIT);
		if (cdp == NULL)
			panic("%s %d\n", __func__, __LINE__);
		cdp->cd_max_size = size;
		cdp->cd_base = fdesc->base;
		LIST_INSERT_HEAD(&all_chunks, cdp, cd_all_le);
	}

	cdp->cd_hash = hash;
	cdp->cd_refcount = 1;
	cdp->cd_cur_size = size;
	cdp->cd_chunk_first = chunk;
	cptbl[chunk].cp_cdp = cdp;
	cptbl[chunk].cp_chunk_next = -1;
	LIST_INSERT_HEAD(&chunk_hashtbl[hash & CHUNK_HASH_MASK], cdp,
	    cd_hash_le);
}


static void
chunk_unref(int chunk)
{
	struct direct_entry *fdesc = &direct_tbl[chunk];
	struct chunk_desc *cdp = cptbl[chunk].cp_cdp;
	struct chunk_desc *unused_cdp;
	int size = fdesc->fragments + 1;
	int i;

	if (--cdp->cd_refcount > 0) {
		if (fdesc->long_format) {
			aggr_fragments_long -= size;
			aggr_chunks_long--;
		} else {
			aggr_fragments_short -= (size << 1);
			aggr_chunks_short--;
		}
		/* Unlink chunk */
		if (cdp->cd_chunk_first == chunk) {
			cdp->cd_chunk_first = cptbl[chunk].cp_chunk_next;
		} else {
			for (i = cdp->cd_chunk_first;
			    cptbl[i].cp_chunk_next != chunk;
			    i = cptbl[i].cp_chunk_next) {};
			cptbl[i].cp_chunk_next = cptbl[chunk].cp_chunk_next;
		}
		return;
	}

	LIST_REMOVE(cdp, cd_hash_le);
	cdp->cd_chunk_first = -1;
	cdp->cd_cur_size = 0;

	/* Keep unused chunks sorted with ascending base indices */
	if (LIST_EMPTY(&unused_chunks))
		LIST_INSERT_HEAD(&unused_chunks, cdp, cd_hash_le);
	else LIST_FOREACH(unused_cdp, &unused_chunks, cd_hash_le) {
		if (unused_cdp->cd_base > cdp->cd_base) {
			LIST_INSERT_BEFORE(unused_cdp, cdp, cd_hash_le);
			break;
		}
		if (LIST_NEXT(unused_cdp, cd_hash_le) == NULL) {
			LIST_INSERT_AFTER(unused_cdp, cdp, cd_hash_le);
			break;
		}
	}

	/* Merge adjacent empty chunks */
	if ((unused_cdp = LIST_NEXT(cdp, cd_all_le)) != NULL &&
	    cdp == LIST_NEXT(unused_cdp, cd_hash_le)) {
		LIST_REMOVE(cdp, cd_hash_le);
		LIST_REMOVE(cdp, cd_all_le);
		unused_cdp->cd_max_size += cdp->cd_max_size;
		uma_zfree(chunk_zone, cdp);
		cdp = unused_cdp;
	}
	if ((unused_cdp = LIST_NEXT(cdp, cd_hash_le)) != NULL &&
	    cdp == LIST_NEXT(unused_cdp, cd_all_le)) {
		LIST_REMOVE(unused_cdp, cd_hash_le);
		LIST_REMOVE(unused_cdp, cd_all_le);
		cdp->cd_max_size += unused_cdp->cd_max_size;
		uma_zfree(chunk_zone, unused_cdp);
	}

	if (fdesc->long_format) {
		chunks_long--;
		fragments_long -= size;
	} else {
		chunks_short--;
		fragments_short -= (size << 1);
	}
}


static void
update_chunk(int chunk)
{
	struct rib_head *rnh = rt_tables_get_rnh(0, AF_INET);
	struct sockaddr_in dst, mask;
	struct direct_entry *fdesc = &direct_tbl[chunk];
	struct range_entry_short *fp;
	struct dxr_heap_entry *fhp;
	uint32_t first = chunk << DXR_RANGE_SHIFT;
	uint32_t last = first | DXR_RANGE_MASK;

#ifdef DXR_BUILD_DEBUG
	printf("Updating chunk %05X\n", chunk);
#endif

	dxr_initheap(first, chunk);

	if (fdesc->base < BASE_MAX)
		chunk_unref(chunk);

	fdesc->base = range_tbl_free;
	fdesc->fragments = 0;
	fdesc->long_format = 0;

	fp = (struct range_entry_short *) &range_tbl[range_tbl_free];
	fp->start = (first & DXR_RANGE_MASK) >> 8;
	fp->nexthop = dxr_heap[0].nexthop;

	dst.sin_family = AF_INET;
	dst.sin_len = sizeof(dst);
	dst.sin_addr.s_addr = htonl(first);
	mask.sin_family = AF_INET;
	mask.sin_len = sizeof(mask);
	mask.sin_addr.s_addr = htonl(~DXR_RANGE_MASK);

	if (rnh->rnh_walktree_from(&rnh->head, &dst, &mask, dxr_walk,
	    (void *) (long) chunk) == ERANGE) {
		update_chunk_long(chunk);
		return;
	}

	/* Flush any remaining objects on the dxr_heap */
	fp = (struct range_entry_short *) &range_tbl[range_tbl_free] +
	    fdesc->fragments;
	fhp = &dxr_heap[heap_index];
	while (fhp->preflen > DXR_DIRECT_BITS) {
		int oend = fhp->end;
#ifdef DXR_BUILD_DEBUG
		printf("  flushing heap, preflen=%d\n", fhp->preflen);
#endif

		if (heap_index > 0) {
			fhp--;
			heap_index--;
		} else
			dxr_initheap(fhp->end + 1, chunk);
		if (fhp->end > oend && fhp->nexthop != fp->nexthop) {
			/* Have we crossed the upper chunk boundary? */
			if (oend >= last)
				break;
			fp++;
			fdesc->fragments++;
			fp->start = ((oend + 1) & DXR_RANGE_MASK) >> 8;
			fp->nexthop = fhp->nexthop;
		}
	}
#ifdef DXR_BUILD_DEBUG
	dxr_heap_dump();
	dxr_chunk_dump(chunk);
#endif
	/*
	 * If the chunk contains only a single fragment, encode
	 * nexthop in the fragments field of the direct lookup table.
	 * In such a case we do not need to store the original chunk
	 * itself any more.
	 *
	 * The actual number of fragments is fdesc->fragments + 1.
	 */
	if (fdesc->fragments) {
		if ((fdesc->fragments & 1) == 0) {
			/* Align mpool_free on a 32 bit boundary */
			fp[1].start = fp->start;
			fp[1].nexthop = fp->nexthop;
			fdesc->fragments++;
		};
		chunks_short++;
		fragments_short += (fdesc->fragments + 1);
		fdesc->fragments >>= 1;
		range_tbl_free += (fdesc->fragments + 1);
		chunk_ref(chunk);
	} else {
		fdesc->base = BASE_MAX;
		fdesc->fragments = fp->nexthop;
	}

	pending_bitmask[chunk >> 5] &= ~(1 << (chunk & 0x1f));
}


static void
update_chunk_long(int chunk)
{
	struct rib_head *rnh = rt_tables_get_rnh(0, AF_INET);
	struct sockaddr_in dst, mask;
	struct direct_entry *fdesc = &direct_tbl[chunk];
	struct range_entry_long *fp;
	struct dxr_heap_entry *fhp;
	uint32_t first = chunk << DXR_RANGE_SHIFT;
	uint32_t last = first | DXR_RANGE_MASK;

#ifdef DXR_BUILD_DEBUG
	printf("Updating chunk %05X\n", chunk);
#endif

	dxr_initheap(first, chunk);

	fdesc->base = range_tbl_free;
	fdesc->fragments = 0;
	fdesc->long_format = 1;

	fp = &range_tbl[range_tbl_free];
	fp->start = first & DXR_RANGE_MASK;
	fp->nexthop = dxr_heap[0].nexthop;

	dst.sin_family = AF_INET;
	dst.sin_len = sizeof(dst);
	dst.sin_addr.s_addr = htonl(first);
	mask.sin_family = AF_INET;
	mask.sin_len = sizeof(mask);
	mask.sin_addr.s_addr = htonl(~DXR_RANGE_MASK);

	rnh->rnh_walktree_from(&rnh->head, &dst, &mask, dxr_walk_long,
	    (void *) (long) chunk);

	/* Flush any remaining objects on the dxr_heap */
	fp = &range_tbl[fdesc->base + fdesc->fragments];
	fhp = &dxr_heap[heap_index];
	while (fhp->preflen > DXR_DIRECT_BITS) {
		int oend = fhp->end;
#ifdef DXR_BUILD_DEBUG
		printf("  flushing heap, preflen=%d\n", fhp->preflen);
#endif

		if (heap_index > 0) {
			fhp--;
			heap_index--;
		} else
			dxr_initheap(fhp->end + 1, chunk);
		if (fhp->end > oend && fhp->nexthop != fp->nexthop) {
			/* Have we crossed the upper chunk boundary? */
			if (oend >= last)
				break;
			fp++;
			fdesc->fragments++;
			fp->start = (oend + 1) & DXR_RANGE_MASK;
			fp->nexthop = fhp->nexthop;
		}
	}
#ifdef DXR_BUILD_DEBUG
	dxr_heap_dump();
	dxr_chunk_dump(chunk);
#endif
	/*
	 * If the chunk contains only a single fragment, encode
	 * nexthop in the fragments field of the direct lookup table.
	 * In such a case we do not need to store the original chunk
	 * itself any more.
	 */
	if (fdesc->fragments) {
		chunks_long++;
		fragments_long += (fdesc->fragments + 1);
		range_tbl_free += (fdesc->fragments + 1);
		chunk_ref(chunk);
	} else {
		fdesc->base = BASE_MAX;
		fdesc->fragments = fp->nexthop;
	}

	pending_bitmask[chunk >> 5] &= ~(1 << (chunk & 0x1f));
}


static int
dxr_walk(struct radix_node *rn, void *arg)
{
	struct rtentry *rt = (struct rtentry *)rn;
	struct sockaddr_in *dst = (struct sockaddr_in *)rt_key(rt);
	struct sockaddr_in *mask = (struct sockaddr_in *)rt_mask(rt);
	uint32_t start, end;
	int chunk = (long) arg;
	int preflen, nh;

#ifdef DXR_BUILD_DEBUG
	print_in_route(rt, "  dxr_walk");
#endif

	start = ntohl(dst->sin_addr.s_addr);
	if (mask) {
		preflen = ffs(ntohl(mask->sin_addr.s_addr));
		if (preflen)
			preflen = 33 - preflen;
		end = start | ~ntohl(mask->sin_addr.s_addr);
	} else {
		preflen = 32;
		end = start;
	}
	nh = rt->rt_dxr_nexthop;

	return(dxr_parse(rt, chunk, start, end, preflen, nh));
}


static int
dxr_walk_long(struct radix_node *rn, void *arg)
{
	struct rtentry *rt = (struct rtentry *)rn;
	struct sockaddr_in *dst = (struct sockaddr_in *)rt_key(rt);
	struct sockaddr_in *mask = (struct sockaddr_in *)rt_mask(rt);
	uint32_t start, end;
	int chunk = (long) arg;
	int preflen, nh;

#ifdef DXR_BUILD_DEBUG
	print_in_route(rt, "  dxr_walk_long");
#endif

	start = ntohl(dst->sin_addr.s_addr);
	if (mask) {
		preflen = ffs(ntohl(mask->sin_addr.s_addr));
		if (preflen)
			preflen = 33 - preflen;
		end = start | ~ntohl(mask->sin_addr.s_addr);
	} else {
		preflen = 32;
		end = start;
	}
	nh = rt->rt_dxr_nexthop;

	return(dxr_parse_long(rt, chunk, start, end, preflen, nh));
}


static void __inline
dxr_heap_inject(uint32_t start, uint32_t end, int preflen, int nh)
{
	struct dxr_heap_entry *fhp;
	int i;

	for (i = heap_index; i >= 0; i--) {
		if (preflen > dxr_heap[i].preflen)
			break;
		else if (preflen < dxr_heap[i].preflen) {
			bcopy(&dxr_heap[i], &dxr_heap[i+1],
			    sizeof(struct dxr_heap_entry));
		} else
			return;
	}

	fhp = &dxr_heap[i + 1];
	fhp->preflen = preflen;
	fhp->start = start;
	fhp->end = end;
	fhp->nexthop = nh;
	heap_index++;
}


static int
dxr_parse(struct rtentry *rt, int chunk, uint32_t start, uint32_t end,
    int preflen, int nh)
{
	struct direct_entry *fdesc = &direct_tbl[chunk];
	struct range_entry_short *fp = (struct range_entry_short *)
					&range_tbl[fdesc->base] +
					fdesc->fragments;
	struct dxr_heap_entry *fhp = &dxr_heap[heap_index];
	uint32_t first = chunk << DXR_RANGE_SHIFT;
	uint32_t last = first | DXR_RANGE_MASK;

	if (start > last)
		return -1;	/* Beyond chunk boundaries, we are done */
	if (start < first)
		return 0;	/* Skip this route */

#ifdef DXR_BUILD_DEBUG
	printf("  dxr_parse %08X..%08X plen %d nexthop %d\n",
		start, end, preflen, nh);
#endif

	/* Switch to long format if needed */
	if ((start & 0xff) || end < (start | 0xff) || nh > 0xff)
		return ERANGE;

	if (start == fhp->start) {
#ifdef DXR_BUILD_PARANOIC
		if (preflen > fhp->preflen) {
			/* This MUST NEVER happen! */
			panic("XXX dxr_parse #1\n");
			fp->nexthop = nh;
		}
#endif
		dxr_heap_inject(start, end, preflen, nh);
#ifdef DXR_BUILD_PARANOIC
	} else if (start < fhp->start) {
		/* This MUST NEVER happen! */
		panic("XXX dxr_parse #2\n");
#endif
	} else {
		/* start > fhp->start */
		while (start > fhp->end) {
			int oend = fhp->end;

			if (heap_index > 0) {
				fhp--;
				heap_index--;
			} else
				dxr_initheap(fhp->end + 1, chunk);
			if (fhp->end > oend && fhp->nexthop != fp->nexthop) {
				fp++;
				fdesc->fragments++;
				fp->start =
				    ((oend + 1) & DXR_RANGE_MASK) >> 8;
				fp->nexthop = fhp->nexthop;
			}
		}
		if (start > ((chunk << DXR_RANGE_SHIFT) | (fp->start << 8))
		    && nh != fp->nexthop) {
			fp++;
			fdesc->fragments++;
			fp->start = (start & DXR_RANGE_MASK) >> 8;
		} else if (fdesc->fragments) {
			if ((--fp)->nexthop == nh)
				fdesc->fragments--;
			else
				fp++;
		}
		fp->nexthop = nh;
		dxr_heap_inject(start, end, preflen, nh);
	}

#ifdef DXR_BUILD_DEBUG
	dxr_heap_dump();
	dxr_chunk_dump(chunk);
#endif
	return 0;
}


static int
dxr_parse_long(struct rtentry *rt, int chunk, uint32_t start, uint32_t end,
    int preflen, int nh)
{
	struct direct_entry *fdesc = &direct_tbl[chunk];
	struct range_entry_long *fp =
	    &range_tbl[fdesc->base + fdesc->fragments];
	struct dxr_heap_entry *fhp = &dxr_heap[heap_index];
	uint32_t first = chunk << DXR_RANGE_SHIFT;
	uint32_t last = first | DXR_RANGE_MASK;

	if (start > last)
		return -1;	/* Beyond chunk boundaries, we are done */
	if (start < first)
		return 0;	/* Skip this route */

#ifdef DXR_BUILD_DEBUG
	printf("  dxr_parse %08X..%08X plen %d nexthop %d\n",
		start, end, preflen, nh);
#endif

	if (start == fhp->start) {
#ifdef DXR_BUILD_PARANOIC
		if (preflen > fhp->preflen) {
			/* This MUST NEVER happen! */
			printf("XXX dxr_parse #1\n");
			fp->nexthop = nh;
		}
#endif
		dxr_heap_inject(start, end, preflen, nh);
#ifdef DXR_BUILD_PARANOIC
	} else if (start < fhp->start) {
		/* This MUST NEVER happen! */
		printf("XXX dxr_parse #2\n");
#endif
	} else {
		/* start > fhp->start */
		while (start > fhp->end) {
			int oend = fhp->end;

			if (heap_index > 0) {
				fhp--;
				heap_index--;
			} else
				dxr_initheap(fhp->end + 1, chunk);
			if (fhp->end > oend && fhp->nexthop != fp->nexthop) {
				fp++;
				fdesc->fragments++;
				fp->start = (oend + 1) & DXR_RANGE_MASK;
				fp->nexthop = fhp->nexthop;
			}
		}
		if (start > ((chunk << DXR_RANGE_SHIFT) | fp->start) &&
		    nh != fp->nexthop) {
			fp++;
			fdesc->fragments++;
			fp->start = start & DXR_RANGE_MASK;
		} else if (fdesc->fragments) {
			if ((--fp)->nexthop == nh)
				fdesc->fragments--;
			else
				fp++;
		}
		fp->nexthop = nh;
		dxr_heap_inject(start, end, preflen, nh);
	}

#ifdef DXR_BUILD_DEBUG
	dxr_heap_dump();
	dxr_chunk_dump(chunk);
#endif
	return 0;
}

void
apply_pending()
{
	uint32_t i, j, mask, bit;

	RIB_LOCK_ASSERT(rt_tables_get_rnh(0, AF_INET));

	for (i = pending_start >> 5; i <= pending_end >> 5; i++) {
		mask = pending_bitmask[i];
		if (mask)
			for (j = 0, bit = 1; j < 32; j++) {
				if ((mask & bit))
					update_chunk((i << 5) + j);
				bit += bit; /* bit <<= 1 */
			}
	}
	pending_start = DIRECT_TBL_SIZE;
	pending_end = 0;
}


static uint16_t
nexthop_ref(struct in_addr gw, struct ifnet *ifp)
{
	int16_t nh_i;

	RIB_LOCK_ASSERT(rt_tables_get_rnh(0, AF_INET));

	/* Search for an existing entry */
	for (nh_i = nexthop_head; nh_i >= 0; nh_i = nexthop_tbl[nh_i].ll_next)
		if (gw.s_addr == nexthop_tbl[nh_i].gw.s_addr &&
		    ifp == nexthop_tbl[nh_i].ifp)
			break;

	if (nh_i >= 0)
		nexthop_tbl[nh_i].refcount++;
	else {
		/* The ifnet must not disappear as long as the nexthop exists */
		if_ref(ifp);

		/* Create a new nexthop entry */
		if (nexthop_empty_head >= 0) {
			nh_i = nexthop_empty_head;
			nexthop_empty_head = nexthop_tbl[nh_i].ll_next;
		} else
			nh_i = nexthop_tbl_size++;
		nexthops++;

		nexthop_tbl[nh_i].refcount = 1;
		nexthop_tbl[nh_i].gw = gw;
		nexthop_tbl[nh_i].ifp = ifp;

		/* Add the entry to the nexthop linked list */
		nexthop_tbl[nh_i].ll_prev = -1;
		nexthop_tbl[nh_i].ll_next = nexthop_head;
		if (nexthop_head >= 0)
			nexthop_tbl[nexthop_head].ll_prev = nh_i;
		nexthop_head = nh_i;
	}
	return (nh_i);
}

static int
nexthop_unref(uint16_t nh_i)
{
	int refc;

	RIB_LOCK_ASSERT(rt_tables_get_rnh(0, AF_INET));

	if ((refc = --nexthop_tbl[nh_i].refcount) == 0) {
		int16_t prev, next;

		/* Let the ifnet go */
		if_rele(nexthop_tbl[nh_i].ifp);
		nexthop_tbl[nh_i].ifp = NULL;

		/* Prune our entry from the nexthop list */
		prev = nexthop_tbl[nh_i].ll_prev;
		next = nexthop_tbl[nh_i].ll_next;
		if (prev >= 0)
			nexthop_tbl[prev].ll_next = next;
		else
			nexthop_head = next;
		if (next >= 0)
			nexthop_tbl[next].ll_prev = prev;

		/* Add the entry to empty nexthop list */
		nexthop_tbl[nh_i].ll_next = nexthop_empty_head;
		nexthop_empty_head = nh_i;

		nexthops--;
	}
	return (refc);
}


static int
dxr_mincore(const void *addr)
{
	pmap_t pmap = vmspace_pmap(curthread->td_proc->p_vmspace);
	vm_paddr_t locked_pa = 0;

	return (pmap_mincore(pmap, (vm_offset_t) addr, &locked_pa));
}


static void
dxr_init(void)
{
	struct proc *p = NULL;
	struct thread *td;
	register int i, j, k;

	/* Allocate memory for DXR lookup tables */
	direct_tbl = malloc(sizeof(*direct_tbl) * DIRECT_TBL_SIZE, M_TEMP,
	    M_NOWAIT);
	range_tbl = malloc(sizeof(*range_tbl) * (BASE_MAX + 1), M_TEMP,
	    M_NOWAIT);
	nexthop_tbl = malloc(sizeof(*nexthop_tbl) * DXR_VPORTS_MAX, M_TEMP,
	    M_NOWAIT);
	for (i = 0; i < DXR_VPORTS_MAX; i++) {
		DXR_HDR_CACHE_CLEAR(nexthop_tbl[i].hdr.ether_dhost);
	}
	if (direct_tbl == NULL || range_tbl == NULL || nexthop_tbl == NULL) {
		printf("DXR malloc failed!\n");
		return;
	}

#ifdef DIR_24_8
	/* Allocate memory for DIR_24_8 lookup tables */
	tbl_0_23 = malloc(sizeof(*tbl_0_23) * (1 << 24), M_TEMP, M_NOWAIT);
	tbl_24_31 = malloc(sizeof(*tbl_24_31) * (1 << 8) * (1 << 15),
	    M_TEMP, M_NOWAIT);
	if (tbl_0_23 == NULL || tbl_24_31 == NULL) {
		printf("DIR_24_8 malloc failed!\n");
		return;
	}
#endif

	/* nexthop_tbl[0] is always used for default route */
	nexthop_tbl[0].gw.s_addr = 0;
	nexthop_tbl[0].ifp = NULL;	/* Init default = discard */
	nexthop_tbl[0].refcount = 0;	/* must never be referenced! */

	dxr_enable = 1;
	async_updates = 1;
	nexthops = 0;			/* counter for non-default nexthops */
	nexthop_tbl_size = 1;		/* First empty slot */
	nexthop_head = -1;		/* No allocated nexthops */
	nexthop_empty_head = -1;	/* Recycle queue empty */

	for (i = 0; i < DIRECT_TBL_SIZE; i++) {
		direct_tbl[i].base = BASE_MAX;
		direct_tbl[i].fragments = 0;
	}
	bzero(&pending_bitmask, sizeof(pending_bitmask));
	pending_start = DIRECT_TBL_SIZE;
	pending_end = 0;

	bzero(&dxr_intrq, sizeof(dxr_intrq));
	dxr_intrq.ifq_maxlen = 256;	/* XXX -> tunable */

	/* Allocate the zone for chunk descriptors */
        chunk_zone =
            uma_zcreate("dxr_chunk", sizeof(struct chunk_desc),
            NULL, NULL, NULL, NULL, UMA_ALIGN_PTR, 0);

	/* Create updater thread */
	if (kproc_kthread_add(dxr_updater, NULL, &p, &td, RFHIGHPID,
	    0, "dxr_update", "dxr_update"))
		panic("Can't create the DXR updater thread");

#ifdef DXR_BUILD_TIMING
	bzero(update_stats, sizeof(update_stats));
#endif

#if defined(DXR_LOOKUP_TIMING) || defined(DXR_ITER_TIMING) || defined(RADIX_TIMING)
	dlp = malloc(sizeof(*dlp) * DUMMY_MEM_SIZE, M_TEMP, M_NOWAIT);
	if (dlp == NULL)
		printf("malloc(%llu) failed for dummy lookup memory\n",
		    (long long) sizeof(*dlp) * DUMMY_MEM_SIZE);
	else {
		uint64_t start = rdtsc();
		uint32_t dst;
		/* Populate with uniformly random (legal) IPv4 addresses */
		for (i = 0; i < DUMMY_MEM_SIZE; i++) {
			dst = arc4random();
			if (dst >> 24 == 0 || dst >> 24 == 10 || 
			    dst >> 24 == 127 || dst >> 24 >= 224)
				dst = 0;
			dlp[i] = dst;
		}
		/* Fix missing keys */
		for (i = 0; i < DUMMY_MEM_SIZE; i++) {
			for (dst = dlp[i];
			    dst >> 24 == 0 || dst >> 24 == 10 || 
			    dst >> 24 == 127 || dst >> 24 >= 224;
			    dlp[i] = dst) {
				dst = arc4random();
			}
		}
		printf("dummy random lookup block initialized:"
		    " %d elements in %llu cycles\n", DUMMY_MEM_SIZE,
		    (long long) (rdtsc() - start));
	}

	bzero(iter_stats, sizeof(iter_stats));

	for (i = 0; i < mp_ncpus; i++) {
		p = NULL;
		if (kproc_kthread_add(dxr_lookup_exercise,
		    (void *) (size_t) i, &p, &td, RFHIGHPID, 0,
		    "dxr_exercise", "dxr_exercise"))
			panic("Can't create the exerciser thread");
	}
#endif

	for (k = 0; k < 100; k++) {
		i = rdtsc();
		j = rdtsc();
	}
	rdtsc_latency = j - i;
	printf("rdtsc() latency estimated at %d ticks\n", rdtsc_latency);

	printf("mincore(range_tbl) = %08x\n", dxr_mincore(range_tbl));
	printf("mincore(direct_tbl)= %08x\n", dxr_mincore(direct_tbl));
	printf("mincore(nexthop_tbl)= %08x\n", dxr_mincore(nexthop_tbl));
#ifdef DIR_24_8
	printf("mincore(tbl_0_23)= %08x\n", dxr_mincore(tbl_0_23));
	printf("mincore(tbl_24_31)= %08x\n", dxr_mincore(tbl_24_31));
#endif
#if defined(DXR_LOOKUP_TIMING) || defined(DXR_ITER_TIMING) || defined(RADIX_TIMING)
	printf("mincore(dlp) = %08x\n", dxr_mincore(dlp));
#endif
}

SYSINIT(dxr, SI_SUB_VNET_DONE, SI_ORDER_ANY, dxr_init, 0);

/*
 * Our sysctl interface - provides access to a few important state
 * and / or performance indicators / counters / statistics, as
 * well as read access to individual DXR entries (.rd_entry sysctl).
 */

#ifdef SYSCTL_NODE
static int	dxr_memory;
static int	direct_bits = DXR_DIRECT_BITS;

static int sysctl_dxr_enable(SYSCTL_HANDLER_ARGS);
static int sysctl_dxr_memory(SYSCTL_HANDLER_ARGS);
static int sysctl_dxr_readentry(SYSCTL_HANDLER_ARGS);
#if defined(DXR_LOOKUP_TIMING) || defined(DXR_ITER_TIMING) || defined(RADIX_TIMING)
static int sysctl_dxr_iterstats(SYSCTL_HANDLER_ARGS);
#endif
#ifdef DXR_BUILD_TIMING
static int sysctl_dxr_updatestats(SYSCTL_HANDLER_ARGS);
#endif

SYSCTL_DECL(_net_inet_ip_dxr);
SYSCTL_NODE(_net_inet_ip, OID_AUTO, dxr, CTLFLAG_RW, 0, "DXR");

SYSCTL_INT(_net_inet_ip_dxr, OID_AUTO, direct_bits, CTLFLAG_RD,
    &direct_bits, 0, "Number of IPv4 MS bits resolved by direct lookup");

SYSCTL_PROC(_net_inet_ip_dxr, OID_AUTO, enable, CTLTYPE_INT|CTLFLAG_RW,
    0, 0, sysctl_dxr_enable, "I", "");

#if defined(DXR_LOOKUP_TIMING) || defined(DXR_ITER_TIMING) || defined(RADIX_TIMING)
SYSCTL_INT(_net_inet_ip_dxr, OID_AUTO, reduce, CTLFLAG_RW,
    &reduce, 0, "Reduce random keys to those resolvable by binary search");
#endif

SYSCTL_INT(_net_inet_ip_dxr, OID_AUTO, async_updates, CTLFLAG_RW,
    &async_updates, 0, "Coalesce route table update requests");
SYSCTL_INT(_net_inet_ip_dxr, OID_AUTO, routes, CTLFLAG_RD,
    &routes, 0, "Number of routes in DXR FIB");
SYSCTL_INT(_net_inet_ip_dxr, OID_AUTO, nexthops, CTLFLAG_RD,
    &nexthops, 0, "Number of next hops used by DXR FIB");

SYSCTL_INT(_net_inet_ip_dxr, OID_AUTO, chunks_short, CTLFLAG_RD,
    &chunks_short, 0, "Number of 16-bit DXR range chunks");
SYSCTL_INT(_net_inet_ip_dxr, OID_AUTO, chunks_long, CTLFLAG_RD,
    &chunks_long, 0, "Number of 32-bit DXR range chunks");
SYSCTL_INT(_net_inet_ip_dxr, OID_AUTO, fragments_short, CTLFLAG_RD,
    &fragments_short, 0, "Number of 16-bit DXR range fragments");
SYSCTL_INT(_net_inet_ip_dxr, OID_AUTO, fragments_long, CTLFLAG_RD,
    &fragments_long, 0, "Number of 32-bit DXR range fragments");

SYSCTL_INT(_net_inet_ip_dxr, OID_AUTO, aggr_chunks_short, CTLFLAG_RD,
    &aggr_chunks_short, 0, "Number of aggregated 16-bit DXR range chunks");
SYSCTL_INT(_net_inet_ip_dxr, OID_AUTO, aggr_chunks_long, CTLFLAG_RD,
    &aggr_chunks_long, 0, "Number of aggregated 32-bit DXR range chunks");
SYSCTL_INT(_net_inet_ip_dxr, OID_AUTO, aggr_fragments_short, CTLFLAG_RD,
    &aggr_fragments_short, 0,
    "Number of aggregated 16-bit DXR range fragments");
SYSCTL_INT(_net_inet_ip_dxr, OID_AUTO, aggr_fragments_long, CTLFLAG_RD,
    &aggr_fragments_long, 0,
    "Number of aggregated 32-bit DXR range fragments");

SYSCTL_PROC(_net_inet_ip_dxr, OID_AUTO, memory, CTLTYPE_INT|CTLFLAG_RD,
    0, 0, sysctl_dxr_memory, "I", "");

SYSCTL_NODE(_net_inet_ip_dxr, OID_AUTO, stats, CTLFLAG_RW, 0,
    "DXR counters and stats");
SYSCTL_UQUAD(_net_inet_ip_dxr_stats, OID_AUTO, local, CTLFLAG_RD,
    &dxr_stats.local, 0, "Number of packets for local addresses");
SYSCTL_UQUAD(_net_inet_ip_dxr_stats, OID_AUTO, slowpath, CTLFLAG_RD,
    &dxr_stats.slowpath, 0, "Number of packets propagated to slowpath");
SYSCTL_UQUAD(_net_inet_ip_dxr_stats, OID_AUTO, fastpath, CTLFLAG_RD,
    &dxr_stats.fastpath, 0, "Number of packets forwarded using DXR lookups");
SYSCTL_UQUAD(_net_inet_ip_dxr_stats, OID_AUTO, no_route, CTLFLAG_RD,
    &dxr_stats.no_route, 0, "Number of packets dropped");
SYSCTL_UQUAD(_net_inet_ip_dxr_stats, OID_AUTO, input_errs, CTLFLAG_RD,
    &dxr_stats.input_errs, 0, "Number of packets dropped");
SYSCTL_UQUAD(_net_inet_ip_dxr_stats, OID_AUTO, output_errs, CTLFLAG_RD,
    &dxr_stats.output_errs, 0, "Number of packets dropped");

#if defined(DXR_LOOKUP_TIMING) || defined(DXR_ITER_TIMING) || defined(RADIX_TIMING)
SYSCTL_INT(_net_inet_ip_dxr, OID_AUTO, rdtsc_latency, CTLFLAG_RW,
    &rdtsc_latency, 0, "");
SYSCTL_INT(_net_inet_ip_dxr, OID_AUTO, ex_threads, CTLFLAG_RW,
    &ex_threads, 0, "");
SYSCTL_INT(_net_inet_ip_dxr, OID_AUTO, ex_preload, CTLFLAG_RW,
    &ex_preload, 0, "");
SYSCTL_INT(_net_inet_ip_dxr, OID_AUTO, ex_iters, CTLFLAG_RD,
    &ex_iters, 0, "");
SYSCTL_PROC(_net_inet_ip_dxr, OID_AUTO, iterstats,
    CTLTYPE_STRING | CTLFLAG_RW, 0, 0, sysctl_dxr_iterstats, "A", "");
#endif

#ifdef DXR_BUILD_TIMING
SYSCTL_PROC(_net_inet_ip_dxr, OID_AUTO, updatestats,
    CTLTYPE_STRING | CTLFLAG_RW, 0, 0, sysctl_dxr_updatestats, "A", "");
#endif

SYSCTL_PROC(_net_inet_ip_dxr, OID_AUTO, rdentry, CTLTYPE_STRING | CTLFLAG_RW,
    0, 0, sysctl_dxr_readentry, "A", "");

static int
sysctl_dxr_enable(SYSCTL_HANDLER_ARGS)
{
	int new_state, error, i;

	new_state = dxr_enable;
	error = sysctl_handle_int(oidp, &new_state, 0, req);

	if (!error && req->newptr && new_state != dxr_enable) {
		switch (new_state) {
		case 0:
			for (i = 0; i < DIRECT_TBL_SIZE; i++) {
				direct_tbl[i].base = BASE_MAX;
				direct_tbl[i].fragments = 0;
			}
			bzero(pending_bitmask, sizeof(pending_bitmask));
			pending_start = DIRECT_TBL_SIZE;
			pending_end = 0;
			fragments_short = 0;
			fragments_long = 0;
			range_tbl_free = 0;
			dxr_enable = 0;
			break;
		case 1:
#if defined(DXR_LOOKUP_TIMING) || defined(DXR_ITER_TIMING) || defined(RADIX_TIMING)
			bzero(iter_stats, sizeof(iter_stats));
#endif
#ifdef DXR_BUILD_TIMING
			bzero(update_stats, sizeof(update_stats));
#endif
			bzero(&dxr_stats, sizeof(dxr_stats));
			memset(pending_bitmask, 0xff, sizeof(pending_bitmask));
			pending_start = 0;
			pending_end = DIRECT_TBL_SIZE - 1;
			apply_pending();
			dxr_enable = 1;
			break;
		default:
			error = EINVAL;
		}
	}
	return (error);
}

static int
sysctl_dxr_memory(SYSCTL_HANDLER_ARGS)
{
	int error = sysctl_handle_int(oidp, &dxr_memory, 0, req);

	if (!error) {
		dxr_memory =
		    sizeof(*direct_tbl) * DIRECT_TBL_SIZE +
		    sizeof(*range_tbl) * range_tbl_free +
		    sizeof(*nexthop_tbl) * (nexthops + 1);
	}
	return (error);
}

static int
sysctl_dxr_readentry(SYSCTL_HANDLER_ARGS)
{
	static int count = 0;
	static char buf[128];
	int error;

	error = sysctl_handle_string(oidp, &buf[0], sizeof(buf), req);
	if (req->newptr) {
		struct range_entry_short *dxr_short;
		struct range_entry_long *dxr_long;
		int nh, next = 0;
		int i;
		struct ifnet *ifp;
		struct in_addr gw;
		char *c = index(&buf[0], '.');
		int chunk = strtol(&buf[0], 0, 0);

		if (chunk >= DIRECT_TBL_SIZE)
			return ERANGE;

		if (c == NULL || chunk < 0 || chunk >= DIRECT_TBL_SIZE)
			return(error);

		c++;
		i = strtol(c, 0, 0);

		if (i < 0 || i > direct_tbl[chunk].fragments)
			return (ERANGE);

		if (i > 0 && direct_tbl[chunk].base == BASE_MAX)
			return (ERANGE);

		dxr_long = &range_tbl[direct_tbl[chunk].base];
		dxr_short = (struct range_entry_short *) dxr_long;

		if (direct_tbl[chunk].base != BASE_MAX) {
			if (direct_tbl[chunk].long_format) {
				nh = dxr_long[i].nexthop;
				next += sprintf(&buf[0], "%d.%d: %08X -> ",
				    chunk, i, dxr_long[i].start);
			} else {
				nh = dxr_short[i].nexthop;
				next += sprintf(&buf[0], "%d.%d: %08X -> ",
				    chunk, i, dxr_short[i].start << 8);
			}
		} else {
			nh = direct_tbl[chunk].fragments;
			next += sprintf(&buf[0], "%d.%d: %08X -> ",
			    chunk, i, 0);
		}

		ifp = nexthop_tbl[nh].ifp;
		gw = nexthop_tbl[nh].gw;

		next += sprintf(&buf[next], "%d:", nh);
		if (ifp)  {
			next += sprintf(&buf[next], "%s", ifp->if_xname);
			if (gw.s_addr)
				sprintf(&buf[next], " %s", inet_ntoa(gw));
		} else
			sprintf(&buf[next], "DISCARD");
		count = 2;
	}
	if (count)
		count--;
	else
		buf[0] = 0;
	return (error);
}


#if defined(DXR_LOOKUP_TIMING) || defined(DXR_ITER_TIMING) || defined(RADIX_TIMING)
static int
sysctl_dxr_iterstats(SYSCTL_HANDLER_ARGS)
{
	char buf[128];
	struct iter_stat stats[32];
	uint64_t pcpu_cycles[32];
	uint64_t sum_cnt = 0;
	uint64_t sum_cycles = 0;
	uint64_t p, c, l;
	int i, cpu, active_cpus = 0;
	int error = 0;

	bzero(stats, sizeof(stats));
	for (cpu = 0; cpu < mp_ncpus; cpu++) {
		pcpu_cycles[cpu] = 0;
		for (i = 0; i < 32 - DXR_DIRECT_BITS; i++) {
			sum_cnt += iter_stats[cpu][i].cnt;
			stats[i].cnt += iter_stats[cpu][i].cnt;
			pcpu_cycles[cpu] += iter_stats[cpu][i].cycles;
			stats[i].cycles += iter_stats[cpu][i].cycles;
		}
		sum_cycles += pcpu_cycles[cpu];
		if (pcpu_cycles[cpu])
			active_cpus++;
	}

	if (sum_cnt == 0)
		return (0);

	sprintf(buf, "\niters:  %% hits     total hits     total cycles"
	    "   cyc/lkp    M lkp/s");
	error = SYSCTL_OUT(req, buf, strlen(buf));
	if (error)
		return (error);
	for (i = 0; i < 32 - DXR_DIRECT_BITS; i++) {
		if (stats[i].cnt == 0)
			continue;
		p = stats[i].cnt * 100000 / sum_cnt;
		c = stats[i].cycles * 100 / stats[i].cnt;
		l = tsc_freq / c * active_cpus / 10;
		sprintf(buf, "\n%5u: %3u.%03u %14llu %16llu %6u.%02u"
		    "   %4u.%03u", i,
		    (int) p / 1000, (int) p % 1000,
		    (long long) stats[i].cnt,
		    (long long) stats[i].cycles,
		    (int) c / 100, (int) c % 100,
		    (int) l / 1000, (int) l % 1000);
		error = SYSCTL_OUT(req, buf, strlen(buf));
		if (error)
			return (error);
	}

	p = 100000;
	c = sum_cycles * 100 / sum_cnt;
	l = tsc_freq / c * active_cpus / 10;
	sprintf(buf, "\n  avg: %3u.%03u %14llu %16llu %6u.%02u   %4u.%03u",
	    (int) p / 1000, (int) p % 1000,
	    (long long) sum_cnt,
	    (long long) sum_cycles,
	    (int) c / 100, (int) c % 100,
	    (int) l / 1000, (int) l % 1000);
	error = SYSCTL_OUT(req, buf, strlen(buf));
	if (error)
		return (error);

	if (sum_cnt > stats[0].cnt) {
		p = (sum_cnt - stats[0].cnt) * 100000 / sum_cnt;
		c = (sum_cycles - stats[0].cycles) * 100 /
		    (sum_cnt - stats[0].cnt);
		l = tsc_freq / c * active_cpus / 10;
		sprintf(buf, "\navg_r: %3u.%03u %14llu %16llu %6u.%02u"
		    "   %4u.%03u",
		    (int) p / 1000, (int) p % 1000,
		    (long long) sum_cnt - stats[0].cnt,
		    (long long) sum_cycles - stats[0].cycles,
		    (int) c / 100, (int) c % 100,
		    (int) l / 1000, (int) l % 1000);
		error = SYSCTL_OUT(req, buf, strlen(buf));
		if (error)
			return (error);
	}

	buf[0] = 0;
	error = sysctl_handle_string(oidp, buf, sizeof(buf), req);
	if (req->newptr && buf[0] != 0)
		for (i = 0; i < 8; i++)
			bzero(iter_stats, sizeof(iter_stats));

	return (error);
}
#endif /* DXR_LOOKUP_TIMING */

#ifdef DXR_BUILD_TIMING
static int
sysctl_dxr_updatestats(SYSCTL_HANDLER_ARGS)
{
	char buf[128];
	uint64_t sum_cnt = 0;
	uint64_t sum_cycles = 0;
	uint64_t p, c, t;
	int i;
	int error;

	for (i = 0; i <= 32; i++) {
		sum_cnt += update_stats[i].cnt;
		sum_cycles += update_stats[i].cycles;
	}
	if (sum_cnt == 0)
		return (0);

	sprintf(buf, "\n plen:  %% hits  total hits    total cycles"
	    "  cyc/update  ms/update");
	error = SYSCTL_OUT(req, buf, strlen(buf));
	if (error)
		return (error);

	for (i = 0; i <= 32; i++) {
		if (update_stats[i].cnt == 0)
			continue;
		p = update_stats[i].cnt * 100000 / sum_cnt;
		c = update_stats[i].cycles / update_stats[i].cnt;
		t = c * 1000000 / tsc_freq;
		sprintf(buf, "\n%5u: %3u.%03u %11llu %15llu %11u"
		    "   %4llu.%03llu", i,
		    (int) p / 1000, (int) p % 1000,
		    (long long) update_stats[i].cnt,
		    (long long) update_stats[i].cycles,
		    (int) c,
		    (long long) t / 1000, (long long) t % 1000);
		error = SYSCTL_OUT(req, buf, strlen(buf));
		if (error)
			return (error);
	}

	p = 100000;
	c = sum_cycles / sum_cnt;
	t = c * 1000000 / tsc_freq;
	sprintf(buf, "\ntotal: %3u.%03u %11llu %15llu %11u"
	    "   %4llu.%03llu",
	    (int) p / 1000, (int) p % 1000,
	    (long long) sum_cnt,
	    (long long) sum_cycles,
	    (int) c,
	    (long long) t / 1000, (long long) t % 1000);
	error = SYSCTL_OUT(req, buf, strlen(buf));
	if (error)
		return (error);

	buf[0] = 0;
	error = sysctl_handle_string(oidp, buf, sizeof(buf), req);
	if (req->newptr && buf[0] != 0)
		bzero(update_stats, sizeof(update_stats));

	return (error);
}
#endif
#endif /* SYSCTL_NODE */


#if defined(DXR_LOOKUP_TIMING) || defined(DXR_ITER_TIMING) || defined(RADIX_TIMING)
static void
dxr_lookup_exercise(void *arg)
{
	int cpu = (size_t) arg;
	uint32_t i, dst = 0;
	int dummy_index = random() & DUMMY_MEM_MASK;
	int nh;
#ifdef ALLOW_OOO_EXEC
	int *result_tbl;
#endif
#if defined(DXR_LOOKUP_TIMING) || defined(RADIX_TIMING)
	uint64_t start, stop;
#endif

#ifdef ALLOW_OOO_EXEC
	result_tbl = malloc(sizeof(*result_tbl) * ex_iters, M_TEMP, M_NOWAIT);
	if (result_tbl == NULL) {
		printf("malloc() for result_tbl failed, stopping thread %d\n",
		    cpu);
		return; /* XXX is this OK? */
	}
#endif

	/* DXR works always and only in vnet0 */
	CURVNET_SET(vnet0);

	for (;;) {
		/* Attempt to maintain CPU affinity */
		if (PCPU_GET(cpuid) != cpu) {
			thread_lock(curthread);
			sched_bind(curthread, cpu);
			thread_unlock(curthread);
		}

		/* XXX needed for DXR_ITER_TIMING */
		DPCPU_SET(valid_timing, 1);

		if (updates_pending || dxr_enable == 0 || dlp == NULL ||
		    PCPU_GET(cpuid) >= ex_threads) {
			if (dlp == NULL || ex_threads == 0)
				pause("-", hz);
			else
				pause("-", hz / 10);
			continue;
		}

		/*
		 * Measure lookup performance on (hopefully) uniformly
		 * random destination addresses in a thight loop.
		 *
		 * XXX locking!
		 */
#if defined(DXR_LOOKUP_CONSISTENCY_CHECK)
		RIB_RLOCK(rt_tables_get_rnh(0, AF_INET));
#endif
#if defined(DXR_LOOKUP_TIMING) || defined(RADIX_TIMING)
		start = rdtsc();
#endif
		for (i = 0; i < ex_iters; i++) {
			/* Fetch new random IPv4 key */
			dst = dlp[dummy_index];
#ifdef REPEAT_SAME_KEY
			/* Repeat same key 16 times */
			if ((i & 0xf) == 0)
#endif
			dummy_index++;
#ifdef DIR_24_8
			nh = dir_24_8_lookup(dst);
#else
#ifdef RADIX_TIMING
			nh = radix_lookup(dst);
#else
			nh = dxr_lookup(dst);
#endif
#endif
#ifdef ALLOW_OOO_EXEC
			result_tbl[i] = nh;
#else
			/*
			 * Create a dependency on nh so that the next
			 * iteration cannot be dispatched out of order,
			 * before completing this one.
			 */
			dummy_index += (nexthop_tbl[nh].refcount & 1);
#endif
			dummy_index &= DUMMY_MEM_MASK;
#ifdef DXR_LOOKUP_CONSISTENCY_CHECK
			if (nh != radix_lookup(dst))
				printf("Mismatch for %08X: DXR %d, radix %d\n",
				    dst, nh, radix_lookup(dst));
#endif
		}
#if defined(DXR_LOOKUP_TIMING) || defined(RADIX_TIMING)
		stop = rdtsc();
		iter_stats[cpu][0].cnt += i;
		iter_stats[cpu][0].cycles += stop - start;
#endif
#if defined(DXR_LOOKUP_CONSISTENCY_CHECK)
		RIB_RUNLOCK(rt_tables_get_rnh(0, AF_INET));
#endif
		dummy_index = random() & DUMMY_MEM_MASK;

		kern_yield(PRI_USER);
	}

	/* Notreached */
}
#endif

#ifdef DXR_BUILD_DEBUG
static void
dxr_heap_dump(void)
{
	struct dxr_heap_entry *fhp = &dxr_heap[0];
	struct ifnet *ifp;
	struct in_addr gw;
	int i;

	for (i = 0; i <= heap_index; i++, fhp++) {
		int nh = fhp->nexthop;
		printf("    dxr_heap[%d]: %08X..%08X (plen %d) -> ",
			i, fhp->start, fhp->end, fhp->preflen);
		printf("%d:", nh);
		ifp = nexthop_tbl[nh].ifp;
		gw = nexthop_tbl[nh].gw;
		if (ifp != NULL) {
			printf("%s", ifp->if_xname);
			if (gw.s_addr)
				printf("/%s", inet_ntoa(gw));
		} else
			printf("DISCARD");
		printf("\n");
	}
}

static void
dxr_chunk_dump(int chunk)
{
	struct direct_entry *fdesc = &direct_tbl[chunk];
	struct range_entry_long *fp_l = &range_tbl[fdesc->base];
	struct range_entry_short *fp_s = (struct range_entry_short *) fp_l;
	struct ifnet *ifp;
	struct in_addr gw;
	int i, nh;

	for (i = 0; i <= fdesc->fragments; i++) {
		if (fdesc->long_format) {
			nh = fp_l[i].nexthop;
			printf("    range[%d]: %08X -> ", i, fp_l[i].start);
		} else {
			nh = fp_s[i].nexthop;
			printf("    range[%d]: %08X -> ", i,
			    fp_s[i].start << 8);
		}
		printf("%d:", nh);
		ifp = nexthop_tbl[nh].ifp;
		gw = nexthop_tbl[nh].gw;
		if (ifp != NULL) {
			printf("%s", ifp->if_xname);
			if (gw.s_addr)
				printf("/%s", inet_ntoa(gw));
		} else
			printf("DISCARD");
		printf("\n");
	}
}

static void
print_in_route(struct rtentry *rt, const char *txt)
{
	struct sockaddr_in *dst = SIN(rt_key(rt));
	struct sockaddr_in *mask = SIN(rt_mask(rt));
	struct sockaddr *gw = rt->rt_gateway;
	int preflen, i;
	u_char *c;

	printf("%s: %s", txt, inet_ntoa(dst->sin_addr));
	if (mask) {
		preflen = ffs(ntohl(mask->sin_addr.s_addr));
		if (preflen)
			preflen = 33-preflen;
	} else
		preflen = 32;
	printf("/%d", preflen);
	printf(" -> %s", rt->rt_ifp->if_xname);
	if (gw) {
		switch (gw->sa_family) {
		case AF_LINK:
			c = (u_char *)LLADDR(SDL(gw));
			printf("/");
			for (i = 0; i < SDL(gw)->sdl_alen; i++) {
				if (i > 0)
					printf(":");
				printf("%02X", *c);
				c++;
			}
			break;
		case AF_INET:
			printf("/%s", inet_ntoa(SIN(gw)->sin_addr));
			break;
		default:
			printf("/??");
		}
	}
	printf(" ");
	if (rt->rt_flags & RTF_UP) printf("UP,");
	if (rt->rt_flags & RTF_GATEWAY) printf("GW,");
	if (rt->rt_flags & RTF_HOST) printf("HST,");
	if (rt->rt_flags & RTF_REJECT) printf("REJ,");
	if (rt->rt_flags & RTF_DYNAMIC) printf("DYN,");
	if (rt->rt_flags & RTF_MODIFIED) printf("MOD,");
	if (rt->rt_flags & RTF_DONE) printf("DONE,");
	if (rt->rt_flags & RTF_XRESOLVE) printf("XRES,");
	if (rt->rt_flags & RTF_LLINFO) printf("LL,");
	if (rt->rt_flags & RTF_STATIC) printf("STA,");
	if (rt->rt_flags & RTF_BLACKHOLE) printf("BH,");
	if (rt->rt_flags & RTF_PROTO1) printf("P1,");
	if (rt->rt_flags & RTF_PROTO2) printf("P2,");
	if (rt->rt_flags & RTF_PROTO3) printf("P3,");
	if (rt->rt_flags & RTF_PINNED) printf("PIN,");
	if (rt->rt_flags & RTF_LOCAL) printf("LCL,");
	if (rt->rt_flags & RTF_BROADCAST) printf("BCAST,");
	if (rt->rt_flags & RTF_MULTICAST) printf("MCAST");
	printf(" nexthop=%d\n", rt->rt_dxr_nexthop);
}
#endif


#ifdef DIR_24_8
static int
dir_24_8_lookup(uint32_t dst)
{
#ifdef DXR_LOOKUP_CONSISTENCY_CHECK
	struct route ro;
	struct rtentry *rt;
	struct sockaddr_in *sin = (struct sockaddr_in *) &ro.ro_dst;
	int check_nh;
#endif
	register int nh = tbl_0_23[dst >> 8];

	if (nh & 0x8000)
		nh = tbl_24_31[((nh & 0x7fff) << 8) | (dst & 0xff)];

#ifdef DXR_LOOKUP_CONSISTENCY_CHECK
	ro.ro_rt = NULL;
	sin->sin_family = AF_INET;
	sin->sin_len = sizeof(*sin);
	sin->sin_addr.s_addr = htonl(dst);
	check_nh = 0;

	rtalloc_ign(&ro, 0);
	if ((rt = ro.ro_rt) != NULL) {
		check_nh = rt->rt_dxr_nexthop;
		RTFREE(ro.ro_rt);
	} else
		check_nh = 0;

	/*
	 * Compare the DIR_24_8 and radix routes - is nexthop the same?
	 */
	if (nh != check_nh) {
		struct ifnet *ifp;
		struct in_addr gw;

		gw.s_addr = htonl(dst);
		printf("%s:", inet_ntoa(gw));

		printf(" DIR_24_8: ");
		ifp = nexthop_tbl[nh].ifp;
		gw = nexthop_tbl[nh].gw;
		if (ifp)  {
			printf("%s", ifp->if_xname);
			if (gw.s_addr)
				printf(" %s", inet_ntoa(gw));
		} else
			printf("DISCARD");

		printf("; radix: ");
		ifp = nexthop_tbl[check_nh].ifp;
		gw = nexthop_tbl[check_nh].gw;
		if (ifp)  {
			printf("%s", ifp->if_xname);
			if (gw.s_addr)
				printf(" %s", inet_ntoa(gw));
		} else
			printf("DISCARD");
		printf("\n");
	}
#endif
	return nh;
}

/*
 * Rebuild DIR_24_8 lookup tables using info from DXR tables.
 * DXR MUST be configured as D24R for this to work!
 */
static void
dir_24_8_rebuild(void)
{
	int i, j, nh;
	int tbl_24_31_free = 0;
	uint32_t dst;

	for (i = 0; i < DIRECT_TBL_SIZE; i++) {
		if (direct_tbl[i].base == BASE_MAX) {
			/* Nexthop is directly resolvable */
			nh = direct_tbl[i].fragments;
			tbl_0_23[i] = nh;
			continue;
		}

		/* Encode 2nd table chunk index in 1st table element */
		tbl_0_23[i] = tbl_24_31_free | 0x8000;

		/* Populate chunk in 2nd table */
		for (j = 0; j < 256; j++) {
			dst = (((uint32_t) i) << 24) + j;
			nh = dxr_lookup(dst);
			tbl_24_31[(tbl_24_31_free << 8) + j] = nh;
		}

		/* 2nd table chunk is occupied now */
		tbl_24_31_free++;
	}
}
#endif
