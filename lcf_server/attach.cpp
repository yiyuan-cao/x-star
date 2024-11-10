// #include "cstar.h"

typedef void* term;
typedef void* thm;

#define HYP_MAX_ORDER 11
#define HYP_NO_ORDER 255
#define HYP_PAGE_SHIFT 12
#define HYP_PAGE_SIZE 4096

typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef unsigned long long u64;
typedef unsigned long long phys_addr_t;

u64 __hyp_vmemmap;

struct list_head
{
	struct list_head *next;
	struct list_head *prev;
};

struct hyp_pool
{
	struct list_head free_area[MAX_ORDER];
	u64 range_start;
	u64 range_end;
	u8 max_order;
};

struct hyp_page
{
	u16 refcount;
	u8 order;
	u8 flags;
};

#define hyp_vmemmap ((struct hyp_page *)__hyp_vmemmap)

#define __hyp_pa(virt)	((phys_addr_t)(virt) + hyp_physvirt_offset)
#define __hyp_va(phys)	((phys_addr_t)(phys) - hyp_physvirt_offset)
void *hyp_phys_to_virt(phys_addr_t phys) { return __hyp_va(phys); }
phys_addr_t hyp_virt_to_phys(void *addr) { return __hyp_pa(addr); }

#define hyp_phys_to_pfn(phys)	((phys) / HYP_PAGE_SIZE)
#define hyp_pfn_to_phys(pfn)	((phys_addr_t)((pfn) * HYP_PAGE_SIZE))
#define hyp_phys_to_page(phys)	(&hyp_vmemmap[hyp_phys_to_pfn(phys)])
#define hyp_virt_to_page(virt)	hyp_phys_to_page(__hyp_pa(virt))
#define hyp_virt_to_pfn(virt)	hyp_phys_to_pfn(__hyp_pa(virt))
#define hyp_page_to_pfn(page)	((struct hyp_page *)(page) - hyp_vmemmap)
#define hyp_page_to_phys(page)  hyp_pfn_to_phys((hyp_page_to_pfn(page)))
#define hyp_page_to_virt(page)	__hyp_va(hyp_page_to_phys(page))


// static struct hyp_page *__find_buddy_nocheck(struct hyp_pool *pool, struct hyp_page *pg, unsigned int order)
// {
// 	phys_addr_t addr = hyp_page_to_phys(pg);
// 	addr ^= (PAGE_SIZE << order);
// 	if (addr < pool->range_start || addr >= pool->range_end)
// 		return NULL;
// 	return hyp_phys_to_page(addr);
// }

// static struct hyp_page *__find_buddy_avail(struct hyp_pool *pool, struct hyp_page *pg, unsigned int order)
// 	[[cstar::require(`
// 		(pool_const pool) **
// 		store_pageinfo_array vmemmap start end l **
//		hfact (LENGTH l = len) **
// 		hfact (pg = vmemmap + &(pi * 4)) **
// 		hfact (pi < len) **
// 		hfact ((2 EXP order) divides (i2id pi))
// 	`)]]
// 	[[cstar::ensure(`
// 	exists buddy bi.
// 		data_at(&"buddy", Tuchar, buddy_v) **
// 		hfact ((buddy_v = &0) ||
// 			~(bi = pi) &&
// 			(buddy_v = vmemmap + &(bi * 4)) &&
// 			(bi < len) &&
// 			(REF (nth l bi) = 0) &&
// 			(ORD (nth l bi) = order) &&
// 			((2 EXP (SUC order)) divides (i2id (MIN pi bi))) &&
//			(abs (&pi - &bi) = &(2 EXP order))) **
// 		(pool_const pool) **
// 		store_pageinfo_array vmemmap start end l **
//		hfact (LENGTH l = len) **
// 		hfact (pg = vmemmap + &(pi * 4)) **
// 		hfact (pi < len) **
// 		hfact ((2 EXP order) divides (i2id pi))
// 	`)]]
// {
// 	struct hyp_page *buddy = __find_buddy_nocheck(pool, pg, order);
// 	if (!buddy || buddy->order != order)
// 		return NULL;
// 	return buddy;
// }

// void page_remove_from_list_pool(struct hyp_pool *pool, struct hyp_page *pg)
// 	[[cstar::require(`
//		hfact (pure_const) **
//		hfact (LENGTH l = len) **
//		hfact (LENGTH dl = len) **
//		hfact (LENGTH hl = max_order) **
// 		hfact (pg = vmemmap + &(pi * 4)) **
// 		hfact (pi < len) **
// 		hfact (ORD (nth l pi) = order) **
// 		hfact (REF (nth l pi) = 0) **
// 		hfact (order < max_order) **
// 		hfact (dlist_node pool (ifilter l) l dl hl start end dl) **
// 		hfact (dlist_head pool l dl 0 max_order hl) **
//		(dlist_head_repr pool_pre 0 max_order hl) **
// 		(free_area_head_repr (ifilter l) start end dl)
// 	`)]]
// 	[[cstar::ensure(`
// 	exists new_l new_dl new_hl.
// 		hfact (new_l = modified l pi (0, NO_ORDER)) **
//		hfact (pure_const) **
//		hfact (LENGTH l = len) **
//		hfact (LENGTH dl = len) **
//		hfact (LENGTH hl = max_order) **
//		hfact (LENGTH new_l = len) **
//		hfact (LENGTH new_dl = len) **
//		hfact (LENGTH new_hl = max_order) **
// 		hfact (pg = vmemmap + &(pi * 4)) **
// 		hfact (pi < len) **
// 		hfact (ORD (nth l pi) = order) **
// 		hfact (REF (nth l pi) = 0) **
// 		hfact (order < max_order) **
// 		hfact (dlist_node pool (ifilter new_l) new_l new_dl new_hl start end new_dl) **
// 		hfact (dlist_head pool new_l new_dl 0 max_order new_hl) **
//		(dlist_head_repr pool_pre 0 max_order new_hl) **
// 		(free_area_head_repr (ifilter new_l) start end new_dl) **
//		(data_at (i2vi pi, Tptr, &0)) **
//		(data_at (i2vi pi + &PTR_SIZE, Tptr, &0))
// 	`)]]
// {}

// void page_add_to_list_pool(struct hyp_pool *pool, struct hyp_page *pg, u8 order)
// 	[[cstar::require(`
// 		hfact (pure_const) **
// 		hfact (LENGTH l = len) **
// 		hfact (LENGTH dl = len) **
// 		hfact (LENGTH hl = max_order) **
// 		hfact (pg = vmemmap + &(pi * 4)) **
// 		hfact (pi < len) **
// 		hfact (ORD (nth l pi) = NO_ORDER) **
// 		hfact (REF (nth l pi) = 0) **
// 		hfact (order < max_order) **
// 		hfact (dlist_node pool (ifilter l) l dl hl start end dl) **
// 		hfact (dlist_head pool l dl 0 max_order hl) **
// 		(dlist_head_repr pool_pre 0 max_order hl) **
// 		(free_area_head_repr (ifilter l) start end dl) **
// 		(data_at (i2vi pi, Tptr, &0)) **
// 		(data_at (i2vi pi + &PTR_SIZE, Tptr, &0))
// 	`)]]
// 	[[cstar::ensure(`
// 	exists new_l new_dl new_hl.
// 		hfact (new_l = modified l pi (0, order)) **
// 		hfact (pure_const) **
// 		hfact (LENGTH l = len) **
// 		hfact (LENGTH dl = len) **
// 		hfact (LENGTH hl = max_order) **
// 		hfact (LENGTH new_l = len) **
// 		hfact (LENGTH new_dl = len) **
// 		hfact (LENGTH new_hl = max_order) **
// 		hfact (pg = vmemmap + &(pi * 4)) **
// 		hfact (pi < len) **
// 		hfact (ORD (nth l pi) = NO_ORDER) **
// 		hfact (REF (nth l pi) = 0) **
// 		hfact (order < max_order) **
// 		hfact (dlist_node pool (ifilter new_l) new_l new_dl new_hl start end new_dl) **
// 		hfact (dlist_head pool new_l new_dl 0 max_order new_hl) **
// 		(dlist_head_repr pool_pre 0 max_order new_hl) **
// 		(free_area_head_repr (ifilter new_l) start end new_dl)
// 	`)]]
// {}


// assmue auto exists elimination
// assmue auto facts elimination

static void __hyp_attach_page(struct hyp_pool *pool, struct hyp_page *pg)
	[[cstar::parameter(`l : ((num#num))list`)]]
	[[cstar::parameter(`dl : ((addr#addr)list)list`)]]
	[[cstar::parameter(`hl : ((addr#addr)list)list`)]]
	[[cstar::parameter(`pi : num`)]]
	[[cstar::parameter(`pref : num`)]]
	[[cstar::parameter(`porder : num`)]]
	[[cstar::parameter(`vmemmap : addr`)]]
	[[cstar::require(`
		data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
		hfact (pure_const) **
		hfact (dlist_node pool (ifilter l) l dl hl start end dl) **
		hfact (dlist_head pool l dl 0 max_order hl) **
		hfact (LENGTH l = len) **
		hfact (LENGTH dl = len) **
		hfact (LENGTH hl = max_order) **
		hfact (pg = vmemmap + &(pi * 4)) **
		hfact (pi < len) **
		hfact (~(porder = NO_ORDER)) **
		hfact (pref > 0) **
		hfact (pref = REF (nth l pi)) **
		hfact (porder = ORD (nth l pi)) **
		(pool_const pool) **
		(dlist_head_repr pool 0 max_order hl) **
		(free_area_repr (ifilter l) start end l) **
		(free_area_head_repr (ifilter l) start end dl) **
		(store_pageinfo_array vmemmap start (i2id pi) (take l pi)) **
			hfact (~(porder = NO_ORDER) ==> (porder < max_order) && ((2 EXP porder) divides (i2id pi))) **
			hfact (pref < REF_LIM) **
			(data_at (vmemmap + &(pi * 4), Tushort, &0)) **
			(data_at (vmemmap + &(pi * 4 + 2), Tuchar, &porder)) **
			(undef_data_at (vmemmap + &(pi * 4 + 3), Tuchar)) **
		(store_pageinfo_array vmemmap (SUC (i2id pi)) end (rest l (SUC pi))) **
		(store_undef_array (i2vi pi) 0 (PAGE_SIZE * (2 EXP porder)) (PAGE_SIZE * (2 EXP porder)))
	`)]]
	[[cstar::ensure(`
		exists new_l new_dl new_hl.
			total_repr pool vmemmap new_l new_dl new_hl
	`)]]
{
    [[cstar::assert(`
		data_at(&"pool", Tptr, pool_pre) **
		data_at(&"pg", Tptr, pg_pre) **
		data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
		hfact (pure_const) **
		hfact (dlist_node pool_pre (ifilter l) l dl hl start end dl) **
		hfact (dlist_head pool_pre l dl 0 max_order hl) **
		hfact (LENGTH l = len) **
		hfact (LENGTH dl = len) **
		hfact (LENGTH hl = max_order) **
		hfact (pg_pre = vmemmap + &(pi * 4)) **
		hfact (pi < len) **
		hfact (~(porder = NO_ORDER)) **
		hfact (pref > 0) **
		hfact (pref = REF (nth l pi)) **
		hfact (porder = ORD (nth l pi)) **
		(pool_const pool_pre) **
		(dlist_head_repr pool_pre 0 max_order hl) **
		(free_area_repr (ifilter l) start end l) **
		(free_area_head_repr (ifilter l) start end dl) **
		(store_pageinfo_array vmemmap start (i2id pi) (take l pi)) **
			hfact (~(porder = NO_ORDER) ==> (porder < max_order) && ((2 EXP porder) divides (i2id pi))) ** 
			hfact (pref < REF_LIM) **
			(data_at (vmemmap + &(pi * 4), Tushort, &0)) **
			(data_at (vmemmap + &(pi * 4 + 2), Tuchar, &porder)) **
			(undef_data_at (vmemmap + &(pi * 4 + 3), Tuchar)) **
		(store_pageinfo_array vmemmap (SUC (i2id pi)) end (rest l (SUC pi))) **
		(store_undef_array (i2vi pi) 0 (PAGE_SIZE * (2 EXP porder)) (PAGE_SIZE * (2 EXP porder)))
    `)]];
struct hyp_page *buddy = NULL;
    [[cstar::assert(`
		data_at(&"buddy", Tptr, &0) **
		data_at(&"pool", Tptr, pool_pre) **
		data_at(&"pg", Tptr, pg_pre) **
		data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
		hfact (pure_const) **
		hfact (dlist_node pool_pre (ifilter l) l dl hl start end dl) **
		hfact (dlist_head pool_pre l dl 0 max_order hl) **
		hfact (LENGTH l = len) **
		hfact (LENGTH dl = len) **
		hfact (LENGTH hl = max_order) **
		hfact (pg_pre = vmemmap + &(pi * 4)) **
		hfact (pi < len) **
		hfact (~(porder = NO_ORDER)) **
		hfact (pref > 0) **
		hfact (pref = REF (nth l pi)) **
		hfact (porder = ORD (nth l pi)) **
		(pool_const pool_pre) **
		(dlist_head_repr pool_pre 0 max_order hl) **
		(free_area_repr (ifilter l) start end l) **
		(free_area_head_repr (ifilter l) start end dl) **
		(store_pageinfo_array vmemmap start (i2id pi) (take l pi)) **
			hfact (~(porder = NO_ORDER) ==> (porder < max_order) && ((2 EXP porder) divides (i2id pi))) ** 
			hfact (pref < REF_LIM) **
			(data_at (vmemmap + &(pi * 4), Tushort, &0)) **
			(data_at (vmemmap + &(pi * 4 + 2), Tuchar, &porder)) **
			(undef_data_at (vmemmap + &(pi * 4 + 3), Tuchar)) **
		(store_pageinfo_array vmemmap (SUC (i2id pi)) end (rest l (SUC pi))) **
		(store_undef_array (i2vi pi) 0 (PAGE_SIZE * (2 EXP porder)) (PAGE_SIZE * (2 EXP porder)))
    `)]];
	[[cstar::proof(
		// open pool_const
		// modify data_at to &""
		thm proof1;
	)]];
    [[cstar::assert(`
		data_at(&"buddy", Tptr, &0) **
		data_at(&"pool", Tptr, pool_pre) **
		data_at(&"pg", Tptr, pg_pre) **
		data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
		hfact (pure_const) **
		hfact (dlist_node pool_pre (ifilter l) l dl hl start end dl) **
		hfact (dlist_head pool_pre l dl 0 max_order hl) **
		hfact (LENGTH l = len) **
		hfact (LENGTH dl = len) **
		hfact (LENGTH hl = max_order) **
		hfact (pg_pre = vmemmap + &(pi * 4)) **
		hfact (pi < len) **
		hfact (~(porder = NO_ORDER)) **
		hfact (pref > 0) **
		hfact (pref = REF (nth l pi)) **
		hfact (porder = ORD (nth l pi)) **
		data_at (pool_pre + &(LIST_HEAD_SIZE * MAX_ORDER), Tuint64, id2ph start) **
        data_at (pool_pre + &(LIST_HEAD_SIZE * MAX_ORDER + 8), Tuint64, id2ph end) **
        data_at (&"pool_pre -> max_order", Tuchar, &max_order) **
		(dlist_head_repr pool_pre 0 max_order hl) **
		(free_area_repr (ifilter l) start end l) **
		(free_area_head_repr (ifilter l) start end dl) **
		(store_pageinfo_array vmemmap start (i2id pi) (take l pi)) **
			hfact (~(porder = NO_ORDER) ==> (porder < max_order) && ((2 EXP porder) divides (i2id pi))) ** 
			hfact (pref < REF_LIM) **
			(data_at (vmemmap + &(pi * 4), Tushort, &0)) **
			(data_at (&"pg_pre -> order", Tuchar, &porder)) **
			(undef_data_at (vmemmap + &(pi * 4 + 3), Tuchar)) **
		(store_pageinfo_array vmemmap (SUC (i2id pi)) end (rest l (SUC pi))) **
		(store_undef_array (i2vi pi) 0 (PAGE_SIZE * (2 EXP porder)) (PAGE_SIZE * (2 EXP porder)))
    `)]];
u8 order = pg -> order;
    [[cstar::assert(`
		data_at(&"order", Tuchar, &porder) **
		data_at(&"buddy", Tptr, &0) **
		data_at(&"pool", Tptr, pool_pre) **
		data_at(&"pg", Tptr, pg_pre) **
		data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
		hfact (pure_const) **
		hfact (dlist_node pool_pre (ifilter l) l dl hl start end dl) **
		hfact (dlist_head pool_pre l dl 0 max_order hl) **
		hfact (LENGTH l = len) **
		hfact (LENGTH dl = len) **
		hfact (LENGTH hl = max_order) **
		hfact (pg_pre = vmemmap + &(pi * 4)) **
		hfact (pi < len) **
		hfact (~(porder = NO_ORDER)) **
		hfact (pref > 0) **
		hfact (pref = REF (nth l pi)) **
		hfact (porder = ORD (nth l pi)) **
		data_at (pool_pre + &(LIST_HEAD_SIZE * MAX_ORDER), Tuint64, id2ph start) **
        data_at (pool_pre + &(LIST_HEAD_SIZE * MAX_ORDER + 8), Tuint64, id2ph end) **
        data_at (&"pool_pre -> max_order", Tuchar, &max_order) **
		(dlist_head_repr pool_pre 0 max_order hl) **
		(free_area_repr (ifilter l) start end l) **
		(free_area_head_repr (ifilter l) start end dl) **
		(store_pageinfo_array vmemmap start (i2id pi) (take l pi)) **
			hfact (~(porder = NO_ORDER) ==> (porder < max_order) && ((2 EXP porder) divides (i2id pi))) ** 
			hfact (pref < REF_LIM) **
			(data_at (vmemmap + &(pi * 4), Tushort, &0)) **
			(data_at (&"pg_pre -> order", Tuchar, &porder)) **
			(undef_data_at (vmemmap + &(pi * 4 + 3), Tuchar)) **
		(store_pageinfo_array vmemmap (SUC (i2id pi)) end (rest l (SUC pi))) **
		(store_undef_array (i2vi pi) 0 (PAGE_SIZE * (2 EXP porder)) (PAGE_SIZE * (2 EXP porder)))
    `)]];
memset(hyp_page_to_virt(pg), 0, HYP_PAGE_SIZE << order);
    [[cstar::assert(`
		data_at(&"order", Tuchar, &porder) **
		data_at(&"buddy", Tptr, &0) **
		data_at(&"pool", Tptr, pool_pre) **
		data_at(&"pg", Tptr, pg_pre) **
		data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
		hfact (pure_const) **
		hfact (dlist_node pool_pre (ifilter l) l dl hl start end dl) **
		hfact (dlist_head pool_pre l dl 0 max_order hl) **
		hfact (LENGTH l = len) **
		hfact (LENGTH dl = len) **
		hfact (LENGTH hl = max_order) **
		hfact (pg_pre = vmemmap + &(pi * 4)) **
		hfact (pi < len) **
		hfact (~(porder = NO_ORDER)) **
		hfact (pref > 0) **
		hfact (pref = REF (nth l pi)) **
		hfact (porder = ORD (nth l pi)) **
		data_at (pool_pre + &(LIST_HEAD_SIZE * MAX_ORDER), Tuint64, id2ph start) **
        data_at (pool_pre + &(LIST_HEAD_SIZE * MAX_ORDER + 8), Tuint64, id2ph end) **
        data_at (&"pool_pre -> max_order", Tuchar, &max_order) **
		(dlist_head_repr pool_pre 0 max_order hl) **
		(free_area_repr (ifilter l) start end l) **
		(free_area_head_repr (ifilter l) start end dl) **
		(store_pageinfo_array vmemmap start (i2id pi) (take l pi)) **
			hfact (~(porder = NO_ORDER) ==> (porder < max_order) && ((2 EXP porder) divides (i2id pi))) ** 
			hfact (pref < REF_LIM) **
			(data_at (vmemmap + &(pi * 4), Tushort, &0)) **
			(data_at (&"pg_pre -> order", Tuchar, &porder)) **
			(undef_data_at (vmemmap + &(pi * 4 + 3), Tuchar)) **
		(store_pageinfo_array vmemmap (SUC (i2id pi)) end (rest l (SUC pi))) **
		(store_zero_array (i2vi pi) 0 (PAGE_SIZE * (2 EXP porder)) (PAGE_SIZE * (2 EXP porder)))
    `)]];
pg -> order = HYP_NO_ORDER;
    [[cstar::assert(`
		data_at(&"order", Tuchar, &porder) **
		data_at(&"buddy", Tptr, &0) **
		data_at(&"pool", Tptr, pool_pre) **
		data_at(&"pg", Tptr, pg_pre) **
		data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
		hfact (pure_const) **
		hfact (dlist_node pool_pre (ifilter l) l dl hl start end dl) **
		hfact (dlist_head pool_pre l dl 0 max_order hl) **
		hfact (LENGTH l = len) **
		hfact (LENGTH dl = len) **
		hfact (LENGTH hl = max_order) **
		hfact (pg_pre = vmemmap + &(pi * 4)) **
		hfact (pi < len) **
		hfact (~(porder = NO_ORDER)) **
		hfact (pref > 0) **
		hfact (pref = REF (nth l pi)) **
		hfact (porder = ORD (nth l pi)) **
		data_at (pool_pre + &(LIST_HEAD_SIZE * MAX_ORDER), Tuint64, id2ph start) **
        data_at (pool_pre + &(LIST_HEAD_SIZE * MAX_ORDER + 8), Tuint64, id2ph end) **
        data_at (&"pool_pre -> max_order", Tuchar, &max_order) **
		(dlist_head_repr pool_pre 0 max_order hl) **
		(free_area_repr (ifilter l) start end l) **
		(free_area_head_repr (ifilter l) start end dl) **
		(store_pageinfo_array vmemmap start (i2id pi) (take l pi)) **
			hfact (~(porder = NO_ORDER) ==> (porder < max_order) && ((2 EXP porder) divides (i2id pi))) ** 
			hfact (pref < REF_LIM) **
			(data_at (vmemmap + &(pi * 4), Tushort, &0)) **
			(data_at (&"pg_pre -> order", Tuchar, &HYP_NO_ORDER)) **
			(undef_data_at (vmemmap + &(pi * 4 + 3), Tuchar)) **
		(store_pageinfo_array vmemmap (SUC (i2id pi)) end (rest l (SUC pi))) **
		(store_zero_array (i2vi pi) 0 (PAGE_SIZE * (2 EXP porder)) (PAGE_SIZE * (2 EXP porder)))
    `)]];
u8 max_order = pool -> max_order;
    [[cstar::assert(`
		data_at(&"max_order", Tuchar, &max_order) **
		data_at(&"order", Tuchar, &porder) **
		data_at(&"buddy", Tptr, &0) **
		data_at(&"pool", Tptr, pool_pre) **
		data_at(&"pg", Tptr, pg_pre) **
		data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
		hfact (pure_const) **
		hfact (dlist_node pool_pre (ifilter l) l dl hl start end dl) **
		hfact (dlist_head pool_pre l dl 0 max_order hl) **
		hfact (LENGTH l = len) **
		hfact (LENGTH dl = len) **
		hfact (LENGTH hl = max_order) **
		hfact (pg_pre = vmemmap + &(pi * 4)) **
		hfact (pi < len) **
		hfact (~(porder = NO_ORDER)) **
		hfact (pref > 0) **
		hfact (pref = REF (nth l pi)) **
		hfact (porder = ORD (nth l pi)) **
		data_at (pool_pre + &(LIST_HEAD_SIZE * MAX_ORDER), Tuint64, id2ph start) **
        data_at (pool_pre + &(LIST_HEAD_SIZE * MAX_ORDER + 8), Tuint64, id2ph end) **
        data_at (&"pool_pre -> max_order", Tuchar, &max_order) **
		(dlist_head_repr pool_pre 0 max_order hl) **
		(free_area_repr (ifilter l) start end l) **
		(free_area_head_repr (ifilter l) start end dl) **
		(store_pageinfo_array vmemmap start (i2id pi) (take l pi)) **
			hfact (~(porder = NO_ORDER) ==> (porder < max_order) && ((2 EXP porder) divides (i2id pi))) ** 
			hfact (pref < REF_LIM) **
			(data_at (vmemmap + &(pi * 4), Tushort, &0)) **
			(data_at (&"pg_pre -> order", Tuchar, &HYP_NO_ORDER)) **
			(undef_data_at (vmemmap + &(pi * 4 + 3), Tuchar)) **
		(store_pageinfo_array vmemmap (SUC (i2id pi)) end (rest l (SUC pi))) **
		(store_zero_array (i2vi pi) 0 (PAGE_SIZE * (2 EXP porder)) (PAGE_SIZE * (2 EXP porder)))
    `)]];
	[[cstar::proof(
		// close pool_const
		// modify data_at to addr
		thm proof2;
	)]];
    [[cstar::assert(`
		data_at(&"max_order", Tuchar, &max_order) **
		data_at(&"order", Tuchar, &porder) **
		data_at(&"buddy", Tptr, &0) **
		data_at(&"pool", Tptr, pool_pre) **
		data_at(&"pg", Tptr, pg_pre) **
		data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
		hfact (pure_const) **
		hfact (dlist_node pool_pre (ifilter l) l dl hl start end dl) **
		hfact (dlist_head pool_pre l dl 0 max_order hl) **
		hfact (LENGTH l = len) **
		hfact (LENGTH dl = len) **
		hfact (LENGTH hl = max_order) **
		hfact (pg_pre = vmemmap + &(pi * 4)) **
		hfact (pi < len) **
		hfact (~(porder = NO_ORDER)) **
		hfact (pref > 0) **
		hfact (pref = REF (nth l pi)) **
		hfact (porder = ORD (nth l pi)) **
		(pool_const pool_pre) **
		(dlist_head_repr pool_pre 0 max_order hl) **
		(free_area_repr (ifilter l) start end l) **
		(free_area_head_repr (ifilter l) start end dl) **
		(store_pageinfo_array vmemmap start (i2id pi) (take l pi)) **
			hfact (~(porder = NO_ORDER) ==> (porder < max_order) && ((2 EXP porder) divides (i2id pi))) ** 
			hfact (pref < REF_LIM) **
			(data_at (vmemmap + &(pi * 4), Tushort, &0)) **
			(data_at (vmemmap + &(pi * 4 + 2), Tuchar, &HYP_NO_ORDER)) **
			(undef_data_at (vmemmap + &(pi * 4 + 3), Tuchar)) **
		(store_pageinfo_array vmemmap (SUC (i2id pi)) end (rest l (SUC pi))) **
		(store_zero_array (i2vi pi) 0 (PAGE_SIZE * (2 EXP porder)) (PAGE_SIZE * (2 EXP porder)))
    `)]];
	[[cstar::proof(
		// l -> new_l:
		// 	dlist_node / dlist_head / LENGTH / ORD / REF
		// merge store_pageinfo_array
		thm proof3;
	)]];
	[[cstar::assert(`
		data_at(&"max_order", Tuchar, &max_order) **
		data_at(&"order", Tuchar, &porder) **
		data_at(&"buddy", Tptr, &0) **
		data_at(&"pool", Tptr, pool_pre) **
		data_at(&"pg", Tptr, pg_pre) **
		data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
		hfact (pure_const) **
		hfact (dlist_node pool_pre (ifilter (modified l pi (0, NO_ORDER))) (modified l pi (0, NO_ORDER)) dl hl start end dl) **
		hfact (dlist_head pool_pre (modified l pi (0, NO_ORDER)) dl 0 max_order hl) **
		hfact (LENGTH (modified l pi (0, NO_ORDER)) = len) **
		hfact (LENGTH dl = len) **
		hfact (LENGTH hl = max_order) **
		hfact (pg_pre = vmemmap + &(pi * 4)) **
		hfact (pi < len) **
		hfact (~(porder = NO_ORDER)) **
   		hfact (porder < max_order) **
   		hfact (2 EXP porder divides i2id pi) **
		hfact (ORD (nth (modified l pi (0, NO_ORDER)) pi) == NO_ORDER) **
		hfact (REF (nth (modified l pi (0, NO_ORDER)) pi) == 0) **
		(pool_const pool_pre) **
		(dlist_head_repr pool_pre 0 max_order hl) **
		(free_area_repr (ifilter (modified l pi (0, NO_ORDER))) start end (modified l pi (0, NO_ORDER))) **
		(free_area_head_repr (ifilter (modified l pi (0, NO_ORDER))) start end dl) **
		(store_pageinfo_array vmemmap start end (modified l pi (0, NO_ORDER))) **
		(store_zero_array (i2vi pi) 0 (PAGE_SIZE * (2 EXP porder)) (PAGE_SIZE * (2 EXP porder)))
    `)]];
buddy = __find_buddy_avail(pool, pg, order);
    [[cstar::assert(`
	exists buddy_v bi.
		hfact ((buddy_v = &0) ||
			~(bi = pi) &&
			(buddy_v = vmemmap + &(bi * 4)) &&
			(bi < len) &&
			(REF (nth (modified l pi (0, NO_ORDER)) bi) = 0) &&
			(ORD (nth (modified l pi (0, NO_ORDER)) bi) = porder) &&
			((2 EXP (SUC porder)) divides (i2id (MIN pi bi))) &&
			(abs (&pi - &bi) = &(2 EXP porder))) **
		data_at(&"max_order", Tuchar, &max_order) **
		data_at(&"order", Tuchar, &porder) **
		data_at(&"buddy", Tptr, buddy_v) **
		data_at(&"pool", Tptr, pool_pre) **
		data_at(&"pg", Tptr, pg_pre) **
		data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
		hfact (pure_const) **
		hfact (dlist_node pool_pre (ifilter (modified l pi (0, NO_ORDER))) (modified l pi (0, NO_ORDER)) dl hl start end dl) **
		hfact (dlist_head pool_pre (modified l pi (0, NO_ORDER)) dl 0 max_order hl) **
		hfact (LENGTH (modified l pi (0, NO_ORDER)) = len) **
		hfact (LENGTH dl = len) **
		hfact (LENGTH hl = max_order) **
		hfact (pg_pre = vmemmap + &(pi * 4)) **
		hfact (pi < len) **
		hfact (~(porder = NO_ORDER)) **
   		hfact (porder < max_order) **
   		hfact (2 EXP porder divides i2id pi) **
		hfact (ORD (nth (modified l pi (0, NO_ORDER)) pi) == NO_ORDER) **
		hfact (REF (nth (modified l pi (0, NO_ORDER)) pi) == 0) **
		(pool_const pool_pre) **
		(dlist_head_repr pool_pre 0 max_order hl) **
		(free_area_repr (ifilter (modified l pi (0, NO_ORDER))) start end (modified l pi (0, NO_ORDER))) **
		(free_area_head_repr (ifilter (modified l pi (0, NO_ORDER))) start end dl) **
		(store_pageinfo_array vmemmap start end (modified l pi (0, NO_ORDER))) **
		(store_zero_array (i2vi pi) 0 (PAGE_SIZE * (2 EXP porder)) (PAGE_SIZE * (2 EXP porder)))
    `)]];
	[[cstar::proof(
		// pi -> i
		// modified l -> inv_l
		// dl -> inv_dl
		// hl -> inv_hl
		// porder -> ord
		// pg -> pg_v
		thm proof4;
	)]];
    [[cstar::invariant(`
	exists pg_v ord i inv_l inv_dl inv_hl buddy_v bi.
		hfact ((buddy_v = &0) ||
			~(bi = i) &&
			(buddy_v = vmemmap + &(bi * 4)) &&
			(bi < len) &&
			(REF (nth inv_l bi) = 0) &&
			(ORD (nth inv_l bi) = ord) &&
			((2 EXP (SUC ord)) divides (i2id (MIN i bi))) &&
			(abs (&i - &bi) = &(2 EXP ord))) **
		data_at(&"max_order", Tuchar, &max_order) **
		data_at(&"order", Tuchar, &ord) **
		data_at(&"buddy", Tptr, buddy_v) **
		data_at(&"pool", Tptr, pool_pre) **
		data_at(&"pg", Tptr, pg_v) **
		data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
		hfact (pure_const) **
		hfact (dlist_node pool_pre (ifilter inv_l) inv_l inv_dl inv_hl start end inv_dl) **
		hfact (dlist_head pool_pre inv_l inv_dl 0 max_order inv_hl) **
		hfact (LENGTH inv_l = len) **
		hfact (LENGTH inv_dl = len) **
		hfact (LENGTH inv_hl = max_order) **
		hfact (pg_v = vmemmap + &(i * 4)) **
		hfact (i < len) **
		hfact (~(ord = NO_ORDER)) **
		hfact (ord < max_order) **
		hfact ((2 EXP ord) divides (i2id i)) **
		hfact (ORD (nth inv_l i) = NO_ORDER) **
		hfact (REF (nth inv_l i) = 0) **
		(pool_const pool_pre) **
		(dlist_head_repr pool_pre 0 max_order inv_hl) **
		(free_area_repr (ifilter inv_l) start end inv_l) **
		(free_area_head_repr (ifilter inv_l) start end inv_dl) **
		(store_pageinfo_array vmemmap start end inv_l) **
		(store_zero_array (i2vi i) 0 (PAGE_SIZE * (2 EXP ord)) (PAGE_SIZE * (2 EXP ord)))
    `)]]
	while ((order + 1) < max_order && buddy != 0)
	{
		[[cstar::assert(`
		exists pg_v ord i inv_l inv_dl inv_hl buddy_v bi.
			hfact (&ord + &1 < &max_order && ~(buddy_v = &0)) **
			hfact ((buddy_v = &0) ||
				~(bi = i) &&
				(buddy_v = vmemmap + &(bi * 4)) &&
				(bi < len) &&
				(REF (nth inv_l bi) = 0) &&
				(ORD (nth inv_l bi) = ord) &&
				((2 EXP (SUC ord)) divides (i2id (MIN i bi))) &&
				(abs (&i - &bi) = &(2 EXP ord))) **
			data_at(&"max_order", Tuchar, &max_order) **
			data_at(&"order", Tuchar, &ord) **
			data_at(&"buddy", Tptr, buddy_v) **
			data_at(&"pool", Tptr, pool_pre) **
			data_at(&"pg", Tptr, pg_v) **
			data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
			hfact (pure_const) **
			hfact (dlist_node pool_pre (ifilter inv_l) inv_l inv_dl inv_hl start end inv_dl) **
			hfact (dlist_head pool_pre inv_l inv_dl 0 max_order inv_hl) **
			hfact (LENGTH inv_l = len) **
			hfact (LENGTH inv_dl = len) **
			hfact (LENGTH inv_hl = max_order) **
			hfact (pg_v = vmemmap + &(i * 4)) **
			hfact (i < len) **
			hfact (~(ord = NO_ORDER)) **
			hfact (ord < max_order) **
			hfact ((2 EXP ord) divides (i2id i)) **
			hfact (ORD (nth inv_l i) = NO_ORDER) **
			hfact (REF (nth inv_l i) = 0) **
			(pool_const pool_pre) **
			(dlist_head_repr pool_pre 0 max_order inv_hl) **
			(free_area_repr (ifilter inv_l) start end inv_l) **
			(free_area_head_repr (ifilter inv_l) start end inv_dl) **
			(store_pageinfo_array vmemmap start end inv_l) **
			(store_zero_array (i2vi i) 0 (PAGE_SIZE * (2 EXP ord)) (PAGE_SIZE * (2 EXP ord)))
		`)]];
		page_remove_from_list_pool(pool, buddy);
		[[cstar::assert(`
		exists new_l new_dl new_hl pg_v ord i inv_l (inv_dl : (addr#addr)list) (inv_hl : (addr#addr)list) buddy_v bi.
			hfact (new_l = modified inv_l bi (0, NO_ORDER)) **
			hfact (LENGTH new_l = len) **
			hfact (LENGTH new_dl = len) **
			hfact (LENGTH new_hl = max_order) **
			hfact (&ord + &1 < &max_order && ~(buddy_v = &0)) **
			hfact ((buddy_v = &0) ||
				~(bi = i) &&
				(buddy_v = vmemmap + &(bi * 4)) &&
				(bi < len) &&
				(REF (nth inv_l bi) = 0) &&
				(ORD (nth inv_l bi) = ord) &&
				((2 EXP (SUC ord)) divides (i2id (MIN i bi))) &&
				(abs (&i - &bi) = &(2 EXP ord))) **
			data_at(i2vi bi, Tptr, &0) **
			data_at(i2vi bi + &PTR_SIZE, Tptr, &0) **
			data_at(&"max_order", Tuchar, &max_order) **
			data_at(&"order", Tuchar, &ord) **
			data_at(&"buddy", Tptr, buddy_v) **
			data_at(&"pool", Tptr, pool_pre) **
			data_at(&"pg", Tptr, pg_v) **
			data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
			hfact (pure_const) **
			hfact (dlist_node pool_pre (ifilter new_l) new_l new_dl new_hl start end new_dl) **
			hfact (dlist_head pool_pre new_l new_dl 0 max_order new_hl) **
			hfact (LENGTH inv_l = len) **
			hfact (LENGTH inv_dl = len) **
			hfact (LENGTH inv_hl = max_order) **
			hfact (pg_v = vmemmap + &(i * 4)) **
			hfact (i < len) **
			hfact (~(ord = NO_ORDER)) **
			hfact (ord < max_order) **
			hfact ((2 EXP ord) divides (i2id i)) **
			hfact (ORD (nth inv_l i) = NO_ORDER) **
			hfact (REF (nth inv_l i) = 0) **
			(pool_const pool_pre) **
			(dlist_head_repr pool_pre 0 max_order new_hl) **
			(free_area_repr (ifilter inv_l) start end inv_l) **
			(free_area_head_repr (ifilter new_l) start end new_dl) **
			(store_pageinfo_array vmemmap start end inv_l) **
			(store_zero_array (i2vi i) 0 (PAGE_SIZE * (2 EXP ord)) (PAGE_SIZE * (2 EXP ord)))
		`)]];
		[[cstar::proof(
			// break store_pageinfo_array
			// modify data_at to &""
			// rewrite bi info
			thm proof5;
		)]];
		[[cstar::assert(`
		exists new_l new_dl new_hl pg_v ord i inv_l (inv_dl : (addr#addr)list) (inv_hl : (addr#addr)list) buddy_v bi.
			hfact (new_l = modified inv_l bi (0, NO_ORDER)) **
			hfact (LENGTH new_l = len) **
			hfact (LENGTH new_dl = len) **
			hfact (LENGTH new_hl = max_order) **
			hfact (&ord + &1 < &max_order) **
			hfact (~(bi = i)) **
			hfact (buddy_v = vmemmap + &(bi * 4)) **
			hfact (bi < len) **
			hfact (REF (nth inv_l bi) = 0) **
			hfact (ORD (nth inv_l bi) = ord) **
			hfact ((2 EXP (SUC ord)) divides (i2id (MIN i bi))) **
			hfact (abs (&i - &bi) = &(2 EXP ord)) **
			data_at(i2vi bi, Tptr, &0) **
			data_at(i2vi bi + &PTR_SIZE, Tptr, &0) **
			data_at(&"max_order", Tuchar, &max_order) **
			data_at(&"order", Tuchar, &ord) **
			data_at(&"buddy", Tptr, buddy_v) **
			data_at(&"pool", Tptr, pool_pre) **
			data_at(&"pg", Tptr, pg_v) **
			data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
			hfact (pure_const) **
			hfact (dlist_node pool_pre (ifilter new_l) new_l new_dl new_hl start end new_dl) **
			hfact (dlist_head pool_pre new_l new_dl 0 max_order new_hl) **
			hfact (LENGTH inv_l = len) **
			hfact (LENGTH inv_dl = len) **
			hfact (LENGTH inv_hl = max_order) **
			hfact (pg_v = vmemmap + &(i * 4)) **
			hfact (i < len) **
			hfact (~(ord = NO_ORDER)) **
			hfact (ord < max_order) **
			hfact ((2 EXP ord) divides (i2id i)) **
			hfact (ORD (nth inv_l i) = NO_ORDER) **
			hfact (REF (nth inv_l i) = 0) **
			(pool_const pool_pre) **
			(dlist_head_repr pool_pre 0 max_order new_hl) **
			(free_area_repr (ifilter inv_l) start end inv_l) **
			(free_area_head_repr (ifilter new_l) start end new_dl) **
			(store_pageinfo_array vmemmap start (i2id bi) (take inv_l bi)) **
				hfact (~(ord = NO_ORDER) ==> (ord < max_order) && ((2 EXP ord) divides (i2id bi))) **
				hfact (0 < REF_LIM) **
				(data_at (vmemmap + &(bi * 4), Tushort, &0)) **
				(data_at (&"buddy_v -> order", Tuchar, &ord)) **
				(undef_data_at (vmemmap + &(bi * 4 + 3), Tuchar)) **
			(store_pageinfo_array vmemmap (SUC (i2id bi)) end (rest inv_l (SUC bi))) **
			(store_zero_array (i2vi i) 0 (PAGE_SIZE * (2 EXP ord)) (PAGE_SIZE * (2 EXP ord)))
		`)]];
		buddy -> order = HYP_NO_ORDER;
		[[cstar::assert(`
		exists new_l new_dl new_hl pg_v ord i inv_l (inv_dl : (addr#addr)list) (inv_hl : (addr#addr)list) buddy_v bi.
			hfact (new_l = modified inv_l bi (0, NO_ORDER)) **
			hfact (LENGTH new_l = len) **
			hfact (LENGTH new_dl = len) **
			hfact (LENGTH new_hl = max_order) **
			hfact (&ord + &1 < &max_order) **
			hfact (~(bi = i)) **
			hfact (buddy_v = vmemmap + &(bi * 4)) **
			hfact (bi < len) **
			hfact (REF (nth inv_l bi) = 0) **
			hfact (ORD (nth inv_l bi) = ord) **
			hfact ((2 EXP (SUC ord)) divides (i2id (MIN i bi))) **
			hfact (abs (&i - &bi) = &(2 EXP ord)) **
			data_at(i2vi bi, Tptr, &0) **
			data_at(i2vi bi + &PTR_SIZE, Tptr, &0) **
			data_at(&"max_order", Tuchar, &max_order) **
			data_at(&"order", Tuchar, &ord) **
			data_at(&"buddy", Tptr, buddy_v) **
			data_at(&"pool", Tptr, pool_pre) **
			data_at(&"pg", Tptr, pg_v) **
			data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
			hfact (pure_const) **
			hfact (dlist_node pool_pre (ifilter new_l) new_l new_dl new_hl start end new_dl) **
			hfact (dlist_head pool_pre new_l new_dl 0 max_order new_hl) **
			hfact (LENGTH inv_l = len) **
			hfact (LENGTH inv_dl = len) **
			hfact (LENGTH inv_hl = max_order) **
			hfact (pg_v = vmemmap + &(i * 4)) **
			hfact (i < len) **
			hfact (~(ord = NO_ORDER)) **
			hfact (ord < max_order) **
			hfact ((2 EXP ord) divides (i2id i)) **
			hfact (ORD (nth inv_l i) = NO_ORDER) **
			hfact (REF (nth inv_l i) = 0) **
			(pool_const pool_pre) **
			(dlist_head_repr pool_pre 0 max_order new_hl) **
			(free_area_repr (ifilter inv_l) start end inv_l) **
			(free_area_head_repr (ifilter new_l) start end new_dl) **
			(store_pageinfo_array vmemmap start (i2id bi) (take inv_l bi)) **
				hfact (~(ord = NO_ORDER) ==> (ord < max_order) && ((2 EXP ord) divides (i2id bi))) **
				hfact (0 < REF_LIM) **
				(data_at (vmemmap + &(bi * 4), Tushort, &0)) **
				(data_at (&"buddy_v -> order", Tuchar, &HYP_NO_ORDER)) **
				(undef_data_at (vmemmap + &(bi * 4 + 3), Tuchar)) **
			(store_pageinfo_array vmemmap (SUC (i2id bi)) end (rest inv_l (SUC bi))) **
			(store_zero_array (i2vi i) 0 (PAGE_SIZE * (2 EXP ord)) (PAGE_SIZE * (2 EXP ord)))
		`)]];
		pg = min(pg, buddy);
		[[cstar::assert(`
		exists new_pg new_l new_dl new_hl pg_v ord i inv_l (inv_dl : (addr#addr)list) (inv_hl : (addr#addr)list) buddy_v bi.
			hfact (new_pg = min pg_v buddy_v) **
			hfact (new_l = modified inv_l bi (0, NO_ORDER)) **
			hfact (LENGTH new_l = len) **
			hfact (LENGTH new_dl = len) **
			hfact (LENGTH new_hl = max_order) **
			hfact (&ord + &1 < &max_order) **
			hfact (~(bi = i)) **
			hfact (buddy_v = vmemmap + &(bi * 4)) **
			hfact (bi < len) **
			hfact (REF (nth inv_l bi) = 0) **
			hfact (ORD (nth inv_l bi) = ord) **
			hfact ((2 EXP (SUC ord)) divides (i2id (MIN i bi))) **
			hfact (abs (&i - &bi) = &(2 EXP ord)) **
			data_at(i2vi bi, Tptr, &0) **
			data_at(i2vi bi + &PTR_SIZE, Tptr, &0) **
			data_at(&"max_order", Tuchar, &max_order) **
			data_at(&"order", Tuchar, &ord) **
			data_at(&"buddy", Tptr, buddy_v) **
			data_at(&"pool", Tptr, pool_pre) **
			data_at(&"pg", Tptr, new_pg) **
			data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
			hfact (pure_const) **
			hfact (dlist_node pool_pre (ifilter new_l) new_l new_dl new_hl start end new_dl) **
			hfact (dlist_head pool_pre new_l new_dl 0 max_order new_hl) **
			hfact (LENGTH inv_l = len) **
			hfact (LENGTH inv_dl = len) **
			hfact (LENGTH inv_hl = max_order) **
			hfact (pg_v = vmemmap + &(i * 4)) **
			hfact (i < len) **
			hfact (~(ord = NO_ORDER)) **
			hfact (ord < max_order) **
			hfact ((2 EXP ord) divides (i2id i)) **
			hfact (ORD (nth inv_l i) = NO_ORDER) **
			hfact (REF (nth inv_l i) = 0) **
			(pool_const pool_pre) **
			(dlist_head_repr pool_pre 0 max_order new_hl) **
			(free_area_repr (ifilter inv_l) start end inv_l) **
			(free_area_head_repr (ifilter new_l) start end new_dl) **
			(store_pageinfo_array vmemmap start (i2id bi) (take inv_l bi)) **
				hfact (~(ord = NO_ORDER) ==> (ord < max_order) && ((2 EXP ord) divides (i2id bi))) **
				hfact (0 < REF_LIM) **
				(data_at (vmemmap + &(bi * 4), Tushort, &0)) **
				(data_at (&"buddy_v -> order", Tuchar, &HYP_NO_ORDER)) **
				(undef_data_at (vmemmap + &(bi * 4 + 3), Tuchar)) **
			(store_pageinfo_array vmemmap (SUC (i2id bi)) end (rest inv_l (SUC bi))) **
			(store_zero_array (i2vi i) 0 (PAGE_SIZE * (2 EXP ord)) (PAGE_SIZE * (2 EXP ord)))
		`)]];		
        order = order + 1;
		[[cstar::assert(`
		exists new_pg new_l new_dl new_hl pg_v ord i inv_l (inv_dl : (addr#addr)list) (inv_hl : (addr#addr)list) buddy_v bi.
			hfact (new_pg = min pg_v buddy_v) **
			hfact (new_l = modified inv_l bi (0, NO_ORDER)) **
			hfact (LENGTH new_l = len) **
			hfact (LENGTH new_dl = len) **
			hfact (LENGTH new_hl = max_order) **
			hfact (&ord + &1 < &max_order) **
			hfact (~(bi = i)) **
			hfact (buddy_v = vmemmap + &(bi * 4)) **
			hfact (bi < len) **
			hfact (REF (nth inv_l bi) = 0) **
			hfact (ORD (nth inv_l bi) = ord) **
			hfact ((2 EXP (SUC ord)) divides (i2id (MIN i bi))) **
			hfact (abs (&i - &bi) = &(2 EXP ord)) **
			data_at(i2vi bi, Tptr, &0) **
			data_at(i2vi bi + &PTR_SIZE, Tptr, &0) **
			data_at(&"max_order", Tuchar, &max_order) **
			data_at(&"order", Tuchar, &ord + &1) **
			data_at(&"buddy", Tptr, buddy_v) **
			data_at(&"pool", Tptr, pool_pre) **
			data_at(&"pg", Tptr, new_pg) **
			data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
			hfact (pure_const) **
			hfact (dlist_node pool_pre (ifilter new_l) new_l new_dl new_hl start end new_dl) **
			hfact (dlist_head pool_pre new_l new_dl 0 max_order new_hl) **
			hfact (LENGTH inv_l = len) **
			hfact (LENGTH inv_dl = len) **
			hfact (LENGTH inv_hl = max_order) **
			hfact (pg_v = vmemmap + &(i * 4)) **
			hfact (i < len) **
			hfact (~(ord = NO_ORDER)) **
			hfact (ord < max_order) **
			hfact ((2 EXP ord) divides (i2id i)) **
			hfact (ORD (nth inv_l i) = NO_ORDER) **
			hfact (REF (nth inv_l i) = 0) **
			(pool_const pool_pre) **
			(dlist_head_repr pool_pre 0 max_order new_hl) **
			(free_area_repr (ifilter inv_l) start end inv_l) **
			(free_area_head_repr (ifilter new_l) start end new_dl) **
			(store_pageinfo_array vmemmap start (i2id bi) (take inv_l bi)) **
				hfact (~(ord = NO_ORDER) ==> (ord < max_order) && ((2 EXP ord) divides (i2id bi))) **
				hfact (0 < REF_LIM) **
				(data_at (vmemmap + &(bi * 4), Tushort, &0)) **
				(data_at (&"buddy_v -> order", Tuchar, &HYP_NO_ORDER)) **
				(undef_data_at (vmemmap + &(bi * 4 + 3), Tuchar)) **
			(store_pageinfo_array vmemmap (SUC (i2id bi)) end (rest inv_l (SUC bi))) **
			(store_zero_array (i2vi i) 0 (PAGE_SIZE * (2 EXP ord)) (PAGE_SIZE * (2 EXP ord)))
		`)]];
		[[cstar::proof(
			// merge spa
			// new_i = MIN i bi
			// new_pg = vmemmap + &(new_i * 4)
			// new_ord = ord + 1
			// 	hfact (new_pg = vmemmap + &(new_i * 4)) **
			// 	hfact (new_i < len) **
			// 	hfact ((2 EXP new_ord) divides (i2id new_i)) **
			// data_at
			// detele fact
			// far sza
			thm proof6;
		)]];
		[[cstar::assert(`
		exists new_ord new_i new_pg new_l new_dl new_hl buddy_v.
			data_at(&"max_order", Tuchar, &max_order) **
			data_at(&"order", Tuchar, &new_ord) **
			data_at(&"buddy", Tptr, buddy_v) **
			data_at(&"pool", Tptr, pool_pre) **
			data_at(&"pg", Tptr, new_pg) **
			data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
			hfact (pure_const) **
			hfact (dlist_node pool_pre (ifilter new_l) new_l new_dl new_hl start end new_dl) **
			hfact (dlist_head pool_pre new_l new_dl 0 max_order new_hl) **
			hfact (LENGTH new_l = len) **
			hfact (LENGTH new_dl = len) **
			hfact (LENGTH new_hl = max_order) **
			hfact (new_pg = vmemmap + &(new_i * 4)) **
			hfact (new_i < len) **
			hfact (~(new_ord = NO_ORDER)) **
			hfact (&new_ord < &max_order) **
			hfact ((2 EXP new_ord) divides (i2id new_i)) **
			hfact (ORD (nth new_l new_i) = NO_ORDER) **
			hfact (REF (nth new_l new_i) = 0) **
			(pool_const pool_pre) **
			(dlist_head_repr pool_pre 0 max_order new_hl) **
			(free_area_repr (ifilter new_l) start end new_l) **
			(free_area_head_repr (ifilter new_l) start end new_dl) **
			(store_pageinfo_array vmemmap start end new_l) **
			(store_zero_array (i2vi new_i) 0 (PAGE_SIZE * (2 EXP new_ord)) (PAGE_SIZE * (2 EXP new_ord)))
		`)]];
		buddy = __find_buddy_avail(pool, pg, order);
		[[cstar::assert(`
		exists new_pg new_ord new_i new_l new_dl new_hl new_buddy new_bi.
			hfact ((new_buddy = &0) ||
				~(new_bi = new_i) &&
				(new_buddy = vmemmap + &(new_bi * 4)) &&
				(new_bi < len) &&
				(REF (nth new_l new_bi) = 0) &&
				(ORD (nth new_l new_bi) = new_ord) &&
				((2 EXP (SUC new_ord)) divides (i2id (MIN new_i new_bi))) &&
				(abs (&new_i - &new_bi) = &(2 EXP new_ord))) **
			data_at(&"max_order", Tuchar, &max_order) **
			data_at(&"order", Tuchar, &new_ord) **
			data_at(&"buddy", Tptr, new_buddy) **
			data_at(&"pool", Tptr, pool_pre) **
			data_at(&"pg", Tptr, new_pg) **
			data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
			hfact (pure_const) **
			hfact (dlist_node pool_pre (ifilter new_l) new_l new_dl new_hl start end new_dl) **
			hfact (dlist_head pool_pre new_l new_dl 0 max_order new_hl) **
			hfact (LENGTH new_l = len) **
			hfact (LENGTH new_dl = len) **
			hfact (LENGTH new_hl = max_order) **
			hfact (new_pg = vmemmap + &(new_i * 4)) **
			hfact (new_i < len) **
			hfact (~(new_ord = NO_ORDER)) **
			hfact (&new_ord < &max_order) **
			hfact ((2 EXP new_ord) divides (i2id new_i)) **
			hfact (ORD (nth new_l new_i) = NO_ORDER) **
			hfact (REF (nth new_l new_i) = 0) **
			(pool_const pool_pre) **
			(dlist_head_repr pool_pre 0 max_order new_hl) **
			(free_area_repr (ifilter new_l) start end new_l) **
			(free_area_head_repr (ifilter new_l) start end new_dl) **
			(store_pageinfo_array vmemmap start end new_l) **
			(store_zero_array (i2vi new_i) 0 (PAGE_SIZE * (2 EXP new_ord)) (PAGE_SIZE * (2 EXP new_ord)))
		`)]];
	}
	[[cstar::assert(`
	exists pg_v ord i inv_l inv_dl inv_hl buddy_v bi.
		hfact (~(&ord + &1 < &max_order && ~(buddy_v = &0))) **
		hfact ((buddy_v = &0) ||
			~(bi = i) &&
			(buddy_v = vmemmap + &(bi * 4)) &&
			(bi < len) &&
			(REF (nth inv_l bi) = 0) &&
			(ORD (nth inv_l bi) = ord) &&
			((2 EXP (SUC ord)) divides (i2id (MIN i bi))) &&
			(abs (&i - &bi) = &(2 EXP ord))) **
		data_at(&"max_order", Tuchar, &max_order) **
		data_at(&"order", Tuchar, &ord) **
		data_at(&"buddy", Tptr, buddy_v) **
		data_at(&"pool", Tptr, pool_pre) **
		data_at(&"pg", Tptr, pg_v) **
		data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
		hfact (pure_const) **
		hfact (dlist_node pool_pre (ifilter inv_l) inv_l inv_dl inv_hl start end inv_dl) **
		hfact (dlist_head pool_pre inv_l inv_dl 0 max_order inv_hl) **
		hfact (LENGTH inv_l = len) **
		hfact (LENGTH inv_dl = len) **
		hfact (LENGTH inv_hl = max_order) **
		hfact (pg_v = vmemmap + &(i * 4)) **
		hfact (i < len) **
		hfact (~(ord = NO_ORDER)) **
		hfact (ord < max_order) **
		hfact ((2 EXP ord) divides (i2id i)) **
		hfact (ORD (nth inv_l i) = NO_ORDER) **
		hfact (REF (nth inv_l i) = 0) **
		(pool_const pool_pre) **
		(dlist_head_repr pool_pre 0 max_order inv_hl) **
		(free_area_repr (ifilter inv_l) start end inv_l) **
		(free_area_head_repr (ifilter inv_l) start end inv_dl) **
		(store_pageinfo_array vmemmap start end inv_l) **
		(store_zero_array (i2vi i) 0 (PAGE_SIZE * (2 EXP ord)) (PAGE_SIZE * (2 EXP ord)))
    `)]];
	[[cstar::proof(
		// break spa
		thm proof7;
	)]];
	[[cstar::assert(`
	exists pg_v ord i inv_l inv_dl inv_hl buddy_v bi.
		hfact (~(&ord + &1 < &max_order && ~(buddy_v = &0))) **
		hfact ((buddy_v = &0) ||
			~(bi = i) &&
			(buddy_v = vmemmap + &(bi * 4)) &&
			(bi < len) &&
			(REF (nth inv_l bi) = 0) &&
			(ORD (nth inv_l bi) = ord) &&
			((2 EXP (SUC ord)) divides (i2id (MIN i bi))) &&
			(abs (&i - &bi) = &(2 EXP ord))) **
		data_at(&"max_order", Tuchar, &max_order) **
		data_at(&"order", Tuchar, &ord) **
		data_at(&"buddy", Tptr, buddy_v) **
		data_at(&"pool", Tptr, pool_pre) **
		data_at(&"pg", Tptr, pg_v) **
		data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
		hfact (pure_const) **
		hfact (dlist_node pool_pre (ifilter inv_l) inv_l inv_dl inv_hl start end inv_dl) **
		hfact (dlist_head pool_pre inv_l inv_dl 0 max_order inv_hl) **
		hfact (LENGTH inv_l = len) **
		hfact (LENGTH inv_dl = len) **
		hfact (LENGTH inv_hl = max_order) **
		hfact (pg_v = vmemmap + &(i * 4)) **
		hfact (i < len) **
		hfact (~(ord = NO_ORDER)) **
		hfact (ord < max_order) **
		hfact ((2 EXP ord) divides (i2id i)) **
		hfact (ORD (nth inv_l i) = NO_ORDER) **
		hfact (REF (nth inv_l i) = 0) **
		(pool_const pool_pre) **
		(dlist_head_repr pool_pre 0 max_order inv_hl) **
		(free_area_repr (ifilter inv_l) start end inv_l) **
		(free_area_head_repr (ifilter inv_l) start end inv_dl) **
		(store_pageinfo_array vmemmap start (i2id i) (take inv_l i)) **
			(data_at (vmemmap + &(i * 4), Tushort, &0)) **
			(data_at (&"pg_v -> order", Tuchar, &NO_ORDER)) **
			(undef_data_at (vmemmap + &(i * 4 + 3), Tuchar)) **
		(store_pageinfo_array vmemmap (SUC (i2id i)) end (rest inv_l (SUC i))) **
		(store_zero_array (i2vi i) 0 (PAGE_SIZE * (2 EXP ord)) (PAGE_SIZE * (2 EXP ord)))
    `)]];
	pg -> order = order;
	[[cstar::assert(`
	exists pg_v ord i inv_l inv_dl inv_hl buddy_v bi.
		hfact (~(&ord + &1 < &max_order && ~(buddy_v = &0))) **
		hfact ((buddy_v = &0) ||
			~(bi = i) &&
			(buddy_v = vmemmap + &(bi * 4)) &&
			(bi < len) &&
			(REF (nth inv_l bi) = 0) &&
			(ORD (nth inv_l bi) = ord) &&
			((2 EXP (SUC ord)) divides (i2id (MIN i bi))) &&
			(abs (&i - &bi) = &(2 EXP ord))) **
		data_at(&"max_order", Tuchar, &max_order) **
		data_at(&"order", Tuchar, &ord) **
		data_at(&"buddy", Tptr, buddy_v) **
		data_at(&"pool", Tptr, pool_pre) **
		data_at(&"pg", Tptr, pg_v) **
		data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
		hfact (pure_const) **
		hfact (dlist_node pool_pre (ifilter inv_l) inv_l inv_dl inv_hl start end inv_dl) **
		hfact (dlist_head pool_pre inv_l inv_dl 0 max_order inv_hl) **
		hfact (LENGTH inv_l = len) **
		hfact (LENGTH inv_dl = len) **
		hfact (LENGTH inv_hl = max_order) **
		hfact (pg_v = vmemmap + &(i * 4)) **
		hfact (i < len) **
		hfact (~(ord = NO_ORDER)) **
		hfact (ord < max_order) **
		hfact ((2 EXP ord) divides (i2id i)) **
		hfact (ORD (nth inv_l i) = NO_ORDER) **
		hfact (REF (nth inv_l i) = 0) **
		(pool_const pool_pre) **
		(dlist_head_repr pool_pre 0 max_order inv_hl) **
		(free_area_repr (ifilter inv_l) start end inv_l) **
		(free_area_head_repr (ifilter inv_l) start end inv_dl) **
		(store_pageinfo_array vmemmap start (i2id i) (take inv_l i)) **
			(data_at (vmemmap + &(i * 4), Tushort, &0)) **
			(data_at (&"pg_v -> order", Tuchar, &ord)) **
			(undef_data_at (vmemmap + &(i * 4 + 3), Tuchar)) **
		(store_pageinfo_array vmemmap (SUC (i2id i)) end (rest inv_l (SUC i))) **
		(store_zero_array (i2vi i) 0 (PAGE_SIZE * (2 EXP ord)) (PAGE_SIZE * (2 EXP ord)))
    `)]];
	[[cstar::proof(
		// merge spa
		// break sza
		// merge far
		thm proof8;
	)]];
	[[cstar::assert(`
	exists pg_v ord i inv_l inv_dl inv_hl buddy_v bi.
		hfact (~(&ord + &1 < &max_order && ~(buddy_v = &0))) **
		hfact ((buddy_v = &0) ||
			~(bi = i) &&
			(buddy_v = vmemmap + &(bi * 4)) &&
			(bi < len) &&
			(REF (nth inv_l bi) = 0) &&
			(ORD (nth inv_l bi) = ord) &&
			((2 EXP (SUC ord)) divides (i2id (MIN i bi))) &&
			(abs (&i - &bi) = &(2 EXP ord))) **
		data_at(&"max_order", Tuchar, &max_order) **
		data_at(&"order", Tuchar, &ord) **
		data_at(&"buddy", Tptr, buddy_v) **
		data_at(&"pool", Tptr, pool_pre) **
		data_at(&"pg", Tptr, pg_v) **
		data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
		hfact (pure_const) **
		hfact (dlist_node pool_pre (ifilter inv_l) inv_l inv_dl inv_hl start end inv_dl) **
		hfact (dlist_head pool_pre inv_l inv_dl 0 max_order inv_hl) **
		hfact (LENGTH inv_l = len) **
		hfact (LENGTH inv_dl = len) **
		hfact (LENGTH inv_hl = max_order) **
		hfact (pg_v = vmemmap + &(i * 4)) **
		hfact (i < len) **
		hfact (~(ord = NO_ORDER)) **
		hfact (ord < max_order) **
		hfact ((2 EXP ord) divides (i2id i)) **
		hfact (ORD (nth inv_l i) = NO_ORDER) **
		hfact (REF (nth inv_l i) = 0) **
		(pool_const pool_pre) **
		(dlist_head_repr pool_pre 0 max_order inv_hl) **
		(free_area_repr (ifilter (modified inv_l i (0, ord))) start end (modified inv_l i (0, ord))) **
		(free_area_head_repr (ifilter inv_l) start end inv_dl) **
		(store_pageinfo_array vmemmap start end (modified inv_l i (0, ord))) **
		data_at(i2vi i, Tptr, &0) **
		data_at(i2vi i + &PTR_SIZE, Tptr, &0)
    `)]];
	page_add_to_list_pool(pool, pg, order);
	[[cstar::assert(`
	exists new_l new_dl new_hl pg_v ord i inv_l (inv_dl : (addr#addr)list) (inv_hl : (addr#addr)list) buddy_v bi.
		hfact (new_l = modified inv_l i (0, ord)) **
		hfact (LENGTH new_l = len) **
		hfact (LENGTH new_dl = len) **
		hfact (LENGTH new_hl = max_order) **
		hfact (~(&ord + &1 < &max_order && ~(buddy_v = &0))) **
		hfact ((buddy_v = &0) ||
			~(bi = i) &&
			(buddy_v = vmemmap + &(bi * 4)) &&
			(bi < len) &&
			(REF (nth inv_l bi) = 0) &&
			(ORD (nth inv_l bi) = ord) &&
			((2 EXP (SUC ord)) divides (i2id (MIN i bi))) &&
			(abs (&i - &bi) = &(2 EXP ord))) **
		data_at(&"max_order", Tuchar, &max_order) **
		data_at(&"order", Tuchar, &ord) **
		data_at(&"buddy", Tptr, buddy_v) **
		data_at(&"pool", Tptr, pool_pre) **
		data_at(&"pg", Tptr, pg_v) **
		data_at(&"__hyp_vmemmap", Tptr, vmemmap) **
		hfact (pure_const) **
		hfact (dlist_node pool_pre (ifilter new_l) new_l new_dl new_hl start end new_dl) **
		hfact (dlist_head pool_pre new_l new_dl 0 max_order new_hl) **
		hfact (LENGTH inv_l = len) **
		hfact (LENGTH inv_dl = len) **
		hfact (LENGTH inv_hl = max_order) **
		hfact (pg_v = vmemmap + &(i * 4)) **
		hfact (i < len) **
		hfact (~(ord = NO_ORDER)) **
		hfact (ord < max_order) **
		hfact ((2 EXP ord) divides (i2id i)) **
		hfact (ORD (nth inv_l i) = NO_ORDER) **
		hfact (REF (nth inv_l i) = 0) **
		(pool_const pool_pre) **
		(dlist_head_repr pool_pre 0 max_order new_hl) **
		(free_area_repr (ifilter (modified inv_l i (0, ord))) start end (modified inv_l i (0, ord))) **
		(free_area_head_repr (ifilter new_l) start end new_dl) **
		(store_pageinfo_array vmemmap start end (modified inv_l i (0, ord)))
    `)]];
	[[cstar::proof(
		// rewrite new_l
		// delete
		thm proof9;
	)]];
	[[cstar::assert(`
		exists new_l new_dl new_hl.
			total_repr pool vmemmap new_l new_dl new_hl
	`)]];
}