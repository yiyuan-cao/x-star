#include "attach.h"

#define HYP_MAX_ORDER 11
#define HYP_NO_ORDER 255
#define HYP_PAGE_SHIFT 12
#define HYP_PAGE_SIZE 4096
#define MAX_ORDER HYP_MAX_ORDER
#define NULL ((void*)0)

typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef long long s64;
typedef unsigned long long u64;
typedef unsigned long long phys_addr_t;

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

struct hyp_page * __hyp_vmemmap;

#define hyp_vmemmap ((struct hyp_page *)__hyp_vmemmap)

extern s64 hyp_physvirt_offset;

struct hyp_page* min(struct hyp_page *x, struct hyp_page *y)
/*@
Require
  emp
Ensure
  __return == MIN(x@pre, y@pre)
*/
;

void memset_page_zero(struct hyp_page *pg, u8 order)
/*@
With
  (i : Z)
  (order_v : Z)
  (vmemmap : addr)
  (PAGE_SIZE : Z)
Require
  data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) &&
  order_v == order &&
  pg == vmemmap + i * 4 &&
  store_undef_array(i2vi(i), 0, PAGE_SIZE * EXP(2, order_v), PAGE_SIZE * EXP(2, order_v))
Ensure
  data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) &&
  order_v == order@pre &&
  pg@pre == vmemmap + i * 4 &&
  store_zero_array(i2vi(i), 0, PAGE_SIZE * EXP(2, order_v), PAGE_SIZE * EXP(2, order_v))
*/
;

static struct hyp_page* __find_buddy_avail(struct hyp_pool *pool, struct hyp_page *pg, u8 order)
/*@
With
  (pi : Z)
  (order_v : Z)
  (vmemmap : addr)
  (l : list (Z * Z))
  (start : Z)
  (end : Z)
  (len : Z)
Require
  data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) &&
  order_v == order &&
  pool_const(pool) *
  store_pageinfo_array(vmemmap, start, end, l) &&
  LENGTH(l) == len &&
  pg == vmemmap + pi * 4 &&
  pi < len &&
  divides(EXP(2, order_v), i2id(pi))
Ensure
  exists bi,
  data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) &&
  order_v == order@pre &&
  (__return == 0 ||
   bi != pi &&
   __return == vmemmap + bi * 4 &&
   bi < len &&
   REF(nth(l, bi)) == 0 &&
   ORD(nth(l, bi)) == order_v &&
   divides(EXP(2, SUC(order_v)), i2id(MIN(pi, bi))) &&
   abs(pi - bi) == EXP(2, order_v)) &&
  pool_const(pool@pre) *
  store_pageinfo_array(vmemmap, start, end, l) &&
  LENGTH(l) == len &&
  pg@pre == vmemmap + pi * 4 &&
  pi < len &&
  divides(EXP(2, order_v), i2id(pi))
*/
;

void page_remove_from_list_pool(struct hyp_pool *pool, struct hyp_page *pg)
/*@
With
  (pi : Z)
  (order : Z)
  (vmemmap : addr)
  (l : list (Z * Z))
  (dl : list (addr * addr))
  (hl : list (addr * addr))
  (start : Z)
  (end : Z)
  (len : Z)
  (max_order : Z)
  (NO_ORDER : Z)
Require
  data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) &&
  pure_const &&
  LENGTH(l) == len &&
  LENGTH(dl) == len &&
  LENGTH(hl) == max_order &&
  pg == vmemmap + pi * 4 &&
  pi < len &&
  ORD(nth(l, pi)) == order &&
  REF(nth(l, pi)) == 0 &&
  order < max_order &&
  dlist_node(pool, ifilter(l), l, dl, hl, start, end, dl) &&
  dlist_head(pool, l, dl, 0, max_order, hl) &&
  free_area_head_repr(ifilter(l), start, end, dl)
Ensure
  exists new_l new_dl new_hl,
  data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) &&
  new_l == modified(l, pi, 0, NO_ORDER) &&
  pure_const &&
  LENGTH(l) == len &&
  LENGTH(dl) == len &&
  LENGTH(hl) == max_order &&
  LENGTH(new_l) == len &&
  LENGTH(new_dl) == len &&
  LENGTH(new_hl) == max_order &&
  pg@pre == vmemmap + pi * 4 &&
  pi < len &&
  ORD(nth(l, pi)) == order &&
  REF(nth(l, pi)) == 0 &&
  order < max_order &&
  dlist_node(pool@pre, ifilter(new_l), new_l, new_dl, new_hl, start, end, new_dl) &&
  dlist_head(pool@pre, new_l, new_dl, 0, max_order, new_hl) &&
  free_area_head_repr(ifilter(new_l), start, end, new_dl) *
  data_at(i2vi(pi), void*, 0) *
  data_at(i2vi(pi) + sizeof(void*), void*, 0)
*/
;

void page_add_to_list_pool(struct hyp_pool *pool, struct hyp_page *pg, u8 order)
/*@
With
  (pi : Z)
  (order_v : Z)
  (vmemmap : addr)
  (l : list (Z * Z))
  (dl : list (addr * addr))
  (hl : list (addr * addr))
  (start : Z)
  (end : Z)
  (len : Z)
  (max_order : Z)
  (NO_ORDER : Z)
Require
  data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) &&
  order_v == order &&
  pure_const &&
  LENGTH(l) == len &&
  LENGTH(dl) == len &&
  LENGTH(hl) == max_order &&
  pg == vmemmap + pi * 4 &&
  pi < len &&
  ORD(nth(l, pi)) == NO_ORDER &&
  REF(nth(l, pi)) == 0 &&
  order_v < max_order &&
  dlist_node(pool, ifilter(l), l, dl, hl, start, end, dl) &&
  dlist_head(pool, l, dl, 0, max_order, hl) &&
  dlist_head_repr(pool, 0, max_order, hl) *
  free_area_head_repr(ifilter(l), start, end, dl) *
  data_at(i2vi(pi), void*, 0) *
  data_at(i2vi(pi) + sizeof(void*), void*, 0)
Ensure
  exists new_l new_dl new_hl,
  data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) &&
  pool == pool@pre &&
  pg == pg@pre &&
  order_v == order@pre &&
  new_l == modified(l, pi, 0, order_v) &&
  pure_const &&
  LENGTH(l) == len &&
  LENGTH(dl) == len &&
  LENGTH(hl) == max_order &&
  LENGTH(new_l) == len &&
  LENGTH(new_dl) == len &&
  LENGTH(new_hl) == max_order &&
  pg@pre == vmemmap + pi * 4 &&
  pi < len &&
  ORD(nth(l, pi)) == NO_ORDER &&
  REF(nth(l, pi)) == 0 &&
  order_v < max_order &&
  dlist_node(pool@pre, ifilter(new_l), new_l, new_dl, new_hl, start, end, new_dl) &&
  dlist_head(pool@pre, new_l, new_dl, 0, max_order, new_hl) &&
  dlist_head_repr(pool@pre, 0, max_order, new_hl) *
  free_area_head_repr(ifilter(new_l), start, end, new_dl)
*/
;

static void __hyp_attach_page(struct hyp_pool *pool, struct hyp_page *pg)
/*@
With
  (l : list (Z * Z))
  (dl : list (addr * addr))
  (hl : list (addr * addr))
  (pi : Z)
  (pref : Z)
  (porder : Z)
  (vmemmap : addr)
  (start : Z)
  (end : Z)
  (len : Z)
  (max_order : Z)
  (NO_ORDER : Z)
  (REF_LIM : Z)
  (PAGE_SIZE : Z)
Require
  data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) &&
  pg == vmemmap + pi * 4 && pi < len &&
  pref == REF(nth(l, pi)) && pref > 0 &&
  porder == ORD(nth(l, pi)) && porder != NO_ORDER &&
  LENGTH(l) == len &&
  LENGTH(dl) == len &&
  LENGTH(hl) == max_order &&
  pure_const &&
  dlist_head(pool, l, dl, 0, max_order, hl) &&
  dlist_node(pool, ifilter(l), l, dl, hl, start, end, dl) &&
  pool_const(pool) *
  dlist_head_repr(pool, 0, max_order, hl) *
  free_area_repr(ifilter(l), start, end, l) *
  free_area_head_repr(ifilter(l), start, end, dl) *
  store_pageinfo_array(vmemmap, start, i2id(pi), take(l, pi)) &&
  (porder == NO_ORDER ||
   porder != NO_ORDER && porder < max_order && divides(EXP(2, porder), i2id(pi))) &&
  pref < REF_LIM &&
  data_at(vmemmap + pi * 4, u16, 0) *
  data_at(vmemmap + pi * 4 + 2, u8, porder) *
  undef_data_at(vmemmap + pi * 4 + 3, u8) *
  store_pageinfo_array(vmemmap, SUC(i2id(pi)), end, rest(l, SUC(pi))) *
  store_undef_array(i2vi(pi), 0, PAGE_SIZE * EXP(2, porder), PAGE_SIZE * EXP(2, porder))
Ensure
  exists new_l new_dl new_hl,
  LENGTH(new_l) == len &&
  LENGTH(new_dl) == len &&
  LENGTH(new_hl) == max_order &&
  pure_const &&
  dlist_head(pool, new_l, new_dl, 0, max_order, new_hl) &&
  dlist_node(pool, ifilter(new_l), new_l, new_dl, new_hl, start, end, new_dl) &&
  pool_const(pool) *
  dlist_head_repr(pool, 0, max_order, new_hl) *
  free_area_repr(ifilter(new_l), start, end, new_l) *
  free_area_head_repr(ifilter(new_l), start, end, new_dl) *
  store_pageinfo_array(vmemmap, start, end, new_l)
*/
{
  /*@ Assert
    data_at(&pool, struct hyp_pool*, pool) *
    data_at(&pg, struct hyp_page*, pg) *
    data_at(&__hyp_vmemmap, struct hyp_page *, vmemmap) *
    pure_const &&
    dlist_node(pool, ifilter(l), l, dl, hl, start, end, dl) &&
    dlist_head(pool, l, dl, 0, max_order, hl) &&
    LENGTH(l) == len &&
    LENGTH(dl) == len &&
    LENGTH(hl) == max_order &&
    pg == vmemmap + pi * 4 &&
    pi < len &&
    porder != NO_ORDER &&
    pref > 0 &&
    pref == REF(nth(l, pi)) &&
    porder == ORD(nth(l, pi)) &&
    pool_const(pool) *
    dlist_head_repr(pool, 0, max_order, hl) *
    free_area_repr(ifilter(l), start, end, l) *
    free_area_head_repr(ifilter(l), start, end, dl) *
    store_pageinfo_array(vmemmap, start, i2id(pi), take(l, pi)) *
    (porder == NO_ORDER ||
     porder != NO_ORDER && porder < max_order && divides(EXP(2, porder), i2id(pi))) &&
    pref < REF_LIM &&
    data_at(vmemmap + pi * 4, u16, 0) *
    data_at(vmemmap + pi * 4 + 2, u8, porder) *
    undef_data_at(vmemmap + pi * 4 + 3, u8) *
    store_pageinfo_array(vmemmap, SUC(i2id(pi)), end, rest(l, SUC(pi))) *
    store_undef_array(i2vi(pi), 0, PAGE_SIZE * EXP(2, porder), PAGE_SIZE * EXP(2, porder))
  */
  struct hyp_page *buddy = NULL;
  /*@ Assert
    data_at(&buddy, struct hyp_page*, 0) *
    data_at(&pool, struct hyp_pool*, pool) *
    data_at(&pg, struct hyp_page*, pg) *
    data_at(&__hyp_vmemmap, struct hyp_page *, vmemmap) *
    pure_const &&
    dlist_node(pool, ifilter(l), l, dl, hl, start, end, dl) &&
    dlist_head(pool, l, dl, 0, max_order, hl) &&
    LENGTH(l) == len &&
    LENGTH(dl) == len &&
    LENGTH(hl) == max_order &&
    pg == vmemmap + pi * 4 &&
    pi < len &&
    porder != NO_ORDER &&
    pref > 0 &&
    pref == REF(nth(l, pi)) &&
    porder == ORD(nth(l, pi)) &&
    pool_const(pool) *
    dlist_head_repr(pool, 0, max_order, hl) *
    free_area_repr(ifilter(l), start, end, l) *
    free_area_head_repr(ifilter(l), start, end, dl) *
    store_pageinfo_array(vmemmap, start, i2id(pi), take(l, pi)) *
    (porder == NO_ORDER ||
     porder != NO_ORDER && porder < max_order && divides(EXP(2, porder), i2id(pi))) &&
    pref < REF_LIM &&
    data_at(vmemmap + pi * 4, u16, 0) *
    data_at(vmemmap + pi * 4 + 2, u8, porder) *
    undef_data_at(vmemmap + pi * 4 + 3, u8) *
    store_pageinfo_array(vmemmap, SUC(i2id(pi)), end, rest(l, SUC(pi))) *
    store_undef_array(i2vi(pi), 0, PAGE_SIZE * EXP(2, porder), PAGE_SIZE * EXP(2, porder))
  */
  // proof1
  /*@ Assert
    data_at(&buddy, struct hyp_page*, 0) *
    data_at(&pool, struct hyp_pool*, pool) *
    data_at(&pg, struct hyp_page*, pg) *
    data_at(&__hyp_vmemmap, struct hyp_page *, vmemmap) *
    pure_const &&
    dlist_node(pool, ifilter(l), l, dl, hl, start, end, dl) &&
    dlist_head(pool, l, dl, 0, max_order, hl) &&
    LENGTH(l) == len &&
    LENGTH(dl) == len &&
    LENGTH(hl) == max_order &&
    pg == vmemmap + pi * 4 &&
    pi < len &&
    porder != NO_ORDER &&
    pref > 0 &&
    pref == REF(nth(l, pi)) &&
    porder == ORD(nth(l, pi)) &&
    data_at(pool + LIST_HEAD_SIZE * MAX_ORDER, u64, id2ph(start)) *
    data_at(pool + LIST_HEAD_SIZE * MAX_ORDER + 8, u64, id2ph(end)) *
    data_at(&pool->max_order, u8, max_order) *
    dlist_head_repr(pool, 0, max_order, hl) *
    free_area_repr(ifilter(l), start, end, l) *
    free_area_head_repr(ifilter(l), start, end, dl) *
    store_pageinfo_array(vmemmap, start, i2id(pi), take(l, pi)) *
    (porder == NO_ORDER ||
     porder != NO_ORDER && porder < max_order && divides(EXP(2, porder), i2id(pi))) &&
    pref < REF_LIM &&
    data_at(vmemmap + pi * 4, u16, 0) *
    data_at(&pg->order, u8, porder) *
    undef_data_at(vmemmap + pi * 4 + 3, u8) *
    store_pageinfo_array(vmemmap, SUC(i2id(pi)), end, rest(l, SUC(pi))) *
    store_undef_array(i2vi(pi), 0, PAGE_SIZE * EXP(2, porder), PAGE_SIZE * EXP(2, porder))
  */
  u8 order = pg -> order;
  /*@ Assert
    data_at(&order, u8, porder) *
    data_at(&buddy, struct hyp_page*, 0) *
    data_at(&pool, struct hyp_pool*, pool) *
    data_at(&pg, struct hyp_page*, pg) *
    data_at(&__hyp_vmemmap, struct hyp_page *, vmemmap) *
    pure_const &&
    dlist_node(pool, ifilter(l), l, dl, hl, start, end, dl) &&
    dlist_head(pool, l, dl, 0, max_order, hl) &&
    LENGTH(l) == len &&
    LENGTH(dl) == len &&
    LENGTH(hl) == max_order &&
    pg == vmemmap + pi * 4 &&
    pi < len &&
    porder != NO_ORDER &&
    pref > 0 &&
    pref == REF(nth(l, pi)) &&
    porder == ORD(nth(l, pi)) &&
    data_at(pool + LIST_HEAD_SIZE * MAX_ORDER, u64, id2ph(start)) *
    data_at(pool + LIST_HEAD_SIZE * MAX_ORDER + 8, u64, id2ph(end)) *
    data_at(&pool->max_order, u8, max_order) *
    dlist_head_repr(pool, 0, max_order, hl) *
    free_area_repr(ifilter(l), start, end, l) *
    free_area_head_repr(ifilter(l), start, end, dl) *
    store_pageinfo_array(vmemmap, start, i2id(pi), take(l, pi)) *
    (porder == NO_ORDER ||
     porder != NO_ORDER && porder < max_order && divides(EXP(2, porder), i2id(pi))) &&
    pref < REF_LIM &&
    data_at(vmemmap + pi * 4, u16, 0) *
    data_at(&pg->order, u8, porder) *
    undef_data_at(vmemmap + pi * 4 + 3, u8) *
    store_pageinfo_array(vmemmap, SUC(i2id(pi)), end, rest(l, SUC(pi))) *
    store_undef_array(i2vi(pi), 0, PAGE_SIZE * EXP(2, porder), PAGE_SIZE * EXP(2, porder))
  */
	pg -> order = (u8)HYP_NO_ORDER;
  /*@ Assert
    data_at(&order, u8, porder) *
    data_at(&buddy, struct hyp_page*, 0) *
    data_at(&pool, struct hyp_pool*, pool) *
    data_at(&pg, struct hyp_page*, pg) *
    data_at(&__hyp_vmemmap, struct hyp_page *, vmemmap) *
    pure_const &&
    dlist_node(pool, ifilter(l), l, dl, hl, start, end, dl) &&
    dlist_head(pool, l, dl, 0, max_order, hl) &&
    LENGTH(l) == len &&
    LENGTH(dl) == len &&
    LENGTH(hl) == max_order &&
    pg == vmemmap + pi * 4 &&
    pi < len &&
    porder != NO_ORDER &&
    pref > 0 &&
    pref == REF(nth(l, pi)) &&
    porder == ORD(nth(l, pi)) &&
    data_at(pool + LIST_HEAD_SIZE * MAX_ORDER, u64, id2ph(start)) *
    data_at(pool + LIST_HEAD_SIZE * MAX_ORDER + 8, u64, id2ph(end)) *
    data_at(&pool->max_order, u8, max_order) *
    dlist_head_repr(pool, 0, max_order, hl) *
    free_area_repr(ifilter(l), start, end, l) *
    free_area_head_repr(ifilter(l), start, end, dl) *
    store_pageinfo_array(vmemmap, start, i2id(pi), take(l, pi)) *
    (porder == NO_ORDER ||
     porder != NO_ORDER && porder < max_order && divides(EXP(2, porder), i2id(pi))) &&
    pref < REF_LIM &&
    data_at(vmemmap + pi * 4, u16, 0) *
    data_at(&pg->order, u8, HYP_NO_ORDER) *
    undef_data_at(vmemmap + pi * 4 + 3, u8) *
    store_pageinfo_array(vmemmap, SUC(i2id(pi)), end, rest(l, SUC(pi))) *
    store_undef_array(i2vi(pi), 0, PAGE_SIZE * EXP(2, porder), PAGE_SIZE * EXP(2, porder))
  */
	u8 max_order_ = pool -> max_order;
  /*@ Assert
    data_at(&max_order_, u8, max_order) *
    data_at(&order, u8, porder) *
    data_at(&buddy, struct hyp_page*, 0) *
    data_at(&pool, struct hyp_pool*, pool) *
    data_at(&pg, struct hyp_page*, pg) *
    data_at(&__hyp_vmemmap, struct hyp_page *, vmemmap) *
    pure_const &&
    dlist_node(pool, ifilter(l), l, dl, hl, start, end, dl) &&
    dlist_head(pool, l, dl, 0, max_order, hl) &&
    LENGTH(l) == len &&
    LENGTH(dl) == len &&
    LENGTH(hl) == max_order &&
    pg == vmemmap + pi * 4 &&
    pi < len &&
    porder != NO_ORDER &&
    pref > 0 &&
    pref == REF(nth(l, pi)) &&
    porder == ORD(nth(l, pi)) &&
    data_at(pool + LIST_HEAD_SIZE * MAX_ORDER, u64, id2ph(start)) *
    data_at(pool + LIST_HEAD_SIZE * MAX_ORDER + 8, u64, id2ph(end)) *
    data_at(&pool->max_order, u8, max_order) *
    dlist_head_repr(pool, 0, max_order, hl) *
    free_area_repr(ifilter(l), start, end, l) *
    free_area_head_repr(ifilter(l), start, end, dl) *
    store_pageinfo_array(vmemmap, start, i2id(pi), take(l, pi)) *
    (porder == NO_ORDER ||
     porder != NO_ORDER && porder < max_order && divides(EXP(2, porder), i2id(pi))) &&
    pref < REF_LIM &&
    data_at(vmemmap + pi * 4, u16, 0) *
    data_at(&pg->order, u8, HYP_NO_ORDER) *
    undef_data_at(vmemmap + pi * 4 + 3, u8) *
    store_pageinfo_array(vmemmap, SUC(i2id(pi)), end, rest(l, SUC(pi))) *
    store_undef_array(i2vi(pi), 0, PAGE_SIZE * EXP(2, porder), PAGE_SIZE * EXP(2, porder))
  */
  // proof 2
  /*@ Assert
    data_at(&max_order_, u8, max_order) *
    data_at(&order, u8, porder) *
    data_at(&buddy, struct hyp_page*, 0) *
    data_at(&pool, struct hyp_pool*, pool) *
    data_at(&pg, struct hyp_page*, pg) *
    data_at(&__hyp_vmemmap, struct hyp_page *, vmemmap) *
    pure_const &&
    dlist_node(pool, ifilter(l), l, dl, hl, start, end, dl) &&
    dlist_head(pool, l, dl, 0, max_order, hl) &&
    LENGTH(l) == len &&
    LENGTH(dl) == len &&
    LENGTH(hl) == max_order &&
    pg == vmemmap + pi * 4 &&
    pi < len &&
    porder != NO_ORDER &&
    pref > 0 &&
    pref == REF(nth(l, pi)) &&
    porder == ORD(nth(l, pi)) &&
    pool_const(pool) *
    dlist_head_repr(pool, 0, max_order, hl) *
    free_area_repr(ifilter(l), start, end, l) *
    free_area_head_repr(ifilter(l), start, end, dl) *
    store_pageinfo_array(vmemmap, start, i2id(pi), take(l, pi)) *
    (porder < max_order && divides(EXP(2, porder), i2id(pi))) &&
    pref < REF_LIM &&
    data_at(vmemmap + pi * 4, u16, 0) *
    data_at(vmemmap + pi * 4 + 2, u8, HYP_NO_ORDER) *
    undef_data_at(vmemmap + pi * 4 + 3, u8) *
    store_pageinfo_array(vmemmap, SUC(i2id(pi)), end, rest(l, SUC(pi))) *
    store_undef_array(i2vi(pi), 0, PAGE_SIZE * EXP(2, porder), PAGE_SIZE * EXP(2, porder))
  */
  memset_page_zero(pg, order) /*@
    where pi = pi, order_v = porder, vmemmap = vmemmap, PAGE_SIZE = PAGE_SIZE */;
  /*@ Assert
    data_at(&max_order_, u8, max_order) *
    data_at(&order, u8, porder) *
    data_at(&buddy, struct hyp_page*, 0) *
    data_at(&pool, struct hyp_pool*, pool) *
    data_at(&pg, struct hyp_page*, pg) *
    data_at(&__hyp_vmemmap, struct hyp_page *, vmemmap) *
    pure_const &&
    dlist_node(pool, ifilter(l), l, dl, hl, start, end, dl) &&
    dlist_head(pool, l, dl, 0, max_order, hl) &&
    LENGTH(l) == len &&
    LENGTH(dl) == len &&
    LENGTH(hl) == max_order &&
    pg == vmemmap + pi * 4 &&
    pi < len &&
    porder != NO_ORDER &&
    pref > 0 &&
    pref == REF(nth(l, pi)) &&
    porder == ORD(nth(l, pi)) &&
    pool_const(pool) *
    dlist_head_repr(pool, 0, max_order, hl) *
    free_area_repr(ifilter(l), start, end, l) *
    free_area_head_repr(ifilter(l), start, end, dl) *
    store_pageinfo_array(vmemmap, start, i2id(pi), take(l, pi)) *
    (porder < max_order && divides(EXP(2, porder), i2id(pi))) &&
    pref < REF_LIM &&
    data_at(vmemmap + pi * 4, u16, 0) *
    data_at(vmemmap + pi * 4 + 2, u8, HYP_NO_ORDER) *
    undef_data_at(vmemmap + pi * 4 + 3, u8) *
    store_pageinfo_array(vmemmap, SUC(i2id(pi)), end, rest(l, SUC(pi))) *
    store_zero_array(i2vi(pi), 0, PAGE_SIZE * EXP(2, porder), PAGE_SIZE * EXP(2, porder))
  */
  // proof3
  /*@ Assert
    data_at(&max_order_, u8, max_order) *
    data_at(&order, u8, porder) *
    data_at(&buddy, struct hyp_page*, 0) *
    data_at(&pool, struct hyp_pool*, pool) *
    data_at(&pg, struct hyp_page*, pg) *
    data_at(&__hyp_vmemmap, struct hyp_page *, vmemmap) *
    pure_const &&
    dlist_node(pool, ifilter(modified(l, pi, 0, NO_ORDER)), modified(l, pi, 0, NO_ORDER), dl, hl, start, end, dl) &&
    dlist_head(pool, modified(l, pi, 0, NO_ORDER), dl, 0, max_order, hl) &&
    LENGTH(modified(l, pi, 0, NO_ORDER)) == len &&
    LENGTH(dl) == len &&
    LENGTH(hl) == max_order &&
    pg == vmemmap + pi * 4 &&
    pi < len &&
    porder != NO_ORDER &&
    porder < max_order &&
    divides(EXP(2, porder), i2id(pi)) &&
    ORD(nth(modified(l, pi, 0, NO_ORDER), pi)) == NO_ORDER &&
    REF(nth(modified(l, pi, 0, NO_ORDER), pi)) == 0 &&
    pool_const(pool) *
    dlist_head_repr(pool, 0, max_order, hl) *
    free_area_repr(ifilter(l), start, end, l) *
    free_area_head_repr(ifilter(l), start, end, dl) *
    store_pageinfo_array(vmemmap, start, end, modified(l, pi, 0, NO_ORDER)) *
    store_zero_array(i2vi(pi), 0, PAGE_SIZE * EXP(2, porder), PAGE_SIZE * EXP(2, porder))
  */
  buddy = __find_buddy_avail(pool, pg, order) /*@
    where pi = pi, order_v = porder, vmemmap = vmemmap, l = modified(l, pi, 0, NO_ORDER), start = start, end = end, len = len */;
  /*@ Assert
    exists buddy_v bi,
    (buddy_v == 0 ||
     bi == pi &&
     buddy_v == vmemmap + bi * 4 &&
     bi < len &&
     REF(nth(modified(l, pi, 0, NO_ORDER), bi)) == 0 &&
     ORD(nth(modified(l, pi, 0, NO_ORDER), bi)) == porder &&
     divides(EXP(2, SUC(porder)), i2id(MIN(pi, bi))) &&
     abs(pi - bi) == EXP(2, porder)) &&
    data_at(&max_order_, u8, max_order) *
    data_at(&order, u8, porder) *
    data_at(&buddy, struct hyp_page*, 0) *
    data_at(&pool, struct hyp_pool*, pool) *
    data_at(&pg, struct hyp_page*, pg) *
    data_at(&__hyp_vmemmap, struct hyp_page *, vmemmap) *
    pure_const &&
    dlist_node(pool, ifilter(modified(l, pi, 0, NO_ORDER)), modified(l, pi, 0, NO_ORDER), dl, hl, start, end, dl) &&
    dlist_head(pool, modified(l, pi, 0, NO_ORDER), dl, 0, max_order, hl) &&
    LENGTH(modified(l, pi, 0, NO_ORDER)) == len &&
    LENGTH(dl) == len &&
    LENGTH(hl) == max_order &&
    pg == vmemmap + pi * 4 &&
    pi < len &&
    porder != NO_ORDER &&
    porder < max_order &&
    divides(EXP(2, porder), i2id(pi)) &&
    ORD(nth(modified(l, pi, 0, NO_ORDER), pi)) == NO_ORDER &&
    REF(nth(modified(l, pi, 0, NO_ORDER), pi)) == 0 &&
    pool_const(pool) *
    dlist_head_repr(pool, 0, max_order, hl) *
    free_area_repr(ifilter(l), start, end, l) *
    free_area_head_repr(ifilter(l), start, end, dl) *
    store_pageinfo_array(vmemmap, start, end, modified(l, pi, 0, NO_ORDER)) *
    store_zero_array(i2vi(pi), 0, PAGE_SIZE * EXP(2, porder), PAGE_SIZE * EXP(2, porder))
  */
  // proof4
  /*@ Assert Inv
    exists buddy_v bi inv_l inv_dl inv_hl i ord pg_v,
    (buddy_v == 0 ||
     bi != i &&
     buddy_v == vmemmap + bi * 4 &&
     bi < len &&
     REF(nth(inv_l, bi)) == 0 &&
     ORD(nth(inv_l, bi)) == ord &&
     divides(EXP(2, SUC(ord)), i2id(MIN(i, bi))) &&
     abs(i - bi) == EXP(2, ord)) &&
    data_at(&max_order_, u8, max_order) *
    data_at(&order, u8, ord) *
    data_at(&buddy, struct hyp_page*, buddy_v) *
    data_at(&pool, struct hyp_pool*, pool) *
    data_at(&pg, struct hyp_page*, pg_v) *
    data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) &&
    pure_const &&
    dlist_node(pool, ifilter(inv_l), inv_l, inv_dl, inv_hl, start, end, inv_dl) &&
    dlist_head(pool, inv_l, inv_dl, 0, max_order, inv_hl) &&
    LENGTH(inv_l) == len &&
    LENGTH(inv_dl) == len &&
    LENGTH(inv_hl) == max_order &&
    pg_v == vmemmap + i * 4 &&
    i < len &&
    ord != NO_ORDER &&
    ord < max_order &&
    divides(EXP(2, ord), i2id(i)) &&
    ORD(nth(inv_l, i)) == NO_ORDER &&
    REF(nth(inv_l, i)) == 0 &&
    pool_const(pool) *
    dlist_head_repr(pool, 0, max_order, inv_hl) *
    free_area_repr(ifilter(inv_l), start, end, inv_l) *
    free_area_head_repr(ifilter(inv_l), start, end, inv_dl) *
    store_pageinfo_array(vmemmap, start, end, inv_l) *
    store_zero_array(i2vi(i), 0, PAGE_SIZE * EXP(2, ord), PAGE_SIZE * EXP(2, ord))
  */
  while (order + (u8)1 < max_order_ && buddy != 0) {
    /*@ Assert
      exists buddy_v bi inv_l inv_dl inv_hl i ord pg_v,
      ord + 1 < max_order && buddy_v != 0 &&
      (buddy_v == 0 ||
       bi != i &&
       buddy_v == vmemmap + bi * 4 &&
       bi < len &&
       REF(nth(inv_l, bi)) == 0 &&
       ORD(nth(inv_l, bi)) == ord &&
       divides(EXP(2, SUC(ord)), i2id(MIN(i, bi))) &&
       abs(i - bi) == EXP(2, ord)) &&
      data_at(&max_order_, u8, max_order) *
      data_at(&order, u8, ord) *
      data_at(&buddy, struct hyp_page*, buddy_v) *
      data_at(&pool, struct hyp_pool*, pool) *
      data_at(&pg, struct hyp_page*, pg_v) *
      data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) &&
      pure_const &&
      dlist_node(pool, ifilter(inv_l), inv_l, inv_dl, inv_hl, start, end, inv_dl) &&
      dlist_head(pool, inv_l, inv_dl, 0, max_order, inv_hl) &&
      LENGTH(inv_l) == len &&
      LENGTH(inv_dl) == len &&
      LENGTH(inv_hl) == max_order &&
      pg_v == vmemmap + i * 4 &&
      i < len &&
      ord != NO_ORDER &&
      ord < max_order &&
      divides(EXP(2, ord), i2id(i)) &&
      ORD(nth(inv_l, i)) == NO_ORDER &&
      REF(nth(inv_l, i)) == 0 &&
      pool_const(pool) *
      dlist_head_repr(pool, 0, max_order, inv_hl) *
      free_area_repr(ifilter(inv_l), start, end, inv_l) *
      free_area_head_repr(ifilter(inv_l), start, end, inv_dl) *
      store_pageinfo_array(vmemmap, start, end, inv_l) *
      store_zero_array(i2vi(i), 0, PAGE_SIZE * EXP(2, ord), PAGE_SIZE * EXP(2, ord))
    */
    // proof5
    /*@ Assert
      exists buddy_v bi inv_l inv_dl inv_hl i ord pg_v,
      ord + 1 < max_order &&
      bi != i &&
      buddy_v == vmemmap + bi * 4 &&
      bi < len &&
      REF(nth(inv_l, bi)) == 0 &&
      ORD(nth(inv_l, bi)) == ord &&
      divides(EXP(2, SUC(ord)), i2id(MIN(i, bi))) &&
      abs(i - bi) == EXP(2, ord) &&
      data_at(&max_order_, u8, max_order) *
      data_at(&order, u8, ord) *
      data_at(&buddy, struct hyp_page*, buddy_v) *
      data_at(&pool, struct hyp_pool*, pool) *
      data_at(&pg, struct hyp_page*, pg_v) *
      data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) &&
      pure_const &&
      dlist_node(pool, ifilter(inv_l), inv_l, inv_dl, inv_hl, start, end, inv_dl) &&
      dlist_head(pool, inv_l, inv_dl, 0, max_order, inv_hl) &&
      LENGTH(inv_l) == len &&
      LENGTH(inv_dl) == len &&
      LENGTH(inv_hl) == max_order &&
      pg_v == vmemmap + i * 4 &&
      i < len &&
      ord != NO_ORDER &&
      ord < max_order &&
      divides(EXP(2, ord), i2id(i)) &&
      ORD(nth(inv_l, i)) == NO_ORDER &&
      REF(nth(inv_l, i)) == 0 &&
      pool_const(pool) *
      dlist_head_repr(pool, 0, max_order, inv_hl) *
      free_area_repr(ifilter(inv_l), start, end, inv_l) *
      free_area_head_repr(ifilter(inv_l), start, end, inv_dl) *
      store_pageinfo_array(vmemmap, start, end, inv_l) *
      store_zero_array(i2vi(i), 0, PAGE_SIZE * EXP(2, ord), PAGE_SIZE * EXP(2, ord))
    */
    // FIXME : VST-IDE
#if 0
    page_remove_from_list_pool(pool, buddy) /*@
      where pi = pi, order_v = ord, vmemmap = vmemmap, l = inv_l, dl = inv_dl, hl = inv_hl, start = start, end = end, max_order = max_order, NO_ORDER = NO_ORDER */;
#endif
    /*@ Assert
      exists (new_l : list (Z * Z)) (new_dl : list (Z * Z)) (new_hl : list (Z * Z)) buddy_v bi inv_l (inv_dl : list (Z * Z)) (inv_hl : list (Z * Z)) i ord pg_v,
      new_l == modified(inv_l, bi, 0, NO_ORDER) &&
      LENGTH(new_l) == len &&
      LENGTH(new_dl) == len &&
      LENGTH(new_hl) == max_order &&
      ord + 1 < max_order &&
      bi != i &&
      buddy_v == vmemmap + bi * 4 &&
      bi < len &&
      REF(nth(inv_l, bi)) == 0 &&
      ORD(nth(inv_l, bi)) == ord &&
      divides(EXP(2, SUC(ord)), i2id(MIN(i, bi))) &&
      abs(i - bi) == EXP(2, ord) &&
      data_at(i2vi(bi), void*, 0) *
      data_at(i2vi(bi) + sizeof(void*), void*, 0) *
      data_at(&max_order_, u8, max_order) *
      data_at(&order, u8, ord) *
      data_at(&buddy, struct hyp_page*, buddy_v) *
      data_at(&pool, struct hyp_pool*, pool) *
      data_at(&pg, struct hyp_page*, pg_v) *
      data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) *
      pure_const &&
      dlist_node(pool, ifilter(new_l), new_l, new_dl, new_hl, start, end, new_dl) &&
      dlist_head(pool, new_l, new_dl, 0, max_order, new_hl) &&
      LENGTH(inv_l) == len &&
      LENGTH(inv_dl) == len &&
      LENGTH(inv_hl) == max_order &&
      pg_v == vmemmap + i * 4 &&
      i < len &&
      ord != NO_ORDER &&
      ord < max_order &&
      divides(EXP(2, ord), i2id(i)) &&
      ORD(nth(inv_l, i)) == NO_ORDER &&
      REF(nth(inv_l, i)) == 0 &&
      pool_const(pool) *
      dlist_head_repr(pool, 0, max_order, new_hl) *
      free_area_repr(ifilter(inv_l), start, end, inv_l) *
      free_area_head_repr(ifilter(new_l), start, end, new_dl) *
      store_pageinfo_array(vmemmap, start, end, inv_l) *
      store_zero_array(i2vi(i), 0, PAGE_SIZE * EXP(2, ord), PAGE_SIZE * EXP(2, ord))
    */
    /*@ Assert
      exists (new_l : list (Z * Z)) (new_dl : list (Z * Z)) (new_hl : list (Z * Z)) buddy_v bi inv_l (inv_dl : list (Z * Z)) (inv_hl : list (Z * Z)) i ord pg_v,
      new_l == modified(inv_l, bi, 0, NO_ORDER) &&
      LENGTH(new_l) == len &&
      LENGTH(new_dl) == len &&
      LENGTH(new_hl) == max_order &&
      ord + 1 < max_order &&
      bi != i &&
      buddy_v == vmemmap + bi * 4 &&
      bi < len &&
      REF(nth(inv_l, bi)) == 0 &&
      ORD(nth(inv_l, bi)) == ord &&
      divides(EXP(2, SUC(ord)), i2id(MIN(i, bi))) &&
      abs(i - bi) == EXP(2, ord) &&
      data_at(i2vi(bi), void*, 0) *
      data_at(i2vi(bi) + sizeof(void*), void*, 0) *
      data_at(&max_order_, u8, max_order) *
      data_at(&order, u8, ord) *
      data_at(&buddy, struct hyp_page*, buddy_v) *
      data_at(&pool, struct hyp_pool*, pool) *
      data_at(&pg, struct hyp_page*, pg_v) *
      data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) *
      pure_const &&
      dlist_node(pool, ifilter(new_l), new_l, new_dl, new_hl, start, end, new_dl) &&
      dlist_head(pool, new_l, new_dl, 0, max_order, new_hl) &&
      LENGTH(inv_l) == len &&
      LENGTH(inv_dl) == len &&
      LENGTH(inv_hl) == max_order &&
      pg_v == vmemmap + i * 4 &&
      i < len &&
      ord != NO_ORDER &&
      ord < max_order &&
      divides(EXP(2, ord), i2id(i)) &&
      ORD(nth(inv_l, i)) == NO_ORDER &&
      REF(nth(inv_l, i)) == 0 &&
      pool_const(pool) *
      dlist_head_repr(pool, 0, max_order, new_hl) *
      free_area_repr(ifilter(inv_l), start, end, inv_l) *
      free_area_head_repr(ifilter(new_l), start, end, new_dl) *
      store_pageinfo_array(vmemmap, start, i2id(bi), take(inv_l, bi)) *
      (ord == NO_ORDER ||
       ord != NO_ORDER && ord < max_order && divides(EXP(2, ord), i2id(bi))) &&
      0 < REF_LIM &&
      data_at(vmemmap + bi * 4, u8, 0) *
      undef_data_at(&buddy->order, u8) *
      undef_data_at(vmemmap + bi * 4 + 3, u8) *
      store_pageinfo_array(vmemmap, SUC(i2id(bi)), end, rest(inv_l, SUC(bi))) *
      store_zero_array(i2vi(i), 0, PAGE_SIZE * EXP(2, ord), PAGE_SIZE * EXP(2, ord))
    */
    buddy->order = (u8)HYP_NO_ORDER;
    /*@ Assert
      exists (new_l : list (Z * Z)) (new_dl : list (Z * Z)) (new_hl : list (Z * Z)) buddy_v bi inv_l (inv_dl : list (Z * Z)) (inv_hl : list (Z * Z)) i ord pg_v,
      new_l == modified(inv_l, bi, 0, NO_ORDER) &&
      LENGTH(new_l) == len &&
      LENGTH(new_dl) == len &&
      LENGTH(new_hl) == max_order &&
      ord + 1 < max_order &&
      bi != i &&
      buddy_v == vmemmap + bi * 4 &&
      bi < len &&
      REF(nth(inv_l, bi)) == 0 &&
      ORD(nth(inv_l, bi)) == ord &&
      divides(EXP(2, SUC(ord)), i2id(MIN(i, bi))) &&
      abs(i - bi) == EXP(2, ord) &&
      data_at(i2vi(bi), void*, 0) *
      data_at(i2vi(bi) + sizeof(void*), void*, 0) *
      data_at(&max_order_, u8, max_order) *
      data_at(&order, u8, ord) *
      data_at(&buddy, struct hyp_page*, buddy_v) *
      data_at(&pool, struct hyp_pool*, pool) *
      data_at(&pg, struct hyp_page*, pg_v) *
      data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) *
      pure_const &&
      dlist_node(pool, ifilter(new_l), new_l, new_dl, new_hl, start, end, new_dl) &&
      dlist_head(pool, new_l, new_dl, 0, max_order, new_hl) &&
      LENGTH(inv_l) == len &&
      LENGTH(inv_dl) == len &&
      LENGTH(inv_hl) == max_order &&
      pg_v == vmemmap + i * 4 &&
      i < len &&
      ord != NO_ORDER &&
      ord < max_order &&
      divides(EXP(2, ord), i2id(i)) &&
      ORD(nth(inv_l, i)) == NO_ORDER &&
      REF(nth(inv_l, i)) == 0 &&
      pool_const(pool) *
      dlist_head_repr(pool, 0, max_order, new_hl) *
      free_area_repr(ifilter(inv_l), start, end, inv_l) *
      free_area_head_repr(ifilter(new_l), start, end, new_dl) *
      store_pageinfo_array(vmemmap, start, i2id(bi), take(inv_l, bi)) *
      (ord == NO_ORDER ||
       ord != NO_ORDER && ord < max_order && divides(EXP(2, ord), i2id(bi))) &&
      0 < REF_LIM &&
      data_at(vmemmap + bi * 4, u8, 0) *
      data_at(&buddy->order, u8, HYP_NO_ORDER) *
      undef_data_at(vmemmap + bi * 4 + 3, u8) *
      store_pageinfo_array(vmemmap, SUC(i2id(bi)), end, rest(inv_l, SUC(bi))) *
      store_zero_array(i2vi(i), 0, PAGE_SIZE * EXP(2, ord), PAGE_SIZE * EXP(2, ord))
    */
    pg = min(pg, buddy);
    /*@ Assert
      exists new_pg (new_l : list (Z * Z)) (new_dl : list (Z * Z)) (new_hl : list (Z * Z)) buddy_v bi inv_l (inv_dl : list (Z * Z)) (inv_hl : list (Z * Z)) i ord pg_v,
      new_pg == MIN(pg_v, buddy_v) &&
      new_l == modified(inv_l, bi, 0, NO_ORDER) &&
      LENGTH(new_l) == len &&
      LENGTH(new_dl) == len &&
      LENGTH(new_hl) == max_order &&
      ord + 1 < max_order &&
      bi != i &&
      buddy_v == vmemmap + bi * 4 &&
      bi < len &&
      REF(nth(inv_l, bi)) == 0 &&
      ORD(nth(inv_l, bi)) == ord &&
      divides(EXP(2, SUC(ord)), i2id(MIN(i, bi))) &&
      abs(i - bi) == EXP(2, ord) &&
      data_at(i2vi(bi), void*, 0) *
      data_at(i2vi(bi) + sizeof(void*), void*, 0) *
      data_at(&max_order_, u8, max_order) *
      data_at(&order, u8, ord) *
      data_at(&buddy, struct hyp_page*, buddy_v) *
      data_at(&pool, struct hyp_pool*, pool) *
      data_at(&pg, struct hyp_page*, new_pg) *
      data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) *
      pure_const &&
      dlist_node(pool, ifilter(new_l), new_l, new_dl, new_hl, start, end, new_dl) &&
      dlist_head(pool, new_l, new_dl, 0, max_order, new_hl) &&
      LENGTH(inv_l) == len &&
      LENGTH(inv_dl) == len &&
      LENGTH(inv_hl) == max_order &&
      pg_v == vmemmap + i * 4 &&
      i < len &&
      ord != NO_ORDER &&
      ord < max_order &&
      divides(EXP(2, ord), i2id(i)) &&
      ORD(nth(inv_l, i)) == NO_ORDER &&
      REF(nth(inv_l, i)) == 0 &&
      pool_const(pool) *
      dlist_head_repr(pool, 0, max_order, new_hl) *
      free_area_repr(ifilter(inv_l), start, end, inv_l) *
      free_area_head_repr(ifilter(new_l), start, end, new_dl) *
      store_pageinfo_array(vmemmap, start, i2id(bi), take(inv_l, bi)) *
      (ord == NO_ORDER ||
       ord != NO_ORDER && ord < max_order && divides(EXP(2, ord), i2id(bi))) &&
      0 < REF_LIM &&
      data_at(vmemmap + bi * 4, u8, 0) *
      data_at(&buddy->order, u8, HYP_NO_ORDER) *
      undef_data_at(vmemmap + bi * 4 + 3, u8) *
      store_pageinfo_array(vmemmap, SUC(i2id(bi)), end, rest(inv_l, SUC(bi))) *
      store_zero_array(i2vi(i), 0, PAGE_SIZE * EXP(2, ord), PAGE_SIZE * EXP(2, ord))
    */
    order = order + (u8)1;
    /*@ Assert
      exists new_pg (new_l : list (Z * Z)) (new_dl : list (Z * Z)) (new_hl : list (Z * Z)) buddy_v bi inv_l (inv_dl : list (Z * Z)) (inv_hl : list (Z * Z)) i ord pg_v,
      new_pg == MIN(pg_v, buddy_v) &&
      new_l == modified(inv_l, bi, 0, NO_ORDER) &&
      LENGTH(new_l) == len &&
      LENGTH(new_dl) == len &&
      LENGTH(new_hl) == max_order &&
      ord + 1 < max_order &&
      bi != i &&
      buddy_v == vmemmap + bi * 4 &&
      bi < len &&
      REF(nth(inv_l, bi)) == 0 &&
      ORD(nth(inv_l, bi)) == ord &&
      divides(EXP(2, SUC(ord)), i2id(MIN(i, bi))) &&
      abs(i - bi) == EXP(2, ord) &&
      data_at(i2vi(bi), void*, 0) *
      data_at(i2vi(bi) + sizeof(void*), void*, 0) *
      data_at(&max_order_, u8, max_order) *
      data_at(&order, u8, ord + 1) *
      data_at(&buddy, struct hyp_page*, buddy_v) *
      data_at(&pool, struct hyp_pool*, pool) *
      data_at(&pg, struct hyp_page*, new_pg) *
      data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) *
      pure_const &&
      dlist_node(pool, ifilter(new_l), new_l, new_dl, new_hl, start, end, new_dl) &&
      dlist_head(pool, new_l, new_dl, 0, max_order, new_hl) &&
      LENGTH(inv_l) == len &&
      LENGTH(inv_dl) == len &&
      LENGTH(inv_hl) == max_order &&
      pg_v == vmemmap + i * 4 &&
      i < len &&
      ord != NO_ORDER &&
      ord < max_order &&
      divides(EXP(2, ord), i2id(i)) &&
      ORD(nth(inv_l, i)) == NO_ORDER &&
      REF(nth(inv_l, i)) == 0 &&
      pool_const(pool) *
      dlist_head_repr(pool, 0, max_order, new_hl) *
      free_area_repr(ifilter(inv_l), start, end, inv_l) *
      free_area_head_repr(ifilter(new_l), start, end, new_dl) *
      store_pageinfo_array(vmemmap, start, i2id(bi), take(inv_l, bi)) *
      (ord == NO_ORDER ||
       ord != NO_ORDER && ord < max_order && divides(EXP(2, ord), i2id(bi))) &&
      0 < REF_LIM &&
      data_at(vmemmap + bi * 4, u8, 0) *
      data_at(&buddy->order, u8, HYP_NO_ORDER) *
      undef_data_at(vmemmap + bi * 4 + 3, u8) *
      store_pageinfo_array(vmemmap, SUC(i2id(bi)), end, rest(inv_l, SUC(bi))) *
      store_zero_array(i2vi(i), 0, PAGE_SIZE * EXP(2, ord), PAGE_SIZE * EXP(2, ord))
    */
    // proof6
    /*@ Assert
      exists new_pg (new_l : list (Z * Z)) (new_dl : list (Z * Z)) (new_hl : list (Z * Z)) buddy_v (inv_dl : list (Z * Z)) (inv_hl : list (Z * Z)) new_i new_ord,
      data_at(&max_order_, u8, max_order) *
      data_at(&order, u8, new_ord) *
      data_at(&buddy, struct hyp_page*, buddy_v) *
      data_at(&pool, struct hyp_pool*, pool) *
      data_at(&pg, struct hyp_page*, new_pg) *
      data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) *
      pure_const &&
      dlist_node(pool, ifilter(new_l), new_l, new_dl, new_hl, start, end, new_dl) &&
      dlist_head(pool, new_l, new_dl, 0, max_order, new_hl) &&
      LENGTH(new_l) == len &&
      LENGTH(new_dl) == len &&
      LENGTH(new_hl) == max_order &&
      new_pg == vmemmap + new_i * 4 &&
      new_i < len &&
      new_ord != NO_ORDER &&
      new_ord < max_order &&
      divides(EXP(2, new_ord), i2id(new_i)) &&
      ORD(nth(new_l, new_i)) == NO_ORDER &&
      REF(nth(new_l, new_i)) == 0 &&
      pool_const(pool) *
      dlist_head_repr(pool, 0, max_order, new_hl) *
      free_area_repr(ifilter(new_l), start, end, new_l) *
      free_area_head_repr(ifilter(new_l), start, end, new_dl) *
      store_pageinfo_array(vmemmap, start, end, new_l) *
      store_zero_array(i2vi(new_i), 0, PAGE_SIZE * EXP(2, new_ord), PAGE_SIZE * EXP(2, new_ord))
    */
    // FIXME : VST-IDE
#if 0
    buddy = __find_buddy_avail(pool, pg, order) /*@
      where pi = new_i, order_v = new_ord, vmemmap = vmemmap, l = new_l, start = start, end = end, len = len */;
#endif
    /*@ Assert
      exists new_buddy new_bi new_pg new_l new_dl new_hl new_i new_ord,
      (new_buddy == 0 ||
       new_bi != new_i &&
       new_buddy == vmemmap + new_bi * 4 &&
       new_bi < len &&
       REF(nth(new_l, new_bi)) == 0 &&
       ORD(nth(new_l, new_bi)) == new_ord &&
       divides(EXP(2, SUC(new_ord)), i2id(MIN(new_i, new_bi))) &&
       abs(new_i - new_bi) == EXP(2, new_ord)) &&
      data_at(&max_order_, u8, max_order) *
      data_at(&order, u8, new_ord) *
      data_at(&buddy, struct hyp_page*, new_buddy) *
      data_at(&pool, struct hyp_pool*, pool) *
      data_at(&pg, struct hyp_page*, new_pg) *
      data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) *
      pure_const &&
      dlist_node(pool, ifilter(new_l), new_l, new_dl, new_hl, start, end, new_dl) &&
      dlist_head(pool, new_l, new_dl, 0, max_order, new_hl) &&
      LENGTH(new_l) == len &&
      LENGTH(new_dl) == len &&
      LENGTH(new_hl) == max_order &&
      new_pg == vmemmap + new_i * 4 &&
      new_i < len &&
      new_ord != NO_ORDER &&
      new_ord < max_order &&
      divides(EXP(2, new_ord), i2id(new_i)) &&
      ORD(nth(new_l, new_i)) == NO_ORDER &&
      REF(nth(new_l, new_i)) == 0 &&
      pool_const(pool) *
      dlist_head_repr(pool, 0, max_order, new_hl) *
      free_area_repr(ifilter(new_l), start, end, new_l) *
      free_area_head_repr(ifilter(new_l), start, end, new_dl) *
      store_pageinfo_array(vmemmap, start, end, new_l) *
      store_zero_array(i2vi(new_i), 0, PAGE_SIZE * EXP(2, new_ord), PAGE_SIZE * EXP(2, new_ord))
    */
  }
  /*@ Assert
    exists pg_v ord i inv_l inv_dl inv_hl buddy_v bi,
    (ord + 1 >= max_order || buddy_v == 0) &&
    (buddy_v == 0 ||
     bi != i &&
     buddy_v == vmemmap + bi * 4 &&
     bi < len &&
     REF(nth(inv_l, bi)) == 0 &&
     ORD(nth(inv_l, bi)) == ord &&
     divides(EXP(2, SUC(ord)), i2id(MIN(i, bi))) &&
     abs(i - bi) == EXP(2, ord)) &&
    data_at(&max_order_, u8, max_order) *
    data_at(&order, u8, ord) *
    data_at(&buddy, struct hyp_page*, buddy_v) *
    data_at(&pool, struct hyp_pool*, pool) *
    data_at(&pg, struct hyp_page*, pg_v) *
    data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) &&
    pure_const &&
    dlist_node(pool, ifilter(inv_l), inv_l, inv_dl, inv_hl, start, end, inv_dl) *
    dlist_head(pool, inv_l, inv_dl, 0, max_order, inv_hl) &&
    LENGTH(inv_l) == len &&
    LENGTH(inv_dl) == len &&
    LENGTH(inv_hl) == max_order &&
    pg_v == vmemmap + i * 4 &&
    i < len &&
    ord != NO_ORDER &&
    ord < max_order &&
    divides(EXP(2, ord), i2id(i)) &&
    ORD(nth(inv_l, i)) == NO_ORDER &&
    REF(nth(inv_l, i)) == 0 &&
    pool_const(pool) *
    dlist_head_repr(pool, 0, max_order, inv_hl) *
    free_area_repr(ifilter(inv_l), start, end, inv_l) *
    free_area_head_repr(ifilter(inv_l), start, end, inv_dl) *
    store_pageinfo_array(vmemmap, start, end, inv_l) *
    store_zero_array(i2vi(i), 0, PAGE_SIZE * EXP(2, ord), PAGE_SIZE * EXP(2, ord))
  */
  // proof7
  /*@ Assert
    exists pg_v ord i inv_l inv_dl inv_hl buddy_v bi,
    (ord + 1 >= max_order || buddy_v == 0) &&
    (buddy_v == 0 ||
     bi != i &&
     buddy_v == vmemmap + bi * 4 &&
     bi < len &&
     REF(nth(inv_l, bi)) == 0 &&
     ORD(nth(inv_l, bi)) == ord &&
     divides(EXP(2, SUC(ord)), i2id(MIN(i, bi))) &&
     abs(i - bi) == EXP(2, ord)) &&
    data_at(&max_order_, u8, max_order) *
    data_at(&order, u8, ord) *
    data_at(&buddy, struct hyp_page*, buddy_v) *
    data_at(&pool, struct hyp_pool*, pool) *
    data_at(&pg, struct hyp_page*, pg_v) *
    data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) *
    pure_const &&
    dlist_node(pool, ifilter(inv_l), inv_l, inv_dl, inv_hl, start, end, inv_dl) &&
    dlist_head(pool, inv_l, inv_dl, 0, max_order, inv_hl) &&
    LENGTH(inv_l) == len &&
    LENGTH(inv_dl) == len &&
    LENGTH(inv_hl) == max_order &&
    pg_v == vmemmap + i * 4 &&
    i < len &&
    ord != NO_ORDER &&
    ord < max_order &&
    divides(EXP(2, ord), i2id(i)) &&
    ORD(nth(inv_l, i)) == NO_ORDER &&
    REF(nth(inv_l, i)) == 0 &&
    pool_const(pool) *
    dlist_head_repr(pool, 0, max_order, inv_hl) *
    free_area_repr(ifilter(inv_l), start, end, inv_l) *
    free_area_head_repr(ifilter(inv_l), start, end, inv_dl) *
    store_pageinfo_array(vmemmap, start, i2id(i), take(inv_l, i)) *
    data_at(vmemmap + i * 4, u8, 0) *
    data_at(&pg->order, u8, NO_ORDER) *
    undef_data_at(vmemmap + i * 4 + 3, u8) *
    store_pageinfo_array(vmemmap, SUC(i2id(i)), end, rest(inv_l, SUC(i))) *
    store_zero_array(i2vi(i), 0, PAGE_SIZE * EXP(2, ord), PAGE_SIZE * EXP(2, ord))
  */
  pg->order = order;
  /*@ Assert
    exists pg_v ord i inv_l inv_dl inv_hl buddy_v bi,
    (ord + 1 >= max_order || buddy_v == 0) &&
    (buddy_v == 0 ||
     bi != i &&
     buddy_v == vmemmap + bi * 4 &&
     bi < len &&
     REF(nth(inv_l, bi)) == 0 &&
     ORD(nth(inv_l, bi)) == ord &&
     divides(EXP(2, SUC(ord)), i2id(MIN(i, bi))) &&
     abs(i - bi) == EXP(2, ord)) &&
    data_at(&max_order_, u8, max_order) *
    data_at(&order, u8, ord) *
    data_at(&buddy, struct hyp_page*, buddy_v) *
    data_at(&pool, struct hyp_pool*, pool) *
    data_at(&pg, struct hyp_page*, pg_v) *
    data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) *
    pure_const &&
    dlist_node(pool, ifilter(inv_l), inv_l, inv_dl, inv_hl, start, end, inv_dl) &&
    dlist_head(pool, inv_l, inv_dl, 0, max_order, inv_hl) &&
    LENGTH(inv_l) == len &&
    LENGTH(inv_dl) == len &&
    LENGTH(inv_hl) == max_order &&
    pg_v == vmemmap + i * 4 &&
    i < len &&
    ord != NO_ORDER &&
    ord < max_order &&
    divides(EXP(2, ord), i2id(i)) &&
    ORD(nth(inv_l, i)) == NO_ORDER &&
    REF(nth(inv_l, i)) == 0 &&
    pool_const(pool) *
    dlist_head_repr(pool, 0, max_order, inv_hl) *
    free_area_repr(ifilter(inv_l), start, end, inv_l) *
    free_area_head_repr(ifilter(inv_l), start, end, inv_dl) *
    store_pageinfo_array(vmemmap, start, i2id(i), take(inv_l, i)) *
    data_at(vmemmap + i * 4, u8, 0) *
    data_at(&pg->order, u8, ord) *
    undef_data_at(vmemmap + i * 4 + 3, u8) *
    store_pageinfo_array(vmemmap, SUC(i2id(i)), end, rest(inv_l, SUC(i))) *
    store_zero_array(i2vi(i), 0, PAGE_SIZE * EXP(2, ord), PAGE_SIZE * EXP(2, ord))
  */
  // proof8
  /*@ Assert
    exists pg_v ord i inv_l inv_dl inv_hl buddy_v bi,
    (ord + 1 >= max_order || buddy_v == 0) &&
    (buddy_v == 0 ||
     bi != i &&
     buddy_v == vmemmap + bi * 4 &&
     bi < len &&
     REF(nth(inv_l, bi)) == 0 &&
     ORD(nth(inv_l, bi)) == ord &&
     divides(EXP(2, SUC(ord)), i2id(MIN(i, bi))) &&
     abs(i - bi) == EXP(2, ord)) &&
    data_at(&max_order_, u8, max_order) *
    data_at(&order, u8, ord) *
    data_at(&buddy, struct hyp_page*, buddy_v) *
    data_at(&pool, struct hyp_pool*, pool) *
    data_at(&pg, struct hyp_page*, pg_v) *
    data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) *
    pure_const &&
    dlist_node(pool, ifilter(inv_l), inv_l, inv_dl, inv_hl, start, end, inv_dl) &&
    dlist_head(pool, inv_l, inv_dl, 0, max_order, inv_hl) &&
    LENGTH(inv_l) == len &&
    LENGTH(inv_dl) == len &&
    LENGTH(inv_hl) == max_order &&
    pg_v == vmemmap + i * 4 &&
    i < len &&
    ord != NO_ORDER &&
    ord < max_order &&
    divides(EXP(2, ord), i2id(i)) &&
    ORD(nth(inv_l, i)) == NO_ORDER &&
    REF(nth(inv_l, i)) == 0 &&
    pool_const(pool) *
    dlist_head_repr(pool, 0, max_order, inv_hl) *
    free_area_repr(ifilter(modified(inv_l, i, 0, ord)), start, end, modified(inv_l, i, 0, ord)) *
    free_area_head_repr(ifilter(inv_l), start, end, inv_dl) *
    store_pageinfo_array(vmemmap, start, end, modified(inv_l, i, 0, ord)) *
    data_at(i2vi(i), void*, 0) *
    data_at(i2vi(i) + sizeof(void*), void*, 0)
  */
  // FIXME : VST-IDE
#if 0
  page_add_to_list_pool(pool, pg, order) /*@
    where pi = pi, order_v = ord, vmemmap = vmemmap, l = inv_l, dl = inv_dl, hl = inv_hl, start = start, end = end, len = len, max_order = max_order, NO_ORDER = NO_ORDER */;
#endif
  /*@ Assert
    exists new_l new_dl new_hl pg_v ord i inv_l (inv_dl : list (Z * Z)) (inv_hl : list (Z * Z)) buddy_v bi,
    new_l == modified(inv_l, i, 0, ord) &&
    LENGTH(new_l) == len &&
    LENGTH(new_dl) == len &&
    LENGTH(new_hl) == max_order &&
    (ord + 1 >= max_order || buddy_v == 0) &&
    (buddy_v == 0 ||
     bi != i &&
     buddy_v == vmemmap + bi * 4 &&
     bi < len &&
     REF(nth(inv_l, bi)) == 0 &&
     ORD(nth(inv_l, bi)) == ord &&
     divides(EXP(2, SUC(ord)), i2id(MIN(i, bi))) &&
     abs(i - bi) == EXP(2, ord)) &&
    data_at(&max_order_, u8, max_order) *
    data_at(&order, u8, ord) *
    data_at(&buddy, struct hyp_page*, buddy_v) *
    data_at(&pool, struct hyp_pool*, pool) *
    data_at(&pg, struct hyp_page*, pg_v) *
    data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) *
    pure_const &&
    dlist_node(pool, ifilter(new_l), new_l, new_dl, new_hl, start, end, new_dl) &&
    dlist_head(pool, new_l, new_dl, 0, max_order, new_hl) &&
    LENGTH(inv_l) == len &&
    LENGTH(inv_dl) == len &&
    LENGTH(inv_hl) == max_order &&
    pg_v == vmemmap + i * 4 &&
    i < len &&
    ord != NO_ORDER &&
    ord < max_order &&
    divides(EXP(2, ord), i2id(i)) &&
    ORD(nth(inv_l, i)) == NO_ORDER &&
    REF(nth(inv_l, i)) == 0 &&
    pool_const(pool) *
    dlist_head_repr(pool, 0, max_order, new_hl) *
    free_area_repr(ifilter(modified(inv_l, i, 0, ord)), start, end, modified(inv_l, i, 0, ord)) *
    free_area_head_repr(ifilter(new_l), start, end, new_dl) *
    store_pageinfo_array(vmemmap, start, end, modified(inv_l, i, 0, ord))
  */
  // proof9
  /*@ Assert
    exists new_l new_dl new_hl pg_v ord i inv_l (inv_dl : list (Z * Z)) (inv_hl : list (Z * Z)) buddy_v bi,
    new_l == modified(inv_l, i, 0, ord) &&
    LENGTH(new_l) == len &&
    LENGTH(new_dl) == len &&
    LENGTH(new_hl) == max_order &&
    (ord + 1 >= max_order || buddy_v == 0) &&
    (buddy_v == 0 ||
     bi != i &&
     buddy_v == vmemmap + bi * 4 &&
     bi < len &&
     REF(nth(inv_l, bi)) == 0 &&
     ORD(nth(inv_l, bi)) == ord &&
     divides(EXP(2, SUC(ord)), i2id(MIN(i, bi))) &&
     abs(i - bi) == EXP(2, ord)) &&
    data_at(&max_order_, u8, max_order) *
    data_at(&order, u8, ord) *
    data_at(&buddy, struct hyp_page*, buddy_v) *
    data_at(&pool, struct hyp_pool*, pool) *
    data_at(&pg, struct hyp_page*, pg_v) *
    data_at(&__hyp_vmemmap, struct hyp_page*, vmemmap) &&
    pure_const &&
    dlist_node(pool, ifilter(new_l), new_l, new_dl, new_hl, start, end, new_dl) &&
    dlist_head(pool, new_l, new_dl, 0, max_order, new_hl) &&
    LENGTH(inv_l) == len &&
    LENGTH(inv_dl) == len &&
    LENGTH(inv_hl) == max_order &&
    pg_v == vmemmap + i * 4 &&
    i < len &&
    ord != NO_ORDER &&
    ord < max_order &&
    divides(EXP(2, ord), i2id(i)) &&
    ORD(nth(inv_l, i)) == NO_ORDER &&
    REF(nth(inv_l, i)) == 0 &&
    pool_const(pool) *
    dlist_head_repr(pool, 0, max_order, new_hl) *
    free_area_repr(ifilter(new_l), start, end, new_l) *
    free_area_head_repr(ifilter(new_l), start, end, new_dl) *
    store_pageinfo_array(vmemmap, start, end, new_l)
  */
}
