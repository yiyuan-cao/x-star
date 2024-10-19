static void __hyp_attach_page(struct hyp_pool *pool, struct hyp_page *p)
/*
PARAMETERS:
	l : ((num#num)#(PTR#PTR))list
	dl : ((PTR#PTR)list)list
	hl : ((PTR#PTR)list)list
	pid : num
	pi : num

	[hided] start : num
	[hided] end : num
	[hided] max_order : num
	[hided] offset : num
	[hided] len : num

	[hided] 
		(start < end) && (end * PAGE_SIZE < PAGE_LIM) /\
		(max_order <= MAX_ORDER) /\
		(offset <= start * PAGE_SIZE) /\
		(PAGESIZE divides offset) /\
		(len = end - start)

REQUIRE:
	pool_const pool **
	dlist_head_repr pool 0 max_order hl **
	free_area_repr (ifilter l) start end l **
    free_area_head_repr (ifilter l) start end dl **
	store_pageinfo_array __hyp_vmemmap start pid (take l pi) **
	(
		DATA_AT... p (0, ORD (nth l pi))
		&& PURE (
			(~((ORD (nth l pi)) = NO_ORDER) ==> 
				(ORD (nth l pi) < max_order) /\ 
				((2 EXP (ORD (nth l pi))) divides pid)) /\ 
			(REF (nth l pi) < REF_LIM)
	)) **
	store_pageinfo_array __hyp_vmemmap (SUC pid) end (rest l (SUC pi)) **
	store_undef_array (id2vi (&pid)) 0 (PAGE_SIZE * (2 EXP (ORD (nth l pi)))) (PAGE_SIZE * (2 EXP (ORD (nth l pi))))
	&& PURE (
		dlist_node pool_ptr (ifilter l) l dl hl start end dl /\
		dlist_head pool_ptr l dl 0 max_order hl /\
		(LENGTH l = len) /\
		(LENGTH dl = len) /\
		(LENGTH hl = max_order) /\
		(p = __hyp_vmemmap + pi * HYP_PAGE_SIZE) /\
		(pi < len) /\
		(pid = start + pi) /\
		~((ORD (nth l pi)) = NO_ORDER) /\
		(REF (nth l pi) > 0)
	)

ENSURE: (i.e. total_repr pool __hyp_vmemmap l' dl' hl')
	pool_const pool **
	dlist_head_repr pool 0 max_order hl **
	free_area_repr (ifilter l') start end l' **
    free_area_head_repr (ifilter l') start end dl' **
	store_pageinfo_array __hyp_vmemmap start end l' **
	&& PURE (
		dlist_node pool_ptr (ifilter l') l' dl' hl' start end dl' /\
		dlist_head pool_ptr l' dl' 0 max_order hl' /\
		(LENGTH l' = len)
		(LENGTH dl' = len) /\
		(LENGTH hl' = max_order)
	)
*/
{
// put PURE () together

	struct hyp_page *buddy = NULL;
// get: buddy = NULL

// from: DATA_AT... p (0, ORD (nth l pi))
	u8 order = p->order;
// get: order = ORD (nth l pi)
// rewrite ORD (nth l pi) to order

// from: store_undef_array (id2vi (&pid)) 0 (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order))
	memset(__cerbvar_copy_alloc_id(hyp_page_to_virt(p), cn_virt_base), 0, PAGE_SIZE << order);
// to: store_zero_array (id2vi (&pid)) 0 (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order))

// from: DATA_AT... p (0, order)
	p->order = HYP_NO_ORDER;
// to: DATA_AT... p (0, NO_ORDER)

/*
NOW:
	pool_const pool **
	dlist_head_repr pool 0 max_order hl **
	free_area_repr (ifilter l) start end l **
    free_area_head_repr (ifilter l) start end dl **
	store_pageinfo_array __hyp_vmemmap start pid (take l pi) **
	DATA_AT... p (0, NO_ORDER) **
	store_pageinfo_array __hyp_vmemmap (SUC pid) end (rest l (SUC pi)) **
	store_zero_array (id2vi (&pid)) 0 (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order))
	&& PURE (
		dlist_node pool_ptr (ifilter l) l dl hl start end dl /\
		dlist_head pool_ptr l dl 0 max_order hl /\
		(LENGTH l = len) /\
		(LENGTH dl = len) /\
		(LENGTH hl = max_order) /\
		(p = __hyp_vmemmap + pi * HYP_PAGE_SIZE) /\
		(pi < len) /\
		(pid = start + pi) /\
		~(order = NO_ORDER) /\
		(REF (nth l pi) > 0) /\
		(~(order = NO_ORDER) ==> 
			(order < max_order) /\ 
			((2 EXP order) divides pid)) /\ 
		(REF (nth l pi) < REF_LIM) /\
		(buddy = NULL) /\
		(order = ORD (nth l pi))
	)
*/

/*
ENTAILMENTS:
1.filter_inv:
	i < LENGTH l ==>
	((REF v = 0 /\ ~(ORD v = NO_ORDER)) <=>
		(REF (nth l i) = 0 /\ ~(ORD (nth l i) = NO_ORDER))) ==>
	ifilter l = ifilter (modified l i v)

-	REF (nth l pi) > 0 ==>
-	ifilter l = ifilter (modified l pi (0, NO_ORDER))

2.far_inv:
	i < len ==>
	len = LENGTH l ==>
	filter (start + i) = F ==>
	free_area_repr filter start end l = 
	free_area_repr filter start end (modified l i v)

-	filter pid = F ==>
-	free_area_repr filter start end l = 
-	free_area_repr filter start end (modified l pi v)

3.	apply merge_modified_list_lemma on store_pageinfo_array

4.dn_inv:
	i < LENGTH l ==>
	~(REF (nth l i) = 0 /\ ~(ORD (nth l i) = NO_ORDER)) ==>
	dlist_node pool_ptr (ifilter l) l dl hl start end dl =
	dlist_node pool_ptr (ifilter l) (modified l i v) dl hl start end dl

-	REF (nth l pi) > 0 ==>
-	dlist_node pool_ptr (ifilter l) l dl hl start end dl =
-	dlist_node pool_ptr (ifilter l) (modified l pi v) dl hl start end dl

5.dh_inv:
	i < LENGTH l ==>
	~(REF (nth l i) = 0 /\ ~(ORD (nth l i) = NO_ORDER)) ==>
	dlist_head pool_ptr l 0 max_order hl ==>
	dlist_head pool_ptr (modified l i v) 0 max_order hl

-	REF (nth l pi) > 0 ==>
-	dlist_head pool_ptr l 0 max_order hl =
-	dlist_head pool_ptr (modified l pi v) 0 max_order hl

6.modified_len:
	LENGTH l = LENGTH (modified l pi v)

inv_l := modified l pi (0, NO_ORDER)
inv_dl := dl
inv_hl := hl
*/

/*
INVARIANT: 
	pool_const pool **
	dlist_head_repr pool 0 max_order inv_hl **
	free_area_repr (ifilter inv_l) start end inv_l **
    free_area_head_repr (ifilter inv_l) start end inv_dl **
	store_pageinfo_array __hyp_vmemmap start end inv_l **
	store_zero_array (id2vi (&pid)) 0 (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order)) **
	&& PURE (
		dlist_node pool_ptr (ifilter inv_l) inv_l inv_dl inv_hl start end inv_dl /\
		dlist_head pool_ptr inv_l inv_dl 0 max_order inv_hl /\
		(LENGTH inv_l = len) /\
		(LENGTH inv_dl = len) /\
		(LENGTH inv_hl = max_order) /\
		(p = __hyp_vmemmap + pi * HYP_PAGE_SIZE) /\
		(pi < len) /\
		(pid = start + pi) /\
		(order + 1 < max_order) /\
		((2 EXP order) divides pid) /\
		(REF (nth inv_l pi) = 0) /\
		(ORD (nth inv_l pi) = NO_ORDER)
	)
*/
	for (; (order + 1) < pool->max_order; order++)
	{
// from: p = __hyp_vmemmap + pi * HYP_PAGE_SIZE
//		 pid = start + pi
//		 (2 EXP order) divides pid
		buddy = __find_buddy_avail(pool, p, order);
		if (!buddy)
			break;
// get: buddy = __hyp_vmemmap + bi * HYP_PAGE_SIZE
//		bi < len
//		bid = start + bi
//		REF (nth inv_l bi) = 0
//		ORD (nth inv_l bi) = order
//		(2 EXP (SUC order)) divides (min pid bid)

// from: dlist_head_repr pool 0 max_order inv_hl
//		dlist_node pool_ptr (ifilter inv_l) inv_l inv_dl inv_hl start end inv_dl
//		dlist_head pool_ptr inv_l inv_dl 0 max_order inv_hl
//		free_area_head_repr (ifilter inv_l) start end inv_dl
// 		buddy = __hyp_vmemmap + bi * HYP_PAGE_SIZE
//		bi < len
//		bid = start + bi
//		REF (nth inv_l bi) = 0
//		ORD (nth inv_l bi) = order
//		order + 1 < max_order
		page_remove_from_list_pool(pool, buddy);
// to: dlist_head_repr pool 0 max_order new_hl
//		dlist_node pool_ptr (ifilter new_l) inv_l new_dl new_hl start end new_dl
//		dlist_head pool_ptr inv_l new_dl 0 max_order new_hl
//		free_area_head_repr (ifilter new_l) start end new_dl **
//		DATA_AT_PTR (id2vi (&bid), &0) **
//		DATA_AT_PTR (id2vi (&bid) + &PTR_SIZE, &0)
// new_l := modified inv_l bi (0, NO_ORDER)

// apply lemma4 lemma5
// get: dlist_node pool_ptr (ifilter new_l) new_l new_dl new_hl start end new_dl
//		dlist_head pool_ptr new_l new_dl 0 max_order new_hl

// apply merge_modified_list_lemma on store_pageinfo_array
// from: store_pageinfo_array __hyp_vmemmap start end inv_l
// to: store_pageinfo_array __hyp_vmemmap start bid (take l bi) **
// 		(
// 			DATA_AT... buddy (0, order)
// 			&& PURE (
// 				(~(order = NO_ORDER) ==> 
// 					(order < max_order) /\ 
// 					((2 EXP order) divides bid)) /\ 
// 				(0 < REF_LIM)
// 		)) **
// 		store_pageinfo_array __hyp_vmemmap (SUC bid) end (rest l (SUC bi))

// from: DATA_AT... buddy (0, order)
		buddy->order = HYP_NO_ORDER;
// to: DATA_AT... buddy (0, NO_ORDER)

// from: (2 EXP (SUC order)) divides (min pid bid)
		p = min(p, buddy);
// get: (2 EXP (SUC order)) divides new_pid

/*
NOW:
	pool_const pool **
	dlist_head_repr pool 0 max_order new_hl **
	free_area_repr (ifilter inv_l) start end inv_l **
    free_area_head_repr (ifilter new_l) start end new_dl **
	DATA_AT_PTR (id2vi (&bid), &0) **
	DATA_AT_PTR (id2vi (&bid) + &PTR_SIZE, &0) **
	store_pageinfo_array __hyp_vmemmap start bid (take l bi) **
	(
		DATA_AT... buddy (0, NO_ORDER)
		&& PURE (
			(~(order = NO_ORDER) ==> 
				(order < max_order) /\ 
				((2 EXP order) divides bid)) /\ 
			(0 < REF_LIM)
 	)) **
 	store_pageinfo_array __hyp_vmemmap (SUC bid) end (rest l (SUC bi)) **
	store_zero_array (id2vi (&pid)) 0 (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order)) **
	&& PURE (
		dlist_node pool_ptr (ifilter new_l) new_l new_dl new_hl start end new_dl /\
		dlist_head pool_ptr new_l new_dl 0 max_order new_hl /\
		(LENGTH inv_l = len) /\
		(LENGTH inv_dl = len) /\
		(LENGTH inv_hl = max_order) /\
		(p = __hyp_vmemmap + new_pi * HYP_PAGE_SIZE) /\
		(new_pi < len) /\
		(new_pid = start + new_pi) /\
		(order + 1 < max_order) /\
		((2 EXP (SUC order)) divides new_pid) /\
		(buddy = __hyp_vmemmap + bi * HYP_PAGE_SIZE) /\
		(bi < len) /\
		(bid = start + bi) /\
		(REF (nth inv_l bi) = 0) /\
		(ORD (nth inv_l bi) = order) /\
		(REF (nth new_l bi) = 0) /\
		(ORD (nth new_l bi) = NO_ORDER) /\
		(REF (nth inv_l pi) = 0) /\
		(ORD (nth inv_l pi) = NO_ORDER)
	)

new_l := modified inv_l bi (0, NO_ORDER)	
*/

/*
ENTAILMENTS:
1.far_split:
	start <= lo ==> lo <= start + i ==> start + i < hi ==> i < LENGTH l ==>
	ifilter l (start + i) = T ==> 
	free_area_repr (ifilter l) start end l =
	free_area_repr (ifilter (modified inv_l i (0, NO_ORDER))) start end l **
	store_zero_array (id2vi (start + i)) (PTR_SIZE * 2) (PAGE_SIZE * (2 EXP (ORD (nth l i)))) (PAGE_SIZE * (2 EXP (ORD (nth l i))) - PAGE_SIZE * 2)

-	ifilter l bid = T ==>
-	free_area_repr (ifilter l) start end l =
-	free_area_repr (ifilter (modified inv_l bi (0, NO_ORDER))) start end l **
-	store_zero_array (id2vi (&bid)) (PTR_SIZE * 2) (PAGE_SIZE * (2 EXP (ORD (nth l bi)))) (PAGE_SIZE * (2 EXP (ORD (nth l bi))) - PAGE_SIZE * 2)

2.far_inv
-	filter bid = F ==>
-	free_area_repr filter start end l =
-	free_area_repr filter start end l (modified inv_l bi v)

3.	apply merge_modified_list_lemma on store_pageinfo_array

4.?
	DATA_AT_PTR (id2vi (&bid), &0) **
	DATA_AT_PTR (id2vi (&bid) + &PTR_SIZE, &0) **
	store_zero_array (id2vi (&bid)) (PTR_SIZE * 2) (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order) - PAGE_SIZE * 2) =
	store_zero_array (id2vi (&bid)) 0 (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order))
5.?
	new_pid = min pid bid /\ ... ==>
	store_zero_array (id2vi (&pid)) 0 (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order)) **
	store_zero_array (id2vi (&bid)) 0 (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order)) =
	store_zero_array (id2vi (&new_pid)) 0 (PAGE_SIZE * (2 EXP (SUC order))) (PAGE_SIZE * (2 EXP (SUC order)))
*/
	}
/*
NOW:
	pool_const pool **
	dlist_head_repr pool 0 max_order hl **
	free_area_repr (ifilter l) start end l **
    free_area_head_repr (ifilter l) start end dl **
	store_pageinfo_array __hyp_vmemmap start end l **
	store_zero_array (id2vi (&pid)) 0 (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order)) **
	&& PURE (
		dlist_node pool_ptr (ifilter l) l dl hl start end dl /\
		dlist_head pool_ptr l dl 0 max_order hl /\
		(LENGTH l = len) /\
		(LENGTH dl = len) /\
		(LENGTH hl = max_order) /\
		(p = __hyp_vmemmap + pi * HYP_PAGE_SIZE) /\
		(pi < len) /\
		(pid = start + pi) /\
		(order + 1 < max_order) /\
		((2 EXP order) divides pid) /\
		(REF (nth l pi) = 0) /\
		(ORD (nth l pi) = NO_ORDER)
	)
*/
	p->order = order;
/*
NOW:
	pool_const pool **
	dlist_head_repr pool 0 max_order hl **
	free_area_repr (ifilter l) start end l **
    free_area_head_repr (ifilter l) start end dl **
	store_pageinfo_array __hyp_vmemmap start end (modified l pi (0, order)) **
	store_zero_array (id2vi (&pid)) 0 (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order)) **
	&& PURE (
		dlist_node pool_ptr (ifilter l) l dl hl start end dl /\
		dlist_head pool_ptr l dl 0 max_order hl /\
		(LENGTH l = len) /\
		(LENGTH dl = len) /\
		(LENGTH hl = max_order) /\
		(p = __hyp_vmemmap + pi * HYP_PAGE_SIZE) /\
		(pi < len) /\
		(pid = start + pi) /\
		(order + 1 < max_order) /\
		((2 EXP order) divides pid) /\
		(REF (nth l pi) = 0) /\
		(ORD (nth l pi) = NO_ORDER)
	)
*/

// from: dlist_head_repr pool 0 max_order hl
//		dlist_node pool_ptr (ifilter l) l dl hl start end dl
//		dlist_head pool_ptr l dl 0 max_order hl
//		free_area_head_repr (ifilter l) start end dl **
//		DATA_AT_PTR (id2vi (&pid), &0) **
//		DATA_AT_PTR (id2vi (&pid) + &PTR_SIZE, &0)
// 		p = __hyp_vmemmap + pi * HYP_PAGE_SIZE
//		pi < len
//		pid = start + pi
//		REF (nth l pi) = 0
//		ORD (nth l pi) = NO_ORDER
	page_add_to_list_pool(pool, p, &pool->free_area[order]);
// to: dlist_head_repr pool 0 max_order new_hl
//		dlist_node pool_ptr (ifilter new_l) new_l new_dl new_hl start end new_dl
//		dlist_head pool_ptr new_l new_dl 0 max_order new_hl
//		free_area_head_repr (ifilter new_l) start end new_dl
// new_l := modified l pi (0, order)

/*
NOW:
	pool_const pool **
	dlist_head_repr pool 0 max_order new_hl **
	free_area_repr (ifilter l) start end l **
    free_area_head_repr (ifilter new_l) start end new_dl **
	store_pageinfo_array __hyp_vmemmap start end new_l **
	store_zero_array (id2vi (&pid)) (PAGE_SIZE * 2) (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order) - PAGE_SIZE * 2) **
	&& PURE (
		dlist_node pool_ptr (ifilter new_l) new_l new_dl new_hl start end new_dl /\
		dlist_head pool_ptr new_l new_dl 0 max_order new_hl /\
		(LENGTH l = len) /\
		(LENGTH dl = len) /\
		(LENGTH hl = max_order) /\
		(p = __hyp_vmemmap + pi * HYP_PAGE_SIZE) /\
		(pi < len) /\
		(pid = start + pi) /\
		(order + 1 < max_order) /\
		((2 EXP order) divides pid) /\
		(REF (nth l pi) = 0) /\
		(ORD (nth l pi) = NO_ORDER)
	)
*/

/*
ENTAILMENT:
1.far_merge
-	(REF (nth l pi) = 0) /\ (ORD (nth l pi) = NO_ORDER) ==>
-	free_area_repr (ifilter l) start end l **
-	store_zero_array (id2vi (&pid)) (PAGE_SIZE * 2) (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order) - PAGE_SIZE * 2) =
-	free_area_repr (ifilter (modified l pi (0, order))) start end (modified l pi (0, order))
*/
}