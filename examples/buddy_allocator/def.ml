let PTR_SIZE_DEF = define `PTR_SIZE : num = 8`;;
let LIST_HEAD_SIZE_DEF = define `LIST_HEAD_SIZE : num = PTR_SIZE * 2`;;

let PAGE_SIZE_DEF = define `PAGE_SIZE : num = 4096`;;
let MAX_ORDER_DEF = define `MAX_ORDER : num = 11`;;
let NO_ORDER_DEF = define `NO_ORDER : num = 255`;;
let RANGE_LIM_DEF = define `RANGE_LIM : num = 4503599627370496`;;
let REF_LIM_DEF = define `REF_LIM : num = 65536`;;
let PTR_LIM_DEF = define `PTR_LIM : num = 18446744073709551616`;;

let START_DEF = define `start = @x : num. T`;;
let END_DEF = define `end = @x : num. x > start /\ x * PAGE_SIZE < RANGE_LIM`;;
let LEN_DEF = define `len : num = end - start`;;
let MAX_ORDER__DEF = define `max_order = @x : num. x <= MAX_ORDER`;;
let OFF_SET_DEF = define `offset = @x : num. x <= start * PAGE_SIZE /\ PAGE_SIZE divides x`;;

let PH2VI_DEF = define `ph2vi (ph : PTR) = ph - &offset`;;
let VI2PH_DEF = define `vi2ph (vi : PTR) = vi + &offset`;;
let PH2ID_DEF = define `ph2id (ph : PTR) = num_of_int (ph div &PAGE_SIZE)`;;
let VI2ID_DEF = define `vi2id (vi : PTR) = ph2id (vi2ph vi)`;;
let ID2PH_DEF = define `id2ph (id : int) = id * &PAGE_SIZE`;;
let ID2VI_DEF = define `id2vi (id : int) = ph2vi (id2ph id)`;;

(* let TUPLE_DEF = define_type "info = INFO (num#num)#(PTR#PTR)";; *)

let REF_DEF = define `REF (i : (num#num)#(PTR#PTR)) = FST (FST i)`;;
let ORD_DEF = define `ORD (i : (num#num)#(PTR#PTR)) = SND (FST i)`;;
let NXT_DEF = define `NXT (i : (num#num)#(PTR#PTR)) = FST (SND i)`;;
let PRV_DEF = define `PRV (i : (num#num)#(PTR#PTR)) = SND (SND i)`;;

let STORE_UNDEF_ARRAY_DEF = define `
    (! (addr : PTR) (lo : num) (hi : num). 
    store_undef_array addr lo hi (0 : num) = (PURE (lo = hi) SEPAND EMP)) /\
    (! (addr : PTR) (lo : num) (hi : num) (n : num).
    store_undef_array addr lo hi (SUC n) = (
        DATA_AT_CHAR_ANY (addr + &lo) SEPCONJ 
        store_undef_array addr (SUC lo) hi n))`;;

let STORE_ZERO_ARRAY_DEF = define `
    (! (addr : PTR) (lo : num) (hi : num). 
    store_zero_array addr lo hi (0 : num) = (PURE (lo = hi) SEPAND EMP)) /\
    (! (addr : PTR) (lo : num) (hi : num) (n : num).
    store_zero_array addr lo hi (SUC n) = (
        DATA_AT_CHAR (addr + &lo, &0) SEPCONJ 
        store_zero_array addr (SUC lo) hi n))`;;

let STORE_PAGEINFO_ARRAY_DEF = define `
    (! (addr : PTR) (lo : num) (hi : num).
    store_pageinfo_array addr lo hi (NIL : ((num#num)#(PTR#PTR))list) = (PURE (lo = hi) SEPAND EMP)) /\
    (! (addr : PTR) (lo : num) (hi : num) (h : (num#num)#(PTR#PTR)) (t : ((num#num)#(PTR#PTR))list).
    store_pageinfo_array addr lo hi (CONS h t) = ((
            PURE (((~((ORD h) = NO_ORDER) ==> (ORD h <= max_order) /\ ((2 EXP (ORD h)) divides lo))) /\ (REF h < REF_LIM)) SEPAND
            DATA_AT_SHORT (addr + &((lo - start) * 4), &(REF h)) SEPCONJ
            DATA_AT_CHAR (addr + &((lo - start) * 4 + 2), &(ORD h)) SEPCONJ
            DATA_AT_CHAR_ANY (addr + &((lo - start) * 4 + 3))
        ) SEPCONJ store_pageinfo_array addr (SUC lo) hi t))`;;

let POOL_CONST_DEF = define `
    pool_const (pool_ptr : PTR) = (
        DATA_AT_INT (pool_ptr + &(LIST_HEAD_SIZE * MAX_ORDER), id2ph (&start)) SEPCONJ
        DATA_AT_INT (pool_ptr + &(LIST_HEAD_SIZE * MAX_ORDER + 8), id2ph (&end)) SEPCONJ
        DATA_AT_CHAR (pool_ptr + &(LIST_HEAD_SIZE * MAX_ORDER + 16), &max_order))`;;

let DLIST_HEAD_REPR_DEF = define `
    (! (addr : PTR) (order : num) (maxorder : num).
    dlist_head_repr addr order maxorder (NIL : (PTR#PTR)list) = (PURE (order = maxorder) SEPAND EMP)) /\
    (! (addr : PTR) (order : num) (maxorder : num) (h : PTR#PTR) (t : (PTR#PTR)list).
    dlist_head_repr addr order maxorder (CONS h t) = ((
        DATA_AT_PTR (addr + &(LIST_HEAD_SIZE * order), FST h) SEPCONJ
        DATA_AT_PTR (addr + &(LIST_HEAD_SIZE * order + PTR_SIZE), SND h)
    ) SEPCONJ dlist_head_repr addr (SUC order) maxorder t))`;;

let NTH_DEF = define `
    (! (h : A) (t : (A)list). nth (CONS h t) (0 : num) = h) /\
    (! (h : A) (t : (A)list) (n : num). nth (CONS h t) (SUC n) = nth t n)`;;

let MODIFIED_DEF = define `
    (! (n : num) (v : A). modified (NIL : (A)list) n v = NIL) /\
    (! (h : A) (t : (A)list) (v : A). modified (CONS h t) (0 : num) v = CONS v t) /\
    (! (h : A) (t : (A)list) (n : num) (v : A). modified (CONS h t) (SUC n) v = 
        CONS h (modified t n v))`;;

let TAKE_DEF = define `
    (! (l : (A)list). take l (0 : num) = NIL) /\
    (! (h : A) (t : (A)list) (n : num). take (CONS h t) (SUC n) = CONS h (take t n))`;;

let REST_DEF = define `
    (! (l : (A)list). rest (l) (0 : num) = l) /\
    (! (h : A) (t : (A)list) (n : num). rest (CONS h t) (SUC n) = rest t n)`;;

(* EQ_EXT *)

let IFILTER_DEF = define `ifilter (l : ((num#num)#(PTR#PTR))list) (i : num) = ((REF (nth l i) = 0) /\ ~(ORD (nth l i) = NO_ORDER))`;;

let () = new_constant("DATA_AT_PTR_ANY", `: PTR -> HPROP`);;

let FREE_AREA_REPR_DEF = define `
    (! (f : num -> bool) (lo : num) (hi : num).
    free_area_repr f lo hi (NIL : ((num#num)#(PTR#PTR))list) = (PURE (lo = hi) SEPAND EMP)) /\
    (! (f : num -> bool) (lo : num) (hi : num) (h : (num#num)#(PTR#PTR)) (t : ((num#num)#(PTR#PTR))list).
    free_area_repr f lo hi (CONS h t) = 
        ((if f lo then
            DATA_AT_PTR (id2vi (&lo), NXT h) SEPCONJ
            DATA_AT_PTR (id2vi (&lo) + &PTR_SIZE, PRV h) SEPCONJ
            (store_zero_array (id2vi (&lo)) (PTR_SIZE * 2) (PAGE_SIZE * (2 EXP (ORD h))) (PAGE_SIZE * (2 EXP (ORD h)) - PAGE_SIZE * 2))
        else EMP) SEPCONJ
        free_area_repr f (SUC lo) hi t))`;;

let DLIST_NODE_DEF = define `
    (! (addr : PTR) (l : ((num#num)#(PTR#PTR))list) (hl : (PTR#PTR)list) (lo : num) (hi : num).
    dlist_node addr l hl lo hi (NIL : ((num#num)#(PTR#PTR))list) = (lo = hi)) /\
    (! (addr : PTR) (l : ((num#num)#(PTR#PTR))list) (hl : (PTR#PTR)list) (lo : num) (hi : num) (h : (num#num)#(PTR#PTR)) (t : ((num#num)#(PTR#PTR))list).
    dlist_node addr l hl lo hi (CONS h t) = ((
        (((NXT h = addr + &(LIST_HEAD_SIZE * (ORD h))) /\ (SND (nth hl (ORD h)) = id2vi (&lo))) \/
        ((PRV (nth l (vi2id (NXT h) - start)) = id2vi (&lo)) /\ (REF (nth l (vi2id (NXT h) - start)) = 0) /\ ~(ORD (nth l (vi2id (NXT h) - start)) = NO_ORDER))) /\
        (((PRV h = addr + &(LIST_HEAD_SIZE * (ORD h))) /\ (FST (nth hl (ORD h)) = id2vi (&lo))) \/
        ((NXT (nth l (vi2id (PRV h) - start)) = id2vi (&lo)) /\ (REF (nth l (vi2id (PRV h) - start)) = 0) /\ ~(ORD (nth l (vi2id (PRV h) - start)) = NO_ORDER)))
    ) /\ dlist_node addr l hl (SUC lo) hi t))`;;

let DLIST_HEAD_DEF = define `
    (! (addr : PTR) (l : ((num#num)#(PTR#PTR))list) (order : num) (maxorder : num).
    dlist_head addr l order maxorder (NIL : (PTR#PTR)list) = (order = maxorder)) /\
    (! (addr : PTR) (l : ((num#num)#(PTR#PTR))list) (order : num) (maxorder : num) (h : PTR#PTR) (t : (PTR#PTR)list).
    dlist_head addr l order maxorder (CONS h t) = ((
        ((FST h = addr + &(LIST_HEAD_SIZE * order)) /\ (SND h = addr + &(LIST_HEAD_SIZE * order))) \/
        ((PRV (nth l (vi2id (FST h) - start)) = addr + &(LIST_HEAD_SIZE * order)) /\ 
        (REF (nth l (vi2id (FST h) - start)) = 0) /\ 
        ~(ORD (nth l (vi2id (FST h) - start)) = NO_ORDER) /\
        (NXT (nth l (vi2id (SND h) - start)) = addr + &(LIST_HEAD_SIZE * order)) /\ 
        (REF (nth l (vi2id (SND h) - start)) = 0) /\ 
        ~(ORD (nth l (vi2id (SND h) - start)) = NO_ORDER))
    ) /\ dlist_head addr l (SUC order) maxorder t))`;;

let TOTAL_REPR_DEF = define `
    total_repr (pool_ptr : PTR) (vmemmap_ptr : PTR) (l : ((num#num)#(PTR#PTR))list) (hl : (PTR#PTR)list) = (
        pool_const pool_ptr SEPCONJ
        dlist_head_repr pool_ptr 0 max_order hl SEPCONJ
        free_area_repr (ifilter l) start end l SEPCONJ
        store_pageinfo_array vmemmap_ptr start end l SEPAND
        PURE (
            dlist_node pool_ptr l hl start end l /\ 
            dlist_head pool_ptr l 0 max_order hl /\ 
            (LENGTH l = len))
    )`;;

(* TODO : 页面越界判断 *)