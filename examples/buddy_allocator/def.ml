let PTR_SIZE_DEF = define `PTR_SIZE : num = 8`;;
let LIST_HEAD_SIZE_DEF = define `LIST_HEAD_SIZE : num = PTR_SIZE * 2`;;

let PAGE_SIZE_DEF = define `PAGE_SIZE : num = 4096`;;
let MAX_ORDER_DEF = define `MAX_ORDER : num = 11`;;
let NO_ORDER_DEF = define `NO_ORDER : num = 255`;;
let RANGE_LIM_DEF = define `RANGE_LIM : num = 4503599627370496`;;
let REF_LIM_DEF = define `REF_LIM : num = 65536`;;

let START_DEF = define `start = @x : num. T`;;
let END_DEF = define `end = @x : num. x > start /\ x * PAGE_SIZE < RANGE_LIM`;;
let LEN_DEF = define `len : num = end - start`;;
let MAX_ORDER__DEF = define `max_order = @x : num. x <= MAX_ORDER`;;
let OFF_SET_DEF = define `offset = @x : num. x <= start * PAGE_SIZE /\ PAGE_SIZE divides x`;;

let PH2VI_DEF = define `ph2vi (ph : PTR) = ph - &offset`;;
let VI2PH_DEF = define `vi2ph (vi : PTR) = vi + &offset`;;
let PH2ID_DEF = define `ph2id (ph : PTR) = ph div &PAGE_SIZE`;;
let VI2ID_DEF = define `vi2id (vi : PTR) = ph2id (vi2ph vi)`;;
let ID2PH_DEF = define `id2ph (id : int) = id * &PAGE_SIZE`;;
let ID2VI_DEF = define `id2vi (id : int) = ph2vi (id2ph id)`;;

let REF_DEF = define `(REF : (A#B) -> A) = FST`;;
let ORD_DEF = define `(ORD : (A#B) -> B) = SND`;;

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
    store_pageinfo_array addr lo hi (NIL : (num#num)list) = (PURE (lo = hi) SEPAND EMP)) /\
    (! (addr : PTR) (lo : num) (hi : num) (h : num#num) (t : (num#num)list).
    store_pageinfo_array addr lo hi (CONS h t) = ((
            DATA_AT_SHORT (addr + &((lo - start) * 4), &(REF h)) SEPCONJ
            DATA_AT_CHAR (addr + &((lo - start) * 4 + 2), &(ORD h)) SEPCONJ
            DATA_AT_CHAR_ANY (addr + &((lo - start) * 4 + 3))
        ) SEPCONJ store_pageinfo_array addr (SUC lo) hi t))`;;

let POOL_CONST_DEF = define `
    pool_const (pool_ptr : PTR) = (
        DATA_AT_INT (pool_ptr + &(LIST_HEAD_SIZE * MAX_ORDER), id2ph (&start)) SEPCONJ
        DATA_AT_INT (pool_ptr + &(LIST_HEAD_SIZE * MAX_ORDER + 8), id2ph (&end)) SEPCONJ
        DATA_AT_CHAR (pool_ptr + &(LIST_HEAD_SIZE * MAX_ORDER + 16), &max_order))`;;

let DLIST_REPR__DEF = new_axiom `
    (! (ptr : PTR) (pre : PTR) (head : PTR) (order : num).
        dlist_repr_ ptr (NIL : (num)list) pre head order = 
        (PURE (ptr = head) SEPAND EMP)) /\
    (! (ptr : PTR) (h : num) (t : (num)list) (pre : PTR) (head : PTR) (order : num).
        dlist_repr_ ptr (CONS h t) pre head order = 
        (SEPEXISTS (next : PTR) (prev : PTR). 
            PURE ((vi2id ptr = &h) /\ (prev = pre)) SEPAND
            (
                DATA_AT_PTR (ptr, next) SEPCONJ
                DATA_AT_PTR (ptr + &PTR_SIZE, prev) SEPCONJ
                (store_zero_array ptr (PTR_SIZE * 2) (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order) - PAGE_SIZE * 2)) SEPCONJ
                (dlist_repr_ next t ptr head order)
            )))`;;
let () = new_constant("dlist_repr_", `: int -> (num)list -> int -> int -> num -> HPROP`);;

(* prove_general_recursive_function_exists *)

let DLIST_REPR_DEF = define `
    dlist_repr (ptr : PTR) (l : (num)list) (order : num) = 
        SEPEXISTS (next : PTR) (prev : PTR).
            DATA_AT_PTR (ptr, next) SEPCONJ
            DATA_AT_PTR (ptr + &PTR_SIZE, prev) SEPCONJ
            if l = NIL then PURE ((prev = ptr) /\ (next = ptr)) SEPAND EMP
            else dlist_repr_ next l ptr ptr order`;;

let FREE_AREA_DLIST_REPR_DEF = define `
    (! (ptr : PTR) (order : num).
    free_area_dlist_repr ptr (NIL : ((num)list)list) order =
        (PURE (order = max_order) SEPAND EMP)) /\
    (! (ptr : PTR) (h : (num)list) (t : ((num)list)list) (order : num).
    free_area_dlist_repr ptr (CONS h t) order =
        (dlist_repr ptr h order SEPCONJ
            free_area_dlist_repr (ptr + &LIST_HEAD_SIZE) t (order + 1)))`;;

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

let BOUND_DEF = define `
    (bound (NIL : (num#num)list) = T) /\
    (! (h : num#num) (t : (num#num)list). bound (CONS h t) = 
        ((REF h < REF_LIM) /\ (~(ORD h = NO_ORDER) ==> (ORD h <= max_order))))`;;

let PAGE_ALIGNED_DEF = define `
    (! (lo : num) (hi : num).
    page_aligned lo hi (NIL : (num#num)list) = (lo = hi)) /\
    (! (lo : num) (hi : num) (h : num#num) (t : (num#num)list).
    page_aligned lo hi (CONS h t) = 
        ((~((ORD h) = NO_ORDER) ==> ((2 EXP (ORD h)) divides lo)) /\
        page_aligned (SUC lo) hi t))`;;

(* EQ_EXT *)

let IFILTER_DEF = define `ifilter (l : (num#num)list) (i : num) = ((REF (nth l i) = 0) /\ ~(ORD (nth l i) = NO_ORDER))`;;

let () = new_constant("DATA_AT_PTR_ANY", `: PTR -> HPROP`);;

let FREE_AREA_ARRAY_REPR_DEF = define `
    (! (f : num -> bool) (lo : num) (hi : num).
    free_area_array_repr f lo hi (NIL : (num#num)list) = (PURE (lo = hi) SEPAND EMP)) /\
    (! (f : num -> bool) (lo : num) (hi : num) (h : num#num) (t : (num#num)list).
    free_area_array_repr f lo hi (CONS h t) = 
        ((if f lo then 
            DATA_AT_PTR_ANY (id2vi (&lo)) SEPCONJ
            DATA_AT_PTR_ANY (id2vi (&lo) + &PTR_SIZE) SEPCONJ
            (store_zero_array (id2vi (&lo)) (PTR_SIZE * 2) (PAGE_SIZE * (2 EXP (ORD h))) (PAGE_SIZE * (2 EXP (ORD h)) - PAGE_SIZE * 2))
        else EMP) SEPCONJ
        free_area_array_repr f (SUC lo) hi t))`;;

let TOTAL_REPR_DEF = define `
    total_repr (pool_ptr : PTR) (L : ((num)list)list) (vmemmap_ptr : PTR) (l : (num#num)list) = (
        pool_const pool_ptr SEPCONJ
        (
            free_area_array_repr (ifilter l) start end l SEPAND
            free_area_dlist_repr pool_ptr L 0
        ) SEPCONJ
        store_pageinfo_array vmemmap_ptr start end l SEPAND
        PURE (page_aligned start end l /\ bound l /\ (LENGTH l = len))
    )`;;

(* TODO : 页面越界判断 *)