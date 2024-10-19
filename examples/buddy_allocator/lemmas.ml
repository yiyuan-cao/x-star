let plus0 = prove (`! (a : num). a + 0 = a`, ARITH_TAC);;
let plus0_ = prove (`! (a : num). 0 + a = a`, ARITH_TAC);;
let minus0 = prove (`! (a : num). a - 0 = a`, ARITH_TAC);;
let minusaa = prove (`! (a : num). (a - a) = 0`, ARITH_TAC);;
let l_suc = prove (`! (a : num). a < SUC a`, ARITH_TAC);;
let l_le = prove (`! (a : num) (b : num). (a < b) ==> (a <= b)`, ARITH_TAC);;
let le_ne = prove (`! (a : num) (b : num). (a <= b) ==> ~(a = b) ==> (SUC a <= b)`, ARITH_TAC);;
let suc_e = prove (`! (a : num) (b : num). (SUC a = SUC b) ==> (a = b)`, ARITH_TAC);;
let suc_ne = prove (`! (a : num) (b : num). ~(SUC a = SUC b) ==> ~(a = b)`, ARITH_TAC);;
let suc_l = prove (`! (a : num) (b : num). (SUC a < SUC b) ==> (a < b)`, ARITH_TAC);;
let suc_l_ = prove (`! (a : num) (b : num). (a < b) ==> (a < SUC b)`, ARITH_TAC);;
let suc_le = prove (`! (a : num) (b : num). (SUC a <= SUC b) ==> (a <= b)`, ARITH_TAC);;
let suc_le_ = prove (`! (a : num) (b : num). (SUC a <= b) ==> (a <= b)`, ARITH_TAC);;
let suc_le__ = prove (`! (a : num) (b : num). (a <= b) ==> (a <= SUC b)`, ARITH_TAC);;
let sucoff = prove (`! (a : num) (b : num) (c : num). (SUC b <= a) ==> (a - SUC b + SUC c = a - b + c)`, ARITH_TAC);;
let sucoff2 = prove (`! (a : num) (b : num). (SUC b <= a) ==> (SUC (a - SUC b) = a - b)`, ARITH_TAC);;
let sucoff3 = prove (`! (a : num) (b : num) (c : num). ((a - b + SUC c) = SUC (a - b + c))`, ARITH_TAC);;
let sucoff4 = prove (`! (a : num) (b : num). (SUC a - SUC b) = (a - b)`, ARITH_TAC);;
let l_ne = prove (`! (a : num) (b : num). (a < b) ==> ~(a = b)`, ARITH_TAC);;
let le_l_l = prove (`! (a : num) (b : num) (c : num). (a <= b) ==> (b < c) ==> (a < c)`, ARITH_TAC);;
let ne_sym = prove (`! (a : num) (b : num). ~(a = b) ==> ~(b = a)`, ARITH_TAC);;
let minus_l = prove (`! (a : num) (b : num). (SUC b <= a) ==> (a - b = SUC (a - SUC b))`, ARITH_TAC);;
let plus_mono = prove (`! (a : num) (b : num) (c : num). (a + c = b + c) = (a = b)`, ARITH_TAC);;
let plus_assoc1 = prove (`! (a : int) (b : num) (c : num). a + &(b + c) = (a + &c) + &b`, ARITH_TAC);;
let suc_plus = prove (`! (a : num) (b : num). SUC (a + b) = SUC a + b`, ARITH_TAC);;
let le1 = prove (`! (a : num). a <= a`, ARITH_TAC);;
let le2 = prove (`! (a : num). a <= (a * 2)`, ARITH_TAC);;
let multi_assoc1 = prove (`! (a : num) (b : num) (c : num). (a * b) * c = a * (b * c)`, ARITH_TAC);;
let multi_minus1 = prove (`! (a : num). (a * 2 - a) = a`, ARITH_TAC);;
let multi2 = prove (`! (a : num). a + a = a * 2`, ARITH_TAC);;

let impl_conj_mono = prove (`! p1 p2 p3 p4. ((p1 ==> p3) /\ (p2 ==> p4)) ==> ((p1 /\ p2) ==> (p3 /\ p4))`, SIMP_TAC []);;
let impl_disj_mono = new_axiom `! p1 p2 p3 p4. ((p1 ==> p3) /\ (p2 ==> p4)) ==> ((p1 \/ p2) ==> (p3 \/ p4))`;;

let pure_t_sepand = prove (`! (hp : HPROP). (PURE T SEPAND hp) = hp`, REWRITE_TAC [SYM SEPTRUE_DEF; MATCH_MP SEPIFF_EXT (SPEC `hp : HPROP` SEPAND_TRUE_LEFT)]);;
let emp_conj = prove (`! (hp : HPROP). (EMP SEPCONJ hp) = hp`, REWRITE_TAC [MATCH_MP SEPIFF_EXT (SPEC `hp : HPROP` SEPCONJ_EMP_LEFT)]);;
let sepconj_comm = GEN_ALL (MATCH_MP SEPIFF_EXT (SPEC_ALL SEPCONJ_COMM));;
let sepconj_assoc1 = GEN_ALL (MATCH_MP SEPIFF_EXT (SPEC_ALL SEPCONJ_ASSOC));;
let sepconj_assoc2 = GEN_ALL (SYM (MATCH_MP SEPIFF_EXT (SPEC_ALL SEPCONJ_ASSOC)));;
let sepconj_elim1 = prove (`! hp1 hp2 hp3. (hp1 = hp2) ==> (hp3 SEPCONJ hp1) = (hp3 SEPCONJ hp2)`, REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC []);;
let sepfalse_and = new_axiom (`! hp. (PURE F SEPAND hp) = PURE F`);;
let sepfalse_conj = new_axiom (`! hp. (PURE F SEPCONJ hp) = PURE F`);;
let sepconj_emp1 = GEN_ALL (MATCH_MP SEPIFF_EXT (SPEC_ALL SEPCONJ_EMP_LEFT));;
let sepconj_mono = prove (`!hp1 hp2 hp1' hp2'. (hp1 = hp1') /\ (hp2 = hp2') ==> (hp1 SEPCONJ hp2) = (hp1' SEPCONJ hp2')`, REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC []);;
let sepconj_mono' = prove (`!hp1 hp2 hp1' hp2'. (hp1 = hp1') /\ (hp2 = hp2') ==> (hp1 SEPCONJ hp2) = (hp2' SEPCONJ hp1')`, REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [sepconj_comm]);;

let start_end = new_axiom `end - (end - start) = start`;;
let start_end2 = prove (`(end - start) <= end`, ARITH_TAC);;
let id2i_inv = prove (`! (a : num). id2i (start + a) = a`, REWRITE_TAC [ID2I_DEF] THEN ARITH_TAC);;
let id2i_l = prove (`! (a : num) (b : num). (start + a < b) ==> (a < id2i b)`, REWRITE_TAC [ID2I_DEF] THEN ARITH_TAC);;
let id2i_ne = prove (`! (a : num) (b : num). (start <= b) ==> ~(b = start + a) ==> ~(id2i b = a)`, REWRITE_TAC [ID2I_DEF] THEN ARITH_TAC);;
let ref_open = prove (`! (ref : num) (order : num). REF (ref, order) = ref`, REWRITE_TAC [REF_DEF]);;
let ord_open = prove (`! (ref : num) (order : num). ORD (ref, order) = order`, REWRITE_TAC [ORD_DEF]);;
let id2vi_plus = new_axiom `! (a : num) (b : num). (offset <= a * PAGE_SIZE) ==> id2vi (a + b) = id2vi a + &(PAGE_SIZE * b)`;;

let IMATCH_MP ith =
    let sth =
      try let tm = concl ith in
          let avs,bod = strip_forall tm in
          let ant,con = dest_imp bod in
          let svs,pvs = partition (C vfree_in ant) avs in
          if pvs = [] then ith else
          let th1 = ISPECL avs (ASSUME tm) in
          let th2 = GENL svs (DISCH ant (GENL pvs (UNDISCH th1))) in
          MP (DISCH tm th2) ith
      with Failure _ -> failwith "MATCH_MP: Not an implication" in
    let match_fun = PART_MATCH (fst o dest_imp) sth in
    fun th -> try MP (match_fun (concl th)) th
              with Failure _ -> failwith "MATCH_MP: No match"
;;

let rest_nth = prove (
    `! (n : num) (l : (A)list).
        (n < LENGTH l) ==> (rest l n = CONS (nth l n) (rest l (SUC n)))`,
    INDUCT_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH] THENL
    [
        ARITH_TAC;
        REWRITE_TAC [REST_DEF; NTH_DEF];
        ARITH_TAC;

        REWRITE_TAC [REST_DEF; NTH_DEF] THEN
        DISCH_TAC THEN
        POP_ASSUM (fun th -> ASSUME_TAC (MATCH_MP suc_l th)) THEN
        NAME_ASSUMS_TAC THEN
        POP_ASSUM (fun th -> USE_THEN "H2" (fun th' -> MATCH_ACCEPT_TAC (MATCH_MP th' th)))
    ]
);;

let modified_nth = prove (
    `! (l : (A)list) (n : num) (v : A). 
        (n < LENGTH l) ==> ((nth (modified l n v) n) = v)`,
    LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH] THENL
    [
        ARITH_TAC;

        INDUCT_TAC THEN
        ONCE_REWRITE_TAC [MODIFIED_DEF] THEN
        ONCE_REWRITE_TAC [NTH_DEF] THEN
        SIMP_TAC [] THEN
        REPEAT GEN_TAC THEN
        DISCH_TAC THEN
        NAME_ASSUMS_TAC THEN
        POP_ASSUM (fun th -> USE_THEN "H2" (fun th' -> MATCH_ACCEPT_TAC (
            MATCH_MP th' (MATCH_MP suc_l th)
        )))
    ]
);;

let modified_n'th = prove (
    `! (l : (A)list) (n : num) (n' : num) (v : A). 
        (n < LENGTH l) ==> ~(n' = n) ==> ((nth (modified l n v) n') = (nth l n'))`,
    LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH] THENL
    [
        ARITH_TAC;

        INDUCT_TAC THEN INDUCT_TAC THEN
        ONCE_REWRITE_TAC [MODIFIED_DEF] THEN
        ONCE_REWRITE_TAC [NTH_DEF] THEN
        SIMP_TAC [] THEN
        REPEAT GEN_TAC THEN
        DISCH_TAC THEN POP_ASSUM (fun th -> ASSUME_TAC (MATCH_MP suc_l th)) THEN
        DISCH_TAC THEN POP_ASSUM (fun th -> ASSUME_TAC (MATCH_MP suc_ne th)) THEN
        NAME_ASSUMS_TAC THEN
        POP_ASSUM (fun th -> POP_ASSUM (fun th' -> USE_THEN "H4" (fun th'' -> MATCH_ACCEPT_TAC (
            MATCH_MP (MATCH_MP th'' th') th
        ))))
    ]
);;

let modified_taken = prove (
    `! (l : (A)list) (n : num) (v : A). 
        (n < LENGTH l) ==> ((take (modified l n v) n) = (take l n))`,
    LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH] THENL
    [
        ARITH_TAC;

        INDUCT_TAC THEN
        ONCE_REWRITE_TAC [MODIFIED_DEF] THEN
        ONCE_REWRITE_TAC [TAKE_DEF] THEN
        SIMP_TAC [] THEN
        REPEAT GEN_TAC THEN
        DISCH_TAC THEN
        NAME_ASSUMS_TAC THEN
        POP_ASSUM (fun th -> USE_THEN "H2" (fun th' -> REWRITE_TAC [
            MATCH_MP th' (MATCH_MP suc_l th)
        ]))
    ]
);;

let modified_restn = prove (
    `! (l : (A)list) (n : num) (v : A). 
        (n < LENGTH l) ==> ((rest (modified l n v) (SUC n)) = (rest l (SUC n)))`,
    LIST_INDUCT_TAC THEN REWRITE_TAC [LENGTH] THENL
    [
        ARITH_TAC;

        INDUCT_TAC THEN
        ONCE_REWRITE_TAC [MODIFIED_DEF] THEN
        ONCE_REWRITE_TAC [REST_DEF] THEN
        SIMP_TAC [] THEN
        REPEAT GEN_TAC THEN
        DISCH_TAC THEN
        NAME_ASSUMS_TAC THEN
        POP_ASSUM (fun th -> USE_THEN "H2" (fun th' -> MATCH_ACCEPT_TAC (
            MATCH_MP th' (MATCH_MP suc_l th)
        )))
    ]
);;

let modified_len = prove (
    `! (l : (A)list) (n : num) (v : A). LENGTH l = LENGTH (modified l n v)`,
    LIST_INDUCT_TAC THEN INDUCT_TAC THEN GEN_TAC THEN
    REWRITE_TAC [LENGTH; MODIFIED_DEF] THEN
    ASM_REWRITE_TAC []
);;

let break_list_sepconj = prove (
    `! (P : B -> num -> num -> (A)list -> HPROP) (ONE : B -> A -> num -> HPROP).
    ((! (arg1 : B) (lo : num) (hi : num). P arg1 lo hi NIL = (PURE (lo = hi) SEPAND EMP)) /\
    (! (arg1 : B) (lo : num) (hi : num) (h : A) (t : (A)list). P arg1 lo hi (CONS h t) = ((ONE arg1 h lo) SEPCONJ (P arg1 (SUC lo) hi t)))) ==>
    (! (len : num) (n : num) (l : (A)list) (arg1 : B) (hi : num).
        (n <= len) /\ (len <= hi) /\ (len = LENGTH l) ==>
        P arg1 (hi - len) hi l = (P arg1 (hi - len) (hi - len + n) (take l n) SEPCONJ P arg1 (hi - len + n) hi (rest l n)))`,
    GEN_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN INDUCT_TAC THENL
    [
        ONCE_REWRITE_TAC [TAKE_DEF; REST_DEF] THEN
        ASM_REWRITE_TAC [plus0; pure_t_sepand; emp_conj];

        ARITH_TAC;

        ONCE_REWRITE_TAC [TAKE_DEF; REST_DEF] THEN
        ASM_REWRITE_TAC [plus0; pure_t_sepand; emp_conj];

        LIST_INDUCT_TAC THENL
        [
            REWRITE_TAC [LENGTH] THEN
            ARITH_TAC;

            REPEAT GEN_TAC THEN DISCH_TAC THEN
            ONCE_REWRITE_TAC [TAKE_DEF; REST_DEF] THEN
            ASM_REWRITE_TAC [] THEN
            FIRST_ASSUM (fun th -> REWRITE_TAC [
                MATCH_MP sucoff (CONJUNCT1 (CONJUNCT2 th));
                SYM (CONJUNCT2 (CONJUNCT2 th));
                MATCH_MP sucoff2 (CONJUNCT1 (CONJUNCT2 th));
                sepconj_assoc2
            ]) THEN
            MATCH_MP_TAC sepconj_elim1 THEN
            FIRST_ASSUM (fun th -> ASSUME_TAC (
                MATCH_MP suc_e (REWRITE_RULE [LENGTH] (CONJUNCT2 (CONJUNCT2 th)))
            )) THEN
            POP_ASSUM (fun th -> FIRST_ASSUM (fun th' -> ASSUME_TAC (
                CONJ (MATCH_MP suc_le_ (CONJUNCT1 (CONJUNCT2 th'))) th
            ))) THEN
            POP_ASSUM (fun th -> FIRST_ASSUM (fun th' -> ASSUME_TAC (
                CONJ (MATCH_MP suc_le (CONJUNCT1 th')) th
            ))) THEN
            NAME_ASSUMS_TAC THEN
            POP_ASSUM (fun th -> USE_THEN "H4" (fun th' -> MATCH_ACCEPT_TAC (
                MATCH_MP th' th
            )))
        ]
    ]
);;

let breaknth_list_sepconj = prove (
    `! (P : B -> num -> num -> (A)list -> HPROP) (ONE : B -> A -> num -> HPROP).
    ((! (arg1 : B) (lo : num) (hi : num). P arg1 lo hi NIL = (PURE (lo = hi) SEPAND EMP)) /\
    (! (arg1 : B) (lo : num) (hi : num) (h : A) (t : (A)list). P arg1 lo hi (CONS h t) = ((ONE arg1 h lo) SEPCONJ (P arg1 (SUC lo) hi t)))) ==>
    (! (len : num) (n : num) (l : (A)list) (arg1 : B) (hi : num).
        (n < len) /\ (len <= hi) /\ (len = LENGTH l) ==> 
        (P arg1 (hi - len) hi l = (
        (P arg1 (hi - len) (hi - len + n) (take l n)) SEPCONJ 
        (ONE arg1 (nth l n) (hi - len + n)) SEPCONJ
        (P arg1 (hi - len + (SUC n)) hi (rest l (SUC n))))))`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    FIRST_ASSUM (fun th -> ASSUME_TAC (MATCH_MP break_list_sepconj th)) THEN
    DISCH_TAC THEN
    FIRST_ASSUM (fun th -> ASSUME_TAC (
        CONJ (MATCH_MP l_le (CONJUNCT1 th)) (CONJUNCT2 th)
    )) THEN
    NAME_ASSUMS_TAC THEN
    POP_ASSUM (fun th -> USE_THEN "H2" (fun th' -> ASSUME_TAC (MATCH_MP th' th))) THEN
    POP_ASSUM (fun th -> USE_THEN "H1" (fun th' -> ASSUME_TAC (
        REWRITE_RULE [MATCH_MP rest_nth (
        REWRITE_RULE [CONJUNCT2 (CONJUNCT2 th')] (CONJUNCT1 th'))] th
    ))) THEN
    POP_ASSUM (fun th -> USE_THEN "H3" (fun th' -> ASSUME_TAC (REWRITE_RULE [th'] th))) THEN
    ASM_SIMP_TAC [sucoff3]
);;

let merge_modified_list_sepconj = prove (
    `! (P : B -> num -> num -> (A)list -> HPROP) (ONE : B -> A -> num -> HPROP).
    ((! (arg1 : B) (lo : num) (hi : num). P arg1 lo hi NIL = (PURE (lo = hi) SEPAND EMP)) /\
    (! (arg1 : B) (lo : num) (hi : num) (h : A) (t : (A)list). P arg1 lo hi (CONS h t) = ((ONE arg1 h lo) SEPCONJ (P arg1 (SUC lo) hi t)))) ==>
    (! (len : num) (n : num) (l : (A)list) (arg1 : B) (hi : num) (v : A).
        (n < len) /\ (len <= hi) /\ (len = LENGTH l) ==> 
        (P arg1 (hi - len) hi (modified l n v) = (
        (P arg1 (hi - len) (hi - len + n) (take l n)) SEPCONJ 
        (ONE arg1 v (hi - len + n)) SEPCONJ
        (P arg1 (hi - len + (SUC n)) hi (rest l (SUC n))))))`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
    FIRST_ASSUM (fun th -> ASSUME_TAC (MATCH_MP breaknth_list_sepconj th)) THEN
    DISCH_TAC THEN
    NAME_ASSUMS_TAC THEN
    FIRST_ASSUM (fun th -> ASSUME_TAC (ONCE_REWRITE_RULE [modified_len] th)) THEN
    POP_ASSUM (fun th -> USE_THEN "H1" (fun th' -> REWRITE_TAC [MATCH_MP th' th])) THEN
    POP_ASSUM (fun th -> ASSUME_TAC (REWRITE_RULE [CONJUNCT2 (CONJUNCT2 th)] (CONJUNCT1 th))) THEN
    POP_ASSUM (fun th -> REWRITE_TAC [
        MATCH_MP modified_nth th; 
        MATCH_MP modified_taken th; 
        MATCH_MP modified_restn th
    ])
);;

let filter_inv = prove (
    `! (l : (num#num)list) (i : num) (v : num#num).
    (i < LENGTH l) ==>
    (((REF v = 0) /\ ~(ORD v = NO_ORDER)) <=> ((REF (nth l i) = 0) /\ ~(ORD (nth l i) = NO_ORDER))) ==>
    ifilter l = ifilter (modified l i v)`,
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC EQ_EXT THEN GEN_TAC THEN
    REWRITE_TAC [IFILTER_DEF] THEN
    ASM_CASES_TAC `(id2i x) = i : num` THENL
    [
        ASM_REWRITE_TAC [] THEN
        NAME_ASSUMS_TAC THEN
        USE_THEN "H2" (fun th -> REWRITE_TAC [MATCH_MP modified_nth th]) THEN
        ASM_REWRITE_TAC [];

        NAME_ASSUMS_TAC THEN
        POP_ASSUM (fun th -> USE_THEN "H2" (fun th' -> REWRITE_TAC [
            MATCH_MP (MATCH_MP modified_n'th th') th
        ]))
    ]
);;

let far_inv = prove (
    `! (l : (num#num)list) (i : num) (v : num#num) (filter : num -> bool).
    (i < len) ==> (len = LENGTH l) ==> (filter (start + i) = F) ==> (
        free_area_repr filter start end l =
        free_area_repr filter start end (modified l i v))`,
    REWRITE_TAC [LEN_DEF] THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    ASSUME_TAC (IMATCH_MP breaknth_list_sepconj FREE_AREA_REPR_DEF) THEN
    POP_ASSUM (fun th -> ASSUME_TAC (
        GEN `l : (num#num)list` (ISPECL [`end - start : num`; `i : num`; `l : (num#num)list`; `filter : num -> bool`; `end`] th)
    )) THEN
    POP_ASSUM (fun th -> ASSUME_TAC (REWRITE_RULE [start_end] th)) THEN
    NAME_ASSUMS_TAC THEN
    USE_THEN "H2" (fun th -> ASSUME_TAC (ONCE_REWRITE_RULE [modified_len] th)) THEN
    USE_THEN "H0" (fun th -> USE_THEN "H3" (fun th' -> POP_ASSUM (fun th'' -> REWRITE_TAC [
        MATCH_MP th (CONJ th' (CONJ start_end2 th''))
    ]))) THEN
    USE_THEN "H3" (fun th -> USE_THEN "H2" (fun th' -> ASSUME_TAC (REWRITE_RULE [th'] th))) THEN
    POP_ASSUM (fun th -> REWRITE_TAC [
        MATCH_MP modified_nth th;
        MATCH_MP modified_taken th;
        MATCH_MP modified_restn th
    ]) THEN
    USE_THEN "H0" (fun th -> USE_THEN "H3" (fun th' -> USE_THEN "H2" (fun th'' -> REWRITE_TAC [
        MATCH_MP th (CONJ th' (CONJ start_end2 th''))
    ]))) THEN
    ASM_REWRITE_TAC []
);;

let dn_inv = prove (
    `! (dl' : (PTR#PTR)list) (l : (num#num)list) (hl : (PTR#PTR)list) (dl : (PTR#PTR)list)
        (i : num) (v : num#num) (addr : PTR) (lo : num) (hi : num).
    (i < LENGTH l) ==>
    ~((REF (nth l i) = 0) /\ ~(ORD (nth l i) = NO_ORDER)) ==>
    dlist_node addr (ifilter l) l dl hl lo hi dl' ==>
    dlist_node addr (ifilter l) (modified l i v) dl hl lo hi dl'`,
    LIST_INDUCT_TAC THEN REWRITE_TAC [DLIST_NODE_DEF] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC impl_conj_mono THEN CONJ_TAC THENL
    [
        ASM_CASES_TAC `id2i lo = (i : num)` THENL
        [
            REWRITE_TAC [IFILTER_DEF] THEN
            ASM_REWRITE_TAC [];

            NAME_ASSUMS_TAC THEN
            USE_THEN "H2" (fun th -> USE_THEN "H0" (fun th' -> REWRITE_TAC [
                MATCH_MP (MATCH_MP modified_n'th th) th'
            ])) THEN
            ASM_CASES_TAC `ifilter l lo` THEN
            ASM_REWRITE_TAC [] THEN
            MATCH_MP_TAC impl_conj_mono THEN CONJ_TAC THENL
            [
                ASM_CASES_TAC `vi2i (NXT h) = i`;
                ASM_CASES_TAC `vi2i (PRV h) = i`
            ] THEN
            ASM_REWRITE_TAC [] THEN
            SIMP_TAC [] THEN
            FIRST_ASSUM (fun th -> USE_THEN "H2" (fun th' -> REWRITE_TAC [
                MATCH_MP (MATCH_MP modified_n'th th') th
            ]));
        ];
        NAME_ASSUMS_TAC THEN
        USE_THEN "H2" (fun th1 -> 
        USE_THEN "H1" (fun th2 ->
        USE_THEN "H0" (fun th3 ->  
        MATCH_ACCEPT_TAC (
            MATCH_MP (MATCH_MP th1 th2) th3
        ))))
    ]
);;

let dh_inv = prove (
    `! (hl : (PTR#PTR)list) (l : (num#num)list) (dl : (PTR#PTR)list)
        (i : num) (v : num#num) (addr : PTR) (order : num) (maxorder : num).
    (i < LENGTH l) ==>
    ~((REF (nth l i) = 0) /\ ~(ORD (nth l i) = NO_ORDER)) ==>
    dlist_head addr l dl order maxorder hl ==>
    dlist_head addr (modified l i v) dl order maxorder hl`,
    LIST_INDUCT_TAC THEN REWRITE_TAC [DLIST_HEAD_DEF] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC impl_conj_mono THEN CONJ_TAC THENL
    [
        MATCH_MP_TAC impl_disj_mono THEN 
        CONJ_TAC THEN SIMP_TAC [] THEN
        ASM_CASES_TAC `vi2i (NXT h) = (i : num)` THEN
        ASM_REWRITE_TAC [] THEN
        NAME_ASSUMS_TAC THEN
        USE_THEN "H2" (fun th -> FIRST_ASSUM (fun th' -> REWRITE_TAC[
            MATCH_MP (MATCH_MP modified_n'th th) th'
        ])) THEN
        ASM_CASES_TAC `vi2i (PRV h) = (i : num)` THEN
        ASM_REWRITE_TAC [] THEN
        USE_THEN "H2" (fun th -> FIRST_ASSUM (fun th' -> REWRITE_TAC[
            MATCH_MP (MATCH_MP modified_n'th th) th'
        ])) THEN
        SIMP_TAC [];

        NAME_ASSUMS_TAC THEN
        USE_THEN "H2" (fun th1 -> 
        USE_THEN "H1" (fun th2 ->
        USE_THEN "H0" (fun th3 ->
            MATCH_ACCEPT_TAC (MATCH_MP (MATCH_MP th1 th2) th3)
        )))
    ]
);;

let far_lemma = prove (
    `! (l' : (num#num)list) (l : (num#num)list) 
        (filter : num -> bool) (i : num) (lo : num) (hi : num) (order : num).
    (start + i < lo) ==> (i < LENGTH l) ==> (
        free_area_repr (ifilter l) lo hi l' =
        free_area_repr (ifilter (modified l i (0, order))) lo hi l')`,
    LIST_INDUCT_TAC THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    ONCE_REWRITE_TAC [FREE_AREA_REPR_DEF] THEN
    SIMP_TAC [] THEN
    MATCH_MP_TAC sepconj_mono THEN CONJ_TAC THENL
    [
        REWRITE_TAC [IFILTER_DEF] THEN
        NAME_ASSUMS_TAC THEN
        USE_THEN "H1" (fun th -> USE_THEN "H0" (fun th' -> REWRITE_TAC [
            MATCH_MP (MATCH_MP modified_n'th th') (MATCH_MP ne_sym (MATCH_MP l_ne (MATCH_MP id2i_l th)))
        ]));

        NAME_ASSUMS_TAC THEN
        USE_THEN "H2" (fun th1 -> 
        USE_THEN "H1" (fun th2 -> 
        USE_THEN "H0" (fun th3 -> MATCH_ACCEPT_TAC (
            MATCH_MP (MATCH_MP th1 (MATCH_MP suc_l_ th2)) th3
        ))))
    ]
);;

let far_split = prove (
    `! (l' : (num#num)list) (l : (num#num)list) 
        (filter : num -> bool) (i : num) (lo : num) (hi : num).
    (start <= lo) ==> (lo <= start + i) ==> (start + i < hi) ==> (i < LENGTH l) ==>
    (ifilter l (start + i) = T) ==> (nth l i = nth l' ((start + i) - lo)) ==> (
        free_area_repr (ifilter l) lo hi l' = (
        free_area_repr (ifilter (modified l i (0, NO_ORDER))) lo hi l' SEPCONJ
        store_zero_array (id2vi (start + i)) (PTR_SIZE * 2) (PAGE_SIZE * (2 EXP (ORD (nth l i)))) (PAGE_SIZE * (2 EXP (ORD (nth l i))) - PAGE_SIZE * 2)))`,
    LIST_INDUCT_TAC THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    ONCE_REWRITE_TAC [FREE_AREA_REPR_DEF] THENL
    [
        NAME_ASSUMS_TAC THEN
        USE_THEN "H4" (fun th -> USE_THEN "H3" (fun th' -> REWRITE_TAC [
            MATCH_MP l_ne (MATCH_MP (MATCH_MP le_l_l th) th')
        ])) THEN
        REWRITE_TAC [sepfalse_and; sepfalse_conj];

        ASM_CASES_TAC `(lo : num) = start + i` THENL
        [
            ASM_REWRITE_TAC [] THEN
            REWRITE_TAC [IFILTER_DEF; id2i_inv] THEN
            NAME_ASSUMS_TAC THEN
            USE_THEN "H3" (fun th -> REWRITE_TAC [MATCH_MP modified_nth th]) THEN
            REWRITE_TAC [ord_open; minusaa; NTH_DEF; sepconj_emp1] THEN
            MATCH_MP_TAC sepconj_mono' THEN
            SIMP_TAC [] THEN
            USE_THEN "H3" (fun th -> MATCH_ACCEPT_TAC (
                MATCH_MP (MATCH_MP far_lemma (SPEC `(start + i) : num` l_suc)) th
            ));

            REWRITE_TAC [IFILTER_DEF; id2i_inv] THEN
            NAME_ASSUMS_TAC THEN
            USE_THEN "H6" (fun th -> FIRST_ASSUM (fun th' -> ASSUME_TAC (
                MATCH_MP (MATCH_MP id2i_ne th) th'
            ))) THEN
            USE_THEN "H3" (fun th -> FIRST_ASSUM (fun th' -> REWRITE_TAC [
                MATCH_MP (MATCH_MP modified_n'th th) th'
            ])) THEN
            REWRITE_TAC [sepconj_assoc2] THEN
            MATCH_MP_TAC sepconj_mono THEN
            SIMP_TAC [] THEN
            USE_THEN "H5" (fun th -> USE_THEN "H0" (fun th' -> ASSUME_TAC (
                MATCH_MP (MATCH_MP le_ne th) th'
            ))) THEN
            USE_THEN "H1" (fun th -> FIRST_ASSUM (fun th' -> ASSUME_TAC (
                REWRITE_RULE [MATCH_MP minus_l th'; NTH_DEF] th
            ))) THEN
            USE_THEN "H7" (fun th1 ->
            USE_THEN "H6" (fun th2 ->
            USE_THEN "H4" (fun th4 ->
            USE_THEN "H3" (fun th5 ->
            USE_THEN "H2" (fun th6 ->
            POP_ASSUM (fun th7 ->
            POP_ASSUM (fun th3 -> MATCH_ACCEPT_TAC (
                MATCH_MP (MATCH_MP (MATCH_MP (MATCH_MP (MATCH_MP (MATCH_MP th1 (MATCH_MP suc_le__ th2)) th3) th4) th5) th6) th7
            ))))))))
        ]
    ]
);;

let far_merge = prove (
    `! (l' : (num#num)list) (l : (num#num)list) 
        (filter : num -> bool) (i : num) (lo : num) (hi : num) (order : num).
    (start <= lo) ==> (lo <= start + i) ==> (start + i < hi) ==> (i < LENGTH l) ==>
    (ifilter l (start + i) = F) ==> ~(order = NO_ORDER) ==> (nth l i = nth l' ((start + i) - lo)) ==> (
        (free_area_repr (ifilter l) lo hi l' SEPCONJ
        store_zero_array (id2vi (start + i)) (PTR_SIZE * 2) (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order) - PAGE_SIZE * 2)) = 
        free_area_repr (ifilter (modified l i (0, order))) lo hi (modified l' ((start + i) - lo) (0, order)))`,
    LIST_INDUCT_TAC THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    REWRITE_TAC [MODIFIED_DEF] THEN
    ONCE_REWRITE_TAC [FREE_AREA_REPR_DEF] THENL
    [
        NAME_ASSUMS_TAC THEN
        USE_THEN "H5" (fun th -> USE_THEN "H4" (fun th' -> REWRITE_TAC [
            MATCH_MP l_ne (MATCH_MP (MATCH_MP le_l_l th) th')
        ])) THEN
        REWRITE_TAC [sepfalse_and; sepfalse_conj];

        ASM_CASES_TAC `(lo : num) = start + i` THENL
        [
            ASM_REWRITE_TAC [] THEN
            REWRITE_TAC [minusaa; MODIFIED_DEF; FREE_AREA_REPR_DEF] THEN
            REWRITE_TAC [IFILTER_DEF; id2i_inv] THEN
            NAME_ASSUMS_TAC THEN
            USE_THEN "H4" (fun th -> REWRITE_TAC [MATCH_MP modified_nth th]) THEN
            REWRITE_TAC [ref_open; ord_open; minusaa; NTH_DEF; sepconj_emp1] THEN
            ASM_REWRITE_TAC [] THEN
            MATCH_MP_TAC sepconj_mono' THEN
            SIMP_TAC [] THEN
            USE_THEN "H4" (fun th -> MATCH_ACCEPT_TAC (
                MATCH_MP (MATCH_MP far_lemma (SPEC `(start + i) : num` l_suc)) th
            ));

            NAME_ASSUMS_TAC THEN
            USE_THEN "H6" (fun th -> FIRST_ASSUM (fun th' -> REWRITE_TAC [
                MATCH_MP minus_l (MATCH_MP (MATCH_MP le_ne th) th')
            ])) THEN
            REWRITE_TAC [MODIFIED_DEF; FREE_AREA_REPR_DEF] THEN
            REWRITE_TAC [IFILTER_DEF; id2i_inv] THEN
            USE_THEN "H7" (fun th -> FIRST_ASSUM (fun th' -> ASSUME_TAC (
                MATCH_MP (MATCH_MP id2i_ne th) th'
            ))) THEN
            USE_THEN "H4" (fun th -> FIRST_ASSUM (fun th' -> REWRITE_TAC [
                MATCH_MP (MATCH_MP modified_n'th th) th'
            ])) THEN
            REWRITE_TAC [sepconj_assoc2] THEN
            MATCH_MP_TAC sepconj_mono THEN
            SIMP_TAC [] THEN
            USE_THEN "H6" (fun th -> USE_THEN "H0" (fun th' -> ASSUME_TAC (
                MATCH_MP (MATCH_MP le_ne th) th'
            ))) THEN
            USE_THEN "H1" (fun th -> FIRST_ASSUM (fun th' -> ASSUME_TAC (
                REWRITE_RULE [MATCH_MP minus_l th'; NTH_DEF] th
            ))) THEN
            USE_THEN "H8" (fun th1 ->
            USE_THEN "H7" (fun th2 ->
            USE_THEN "H5" (fun th4 ->
            USE_THEN "H4" (fun th5 ->
            USE_THEN "H3" (fun th6 ->
            USE_THEN "H2" (fun th7 ->
            POP_ASSUM (fun th8 ->
            POP_ASSUM (fun th3 -> MATCH_ACCEPT_TAC (
                MATCH_MP (MATCH_MP (MATCH_MP (MATCH_MP (MATCH_MP (MATCH_MP (MATCH_MP th1 (MATCH_MP suc_le__ th2)) th3) th4) th5) th6) th7) th8
            )))))))))
        ]
    ]
);;

let break_array_sepconj = prove (
    `! (P : B -> num -> num -> num -> HPROP) (ONE : B -> num -> HPROP).
    ((! (arg1 : B) (lo : num) (hi : num). P arg1 lo hi 0 = (PURE (lo = hi) SEPAND EMP)) /\
    (! (arg1 : B) (lo : num) (hi : num) (n : num). P arg1 lo hi (SUC n) = ((ONE arg1 lo) SEPCONJ (P arg1 (SUC lo) hi n)))) ==>
    (! (n : num) (i : num) (arg1 : B) (hi : num).
        (i <= n) ==> (n <= hi) ==>
        P arg1 (hi - n) hi n = (P arg1 (hi - n) (hi - n + i) i SEPCONJ P arg1 (hi - n + i) hi (n - i)))`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN INDUCT_TAC THENL
    [
        ASM_REWRITE_TAC [plus0; minus0] THEN
        ASM_REWRITE_TAC [pure_t_sepand; emp_conj];

        ARITH_TAC;

        ASM_REWRITE_TAC [plus0; minus0] THEN
        ASM_REWRITE_TAC [pure_t_sepand; emp_conj];

        REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
        ASM_REWRITE_TAC [] THEN
        FIRST_ASSUM (fun th -> REWRITE_TAC [
            MATCH_MP sucoff th;
            MATCH_MP sucoff2 th;
            sucoff4
        ]) THEN
        REWRITE_TAC [sepconj_assoc2] THEN
        MATCH_MP_TAC sepconj_mono THEN
        SIMP_TAC [] THEN
        NAME_ASSUMS_TAC THEN
        POP_ASSUM (fun th -> POP_ASSUM (fun th' -> USE_THEN "H3" (fun th'' -> MATCH_ACCEPT_TAC (
            MATCH_MP (MATCH_MP th'' (MATCH_MP suc_le th')) (MATCH_MP suc_le_ th)
        ))))
    ]
);;

let store_array_addr = prove (
    `! (n : num) (i : num) (lo : num) (hi : num) (addr : PTR).
    store_zero_array (addr + &i) lo hi n =
    store_zero_array addr (lo + i) (hi + i) n`,
    INDUCT_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC [STORE_ZERO_ARRAY_DEF] THENL
    [
        REWRITE_TAC [plus_mono];
        ASM_REWRITE_TAC [plus_assoc1; suc_plus]
    ]
);;

let sza_merge = prove (
    `! (n : num) (pid : num).
    offset <= pid * PAGE_SIZE ==>
    (store_zero_array (id2vi pid) 0 (PAGE_SIZE * n) (PAGE_SIZE * n) SEPCONJ
    store_zero_array (id2vi (pid + n)) 0 (PAGE_SIZE * n) (PAGE_SIZE * n)) =
    store_zero_array (id2vi pid) 0 (PAGE_SIZE * (n * 2)) (PAGE_SIZE * (n * 2))`,
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    FIRST_ASSUM (fun th -> REWRITE_TAC [MATCH_MP id2vi_plus th]) THEN
    REWRITE_TAC [store_array_addr] THEN
    ASSUME_TAC (MATCH_MP (MATCH_MP (IMATCH_MP break_array_sepconj STORE_ZERO_ARRAY_DEF) (SPEC `PAGE_SIZE * n` le2)) (SPEC `(PAGE_SIZE * n) * 2` le1)) THEN
    POP_ASSUM (fun th -> ASSUME_TAC (
        REWRITE_RULE [minusaa; multi_minus1; multi_assoc1; plus0_] th
    )) THEN
    ASM_REWRITE_TAC [plus0_; multi2; multi_assoc1]
);;

(* 
	DATA_AT_PTR (id2vi (&bid), &0) **
	DATA_AT_PTR (id2vi (&bid) + &PTR_SIZE, &0) **
	store_zero_array (id2vi (&bid)) (PTR_SIZE * 2) (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order) - PAGE_SIZE * 2) =
	store_zero_array (id2vi (&bid)) 0 (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order))
*)