#include "proof-user.h"
#include "proof-conv.h"
#include "def.h"
#include "drule.h"
#include "lemma.h"
#include "interface.h"
#include <stdio.h>

term __state;
thm __transform;

void test_lemma()
{
    printf("%s\n\n", string_of_thm(break_list_sepconj()));
    printf("%s\n\n", string_of_thm(modified_nth()));
    printf("%s\n\n", string_of_thm(modified_mth()));
    printf("%s\n\n", string_of_thm(modified_taken()));
    printf("%s\n\n", string_of_thm(modified_restn()));
    printf("%s\n\n", string_of_thm(modified_len()));
    printf("%s\n\n", string_of_thm(filter_inv()));
    printf("%s\n\n", string_of_thm(far_inv()));
    printf("%s\n\n", string_of_thm(dn_inv()));
    printf("%s\n\n", string_of_thm(dh_inv()));
    printf("%s\n\n", string_of_thm(far_lemma()));
    printf("%s\n\n", string_of_thm(far_split()));
    printf("%s\n\n", string_of_thm(far_merge()));
    printf("%s\n\n", string_of_thm(store_array_addr()));
    printf("%s\n\n", string_of_thm(sza_merge()));
}

void proof1()
{
    __state = parse_term("\n  data_at(&\"buddy\", Tptr, &0) **\n  data_at(&\"pool\", Tptr, pool_pre) **\n  data_at(&\"pg\", Tptr, pg_pre) **\n  data_at(&\"__hyp_vmemmap\", Tptr, vmemmap) **\n  hfact (pure_const) **\n  hfact (dlist_node pool_pre (ifilter l) l dl hl start end dl) **\n  hfact (dlist_head pool_pre l dl 0 max_order hl) **\n  hfact (LENGTH l = len) **\n  hfact (LENGTH dl = len) **\n  hfact (LENGTH hl = max_order) **\n  hfact (pg_pre = vmemmap + &(pi * 4)) **\n  hfact (pi < len) **\n  hfact (~(porder = NO_ORDER)) **\n  hfact (pref > 0) **\n  hfact (pref = REF (nth l pi)) **\n  hfact (porder = ORD (nth l pi)) **\n  (pool_const pool_pre) **\n  (dlist_head_repr pool_pre 0 max_order hl) **\n  (free_area_repr (ifilter l) start end l) **\n  (free_area_head_repr (ifilter l) start end dl) **\n  (store_pageinfo_array vmemmap start (i2id pi) (take l pi)) **\n   hfact (~(porder = NO_ORDER) ==> (porder < max_order) && ((2 EXP porder) divides (i2id pi))) **\n   hfact (pref < REF_LIM) **\n   (data_at (vmemmap + &(pi * 4), Tushort, &0)) **\n   (data_at ((vmemmap + &(pi * 4)) + &2, Tuchar, &porder)) **\n   (undef_data_at ((vmemmap + &(pi * 4)) + &3, Tuchar)) **\n  (store_pageinfo_array vmemmap (SUC (i2id pi)) end (rest l (SUC pi))) **\n  (store_undef_array (i2vi pi) 0 (PAGE_SIZE * (2 EXP porder)) (PAGE_SIZE * (2 EXP porder)))\n    ");
  
    term fact = parse_term("pg_pre = vmemmap + &((pi : num) * 4)");
    thm data_at_pg_pre2order = use_fact_symm_rewrite(
        fact, parse_term("data_at ((vmemmap + &(pi * 4)) + &2, Tuchar, &(porder : num))"));
    thm pool_const_unfold = unfold(parse_term("pool_const pool_pre"), POOL_CONST_DEF);
    thm trans = create_trans_auto((term[]){NULL}, (term[]){fact, NULL}, (thm[]){NULL}, (thm[]){pool_const_unfold, data_at_pg_pre2order, NULL});

    __transform = which_implies(__state, trans);
    // printf("%s\n\n", string_of_thm(__transform));

    compare_hprop(__state, dest_bin_fst_comb(concl(__transform)));
    __state = parse_term("\n  data_at(&\"buddy\", Tptr, &0) **\n  data_at(&\"pool\", Tptr, pool_pre) **\n  data_at(&\"pg\", Tptr, pg_pre) **\n  data_at(&\"__hyp_vmemmap\", Tptr, vmemmap) **\n  hfact (pure_const) **\n  hfact (dlist_node pool_pre (ifilter l) l dl hl start end dl) **\n  hfact (dlist_head pool_pre l dl 0 max_order hl) **\n  hfact (LENGTH l = len) **\n  hfact (LENGTH dl = len) **\n  hfact (LENGTH hl = max_order) **\n  hfact (pg_pre = vmemmap + &(pi * 4)) **\n  hfact (pi < len) **\n  hfact (~(porder = NO_ORDER)) **\n  hfact (pref > 0) **\n  hfact (pref = REF (nth l pi)) **\n  hfact (porder = ORD (nth l pi)) **\n  data_at (pool_pre + &(LIST_HEAD_SIZE * MAX_ORDER), Tuint64, id2ph start) **\n        data_at (pool_pre + &(LIST_HEAD_SIZE * MAX_ORDER + 8), Tuint64, id2ph end) **\n        data_at (pool_pre + &(LIST_HEAD_SIZE * MAX_ORDER + 16), Tuchar, &max_order) **\n  (dlist_head_repr pool_pre 0 max_order hl) **\n  (free_area_repr (ifilter l) start end l) **\n  (free_area_head_repr (ifilter l) start end dl) **\n  (store_pageinfo_array vmemmap start (i2id pi) (take l pi)) **\n   hfact (~(porder = NO_ORDER) ==> (porder < max_order) && ((2 EXP porder) divides (i2id pi))) **\n   hfact (pref < REF_LIM) **\n   (data_at (vmemmap + &(pi * 4), Tushort, &0)) **\n   (data_at (pg_pre + &2, Tuchar, &porder)) **\n   (undef_data_at ((vmemmap + &(pi * 4)) + &3, Tuchar)) **\n  (store_pageinfo_array vmemmap (SUC (i2id pi)) end (rest l (SUC pi))) **\n  (store_undef_array (i2vi pi) 0 (PAGE_SIZE * (2 EXP porder)) (PAGE_SIZE * (2 EXP porder)))\n    ");
    compare_hprop(__state, dest_bin_snd_comb(concl(__transform)));
}

void proof2()
{
    __state = parse_term("\n  data_at(&\"max_order\", Tuchar, &max_order) **\n  data_at(&\"order\", Tuchar, &porder) **\n  data_at(&\"buddy\", Tptr, &0) **\n  data_at(&\"pool\", Tptr, pool_pre) **\n  data_at(&\"pg\", Tptr, pg_pre) **\n  data_at(&\"__hyp_vmemmap\", Tptr, vmemmap) **\n  hfact (pure_const) **\n  hfact (dlist_node pool_pre (ifilter l) l dl hl start end dl) **\n  hfact (dlist_head pool_pre l dl 0 max_order hl) **\n  hfact (LENGTH l = len) **\n  hfact (LENGTH dl = len) **\n  hfact (LENGTH hl = max_order) **\n  hfact (pg_pre = vmemmap + &(pi * 4)) **\n  hfact (pi < len) **\n  hfact (~(porder = NO_ORDER)) **\n  hfact (pref > 0) **\n  hfact (pref = REF (nth l pi)) **\n  hfact (porder = ORD (nth l pi)) **\n  data_at (pool_pre + &(LIST_HEAD_SIZE * MAX_ORDER), Tuint64, id2ph start) **\n        data_at (pool_pre + &(LIST_HEAD_SIZE * MAX_ORDER + 8), Tuint64, id2ph end) **\n        data_at (pool_pre + &(LIST_HEAD_SIZE * MAX_ORDER + 16), Tuchar, &max_order) **\n  (dlist_head_repr pool_pre 0 max_order hl) **\n  (free_area_repr (ifilter l) start end l) **\n  (free_area_head_repr (ifilter l) start end dl) **\n  (store_pageinfo_array vmemmap start (i2id pi) (take l pi)) **\n   hfact (~(porder = NO_ORDER) ==> (porder < max_order) && ((2 EXP porder) divides (i2id pi))) **\n   hfact (pref < REF_LIM) **\n   (data_at (vmemmap + &(pi * 4), Tushort, &0)) **\n   (data_at (pg_pre + &2, Tuchar, &255)) **\n   (undef_data_at ((vmemmap + &(pi * 4)) + &3, Tuchar)) **\n  (store_pageinfo_array vmemmap (SUC (i2id pi)) end (rest l (SUC pi))) **\n  (store_zero_array (i2vi pi) 0 (PAGE_SIZE * (2 EXP porder)) (PAGE_SIZE * (2 EXP porder)))\n    ");
  
    term fact = parse_term("pg_pre = vmemmap + &(pi * 4)");
    thm data_at_pg_pre2order = use_fact_rewrite(
        fact, parse_term("data_at (pg_pre + &2, Tuchar, &255)")); /////////////////////////////
    data_at_pg_pre2order = rewrite_after_ent(symm(NO_ORDER_DEF), data_at_pg_pre2order);
	thm pool_const_fold = fold(parse_term("pool_const pool_pre"), POOL_CONST_DEF);
    thm trans = create_trans_auto((term[]){NULL}, (term[]){fact, NULL}, (thm[]){NULL}, (thm[]){pool_const_fold, data_at_pg_pre2order, NULL});
    
    __transform = which_implies(__state, trans);
    // printf("%s\n\n", string_of_thm(__transform));

    compare_hprop(__state, dest_bin_fst_comb(concl(__transform)));
    __state = parse_term("\n  data_at(&\"max_order\", Tuchar, &max_order) **\n  data_at(&\"order\", Tuchar, &porder) **\n  data_at(&\"buddy\", Tptr, &0) **\n  data_at(&\"pool\", Tptr, pool_pre) **\n  data_at(&\"pg\", Tptr, pg_pre) **\n  data_at(&\"__hyp_vmemmap\", Tptr, vmemmap) **\n  hfact (pure_const) **\n  hfact (dlist_node pool_pre (ifilter l) l dl hl start end dl) **\n  hfact (dlist_head pool_pre l dl 0 max_order hl) **\n  hfact (LENGTH l = len) **\n  hfact (LENGTH dl = len) **\n  hfact (LENGTH hl = max_order) **\n  hfact (pg_pre = vmemmap + &(pi * 4)) **\n  hfact (pi < len) **\n  hfact (~(porder = NO_ORDER)) **\n  hfact (pref > 0) **\n  hfact (pref = REF (nth l pi)) **\n  hfact (porder = ORD (nth l pi)) **\n  (pool_const pool_pre) **\n  (dlist_head_repr pool_pre 0 max_order hl) **\n  (free_area_repr (ifilter l) start end l) **\n  (free_area_head_repr (ifilter l) start end dl) **\n  (store_pageinfo_array vmemmap start (i2id pi) (take l pi)) **\n   hfact (~(porder = NO_ORDER) ==> (porder < max_order) && ((2 EXP porder) divides (i2id pi))) **\n   hfact (pref < REF_LIM) **\n   (data_at (vmemmap + &(pi * 4), Tushort, &0)) **\n   (data_at ((vmemmap + &(pi * 4)) + &2, Tuchar, &NO_ORDER)) **\n   (undef_data_at ((vmemmap + &(pi * 4)) + &3, Tuchar)) **\n  (store_pageinfo_array vmemmap (SUC (i2id pi)) end (rest l (SUC pi))) **\n  (store_zero_array (i2vi pi) 0 (PAGE_SIZE * (2 EXP porder)) (PAGE_SIZE * (2 EXP porder)))\n    ");
    compare_hprop(__state, dest_bin_snd_comb(concl(__transform)));
}

void proof3()
{
    __state = parse_term("\n  data_at(&\"max_order\", Tuchar, &max_order) **\n  data_at(&\"order\", Tuchar, &porder) **\n  data_at(&\"buddy\", Tptr, &0) **\n  data_at(&\"pool\", Tptr, pool_pre) **\n  data_at(&\"pg\", Tptr, pg_pre) **\n  data_at(&\"__hyp_vmemmap\", Tptr, vmemmap) **\n  hfact (pure_const) **\n  hfact (dlist_node pool_pre (ifilter l) l dl hl start end dl) **\n  hfact (dlist_head pool_pre l dl 0 max_order hl) **\n  hfact (LENGTH l = len) **\n  hfact (LENGTH dl = len) **\n  hfact (LENGTH hl = max_order) **\n  hfact (pg_pre = vmemmap + &(pi * 4)) **\n  hfact (pi < len) **\n  hfact (~(porder = NO_ORDER)) **\n  hfact (pref > 0) **\n  hfact (pref = REF (nth l pi)) **\n  hfact (porder = ORD (nth l pi)) **\n  (pool_const pool_pre) **\n  (dlist_head_repr pool_pre 0 max_order hl) **\n  (free_area_repr (ifilter l) start end l) **\n  (free_area_head_repr (ifilter l) start end dl) **\n  (store_pageinfo_array vmemmap start (i2id pi) (take l pi)) **\n   hfact (~(porder = NO_ORDER) ==> (porder < max_order) && ((2 EXP porder) divides (i2id pi))) **\n   hfact (pref < REF_LIM) **\n   (data_at (vmemmap + &(pi * 4), Tushort, &0)) **\n   (data_at ((vmemmap + &(pi * 4)) + &2, Tuchar, &NO_ORDER)) **\n   (undef_data_at ((vmemmap + &(pi * 4)) + &3, Tuchar)) **\n  (store_pageinfo_array vmemmap (SUC (i2id pi)) end (rest l (SUC pi))) **\n  (store_zero_array (i2vi pi) 0 (PAGE_SIZE * (2 EXP porder)) (PAGE_SIZE * (2 EXP porder)))\n    ");
  
    thm tmpth;

    term v = parse_term("(0, NO_ORDER) : num#num");
    term l = parse_term("l : (num#num)list");
    term pi = parse_term("pi : num");
    term ifilterl = parse_term("ifilter l");
// inv_l = modified l pi (0, NO_ORDER)

// pi < LENGTH l
    term fact1 = parse_term("pi < len : num");
    term fact_len = parse_term("LENGTH (l : (num#num)list) = len");
    thm pi_l_len = rewrite_rule(symm(assume(fact_len)), assume(fact1));
// ~free_head (nth l pi)
    term goal_fh1 = parse_term("~free_head (nth l pi)");
    term fact2 = parse_term("pref = REF (nth l pi)");
    term fact3 = parse_term("pref > 0");
    thm ar1 = arith_rule(parse_term("! a : num. a > 0 ==> ~(a = 0)"));
    thm thl1[] = {FREE_HEAD_DEF, symm(assume(fact2)), mp(ar1, assume(fact3)), NULL};
    thm fh1 = simp(rewrite_after_term_list(thl1, goal_fh1));
// ~(ifilter l (i2id pi))
    term goal_ifl = parse_term("~((ifilter l) (i2id pi))");
    thm thl2[] = {IFILTER_DEF, i2id2i(), fh1, NULL};
    thm ifl = simp(rewrite_after_term_list(thl2, goal_ifl));
// free_head (0,NO_ORDER) <=> free_head (nth l pi)
    term goal_fh2 = parse_term("free_head (0, NO_ORDER) <=> free_head (nth l pi)");
    thm thl3[] = {fh1, FREE_HEAD_DEF, ORD_DEF, NULL};
    thm fh2 = simp(rewrite_after_term_list(thl3, goal_fh2));
// ifilter l == ifilter inv_l
    thm ifl_inv = mp(mp(filter_inv(), pi_l_len), fh2);
// dlist_node pool_pre (ifilter inv_l) inv_l dl hl start end dl
    term fact_dn = parse_term("dlist_node pool_pre (ifilter l) l dl hl start end dl");
    tmpth = mp(mp(mp(dn_inv(), pi_l_len), fh1), assume(fact_dn));
    thm dn = once_rewrite_rule(ifl_inv, spec(v, tmpth));
// dlist_head pool_pre inv_l dl 0 max_order hl
    term fact_dh = parse_term("dlist_head pool_pre l dl 0 max_order hl");
    tmpth = mp(mp(mp(dh_inv(), pi_l_len), fh1), assume(fact_dh));
    thm dh = spec(v, tmpth);
// LENGTH inv_l == len
    tmpth = spec(v, spec(pi, spec(l, modified_len())));
    thm len = trans(tmpth, assume(fact_len));
// REF (nth inv_l pi) == 0
    term goal_ref = parse_term("REF (nth (modified l pi (0,NO_ORDER)) pi) = 0");
    thm thl4[] = {mp(modified_nth(), pi_l_len), REF_DEF, NULL};
    thm ref = simp(rewrite_after_term_list(thl4, goal_ref));
// ORD (nth inv_l pi) == NO_ORDER
    term goal_ord = parse_term("ORD (nth (modified l pi (0,NO_ORDER)) pi) = NO_ORDER");
    thm thl5[] = {mp(modified_nth(), pi_l_len), ORD_DEF, NULL};
    thm ord = simp(rewrite_after_term_list(thl5, goal_ord));
// pfact
    term pfact = parse_term("~(porder = NO_ORDER) ==> (porder < max_order) && ((2 EXP porder) divides (i2id pi))");
    term fact4 = parse_term("~(porder = NO_ORDER)");
    tmpth = mp(assume(pfact), assume(fact4));
    thm pf1 = conjunct1(tmpth);
    thm pf2 = conjunct2(tmpth);

// free_area_repr (ifilter l) start end l |--
// free_area_repr (ifilter inv_l) start end inv_l
    term fact_pc = parse_term("pure_const");
    thm pc = rewrite_rule(PURE_CONST_DEF, assume(fact_pc));
    thm pc1 = conjunct1(pc);
    thm ar2 = arith_rule(parse_term("start < end ==> start <= end"));
    tmpth = mp(mp(far_inv(), mp(ar2, pc1)), LEN_DEF);
    tmpth = mp(mp(tmpth, assume(fact1)), symm(assume(fact_len)));
    tmpth = mp(spec(ifilterl, spec(v, tmpth)), ifl);
    tmpth = rewrite_after(ifl_inv, tmpth);
    thm far = eq2ent(tmpth);
// free_area_head_repr (ifilter l) start end dl |--
// free_area_head_repr (ifilter inv_l) start end dl
    term hp_fahr = parse_term("free_area_head_repr (ifilter l) start end dl");
    tmpth = once_rewrite(ifl_inv, hp_fahr);
    thm fahr = eq2ent(tmpth);
// store_pageinfo_array
    term spa_obj = parse_term("store_pageinfo_array vmemmap start end (modified l pi (0,NO_ORDER))");
    tmpth = break_spa_at_i(spa_obj, assume(fact1), symm(len), pc1);
    thm nth = mp(modified_nth(), pi_l_len);
    thm taken = mp(modified_taken(), pi_l_len);
    thm restn = mp(modified_restn(), pi_l_len);
    thm ar7 = arith_rule(parse_term("0 < 65536"));
    thm thl6[] = {nth, taken, restn, REF_DEF, ORD_DEF, REF_LIM_DEF, ar7, hfact_true, hsep_assoc, NULL};
    tmpth = rewrite_after_list(thl6, tmpth);
    thm spa = eq2ent(symm(tmpth));

    term cfactl[] = {fact_dn, fact_dh, fact_len, pfact, NULL};
    term kfactl[] = {fact1, fact2, fact3, fact4, fact_pc, NULL};
    thm pthl[] = {dn, dh, len, ref, ord, pf1, pf2, NULL};
    thm hthl[] = {far, fahr, spa, NULL};
    thm part_ent = create_trans_auto(cfactl, kfactl, pthl, hthl);
    tmpth = which_implies(__state, part_ent);
    term ifact1 = parse_term("porder == ORD (nth l pi)");
    term ifact2 = parse_term("pref < REF_LIM");
    term ifact3 = parse_term("pref > 0");
    term ifact4 = parse_term("pref == REF (nth l pi)");
    term ifactl[] = {ifact1, ifact2, ifact3, ifact4, NULL};
    tmpth = give_up_facts(ifactl, tmpth);
    __transform = tmpth;
    // printf("%s\n\n", string_of_thm(__transform));

    compare_hprop(__state, dest_bin_fst_comb(concl(__transform)));
    __state = parse_term("\n  data_at(&\"max_order\", Tuchar, &max_order) **\n  data_at(&\"order\", Tuchar, &porder) **\n  data_at(&\"buddy\", Tptr, &0) **\n  data_at(&\"pool\", Tptr, pool_pre) **\n  data_at(&\"pg\", Tptr, pg_pre) **\n  data_at(&\"__hyp_vmemmap\", Tptr, vmemmap) **\n  hfact (pure_const) **\n  hfact (dlist_node pool_pre (ifilter (modified l pi (0, NO_ORDER))) (modified l pi (0, NO_ORDER)) dl hl start end dl) **\n  hfact (dlist_head pool_pre (modified l pi (0, NO_ORDER)) dl 0 max_order hl) **\n  hfact (LENGTH (modified l pi (0, NO_ORDER)) = len) **\n  hfact (LENGTH dl = len) **\n  hfact (LENGTH hl = max_order) **\n  hfact (pg_pre = vmemmap + &(pi * 4)) **\n  hfact (pi < len) **\n  hfact (~(porder = NO_ORDER)) **\n     hfact (porder < max_order) **\n     hfact (2 EXP porder divides i2id pi) **\n  hfact (ORD (nth (modified l pi (0, NO_ORDER)) pi) == NO_ORDER) **\n  hfact (REF (nth (modified l pi (0, NO_ORDER)) pi) == 0) **\n  (pool_const pool_pre) **\n  (dlist_head_repr pool_pre 0 max_order hl) **\n  (free_area_repr (ifilter (modified l pi (0, NO_ORDER))) start end (modified l pi (0, NO_ORDER))) **\n  (free_area_head_repr (ifilter (modified l pi (0, NO_ORDER))) start end dl) **\n  (store_pageinfo_array vmemmap start end (modified l pi (0, NO_ORDER))) **\n  (store_zero_array (i2vi pi) 0 (PAGE_SIZE * (2 EXP porder)) (PAGE_SIZE * (2 EXP porder)))\n    ");
    compare_hprop(__state, dest_bin_snd_comb(concl(__transform)));
}

void proof4()
{
    __state = parse_term("\n exists buddy_v bi.\n  hfact ((buddy_v = &0) ||\n   ~(bi = pi) &&\n   (buddy_v = vmemmap + &(bi * 4)) &&\n   (bi < len) &&\n   (REF (nth (modified l pi (0, NO_ORDER)) bi) = 0) &&\n   (ORD (nth (modified l pi (0, NO_ORDER)) bi) = porder) &&\n   ((2 EXP (SUC porder)) divides (i2id (MIN pi bi))) &&\n   (abs (&pi - &bi) = &(2 EXP porder))) **\n  data_at(&\"max_order\", Tuchar, &max_order) **\n  data_at(&\"order\", Tuchar, &porder) **\n  data_at(&\"buddy\", Tptr, buddy_v) **\n  data_at(&\"pool\", Tptr, pool_pre) **\n  data_at(&\"pg\", Tptr, pg_pre) **\n  data_at(&\"__hyp_vmemmap\", Tptr, vmemmap) **\n  hfact (pure_const) **\n  hfact (dlist_node pool_pre (ifilter (modified l pi (0, NO_ORDER))) (modified l pi (0, NO_ORDER)) dl hl start end dl) **\n  hfact (dlist_head pool_pre (modified l pi (0, NO_ORDER)) dl 0 max_order hl) **\n  hfact (LENGTH (modified l pi (0, NO_ORDER)) = len) **\n  hfact (LENGTH dl = len) **\n  hfact (LENGTH hl = max_order) **\n  hfact (pg_pre = vmemmap + &(pi * 4)) **\n  hfact (pi < len) **\n  hfact (~(porder = NO_ORDER)) **\n     hfact (porder < max_order) **\n     hfact (2 EXP porder divides i2id pi) **\n  hfact (ORD (nth (modified l pi (0, NO_ORDER)) pi) == NO_ORDER) **\n  hfact (REF (nth (modified l pi (0, NO_ORDER)) pi) == 0) **\n  (pool_const pool_pre) **\n  (dlist_head_repr pool_pre 0 max_order hl) **\n  (free_area_repr (ifilter (modified l pi (0, NO_ORDER))) start end (modified l pi (0, NO_ORDER))) **\n  (free_area_head_repr (ifilter (modified l pi (0, NO_ORDER))) start end dl) **\n  (store_pageinfo_array vmemmap start end (modified l pi (0, NO_ORDER))) **\n  (store_zero_array (i2vi pi) 0 (PAGE_SIZE * (2 EXP porder)) (PAGE_SIZE * (2 EXP porder)))\n    ");
  
    thm tmpth;
    tmpth = spec(__state, hentail_refl);
    tmpth = hexists_intro_auto(tmpth, parse_term("modified l pi (0,NO_ORDER) = inv_l"));
    tmpth = hexists_intro_auto(tmpth, parse_term("dl = inv_dl : (addr#addr)list"));
    tmpth = hexists_intro_auto(tmpth, parse_term("hl = inv_hl : (addr#addr)list"));
    tmpth = hexists_intro_auto(tmpth, parse_term("pi = i : num"));
    tmpth = hexists_intro_auto(tmpth, parse_term("porder = ord : num"));
    tmpth = hexists_intro_auto(tmpth, parse_term("pg_pre = pg_v : addr"));
    __transform = tmpth;

    // printf("%s\n\n", string_of_thm(__transform));
    compare_hprop(__state, dest_bin_fst_comb(concl(__transform)));
    __state = parse_term("\n exists buddy_v bi inv_l inv_dl inv_hl i ord pg_v.\n  hfact ((buddy_v = &0) ||\n   ~(bi = i) &&\n   (buddy_v = vmemmap + &(bi * 4)) &&\n   (bi < len) &&\n   (REF (nth inv_l bi) = 0) &&\n   (ORD (nth inv_l bi) = ord) &&\n   ((2 EXP (SUC ord)) divides (i2id (MIN i bi))) &&\n   (abs (&i - &bi) = &(2 EXP ord))) **\n  data_at(&\"max_order\", Tuchar, &max_order) **\n  data_at(&\"order\", Tuchar, &ord) **\n  data_at(&\"buddy\", Tptr, buddy_v) **\n  data_at(&\"pool\", Tptr, pool_pre) **\n  data_at(&\"pg\", Tptr, pg_v) **\n  data_at(&\"__hyp_vmemmap\", Tptr, vmemmap) **\n  hfact (pure_const) **\n  hfact (dlist_node pool_pre (ifilter inv_l) inv_l inv_dl inv_hl start end inv_dl) **\n  hfact (dlist_head pool_pre inv_l inv_dl 0 max_order inv_hl) **\n  hfact (LENGTH inv_l = len) **\n  hfact (LENGTH inv_dl = len) **\n  hfact (LENGTH inv_hl = max_order) **\n  hfact (pg_v = vmemmap + &(i * 4)) **\n  hfact (i < len) **\n  hfact (~(ord = NO_ORDER)) **\n  hfact (ord < max_order) **\n  hfact ((2 EXP ord) divides (i2id i)) **\n  hfact (ORD (nth inv_l i) = NO_ORDER) **\n  hfact (REF (nth inv_l i) = 0) **\n  (pool_const pool_pre) **\n  (dlist_head_repr pool_pre 0 max_order inv_hl) **\n  (free_area_repr (ifilter inv_l) start end inv_l) **\n  (free_area_head_repr (ifilter inv_l) start end inv_dl) **\n  (store_pageinfo_array vmemmap start end inv_l) **\n  (store_zero_array (i2vi i) 0 (PAGE_SIZE * (2 EXP ord)) (PAGE_SIZE * (2 EXP ord)))\n    ");
    compare_hprop(__state, dest_bin_snd_comb(concl(__transform)));
}

void proof5()
{
    __state = parse_term("\n  exists new_l new_dl new_hl buddy_v bi inv_l (inv_dl : (addr#addr)list) (inv_hl : (addr#addr)list) i ord pg_v.\n   hfact (new_l = modified inv_l bi (0, NO_ORDER)) **\n   hfact (LENGTH new_l = len) **\n   hfact (LENGTH new_dl = len) **\n   hfact (LENGTH new_hl = max_order) **\n   hfact (&ord + &1 < &max_order && ~(buddy_v = &0)) **\n   hfact ((buddy_v = &0) ||\n    ~(bi = i) &&\n    (buddy_v = vmemmap + &(bi * 4)) &&\n    (bi < len) &&\n    (REF (nth inv_l bi) = 0) &&\n    (ORD (nth inv_l bi) = ord) &&\n    ((2 EXP (SUC ord)) divides (i2id (MIN i bi))) &&\n    (abs (&i - &bi) = &(2 EXP ord))) **\n   data_at(i2vi bi, Tptr, &0) **\n   data_at(i2vi bi + &PTR_SIZE, Tptr, &0) **\n   data_at(&\"max_order\", Tuchar, &max_order) **\n   data_at(&\"order\", Tuchar, &ord) **\n   data_at(&\"buddy\", Tptr, buddy_v) **\n   data_at(&\"pool\", Tptr, pool_pre) **\n   data_at(&\"pg\", Tptr, pg_v) **\n   data_at(&\"__hyp_vmemmap\", Tptr, vmemmap) **\n   hfact (pure_const) **\n   hfact (dlist_node pool_pre (ifilter new_l) new_l new_dl new_hl start end new_dl) **\n   hfact (dlist_head pool_pre new_l new_dl 0 max_order new_hl) **\n   hfact (LENGTH inv_l = len) **\n   hfact (LENGTH inv_dl = len) **\n   hfact (LENGTH inv_hl = max_order) **\n   hfact (pg_v = vmemmap + &(i * 4)) **\n   hfact (i < len) **\n   hfact (~(ord = NO_ORDER)) **\n   hfact (ord < max_order) **\n   hfact ((2 EXP ord) divides (i2id i)) **\n   hfact (ORD (nth inv_l i) = NO_ORDER) **\n   hfact (REF (nth inv_l i) = 0) **\n   (pool_const pool_pre) **\n   (dlist_head_repr pool_pre 0 max_order new_hl) **\n   (free_area_repr (ifilter inv_l) start end inv_l) **\n   (free_area_head_repr (ifilter new_l) start end new_dl) **\n   (store_pageinfo_array vmemmap start end inv_l) **\n   (store_zero_array (i2vi i) 0 (PAGE_SIZE * (2 EXP ord)) (PAGE_SIZE * (2 EXP ord)))\n  ");
    
    term fact_inv = parse_term("&(ord : num) + &1 < &max_order && ~(buddy_v = &0)");
    term fact_buddy = parse_term(" \
        (buddy_v = &0) || \
        ~(bi = i) && \
        (buddy_v = vmemmap + &(bi * 4)) && \
        (bi < len) && \
        (REF (nth inv_l bi) = 0) && \
        (ORD (nth inv_l bi) = ord) && \
        ((2 EXP (SUC ord)) divides (i2id (MIN i bi))) && \
		(abs(&i - &bi) = &(2 EXP ord))");
    thm bfact[9];
    bfact[0] = conjunct1(assume(fact_inv));
    thm bfacts = rewrite_rule(conjunct2(assume(fact_inv)), assume(fact_buddy));
    for(int i = 1; i <= 7; i++)
        bfact[i] = conjunctn(bfacts, i);
    bfact[8] = NULL;

    term fact_len = parse_term("LENGTH (inv_l : (num#num)list) = len");
    term fact_pc = parse_term("pure_const");
    thm start_end = conjunct1(rewrite_rule(PURE_CONST_DEF, assume(fact_pc)));
    term spa_obj = parse_term("store_pageinfo_array vmemmap start end inv_l");
    thm split_eq = break_spa_at_i(spa_obj, bfact[3], symm(assume(fact_len)), start_end);
    thm data_at_buddy_v2order = rewrite(
        symm(bfact[2]), parse_term("data_at ((vmemmap + &(bi * 4)) + &2, Tuchar, &(porder : num))"));
    thm spa = eq2ent(rewrite_after_list((thm[]){data_at_buddy_v2order, bfact[4], bfact[5], NULL}, split_eq));

    thm trans = create_trans_auto(
        (term[]){fact_inv, fact_buddy, NULL}, 
        (term[]){fact_len, fact_pc, NULL},
        bfact, (thm[]){spa, NULL});
    __transform = which_implies(__state, trans);
    // printf("%s\n\n", string_of_thm(__transform));

    compare_hprop(__state, dest_bin_fst_comb(concl(__transform)));
    __state = parse_term("\n  exists new_l new_dl new_hl buddy_v bi inv_l (inv_dl : (addr#addr)list) (inv_hl : (addr#addr)list) i ord pg_v.\n   hfact (new_l = modified inv_l bi (0, NO_ORDER)) **\n   hfact (LENGTH new_l = len) **\n   hfact (LENGTH new_dl = len) **\n   hfact (LENGTH new_hl = max_order) **\n   hfact (&ord + &1 < &max_order) **\n   hfact (~(bi = i)) **\n   hfact (buddy_v = vmemmap + &(bi * 4)) **\n   hfact (bi < len) **\n   hfact (REF (nth inv_l bi) = 0) **\n   hfact (ORD (nth inv_l bi) = ord) **\n   hfact ((2 EXP (SUC ord)) divides (i2id (MIN i bi))) **\n   hfact (abs (&i - &bi) = &(2 EXP ord)) **\n   data_at(i2vi bi, Tptr, &0) **\n   data_at(i2vi bi + &PTR_SIZE, Tptr, &0) **\n   data_at(&\"max_order\", Tuchar, &max_order) **\n   data_at(&\"order\", Tuchar, &ord) **\n   data_at(&\"buddy\", Tptr, buddy_v) **\n   data_at(&\"pool\", Tptr, pool_pre) **\n   data_at(&\"pg\", Tptr, pg_v) **\n   data_at(&\"__hyp_vmemmap\", Tptr, vmemmap) **\n   hfact (pure_const) **\n   hfact (dlist_node pool_pre (ifilter new_l) new_l new_dl new_hl start end new_dl) **\n   hfact (dlist_head pool_pre new_l new_dl 0 max_order new_hl) **\n   hfact (LENGTH inv_l = len) **\n   hfact (LENGTH inv_dl = len) **\n   hfact (LENGTH inv_hl = max_order) **\n   hfact (pg_v = vmemmap + &(i * 4)) **\n   hfact (i < len) **\n   hfact (~(ord = NO_ORDER)) **\n   hfact (ord < max_order) **\n   hfact ((2 EXP ord) divides (i2id i)) **\n   hfact (ORD (nth inv_l i) = NO_ORDER) **\n   hfact (REF (nth inv_l i) = 0) **\n   (pool_const pool_pre) **\n   (dlist_head_repr pool_pre 0 max_order new_hl) **\n   (free_area_repr (ifilter inv_l) start end inv_l) **\n   (free_area_head_repr (ifilter new_l) start end new_dl) **\n   (store_pageinfo_array vmemmap start (i2id bi) (take inv_l bi)) **\n    hfact (~(ord = NO_ORDER) ==> (ord < max_order) && ((2 EXP ord) divides (i2id bi))) **\n    hfact (0 < REF_LIM) **\n    (data_at (vmemmap + &(bi * 4), Tushort, &0)) **\n    (data_at (buddy_v + &2, Tuchar, &ord)) **\n    (undef_data_at ((vmemmap + &(bi * 4)) + &3, Tuchar)) **\n   (store_pageinfo_array vmemmap (SUC (i2id bi)) end (rest inv_l (SUC bi))) **\n   (store_zero_array (i2vi i) 0 (PAGE_SIZE * (2 EXP ord)) (PAGE_SIZE * (2 EXP ord)))\n  ");
    compare_hprop(__state, dest_bin_snd_comb(concl(__transform)));
}

void proof6()
{
    __state = parse_term("\n  exists new_pg new_l new_dl new_hl buddy_v bi inv_l (inv_dl : (addr#addr)list) (inv_hl : (addr#addr)list) i ord pg_v.\n   hfact (new_pg = min pg_v buddy_v) **\n   hfact (new_l = modified inv_l bi (0, NO_ORDER)) **\n   hfact (LENGTH new_l = len) **\n   hfact (LENGTH new_dl = len) **\n   hfact (LENGTH new_hl = max_order) **\n   hfact (&ord + &1 < &max_order) **\n   hfact (~(bi = i)) **\n   hfact (buddy_v = vmemmap + &(bi * 4)) **\n   hfact (bi < len) **\n   hfact (REF (nth inv_l bi) = 0) **\n   hfact (ORD (nth inv_l bi) = ord) **\n   hfact ((2 EXP (SUC ord)) divides (i2id (MIN i bi))) **\n   hfact (abs (&i - &bi) = &(2 EXP ord)) **\n   data_at(i2vi bi, Tptr, &0) **\n   data_at(i2vi bi + &PTR_SIZE, Tptr, &0) **\n   data_at(&\"max_order\", Tuchar, &max_order) **\n   data_at(&\"order\", Tuchar, &ord + &1) **\n   data_at(&\"buddy\", Tptr, buddy_v) **\n   data_at(&\"pool\", Tptr, pool_pre) **\n   data_at(&\"pg\", Tptr, new_pg) **\n   data_at(&\"__hyp_vmemmap\", Tptr, vmemmap) **\n   hfact (pure_const) **\n   hfact (dlist_node pool_pre (ifilter new_l) new_l new_dl new_hl start end new_dl) **\n   hfact (dlist_head pool_pre new_l new_dl 0 max_order new_hl) **\n   hfact (LENGTH inv_l = len) **\n   hfact (LENGTH inv_dl = len) **\n   hfact (LENGTH inv_hl = max_order) **\n   hfact (pg_v = vmemmap + &(i * 4)) **\n   hfact (i < len) **\n   hfact (~(ord = NO_ORDER)) **\n   hfact (ord < max_order) **\n   hfact ((2 EXP ord) divides (i2id i)) **\n   hfact (ORD (nth inv_l i) = NO_ORDER) **\n   hfact (REF (nth inv_l i) = 0) **\n   (pool_const pool_pre) **\n   (dlist_head_repr pool_pre 0 max_order new_hl) **\n   (free_area_repr (ifilter inv_l) start end inv_l) **\n   (free_area_head_repr (ifilter new_l) start end new_dl) **\n   (store_pageinfo_array vmemmap start (i2id bi) (take inv_l bi)) **\n    hfact (~(ord = NO_ORDER) ==> (ord < max_order) && ((2 EXP ord) divides (i2id bi))) **\n    hfact (0 < REF_LIM) **\n    (data_at (vmemmap + &(bi * 4), Tushort, &0)) **\n    (data_at (buddy_v + &2, Tuchar, &255)) **\n    (undef_data_at ((vmemmap + &(bi * 4)) + &3, Tuchar)) **\n   (store_pageinfo_array vmemmap (SUC (i2id bi)) end (rest inv_l (SUC bi))) **\n   (store_zero_array (i2vi i) 0 (PAGE_SIZE * (2 EXP ord)) (PAGE_SIZE * (2 EXP ord)))\n  ");
    
    thm tmpth;

// merge spa
    term fact_new_len = parse_term("LENGTH (new_l : (num#num)list) = len");
    term fact_pc = parse_term("pure_const");
    thm pc = rewrite_rule(PURE_CONST_DEF, assume(fact_pc));
    thm pc1 = conjunct1(pc);

    term fact_inv_len = parse_term("LENGTH (inv_l : (num#num)list) = len");
    term fact_newl = parse_term("new_l = modified inv_l bi (0, NO_ORDER)");
    term fact2 = parse_term("buddy_v = vmemmap + &(bi * 4)");
    term fact3 = parse_term("bi < len");
    thm bi_l_len = rewrite_rule(symm(assume(fact_inv_len)), assume(fact3));
    term fact4 = parse_term("REF (nth inv_l bi) = 0");
    term fact5 = parse_term("ORD (nth inv_l bi) = ord");

    term spa_obj = parse_term("store_pageinfo_array vmemmap start end new_l");
    thm split = break_spa_at_i(spa_obj, assume(fact3), symm(assume(fact_new_len)), pc1);
    
    thm data_at_buddy_v2order = rewrite(
        assume(fact2), parse_term("data_at (buddy_v + &2, Tuchar, &255)")); /////////////////////////////
	
    thm nth = mp(modified_nth(), bi_l_len);
    thm taken = mp(modified_taken(), bi_l_len);
    thm restn = mp(modified_restn(), bi_l_len);
    thm ar7 = arith_rule(parse_term("0 < 65536"));
    thm thl1[] = {assume(fact_newl), nth, taken, restn, REF_DEF, ORD_DEF, REF_LIM_DEF, 
                    ar7, NO_ORDER_DEF, symm(data_at_buddy_v2order), hfact_true, hsep_assoc, NULL};

    tmpth = rewrite_after_list(thl1, split);
    thm spa = eq2ent(symm(tmpth));

// new_i = MIN i bi
    term fact_npg = parse_term("(new_pg : addr) = min (pg_v : addr) (buddy_v : addr)");
    term fact_opg = parse_term("pg_v = vmemmap + &(i * 4)");
    term MIN_ob = parse_term("MIN i bi");
    thm MIN_def = rewrite(get_theorem("MIN"), MIN_ob);
    thm min_def = rewrite_rule(assume(fact_opg), rewrite_rule(assume(fact2), rewrite_rule(get_theorem("INT_MIN"), assume(fact_npg))));

    term casep = parse_term("(i : num) <= bi");
    term casen = mk_comb(parse_term("~"), casep);

    thm ar2 = arith_rule(parse_term("i <= bi ==> (i * 4) <= (bi * 4)"));
    thm ar3 = arith_rule(parse_term("! a b. a <= b ==> vmemmap + &a <= vmemmap + &b"));
    tmpth = mp(ar3, mp(ar2, assume(casep)));
    tmpth = rewrite_rule(tmpth, min_def);
    thm thp = once_rewrite_rule(symm(rewrite_rule(assume(casep), MIN_def)), tmpth);

    thm ar4 = arith_rule(parse_term("~(i <= bi) ==> ~((i * 4) <= (bi * 4))"));
    thm ar5 = arith_rule(parse_term("! a b. ~(a <= b) ==> ~(vmemmap + &a <= vmemmap + &b)"));
    tmpth = mp(ar5, mp(ar4, assume(casen)));
    tmpth = rewrite_rule(tmpth, min_def);
    thm thn = once_rewrite_rule(symm(rewrite_rule(assume(casen), MIN_def)), tmpth);
    thm new_i = merge_disj_cases(casep, thp, thn);

// rewrite fact
    term fact_i = parse_term("i < len");
    thm ar6 = arith_rule(parse_term("i < len ==> bi < len ==> MIN i bi < len"));
    thm ni_l_len = mp(mp(ar6, assume(fact_i)), assume(fact3));

// far sza
    thm prec1 = arith_rule(parse_term("start <= start"));
    thm ar9 = arith_rule(parse_term("start <= start + i"));
    thm prec2 = rewrite_rule(symm(I2ID_DEF), ar9);
    thm ar10 = arith_rule(parse_term("bi < end - start ==> start + bi < end"));
    thm prec3 = rewrite_rule(symm(I2ID_DEF), mp(ar10, rewrite_rule(LEN_DEF, assume(fact3))));
    thm prec4 = bi_l_len;
    term goal_prec5 = parse_term("ifilter inv_l (i2id bi)");
    term fact_ord = parse_term("~((ord : num) = NO_ORDER)");
    thm thl3[] = {IFILTER_DEF, i2id2i(), FREE_HEAD_DEF, assume(fact4), assume(fact5), assume(fact_ord), NULL};
    thm prec5 = simp(rewrite_after_term_list(thl3, goal_prec5));
    term goal_prec6 = parse_term("nth (inv_l : (num#num)list) ((i2id bi) - start)");
    thm ar11 = arith_rule(parse_term("(start + bi) - start = bi"));
    thm prec6 = symm(rewrite_after(ar11, rewrite(I2ID_DEF, goal_prec6)));
    tmpth = mp(mp(mp(mp(mp(mp(far_split(), prec1), prec2), prec3), prec4), prec5), prec6);
    thm far = rewrite_rule(symm(I2VI_DEF), tmpth);

    term subgoal = parse_term("~(ifilter (modified inv_l bi (0, NO_ORDER)) (i2id bi))");
    thm thl2[] = {IFILTER_DEF, FREE_HEAD_DEF, i2id2i(), mp(modified_nth(), bi_l_len), ORD_DEF, REF_DEF, NULL};
    thm subth = simp(rewrite_after_term_list(thl2, subgoal));
    term v = parse_term("(0, NO_ORDER) : num#num");
    term ifilterl = parse_term("ifilter (modified inv_l bi (0, NO_ORDER))");
    thm ar12 = arith_rule(parse_term("start < end ==> start <= end"));
    tmpth = mp(mp(far_inv(), mp(ar12, pc1)), LEN_DEF);
    tmpth = mp(mp(tmpth, assume(fact3)), symm(assume(fact_inv_len)));
    tmpth = mp(spec(ifilterl, spec(v, tmpth)), subth);
    far = rewrite_rule(symm(assume(fact_newl)), rewrite_after(tmpth, far));

    term head = parse_term(" \
        data_at(i2vi bi, Tptr, &0) ** \
        data_at(i2vi bi + &PTR_SIZE, Tptr, &0)");
    tmpth = rewrite_rule(hsep_assoc, spec(head, mp(hsep_cancel_right, eq2ent(far))));
    tmpth = rewrite_rule(merge_head_body_axiom(), tmpth);
    tmpth = rewrite_rule(assume(fact5), tmpth);
    term iblock = parse_term("store_zero_array (i2vi i) 0 (PAGE_SIZE * (2 EXP ord)) (PAGE_SIZE * (2 EXP ord))");
    tmpth = rewrite_rule(hsep_assoc, spec(iblock, mp(hsep_cancel_right, tmpth)));
    term fact6 = parse_term("abs (&(i : num) - &(bi : num)) = &(2 EXP (ord : num))");
    thm far_sza = rewrite_rule(mp(sza_merge(), assume(fact6)), tmpth);

// order facts
    term fact_new_ord = parse_term("&(ord : num) + &1 < &max_order");
    thm ar13 = arith_rule(parse_term("&(ord : num) + &1 < &max_order ==> SUC ord < max_order"));
    thm ord1 = mp(ar13, assume(fact_new_ord));
    thm ar14 = arith_rule(parse_term("!ord : num. ord < max_order ==> max_order <= 11 ==> ~(ord = 255)"));
    thm pc2 = conjunct1(conjunct2(pc));
    thm max_order_lim = rewrite_rule(MAX_ORDER_DEF, pc2);
    tmpth = mp(mp(ar14, ord1), max_order_lim);
    thm ord2 = rewrite_rule(symm(NO_ORDER_DEF), tmpth);

// ORD REF of nth new_l new_i
    term fact1 = parse_term("~((bi : num) = i)");
    term fact_i_ord = parse_term("ORD (nth (inv_l : (num#num)list) i) = NO_ORDER");
    term fact_i_ref = parse_term("REF (nth (inv_l : (num#num)list) i) = 0");
    term goal_ord = parse_term("ORD (nth new_l (MIN i bi))");
    term goal_ref = parse_term("REF (nth new_l (MIN i bi))");

    thm pfact = rewrite_after(assume(casep), rewrite(get_theorem("MIN"), MIN_ob));
    thm ar15 = arith_rule(parse_term("~((bi : num) = i) ==> ~(i = bi)"));
    tmpth = mp(mp(modified_mth(), bi_l_len), mp(ar15, assume(fact1)));
    thm thl4[] = {pfact, assume(fact_newl), tmpth, NULL};
    thm thp_ord = rewrite_after(assume(fact_i_ord), rewrite_after_term_list(thl4, goal_ord));
    thm thp_ref = rewrite_after(assume(fact_i_ref), rewrite_after_term_list(thl4, goal_ref));

    thm nfact = rewrite_after(assume(casen), rewrite(get_theorem("MIN"), MIN_ob));
    tmpth = mp(modified_nth(), bi_l_len);
    thm thl5[] = {nfact, assume(fact_newl), tmpth, NULL};
    thm thn_ord = rewrite_after(ORD_DEF, rewrite_after_term_list(thl5, goal_ord));
    thm thn_ref = rewrite_after(REF_DEF, rewrite_after_term_list(thl5, goal_ref));

    thm th_ord = merge_disj_cases(casep, thp_ord, thn_ord);
    thm th_ref = merge_disj_cases(casep, thp_ref, thn_ref);

    term fact_neg1 = parse_term("~(ord == NO_ORDER) ==> ord < max_order && 2 EXP ord divides i2id bi");
    term fact_neg2 = parse_term("LENGTH (inv_dl : (addr#addr)list) == len");
    term fact_neg3 = parse_term("LENGTH (inv_hl : (addr#addr)list) == max_order");
    term fact_neg4 = parse_term("(ord : num) < max_order");
    term fact_neg5 = parse_term("2 EXP (ord : num) divides i2id (i : num)");
    term fact_neg6 = parse_term("0 < REF_LIM");

    term cfactl[] = {fact1, fact2, fact3, fact4, fact5, fact6, 
        fact_ord, fact_new_ord, fact_i_ord, fact_i_ref, fact_newl, fact_i, 
        fact_inv_len, fact_npg, fact_opg, fact_neg1, fact_neg2, fact_neg3, 
        fact_neg4, fact_neg5, fact_neg6, NULL};
    term kfactl[] = {fact_pc, fact_new_len, NULL};
    thm pthl[] = {new_i, ni_l_len, ord1, ord2, th_ord, th_ref, NULL};
    thm hthl[] = {spa, far_sza, NULL};
    tmpth = create_trans_auto(cfactl, kfactl, pthl, hthl);
    thm ent = which_implies(__state, tmpth);

    thm ar8 = arith_rule(parse_term("&(ord : num) + &1 = &(SUC ord)"));
    tmpth = rewrite(ar8, dest_bin_snd_comb(concl(ent)));
    tmpth = htrans(ent, eq2ent(tmpth));
    tmpth = hexists_intro_auto(tmpth, parse_term("MIN (i : num) (bi : num) = (new_i : num)"));
    tmpth = hexists_intro_auto(tmpth, parse_term("SUC ord = new_ord : num"));
    __transform = tmpth;
    // printf("%s\n\n", string_of_thm(__transform));

    compare_hprop(__state, dest_bin_fst_comb(concl(__transform)));
    __state = parse_term("\n  exists new_pg new_l new_dl new_hl (buddy_v : addr) (bi : num) (inv_l : (num#num)list) (inv_dl : (addr#addr)list) (inv_hl : (addr#addr)list) (i : num) (ord : num) (pg_v : addr) new_i new_ord.\n   data_at(&\"max_order\", Tuchar, &max_order) **\n   data_at(&\"order\", Tuchar, &new_ord) **\n   data_at(&\"buddy\", Tptr, buddy_v) **\n   data_at(&\"pool\", Tptr, pool_pre) **\n   data_at(&\"pg\", Tptr, new_pg) **\n   data_at(&\"__hyp_vmemmap\", Tptr, vmemmap) **\n   hfact (pure_const) **\n   hfact (dlist_node pool_pre (ifilter new_l) new_l new_dl new_hl start end new_dl) **\n   hfact (dlist_head pool_pre new_l new_dl 0 max_order new_hl) **\n   hfact (LENGTH new_l = len) **\n   hfact (LENGTH new_dl = len) **\n   hfact (LENGTH new_hl = max_order) **\n   hfact (new_pg = vmemmap + &(new_i * 4)) **\n   hfact (new_i < len) **\n   hfact (~(new_ord = NO_ORDER)) **\n   hfact (new_ord < max_order) **\n   hfact ((2 EXP new_ord) divides (i2id new_i)) **\n   hfact (ORD (nth new_l new_i) = NO_ORDER) **\n   hfact (REF (nth new_l new_i) = 0) **\n   (pool_const pool_pre) **\n   (dlist_head_repr pool_pre 0 max_order new_hl) **\n   (free_area_repr (ifilter new_l) start end new_l) **\n   (free_area_head_repr (ifilter new_l) start end new_dl) **\n   (store_pageinfo_array vmemmap start end new_l) **\n   (store_zero_array (i2vi new_i) 0 (PAGE_SIZE * (2 EXP new_ord)) (PAGE_SIZE * (2 EXP new_ord)))\n  ");
    compare_hprop(__state, dest_bin_snd_comb(concl(__transform)));
}

void proof7()
{
    __state = parse_term("\n exists pg_v ord i inv_l inv_dl inv_hl buddy_v bi.\n  hfact (~(&ord + &1 < &max_order && ~(buddy_v = &0))) **\n  hfact ((buddy_v = &0) ||\n   ~(bi = i) &&\n   (buddy_v = vmemmap + &(bi * 4)) &&\n   (bi < len) &&\n   (REF (nth inv_l bi) = 0) &&\n   (ORD (nth inv_l bi) = ord) &&\n   ((2 EXP (SUC ord)) divides (i2id (MIN i bi))) &&\n   (abs (&i - &bi) = &(2 EXP ord))) **\n  data_at(&\"max_order\", Tuchar, &max_order) **\n  data_at(&\"order\", Tuchar, &ord) **\n  data_at(&\"buddy\", Tptr, buddy_v) **\n  data_at(&\"pool\", Tptr, pool_pre) **\n  data_at(&\"pg\", Tptr, pg_v) **\n  data_at(&\"__hyp_vmemmap\", Tptr, vmemmap) **\n  hfact (pure_const) **\n  hfact (dlist_node pool_pre (ifilter inv_l) inv_l inv_dl inv_hl start end inv_dl) **\n  hfact (dlist_head pool_pre inv_l inv_dl 0 max_order inv_hl) **\n  hfact (LENGTH inv_l = len) **\n  hfact (LENGTH inv_dl = len) **\n  hfact (LENGTH inv_hl = max_order) **\n  hfact (pg_v = vmemmap + &(i * 4)) **\n  hfact (i < len) **\n  hfact (~(ord = NO_ORDER)) **\n  hfact (ord < max_order) **\n  hfact ((2 EXP ord) divides (i2id i)) **\n  hfact (ORD (nth inv_l i) = NO_ORDER) **\n  hfact (REF (nth inv_l i) = 0) **\n  (pool_const pool_pre) **\n  (dlist_head_repr pool_pre 0 max_order inv_hl) **\n  (free_area_repr (ifilter inv_l) start end inv_l) **\n  (free_area_head_repr (ifilter inv_l) start end inv_dl) **\n  (store_pageinfo_array vmemmap start end inv_l) **\n  (store_zero_array (i2vi i) 0 (PAGE_SIZE * (2 EXP ord)) (PAGE_SIZE * (2 EXP ord)))\n    ");

    term fact_ilen = parse_term("i < len");
    term fact_ord = parse_term("ORD (nth (inv_l : (num#num)list) i) = NO_ORDER");
    term fact_ref = parse_term("REF (nth (inv_l : (num#num)list) i) = 0");
    term fact_len = parse_term("LENGTH (inv_l : (num#num)list) = len");
    term fact_pgv = parse_term("(pg_v : addr) = vmemmap + &(i * 4)");
    term fact_pc = parse_term("pure_const");
    thm start_end = conjunct1(rewrite_rule(PURE_CONST_DEF, assume(fact_pc)));

    term spa_obj = parse_term("store_pageinfo_array vmemmap start end inv_l");
    thm split = break_spa_at_i(spa_obj, assume(fact_ilen), symm(assume(fact_len)), start_end);

    thm data_at_pg_v_order = rewrite(
        symm(assume(fact_pgv)), parse_term("data_at ((vmemmap + &(i * 4)) + &2, Tuchar, &NO_ORDER)"));
    
    thm ar = arith_rule(parse_term("0 < 65536"));

    thm thl[] = {assume(fact_ord), assume(fact_ref), data_at_pg_v_order, REF_LIM_DEF, ar, hfact_true, hsep_assoc, NULL};
    thm spa = eq2ent(rewrite_after_list(thl, split));

    term kfactl[] = {fact_ilen, fact_ord, fact_ref, fact_len, fact_pgv, fact_pc, NULL};
    thm trans = create_trans_auto((term[]){NULL}, kfactl, (thm[]){NULL}, (thm[]){spa, NULL});
    __transform = which_implies(__state, trans);
    // printf("%s\n\n", string_of_thm(__transform));

    compare_hprop(__state, dest_bin_fst_comb(concl(__transform)));
    __state = parse_term("\n exists pg_v ord i inv_l inv_dl inv_hl buddy_v bi.\n  hfact (~(&ord + &1 < &max_order && ~(buddy_v = &0))) **\n  hfact ((buddy_v = &0) ||\n   ~(bi = i) &&\n   (buddy_v = vmemmap + &(bi * 4)) &&\n   (bi < len) &&\n   (REF (nth inv_l bi) = 0) &&\n   (ORD (nth inv_l bi) = ord) &&\n   ((2 EXP (SUC ord)) divides (i2id (MIN i bi))) &&\n   (abs (&i - &bi) = &(2 EXP ord))) **\n  data_at(&\"max_order\", Tuchar, &max_order) **\n  data_at(&\"order\", Tuchar, &ord) **\n  data_at(&\"buddy\", Tptr, buddy_v) **\n  data_at(&\"pool\", Tptr, pool_pre) **\n  data_at(&\"pg\", Tptr, pg_v) **\n  data_at(&\"__hyp_vmemmap\", Tptr, vmemmap) **\n  hfact (pure_const) **\n  hfact (dlist_node pool_pre (ifilter inv_l) inv_l inv_dl inv_hl start end inv_dl) **\n  hfact (dlist_head pool_pre inv_l inv_dl 0 max_order inv_hl) **\n  hfact (LENGTH inv_l = len) **\n  hfact (LENGTH inv_dl = len) **\n  hfact (LENGTH inv_hl = max_order) **\n  hfact (pg_v = vmemmap + &(i * 4)) **\n  hfact (i < len) **\n  hfact (~(ord = NO_ORDER)) **\n  hfact (ord < max_order) **\n  hfact ((2 EXP ord) divides (i2id i)) **\n  hfact (ORD (nth inv_l i) = NO_ORDER) **\n  hfact (REF (nth inv_l i) = 0) **\n  (pool_const pool_pre) **\n  (dlist_head_repr pool_pre 0 max_order inv_hl) **\n  (free_area_repr (ifilter inv_l) start end inv_l) **\n  (free_area_head_repr (ifilter inv_l) start end inv_dl) **\n  (store_pageinfo_array vmemmap start (i2id i) (take inv_l i)) **\n   (data_at (vmemmap + &(i * 4), Tushort, &0)) **\n   (data_at (pg_v + &2, Tuchar, &NO_ORDER)) **\n   (undef_data_at ((vmemmap + &(i * 4)) + &3, Tuchar)) **\n  (store_pageinfo_array vmemmap (SUC (i2id i)) end (rest inv_l (SUC i))) **\n  (store_zero_array (i2vi i) 0 (PAGE_SIZE * (2 EXP ord)) (PAGE_SIZE * (2 EXP ord)))\n    ");
    compare_hprop(__state, dest_bin_snd_comb(concl(__transform)));
}

void proof8()
{
    __state = parse_term("\n exists pg_v ord i inv_l inv_dl inv_hl buddy_v bi.\n  hfact (~(&ord + &1 < &max_order && ~(buddy_v = &0))) **\n  hfact ((buddy_v = &0) ||\n   ~(bi = i) &&\n   (buddy_v = vmemmap + &(bi * 4)) &&\n   (bi < len) &&\n   (REF (nth inv_l bi) = 0) &&\n   (ORD (nth inv_l bi) = ord) &&\n   ((2 EXP (SUC ord)) divides (i2id (MIN i bi))) &&\n   (abs (&i - &bi) = &(2 EXP ord))) **\n  data_at(&\"max_order\", Tuchar, &max_order) **\n  data_at(&\"order\", Tuchar, &ord) **\n  data_at(&\"buddy\", Tptr, buddy_v) **\n  data_at(&\"pool\", Tptr, pool_pre) **\n  data_at(&\"pg\", Tptr, pg_v) **\n  data_at(&\"__hyp_vmemmap\", Tptr, vmemmap) **\n  hfact (pure_const) **\n  hfact (dlist_node pool_pre (ifilter inv_l) inv_l inv_dl inv_hl start end inv_dl) **\n  hfact (dlist_head pool_pre inv_l inv_dl 0 max_order inv_hl) **\n  hfact (LENGTH inv_l = len) **\n  hfact (LENGTH inv_dl = len) **\n  hfact (LENGTH inv_hl = max_order) **\n  hfact (pg_v = vmemmap + &(i * 4)) **\n  hfact (i < len) **\n  hfact (~(ord = NO_ORDER)) **\n  hfact (ord < max_order) **\n  hfact ((2 EXP ord) divides (i2id i)) **\n  hfact (ORD (nth inv_l i) = NO_ORDER) **\n  hfact (REF (nth inv_l i) = 0) **\n  (pool_const pool_pre) **\n  (dlist_head_repr pool_pre 0 max_order inv_hl) **\n  (free_area_repr (ifilter inv_l) start end inv_l) **\n  (free_area_head_repr (ifilter inv_l) start end inv_dl) **\n  (store_pageinfo_array vmemmap start (i2id i) (take inv_l i)) **\n   (data_at (vmemmap + &(i * 4), Tushort, &0)) **\n   (data_at (pg_v + &2, Tuchar, &ord)) **\n   (undef_data_at ((vmemmap + &(i * 4)) + &3, Tuchar)) **\n  (store_pageinfo_array vmemmap (SUC (i2id i)) end (rest inv_l (SUC i))) **\n  (store_zero_array (i2vi i) 0 (PAGE_SIZE * (2 EXP ord)) (PAGE_SIZE * (2 EXP ord)))\n    ");
  
    thm tmpth;

// spa
    term fact_ilen = parse_term("i < len");
    term fact_ord = parse_term("ORD (nth (inv_l : (num#num)list) i) = NO_ORDER");
    term fact_ref = parse_term("REF (nth (inv_l : (num#num)list) i) = 0");
    term fact_len = parse_term("LENGTH (inv_l : (num#num)list) = len");
    term fact_pgv = parse_term("(pg_v : addr) = vmemmap + &(i * 4)");
    term fact_ord1 = parse_term("(ord : num) < max_order");
    term fact_ord2 = parse_term("(2 EXP ord) divides (i2id i)");
    term fact_ord3 = parse_term("~(ord = NO_ORDER)");
    term fact_pc = parse_term("pure_const");
    thm pc = rewrite_rule(PURE_CONST_DEF, assume(fact_pc));
    thm pc1 = conjunct1(pc);
    thm i_l_len = rewrite_rule(symm(assume(fact_len)), assume(fact_ilen));
    
    tmpth = spec(parse_term("(0, ord) : num#num"), spec(parse_term("i : num"), spec(parse_term("inv_l : (num#num)list"), modified_len())));
    thm newl_len = trans(tmpth, assume(fact_len));

    term spa_obj = parse_term("store_pageinfo_array vmemmap start end (modified inv_l i (0, ord))");
    thm split = break_spa_at_i(spa_obj, assume(fact_ilen), symm(newl_len), pc1);
        
    thm data_at_pg_v2order = rewrite(
        assume(fact_pgv), parse_term("data_at (pg_v + &2, Tuchar, &(ord : num))"));

    thm ar2 = arith_rule(parse_term("0 < 65536"));
    thm nth = mp(modified_nth(), i_l_len);
    thm taken = mp(modified_taken(), i_l_len);
    thm restn = mp(modified_restn(), i_l_len);

    thm thl1[] = {assume(fact_ord), assume(fact_ref), nth, taken, restn, ORD_DEF, REF_DEF, symm(data_at_pg_v2order),
        assume(fact_ord1), assume(fact_ord2), REF_LIM_DEF, ar2, hfact_true, hsep_assoc, NULL};
    tmpth = rewrite_after_list(thl1, split);
    thm spa = eq2ent(symm(tmpth));

// far sza
    thm prec1 = arith_rule(parse_term("start <= start"));
    thm ar9 = arith_rule(parse_term("start <= start + i"));
    thm prec2 = rewrite_rule(symm(I2ID_DEF), ar9);
    thm ar10 = arith_rule(parse_term("bi < end - start ==> start + bi < end"));
    thm prec3 = rewrite_rule(symm(I2ID_DEF), mp(ar10, rewrite_rule(LEN_DEF, assume(fact_ilen))));
    thm prec4 = i_l_len;
    term goal_prec5 = parse_term("~(ifilter inv_l (i2id i))");\
    thm thl3[] = {IFILTER_DEF, i2id2i(), FREE_HEAD_DEF, assume(fact_ord), assume(fact_ord), NULL};
    thm prec5 = simp(rewrite_after_term_list(thl3, goal_prec5));
    thm prec6 = assume(fact_ord3);
    term goal_prec7 = parse_term("nth (inv_l : (num#num)list) ((i2id i) - start)");
    thm ar11 = arith_rule(parse_term("(start + i) - start = i"));
    thm prec7 = symm(rewrite_after(ar11, rewrite(I2ID_DEF, goal_prec7)));
    tmpth = mp(mp(mp(mp(mp(mp(mp(far_merge(), prec1), prec2), prec3), prec4), prec5), prec6), prec7);
    tmpth = rewrite_rule(symm(I2VI_DEF), tmpth);
    thm far = rewrite_after(ar11, rewrite_after(I2ID_DEF, tmpth));
    
    term block1 = parse_term("free_area_repr (ifilter inv_l) start end inv_l");
    term block2 = parse_term("store_zero_array (i2vi i) 0 (PAGE_SIZE * (2 EXP ord)) (PAGE_SIZE * (2 EXP ord))");
    tmpth = rewrite(symm(merge_head_body_axiom()), block2);
    tmpth = rewrite_rule(hsep_assoc, spec(block1, mp(hsep_cancel_left, eq2ent(tmpth))));
    tmpth = once_rewrite_rule(symm(hsep_assoc), tmpth);
    thm far_sza = rewrite_rule(far, tmpth);
    
    term kfactl[] = {fact_ilen, fact_ord, fact_ref, fact_len, fact_pgv, fact_ord1, fact_ord2, fact_ord3, fact_pc, NULL};
    thm hthl[] = {spa, far_sza, NULL};
    tmpth = create_trans_auto((term[]){NULL}, kfactl, (thm[]){NULL}, hthl);
    __transform = which_implies(__state, tmpth);
    // printf("%s\n\n", string_of_thm(__transform));
    
    compare_hprop(__state, dest_bin_fst_comb(concl(__transform)));
    __state = parse_term("\n exists pg_v ord i inv_l inv_dl inv_hl buddy_v bi.\n  hfact (~(&ord + &1 < &max_order && ~(buddy_v = &0))) **\n  hfact ((buddy_v = &0) ||\n   ~(bi = i) &&\n   (buddy_v = vmemmap + &(bi * 4)) &&\n   (bi < len) &&\n   (REF (nth inv_l bi) = 0) &&\n   (ORD (nth inv_l bi) = ord) &&\n   ((2 EXP (SUC ord)) divides (i2id (MIN i bi))) &&\n   (abs (&i - &bi) = &(2 EXP ord))) **\n  data_at(&\"max_order\", Tuchar, &max_order) **\n  data_at(&\"order\", Tuchar, &ord) **\n  data_at(&\"buddy\", Tptr, buddy_v) **\n  data_at(&\"pool\", Tptr, pool_pre) **\n  data_at(&\"pg\", Tptr, pg_v) **\n  data_at(&\"__hyp_vmemmap\", Tptr, vmemmap) **\n  hfact (pure_const) **\n  hfact (dlist_node pool_pre (ifilter inv_l) inv_l inv_dl inv_hl start end inv_dl) **\n  hfact (dlist_head pool_pre inv_l inv_dl 0 max_order inv_hl) **\n  hfact (LENGTH inv_l = len) **\n  hfact (LENGTH inv_dl = len) **\n  hfact (LENGTH inv_hl = max_order) **\n  hfact (pg_v = vmemmap + &(i * 4)) **\n  hfact (i < len) **\n  hfact (~(ord = NO_ORDER)) **\n  hfact (ord < max_order) **\n  hfact ((2 EXP ord) divides (i2id i)) **\n  hfact (ORD (nth inv_l i) = NO_ORDER) **\n  hfact (REF (nth inv_l i) = 0) **\n  (pool_const pool_pre) **\n  (dlist_head_repr pool_pre 0 max_order inv_hl) **\n  (free_area_repr (ifilter (modified inv_l i (0, ord))) start end (modified inv_l i (0, ord))) **\n  (free_area_head_repr (ifilter inv_l) start end inv_dl) **\n  (store_pageinfo_array vmemmap start end (modified inv_l i (0, ord))) **\n  data_at(i2vi i, Tptr, &0) **\n  data_at(i2vi i + &PTR_SIZE, Tptr, &0)\n    ");
    compare_hprop(__state, dest_bin_snd_comb(concl(__transform)));
}

void proof9()
{
    __state = parse_term("\n exists new_l new_dl new_hl pg_v ord i inv_l (inv_dl : (addr#addr)list) (inv_hl : (addr#addr)list) buddy_v bi.\n  hfact (new_l = modified inv_l i (0, ord)) **\n  hfact (LENGTH new_l = len) **\n  hfact (LENGTH new_dl = len) **\n  hfact (LENGTH new_hl = max_order) **\n  hfact (~(&ord + &1 < &max_order && ~(buddy_v = &0))) **\n  hfact ((buddy_v = &0) ||\n   ~(bi = i) &&\n   (buddy_v = vmemmap + &(bi * 4)) &&\n   (bi < len) &&\n   (REF (nth inv_l bi) = 0) &&\n   (ORD (nth inv_l bi) = ord) &&\n   ((2 EXP (SUC ord)) divides (i2id (MIN i bi))) &&\n   (abs (&i - &bi) = &(2 EXP ord))) **\n  data_at(&\"max_order\", Tuchar, &max_order) **\n  data_at(&\"order\", Tuchar, &ord) **\n  data_at(&\"buddy\", Tptr, buddy_v) **\n  data_at(&\"pool\", Tptr, pool_pre) **\n  data_at(&\"pg\", Tptr, pg_v) **\n  data_at(&\"__hyp_vmemmap\", Tptr, vmemmap) **\n  hfact (pure_const) **\n  hfact (dlist_node pool_pre (ifilter new_l) new_l new_dl new_hl start end new_dl) **\n  hfact (dlist_head pool_pre new_l new_dl 0 max_order new_hl) **\n  hfact (LENGTH inv_l = len) **\n  hfact (LENGTH inv_dl = len) **\n  hfact (LENGTH inv_hl = max_order) **\n  hfact (pg_v = vmemmap + &(i * 4)) **\n  hfact (i < len) **\n  hfact (~(ord = NO_ORDER)) **\n  hfact (ord < max_order) **\n  hfact ((2 EXP ord) divides (i2id i)) **\n  hfact (ORD (nth inv_l i) = NO_ORDER) **\n  hfact (REF (nth inv_l i) = 0) **\n  (pool_const pool_pre) **\n  (dlist_head_repr pool_pre 0 max_order new_hl) **\n  (free_area_repr (ifilter (modified inv_l i (0, ord))) start end (modified inv_l i (0, ord))) **\n  (free_area_head_repr (ifilter new_l) start end new_dl) **\n  (store_pageinfo_array vmemmap start end (modified inv_l i (0, ord)))\n    ");
  
    term fact = parse_term("new_l = modified inv_l i (0, (ord : num))");
    term far = parse_term("free_area_repr (ifilter new_l) start end new_l");
    term spa = parse_term("store_pageinfo_array vmemmap start end new_l");

    thm far_ent = eq2ent(symm(rewrite(assume(fact), far)));
    thm spa_ent = eq2ent(symm(rewrite(assume(fact), spa)));

    thm trans = create_trans_auto((term[]){NULL}, (term[]){fact, NULL}, (thm[]){NULL}, (thm[]){far_ent, spa_ent, NULL});
    __transform = which_implies(__state, trans);
    // printf("%s\n\n", string_of_thm(__transform));

    compare_hprop(__state, dest_bin_fst_comb(concl(__transform)));
    __state = parse_term("\n exists new_l new_dl new_hl pg_v ord i inv_l (inv_dl : (addr#addr)list) (inv_hl : (addr#addr)list) buddy_v bi.\n  hfact (new_l = modified inv_l i (0, ord)) **\n  hfact (LENGTH new_l = len) **\n  hfact (LENGTH new_dl = len) **\n  hfact (LENGTH new_hl = max_order) **\n  hfact (~(&ord + &1 < &max_order && ~(buddy_v = &0))) **\n  hfact ((buddy_v = &0) ||\n   ~(bi = i) &&\n   (buddy_v = vmemmap + &(bi * 4)) &&\n   (bi < len) &&\n   (REF (nth inv_l bi) = 0) &&\n   (ORD (nth inv_l bi) = ord) &&\n   ((2 EXP (SUC ord)) divides (i2id (MIN i bi))) &&\n   (abs (&i - &bi) = &(2 EXP ord))) **\n  data_at(&\"max_order\", Tuchar, &max_order) **\n  data_at(&\"order\", Tuchar, &ord) **\n  data_at(&\"buddy\", Tptr, buddy_v) **\n  data_at(&\"pool\", Tptr, pool_pre) **\n  data_at(&\"pg\", Tptr, pg_v) **\n  data_at(&\"__hyp_vmemmap\", Tptr, vmemmap) **\n  hfact (pure_const) **\n  hfact (dlist_node pool_pre (ifilter new_l) new_l new_dl new_hl start end new_dl) **\n  hfact (dlist_head pool_pre new_l new_dl 0 max_order new_hl) **\n  hfact (LENGTH inv_l = len) **\n  hfact (LENGTH inv_dl = len) **\n  hfact (LENGTH inv_hl = max_order) **\n  hfact (pg_v = vmemmap + &(i * 4)) **\n  hfact (i < len) **\n  hfact (~(ord = NO_ORDER)) **\n  hfact (ord < max_order) **\n  hfact ((2 EXP ord) divides (i2id i)) **\n  hfact (ORD (nth inv_l i) = NO_ORDER) **\n  hfact (REF (nth inv_l i) = 0) **\n  (pool_const pool_pre) **\n  (dlist_head_repr pool_pre 0 max_order new_hl) **\n  (free_area_repr (ifilter new_l) start end new_l) **\n  (free_area_head_repr (ifilter new_l) start end new_dl) **\n  (store_pageinfo_array vmemmap start end new_l)\n ");
    compare_hprop(__state, dest_bin_snd_comb(concl(__transform)));
}

int main()
{
    cst_init();
    definitions();
    puts("definitions loaded!");
    load_axioms();
    puts("axioms loaded!");
    test_lemma();
    proof1();
    proof2();
    proof3();
    proof4();
    proof5();
    proof6();
    proof7();
    proof8();
    proof9();

    return 0;
}