#include "proof-user.h"
#include "def.h"
#include "drule.h"
#include "lemma.h"
#include <stdio.h>

/*
    ((! (arg1 : B) (lo : num) (hi : num). P arg1 lo hi NIL = (hfact (lo = hi))) /\
    (! (arg1 : B) (lo : num) (hi : num) (h : A) (t : (A)list). P arg1 lo hi (CONS h t) = ((ONE arg1 h lo) ** (P arg1 (SUC lo) hi t)))) ==>
    (! (len : num) (n : num) (l : (A)list) (arg1 : B) (hi : num).
        (n <= len) ==> (len <= hi) ==> (len = LENGTH l) ==>
        P arg1 (hi - len) hi l = (P arg1 (hi - len) (hi - len + n) (take l n) ** P arg1 (hi - len + n) hi (rest l n)))
*/
thm break_list_sepconj()
{
    term asmp_tm = parse_term("(! (arg1 : B) (lo : num) (hi : num). P arg1 lo hi NIL = (hfact (lo = hi))) /\\ \
        (! (arg1 : B) (lo : num) (hi : num) (h : A) (t : (A)list). P arg1 lo hi (CONS h t) = ((ONE arg1 h lo) ** (P arg1 (SUC lo) hi t)))");
    thm asmp1 = conjunct1(assume(asmp_tm));
    thm asmp2 = conjunct2(assume(asmp_tm));
    term goal = parse_term("! (lent : num) (n : num) (l : (A)list) (arg1 : B) (hi : num). \
        (n <= lent) ==> (lent <= hi) ==> (lent = LENGTH l) ==> \
        (P arg1 (hi - lent) hi l) = ((P arg1 (hi - lent) (hi - lent + n) (take l n)) ** (P arg1 (hi - lent + n) hi (rest l n)))");
    term lent = parse_term("lent : num");
    term n = parse_term("n : num");
    term l = parse_term("l : (A)list");
    thm LENGTH = get_theorem("LENGTH");
    thm ar1 = arith_rule(parse_term("! a. a - 0 = a"));
    thm ar2 = arith_rule(parse_term("! a. a + 0 = a"));
    thm ar3 = arith_rule(parse_term("! n. SUC n <= 0 <=> F"));
    thm ar4 = arith_rule(parse_term("! a b c. SUC b <= a ==> (a - SUC b + SUC c) = (a - b + c)"));
    thm ar5 = arith_rule(parse_term("! n. SUC n == 0 <=> F"));
    thm ar6 = arith_rule(parse_term("! a b. SUC a <= SUC b ==> a <= b"));
    thm ar7 = arith_rule(parse_term("! a b. SUC a <= b ==> a <= b"));
    thm ar8 = arith_rule(parse_term("! a b. SUC a <= b ==> SUC (b - SUC a) = b - a"));
    thm ar9 = arith_rule(parse_term("! a b. SUC a = SUC b ==> a = b"));

    term goal_lent = concl(spec(lent, assume(goal)));
    // show_induct_goal(lent, goal_lent, num_INDUCTION);

    // lent = 0
    term goal_lent0 = rewrite_term(parse_term("lent = 0"), goal_lent);
    term goal_lent0_n = concl(spec(n, assume(goal_lent0)));
    term casen0 = parse_term("n = 0");
    term casenS = parse_term("n = SUC n'");
    // n = 0
    thm thml1[] = {assume(casen0), ar1, ar2, TAKE_DEF, REST_DEF, asmp1, hfact_def, sepand_t, hsep_hemp_left, NULL};
    thm th2 = rewrite_after_term_list(thml1, goal_lent0_n);
    thm thl0n0 = simp(th2);
    // n = SUC n'
    thm th3 = rewrite(assume(casenS), goal_lent0_n);
    thm th4 = rewrite_after(ar3, th3);
    thm th5 = simp(th4);
    thm thl0nS = choose(parse_term("n' : num"), th5);
    thm th6 = disj_cases(spec(n, num_CASES), thl0n0, thl0nS);
    thm thl0 = gen(n, th6);
    // lent = SUC lent
    term goal_lentS = rewrite_term(parse_term("SUC lent' = SUC lent"),
                        rewrite_term(parse_term("lent = SUC lent'"), goal_lent));
    term goal_lentS_n = concl(spec(n, assume(goal_lentS)));
    // n = 0    
    thm th7 = rewrite_after_term_list(thml1, goal_lentS_n);
    thm thlSn0 = simp(th7);
    // n = SUC n'
    thm th8 = rewrite(assume(casenS), goal_lentS_n);
    term subgoal = concl(spec(l, assume(dest_bin_snd_comb(concl(th8)))));
    term subasump1_tm = parse_term("SUC n' <= SUC lent");
    term subasump2_tm = parse_term("SUC lent <= hi");
    term concgoal = parse_term("SUC lent == LENGTH (l : (A)list) ==> \
        (P (arg1 : B) (hi - SUC lent) hi (l : (A)list) -|- \
        P arg1 (hi - SUC lent) (hi - SUC lent + SUC n') (take l (SUC n')) ** \
        P arg1 (hi - SUC lent + SUC n') hi (rest l (SUC n')))");
    // show_induct_goal(l, subgoal, list_INDUCT);
    // l = []
    term subgoal_nil = rewrite_term(parse_term("(l : (A)list) = []"), concgoal);
    thm th9 = rewrite(LENGTH, subgoal_nil);
    thm th10 = rewrite_after(ar5, th9);
    thm th11 = disch(disch(simp(th10), subasump2_tm), subasump1_tm);
    thm thnil = gen(parse_term("arg1 : B"), gen(parse_term("hi : num"), th11));
    // l = CONS
    term subgoal_cons = rewrite_term(parse_term("CONS (h : A) l' = CONS h l"), 
                        rewrite_term(parse_term("l = CONS (h : A) l'"), concgoal));
    thm subasump1 = assume(subasump1_tm);
    thm subasump2 = assume(subasump2_tm);
    thm thml2[] = {TAKE_DEF, REST_DEF, asmp2, mp(ar4, subasump2), mp(ar8, subasump2), NULL};
    thm th12 = rewrite_after_term_list(thml2, subgoal_cons);
    thm subasump1_ = mp(ar6, subasump1);
    thm subasump2_ = mp(ar7, subasump2);
    term subasump3_tm = dest_bin_fst_comb(dest_bin_snd_comb(concl(th12)));
    term subconcgoal = dest_bin_snd_comb(dest_bin_snd_comb(concl(th12)));
    thm subasump3_ = mp(ar9, rewrite_rule(LENGTH, assume(subasump3_tm)));
    thm th13 = mp(mp(mp(assume(goal_lent), subasump1_), subasump2_), subasump3_);
    thm th14 = rewrite(th13, subconcgoal);
    thm th15 = rewrite_after(hsep_assoc, th14);
    thm th16 = disch(simp(th15), subasump3_tm);
    thm th17 = rewrite_after(th16, th12);
    thm th18 = disch(disch(simp(th17), subasump2_tm), subasump1_tm);
    thm th19 = gen(parse_term("arg1 : B"), gen(parse_term("hi : num"), th18));
    thm thcons = gen(parse_term("h : A"), gen(l, disch(th19, subgoal)));
    thm th20 = mp(list_INDUCT, conjunct(thnil, thcons));
    thm th21 = rewrite_rule(symm(assume(casenS)), th20);
    thm thlSnS = undisch(undisch(choose(parse_term("n' : num"), disch(disch(th21, asmp_tm), goal_lent))));
    thm th22 = disj_cases(spec(n, num_CASES), thlSn0, thlSnS);
    thm thlS = gen(lent, disch(gen(n, th22), goal_lent));
    thm solve = mp(num_INDUCTION, conjunct(thl0, thlS));

    thm th = gen(parse_term("P : B -> num -> num -> (A)list -> hprop"), gen(parse_term("ONE : B -> A -> num -> hprop"), disch(solve, asmp_tm)));
    return th;
}

thm breaknth_list_sepconj()
{
    return new_axiom(parse_term("! (P : B -> num -> num -> (A)list -> hprop) (ONE : B -> A -> num -> hprop). \
    ((! (arg1 : B) (lo : num) (hi : num). P arg1 lo hi NIL = (hfact (lo = hi))) /\\ \
    (! (arg1 : B) (lo : num) (hi : num) (h : A) (t : (A)list). P arg1 lo hi (CONS h t) = ((ONE arg1 h lo) ** (P arg1 (SUC lo) hi t)))) ==> \
    (! (len : num) (n : num) (l : (A)list) (arg1 : B) (hi : num). \
        (n < len) ==> (len <= hi) ==> (len = LENGTH l) ==>  \
        (P arg1 (hi - len) hi l = ( \
        (P arg1 (hi - len) (hi - len + n) (take l n)) **  \
        (ONE arg1 (nth l n) (hi - len + n)) ** \
        (P arg1 (hi - len + (SUC n)) hi (rest l (SUC n))))))"));
}

thm break_array_sepconj()
{
    return new_axiom(parse_term("! (P : B -> num -> num -> num -> hprop) (ONE : B -> num -> hprop). \
    ((! (arg1 : B) (lo : num) (hi : num). P arg1 lo hi 0 = (hfact (lo = hi))) /\\ \
    (! (arg1 : B) (lo : num) (hi : num) (n : num). P arg1 lo hi (SUC n) = ((ONE arg1 lo) ** (P arg1 (SUC lo) hi n)))) ==> \
    (! (n : num) (i : num) (arg1 : B) (hi : num). \
        (i <= n) ==> (n <= hi) ==> \
        P arg1 (hi - n) hi n = (P arg1 (hi - n) (hi - n + i) i ** P arg1 (hi - n + i) hi (n - i)))"));
}

/*
    n < LENGTH l
==> (nth (modified l n v) n) = v
*/
thm modified_nth()
{
    term l = parse_term("l : (A)list");
    term n = parse_term("n : num");
    term v = parse_term("v : A");
    term goal = parse_term("!(n : num). n < LENGTH (l : (A)list) ==> (nth (modified l n (v : A)) n) = v");
    // show_induct_goal(l, goal, list_INDUCT);

    term tm1 = parse_term("(n : num) < LENGTH ([] : (A)list)");
    thm LENGTH = get_theorem("LENGTH");
    thm th1 = rewrite(LENGTH, tm1);
    term tm2 = parse_term("(n:num) < 0 <=> F");
    thm th2 = arith_rule(tm2);
    thm th3 = trans(th1, th2);
    term tm3 = parse_term("(n : num) < LENGTH ([] : (A)list) ==> (nth (modified [] n (v : A)) n) = v");
    thm th4 = rewrite_rule(refl(l), rewrite(th3, tm3));
    thm basis = gen(n, th4);

    thm asmp = assume(goal);
    
    term goal2 = parse_term("(n : num) < LENGTH (CONS (h : A) l) ==> (nth (modified (CONS h l) n (v : A)) n = v)");
    // show_induct_goal(n, goal2, num_INDUCTION);
    
    term tm4 = parse_term("nth (modified (CONS (h : A) l) 0 (v : A)) 0");
    thm th5 = rewrite(MODIFIED_DEF, tm4);
    thm th6 = rewrite_rule(NTH_DEF, th5);
    term tm5 = parse_term("0 < LENGTH (CONS (h : A) l)");
    thm basis2 = disch(th6, tm5);

    thm asmp2 = assume(goal2);
    term asmp3_tm = parse_term("SUC (n : num) < LENGTH (CONS (h : A) l)");
    thm asmp3 = assume(asmp3_tm);
    thm th7 = rewrite_rule(LENGTH, asmp3);
    term tm6 = parse_term("!(a : num) (b : num). SUC a < SUC b ==> a < b");
    thm th8 = arith_rule(tm6);
    thm th9 = mp(th8, th7);
    thm th10 = mp(asmp, th9);
    term tm7 = parse_term("nth (modified (CONS (h : A) l) (SUC (n : num)) (v : A)) (SUC n) = v");
    thm th11 = rewrite(MODIFIED_DEF, tm7);
    thm th12 = rewrite_rule(NTH_DEF, th11);
    thm th13 = once_rewrite_rule(symm(th12), th10);
    thm th14 = disch(th13, asmp3_tm);
    thm th15 = disch(th14, goal2);
    thm step2 = gen(n, th15);

    thm goal2_th = mp(num_INDUCTION, conjunct(basis2, step2));

    thm th16 = disch(goal2_th, goal);
    thm th17 = gen(l, th16);
    term h = parse_term("h : A");
    thm step = gen(h, th17);

    thm goal_th = gen(v, mp(list_INDUCT, conjunct(basis, step)));
    return goal_th;
}

/*
    n < LENGTH l
==> ~(m = n)
==> (nth (modified l n v) m) = nth l m
*/
thm modified_mth()
{
    term l = parse_term("l : (A)list");
    term n = parse_term("n : num");
    term m = parse_term("m : num");
    term v = parse_term("v : A");
    term goal = parse_term("!(n : num) (m : num). n < LENGTH (l : (A)list) ==> ~(m = n) ==> (nth (modified l n (v : A)) m) = nth l m");
    // show_induct_goal(l, goal, list_INDUCT);

    term tm1 = parse_term("(n : num) < LENGTH ([] : (A)list)");
    thm LENGTH = get_theorem("LENGTH");
    thm th1 = rewrite(LENGTH, tm1);
    term tm2 = parse_term("(n:num) < 0 <=> F");
    thm th2 = arith_rule(tm2);
    thm th3 = trans(th1, th2);
    term tm3 = parse_term("(n : num) < LENGTH ([] : (A)list) ==> ~(m = n) ==> (nth (modified [] n (v : A)) m) = nth [] m");
    thm th4 = rewrite_rule(refl(l), rewrite(th3, tm3));
    thm basis = gen(n, gen(m, th4));

    thm asmp = assume(goal);
    
    term asmp1 = parse_term("(n : num) < LENGTH (CONS (h : A) l)");
    term asmp2 = parse_term("~((m : num) = n)");
    term goal2 = parse_term("nth (modified (CONS h l) n (v : A)) m = nth (CONS h l) m");
    term goal3 = parse_term("(n : num) < LENGTH (CONS (h : A) l) ==> ~(m = n) ==> nth (modified (CONS h l) n (v : A)) m = nth (CONS h l) m");

    thm n_CASES = spec(n, num_CASES);
    thm m_CASES = spec(m, num_CASES);
    term n0 = parse_term("(n : num) = 0");
    term nS = parse_term("n = SUC n'");
    term m0 = parse_term("(m : num) = 0");
    term mS = parse_term("m = SUC m'");
    thm asmpn0 = assume(n0);
    thm asmpnS = assume(nS);
    thm asmpm0 = assume(m0);
    thm asmpmS = assume(mS);
    
    term tm4 = parse_term("~((m : num) = n)");
    term tm5 = parse_term("~((m : num) = 0)");
    thm th5 = rewrite_refl(asmpn0, tm4, tm5);
    thm th6 = rewrite(asmpm0, tm5);
    thm th7 = trans(th5, th6);
    thm thn0m0 = rewrite_rule(refl(l), rewrite(th7, goal3));
    
    thm th10 = rewrite(asmpn0, goal2);
    thm th11 = rewrite_after(asmpmS, th10);
    thm th12 = rewrite_after(MODIFIED_DEF, th11);
    thm th13 = rewrite_after(NTH_DEF, th12);
    thm th14 = rewrite_rule(refl(l), th13);
    thm thn0mS = choose(parse_term("m' : num"), disch(disch(th14, asmp2), asmp1));

    thm thn0 = disj_cases(m_CASES, thn0m0, thn0mS);

    thm th15 = rewrite(asmpnS, goal2);
    thm th16 = rewrite_after(asmpm0, th15);
    thm th17 = rewrite_after(MODIFIED_DEF, th16);
    thm th18 = rewrite_after(NTH_DEF, th17);
    thm th19 = rewrite_rule(refl(l), th18);
    thm thnSm0 = disch(disch(th19, asmp2), asmp1);

    thm th20 = rewrite(asmpnS, goal3);
    thm th21 = rewrite_after(asmpmS, th20);
    thm th22 = rewrite_after(MODIFIED_DEF, th21);
    thm th23 = rewrite_after(NTH_DEF, th22);
    thm th24 = rewrite_after(LENGTH, th23);
    term tm6 = parse_term("~(SUC m' = SUC n') ==> ~(m' = n')");
    thm th25 = undisch(arith_rule(tm6));
    term tm7 = parse_term("SUC n' < SUC (LENGTH (l : (A)list)) ==> n' < (LENGTH l)");
    thm th26 = undisch(arith_rule(tm7));
    thm th27 = mp(mp(assume(goal), th26), th25);
    thm th28 = disch(th27, parse_term("~(SUC m' = SUC n')"));
    thm th29 = disch(th28, parse_term("SUC n' < SUC (LENGTH (l : (A)list))"));
    thm th30 = rewrite_rule(symm(th24), th29);
    thm th31 = choose(parse_term("m' : num"), disch(th30, goal));
    thm thnSmS = undisch(th31);

    thm th32 = disj_cases(m_CASES, thnSm0, thnSmS);
    thm th33 = choose(parse_term("n' : num"), disch(th32, goal));
    thm thnS = undisch(th33);

    thm th34 = disj_cases(n_CASES, thn0, thnS);
    thm th35 = gen(n, gen(m, th34));
    thm th36 = disch(th35, goal);
    thm step = gen(parse_term("h : A"), gen(l, th36));

    thm goal_th = gen(v, mp(list_INDUCT, conjunct(basis, step)));

    return goal_th;
}

thm modified_taken_restn_lemma(term goal, term subgoal, thm DEF)
{
    term l = parse_term("l : (A)list");

    thm LENGTH = get_theorem("LENGTH");

    // basis
    term basis_goal = rewrite_term(parse_term("(l : (A)list) = []"), goal);
    thm th1 = rewrite(LENGTH, basis_goal);
    thm th2 = arith_rule(parse_term("n < 0 <=> F"));
    thm th3 = rewrite_after(th2, th1);
    thm basis = simp(th3);

    // step
    thm step_asmp = assume(goal);
    term step_goal = rewrite_term(parse_term("l' = (l : (A)list)"), 
                    rewrite_term(parse_term("(l : (A)list) = CONS h l'"), goal));
    thm th4 = rewrite(LENGTH, step_goal);
    term subasmp = parse_term("n < LENGTH (CONS (h : A) l)");
    // case0
    term case0 = parse_term("n = 0");
    thm th5 = rewrite(assume(case0), subgoal);
    thm th6 = rewrite_after(DEF, rewrite_after(MODIFIED_DEF, th5));
    thm thcase0 = disch(simp(th6), subasmp);
    // caseS
    term caseS = parse_term("n = SUC n'");
    thm th7 = rewrite(assume(caseS), subgoal);
    thm th8 = rewrite_after(MODIFIED_DEF, th7);
    thm th9 = rewrite_after(DEF, th8);
    thm th10 = assume(subasmp);
    thm th11 = rewrite_rule(assume(caseS), th10);
    thm th12 = rewrite_rule(LENGTH, th11);
    thm th13 = arith_rule(parse_term("SUC n' < SUC (LENGTH l) ==> n' < LENGTH (l : (A)list)"));
    thm asmp_ = mp(th13, th12);
    thm th14 = mp(step_asmp, asmp_);
    thm th15 = rewrite_after(th14, th9);
    thm th16 = disch(simp(th15), subasmp);
    thm thcaseS = undisch(choose(parse_term("n' : num"), disch(th16, goal)));
    // merge
    term n = parse_term("n : num");
    thm th17 = disj_cases(spec(n, num_CASES), thcase0, thcaseS);
    thm th18 = gen(n, gen(parse_term("v : A"), th17));
    thm th19 = disch(th18, goal);
    thm step = gen(parse_term("h : A"), gen(l, th19));

    thm th = mp(list_INDUCT, conjunct(basis, step));
    return th;
}

/*
    n < LENGTH l
==> (take (modified l n v) n) = (take l n)
*/
thm modified_taken()
{
    term goal = parse_term("! (n : num) (v : A). \
        (n < LENGTH l) ==> ((take (modified l n v) n) = (take l n))");
    term subgoal = parse_term("take (modified (CONS (h : A) l) n v) n == take (CONS h l) n");
    return modified_taken_restn_lemma(goal, subgoal, TAKE_DEF);
}

/*
    n < LENGTH l
==> (rest (modified l n v) (SUC n)) = (rest l (SUC n))
*/
thm modified_restn()
{
    term goal = parse_term("! (n : num) (v : A). \
        (n < LENGTH l) ==> ((rest (modified l n v) (SUC n)) = (rest l (SUC n)))");
    term subgoal = parse_term("rest (modified (CONS (h : A) l) n v) (SUC n) == rest (CONS h l) (SUC n)");
    return modified_taken_restn_lemma(goal, subgoal, REST_DEF);
}

/*
    LENGTH (modified l n v) = LENGTH l
*/
thm modified_len()
{
    term l = parse_term("l : (A)list");
    term goal = parse_term("! n v. LENGTH (modified l n (v : A)) = LENGTH l");
    // show_induct_goal(l, goal, list_INDUCT);

    thm LENGTH = get_theorem("LENGTH");

    // basis
    term basis_goal = rewrite_term(parse_term("(l : (A)list) = []"), goal);
    thm th1 = rewrite(MODIFIED_DEF, basis_goal);
    thm th2 = rewrite_after(LENGTH, th1);
    thm basis = simp(th2);

    // step
    thm step_asmp = assume(goal);
    term step_goal = parse_term("! v. LENGTH (modified (CONS h l) n (v : A)) = LENGTH (CONS h l)");
    // case0
    term case0 = parse_term("n = 0");
    thm th3 = rewrite(assume(case0), step_goal);
    thm th4 = rewrite_after(MODIFIED_DEF, th3);
    thm th5 = rewrite_after(LENGTH, th4);
    thm thcase0 = simp(th5);
    // caseS
    term caseS = parse_term("n = SUC n'");
    thm th6 = rewrite(assume(caseS), step_goal);
    thm th7 = rewrite_after(MODIFIED_DEF, th6);
    thm th8 = rewrite_after(LENGTH, th7);
    thm th9 = spec(parse_term("n' : num"), assume(goal));
    thm th10 = rewrite_after(th9, th8);
    thm th11 = simp(th10);
    thm thcaseS = undisch(choose(parse_term("n' : num"), disch(th11, goal)));
    // merge
    term n = parse_term("n : num");
    thm th12 = disj_cases(spec(n, num_CASES), thcase0, thcaseS);
    thm th13 = gen(n, th12);
    thm th14 = disch(th13, goal);
    thm step = gen(parse_term("h : A"), gen(l, th14));

    thm th = mp(list_INDUCT, conjunct(basis, step));
    return th;
}

/*
    i < LENGTH l
==> free_head v = free_head (nth l i)
==> ifilter l = ifilter (modified l i v)
*/
thm filter_inv()
{
    term j = parse_term("j : num");
    term asmp1_tm = parse_term("(i : num) < LENGTH (l : (num#num)list)");
    term asmp2_tm = parse_term("free_head v = free_head (nth l i)");
    term goal = parse_term("ifilter l = ifilter (modified l i v)");
    thm asmp1 = assume(asmp1_tm);
    thm asmp2 = assume(asmp2_tm);
    term tm1 = parse_term("(ifilter (modified l i v)) j");
    term tm2 = parse_term("(ifilter l) j");
    thm th1 = rewrite(IFILTER_DEF, tm1);
    thm th2 = rewrite(IFILTER_DEF, tm2);

    term casep = parse_term("id2i j = (i : num)");
    term casen = mk_comb(parse_term("~"), casep);

    thm asmpp = assume(casep);
    thm th3 = rewrite_rule(asmpp, th1);
    thm th4 = rewrite_rule(mp(modified_nth(), asmp1), th3);
    thm th5 = rewrite_rule(asmp2, th4);
    thm th6 = rewrite_rule(asmpp, th2);
    thm thp = trans(th6, symm(th5));

    thm asmpn = assume(casen);
    thm th7 = mp(mp(modified_mth(), asmp1), asmpn);
    thm th8 = rewrite_rule(th7, th1);
    thm thn = trans(th2, symm(th8));

    thm th9 = merge_disj_cases(casep, thp, thn);
    thm EQ_EXT = get_theorem("EQ_EXT");
    term tm3 = parse_term("ifilter l");
    term tm4 = parse_term("ifilter (modified l i v)");
    thm th10 = spec(tm4, spec(tm3, EQ_EXT));
    thm th11 = mp(th10, gen(j, th9));
    thm th = disch(disch(th11, asmp2_tm), asmp1_tm);
    
    return th;
}

/*
    start <= end
==> len = end - start
==> i < len
==> len = LENGTH l
==> ~filter (i2id i)
==> free_area_repr filter start end l =
    free_area_repr filter start end (modified l i v)
*/
thm far_inv()
{
    term asmp0_tm = parse_term("(start : num) <= end");
    term asmp1_tm = parse_term("(len : num) = end - start");
    term asmp2_tm = parse_term("(i : num) < len");
    term asmp3_tm = parse_term("len = LENGTH (l : (num#num)list)");
    term asmp4_tm = parse_term("~((filter : num -> bool) (i2id i))");
    thm asmp0 = assume(asmp0_tm);
    thm asmp1 = assume(asmp1_tm);
    thm asmp2 = rewrite_rule(asmp1, assume(asmp2_tm));
    thm asmp3 = rewrite_rule(asmp1, assume(asmp3_tm));
    thm asmp4 = rewrite_rule(I2ID_DEF, assume(asmp4_tm));
    term lhs = parse_term("free_area_repr filter start end l");
    term rhs = parse_term("free_area_repr filter start end (modified l i v)");
    thm th1 = mp(breaknth_list_sepconj(), FREE_AREA_REPR_DEF);
    thm th2 = mp(th1, asmp2);
    term tm1 = parse_term("end - start <= (end : num)");
    thm th3 = arith_rule(tm1);
    thm th4 = mp(th2, th3);

    thm th5 = mp(th4, asmp3);
    term tm2 = parse_term("start <= end ==> end - (end - start) = (start : num)");
    thm th6 = mp(arith_rule(tm2), asmp0);
    thm th7 = rewrite_rule(th6, th5);
    thm th8 = rewrite(th7, lhs);

    term tm3 = parse_term("LENGTH (modified l i (v : num#num))");
    thm th9 = rewrite(modified_len(), tm3);
    thm th10 = trans(asmp3, symm(th9));
    thm th11 = mp(th4, th10);
    thm th12 = rewrite_rule(th6, th11);
    thm th13 = rewrite(th12, rhs);
    thm th14 = rewrite_rule(asmp3, asmp2);
    thm th15 = rewrite_rule(mp(modified_taken(), th14), th13);
    thm th16 = rewrite_rule(mp(modified_restn(), th14), th15);
    thm th17 = rewrite_rule(mp(modified_nth(), th14), th16);
    thm th18 = rewrite_rule(asmp4, th17);
    thm th19 = rewrite_rule(asmp4, th8);
    thm th20 = trans(th19, symm(th18));
    thm th21 = disch(disch(disch(disch(disch(th20, asmp4_tm), asmp3_tm), asmp2_tm), asmp1_tm), asmp0_tm);
    thm th = gen(parse_term("l : (num#num)list"), gen(parse_term("i : num"), gen(parse_term("v : num#num"), gen(parse_term("filter : num -> bool"), th21))));
    return th;
}

thm dn_inv_lemma(term goal, thm asmp1, thm asmp2, thm asmp3, term casep_tm, term casen_tm)
{
    thm th1 = rewrite(DLIST_NODE_ONE_DEF, goal);

    thm casep = assume(casep_tm);
    thm th2 = rewrite_after(casep, th1);
    thm th3 = rewrite_after(asmp3, th2);
    thm th4 = rewrite_after(asmp2, th3);
    thm th5 = rewrite_after(disconj1, th4);
    thm thp = simp(th5);

    thm casen = assume(casen_tm);
    thm th6 = mp(mp(modified_mth(), asmp1), casen);
    thm th7 = rewrite_after(th6, th1);
    thm th8 = rewrite_after(asmp3, th7);
    thm thn = simp(th8);

    thm th = merge_disj_cases(casep_tm, thp, thn);

    return th;
}

/*
    i < LENGTH l
==> ~free_head (nth l i)
==> dlist_node addr (ifilter l) l dl hl lo hi dl'
==> dlist_node addr (ifilter l) (modified l i v) dl hl lo hi dl'
*/
thm dn_inv()
{
    term dl_ = parse_term("dl' : (addr#addr)list");
    term goal = parse_term("! l hl dl i v addr lo hi. \
        i < LENGTH l \
        ==> ~free_head (nth l i) \
        ==> dlist_node addr (ifilter l) l dl hl lo hi dl' \
        ==> dlist_node addr (ifilter l) (modified l i v) dl hl lo hi dl'");
    // show_induct_goal(dl_, goal, list_INDUCT);

    term tm1 = parse_term("(dl' : (addr#addr)list) = []");
    term basis_goal = rewrite_term(tm1, goal);
    thm th1 = rewrite(DLIST_NODE_DEF, basis_goal);
    thm basis = rewrite_rule(refl(dl_), th1);

    term asmp1_tm = parse_term("i < LENGTH (l : (num#num)list)");
    term asmp2_tm = parse_term("~free_head (nth l i)");
    term asmp3_tm = parse_term("dlist_node addr (ifilter l) l dl hl lo hi dl'");
    thm asmp1 = assume(asmp1_tm);
    thm asmp2 = assume(asmp2_tm);
    thm asmp3 = assume(asmp3_tm);

    thm ind_asmp = assume(goal);
    term ind_goal = parse_term(" \
        dlist_node addr (ifilter l) l dl hl lo hi (CONS h dl') \
    ==> dlist_node addr (ifilter l) (modified l i v) dl hl lo hi (CONS h dl')");
    thm th2 = rewrite(DLIST_NODE_DEF, ind_goal);
    thm th3 = rewrite_rule(IFILTER_DEF, th2);

    term casep = parse_term("id2i lo = i");
    term casen = mk_comb(parse_term("~"), casep);

    thm th4 = assume(casep);
    thm th5 = rewrite_rule(th4, th3);
    thm th6 = rewrite_rule(asmp2, th5);
    thm th7 = mp(mp(ind_asmp, asmp1), asmp2);
    thm thp = rewrite_rule(th7, th6);

    thm th8 = assume(casen);
    thm th9 = mp(mp(modified_mth(), asmp1), th8);
    
    term goal1 = parse_term("dlist_node_one addr l dl hl lo h NXT PRV \
                        ==> dlist_node_one addr (modified l i v) dl hl lo h NXT PRV");
    term case1p_tm = parse_term("vi2i (NXT h) = i");
    term case1n_tm = mk_comb(parse_term("~"), case1p_tm);
    thm solve1 = dn_inv_lemma(goal1, asmp1, asmp2, th9, case1p_tm, case1n_tm);

    term goal2 = parse_term("dlist_node_one addr l dl hl lo h PRV NXT \
                        ==> dlist_node_one addr (modified l i v) dl hl lo h PRV NXT");
    term case2p_tm = parse_term("vi2i (PRV h) = i");
    term case2n_tm = mk_comb(parse_term("~"), case2p_tm);
    thm solve2 = dn_inv_lemma(goal2, asmp1, asmp2, th9, case2p_tm, case2n_tm);

    term cond = parse_term("free_head (nth l (id2i lo))");
    thm th10 = impl_conj_mono(solve1, solve2);
    thm th11 = disch(assume(parse_term("T")), parse_term("T"));
    thm th12 = impl_if_mono(cond, th10, th11);

    term goal3 = parse_term("dlist_node addr (ifilter l) l dl hl (SUC lo) hi dl' \
                        ==> dlist_node addr (ifilter l) (modified l i v) dl hl (SUC lo) hi dl'");
    thm solve3 = rewrite_rule(refl(dl_), rewrite(th7, goal3));
    
    thm th13 = impl_conj_mono(th12, solve3);
    thm th14 = rewrite_after(th13, th3);
    thm thn = simp(th14);

    thm th16 = merge_disj_cases(casep, thp, thn);
    thm th17 = disch(disch(th16, asmp2_tm), asmp1_tm);
    thm th18 = gen(parse_term("l : (num#num)list"), gen(parse_term("hl : (addr#addr)list"), 
                gen(parse_term("dl : (addr#addr)list"), gen(parse_term("i : num"), 
                gen(parse_term("v : num#num"), gen(parse_term("addr : addr"), 
                gen(parse_term("lo : num"), gen(parse_term("hi : num"), th17))))))));
    thm th19 = disch(th18, goal);
    thm step = gen(parse_term("h : addr#addr"), gen(dl_, th19));

    thm th = mp(list_INDUCT, conjunct(basis, step));

    return th;
}

/*
    i < LENGTH l
==> ~free_head (nth l i)
==> dlist_head addr l dl order maxorder hl
==> dlist_head addr (modified l i v) dl order maxorder hl
*/
thm dh_inv()
{
    term hl = parse_term("hl : (addr#addr)list");
    term goal = parse_term("! l dl i v addr order maxorder. \
        i < LENGTH l \
        ==> ~free_head (nth l i) \
        ==> dlist_head addr l dl order maxorder hl \
        ==> dlist_head addr (modified l i v) dl order maxorder hl");
    // show_induct_goal(hl, goal, list_INDUCT);

    term tm1 = parse_term("(hl : (addr#addr)list) = []");
    term basis_goal = rewrite_term(tm1, goal);
    thm th1 = rewrite(DLIST_HEAD_DEF, basis_goal);
    thm basis = rewrite_rule(refl(hl), th1);

    thm ind_asmp = assume(goal);
    term ind_goal = parse_term(" \
        dlist_head addr l dl order maxorder (CONS h hl) \
    ==> dlist_head addr (modified l i v) dl order maxorder (CONS h hl)");
    thm th2 = rewrite(DLIST_HEAD_DEF, ind_goal);

    term asmp1_tm = parse_term("i < LENGTH (l : (num#num)list)");
    term asmp2_tm = parse_term("~free_head (nth l i)");
    thm asmp1 = assume(asmp1_tm);
    thm asmp2 = assume(asmp2_tm);

    term goal1 = parse_term("dlist_head_one addr l dl order h \
                        ==> dlist_head_one addr (modified l i v) dl order h");
    term case1p_tm = parse_term("vi2i (NXT h) = i");
    term case1n_tm = mk_comb(parse_term("~"), case1p_tm);
    term case2p_tm = parse_term("vi2i (PRV h) = i");
    term case2n_tm = mk_comb(parse_term("~"), case2p_tm);
    thm case1p = assume(case1p_tm);
    thm case1n = assume(case1n_tm);
    thm case2p = assume(case2p_tm);
    thm case2n = assume(case2n_tm);

    thm th3 = rewrite_after(DLIST_HEAD_HALF_DEF, rewrite(DLIST_HEAD_ONE_DEF, goal1));
    thm th4 = rewrite_after(case1p, th3);
    thm th5 = rewrite_after(asmp2, th4);
    thm th6 = rewrite_after(disconj1, th5);
    thm thp = simp(th6);

    thm th7 = rewrite_after(case2p, th3);
    thm th8 = rewrite_after(asmp2, th7);
    thm th9 = rewrite_after(disconj1, th8);
    thm thnp = simp(th9);

    thm th10 = mp(mp(modified_mth(), asmp1), case1n);
    thm th11 = mp(mp(modified_mth(), asmp1), case2n);
    thm th12 = rewrite_after(th10, th3);
    thm th13 = rewrite_after(th11, th12);
    thm thnn = simp(th13);
    thm thn = merge_disj_cases(case2p_tm, thnp, thnn);
    thm solve1 = merge_disj_cases(case1p_tm, thp, thn);

    term goal2 = parse_term("dlist_head addr l dl (SUC order) maxorder hl \
                        ==> dlist_head addr (modified l i v) dl (SUC order) maxorder hl");
    thm th14 = mp(mp(ind_asmp, asmp1), asmp2);
    thm solve2 = simp(rewrite(th14, goal2));

    thm th15 = rewrite_rule(impl_conj_mono(solve1, solve2), th2);
    thm th16 = disch(disch(th15, asmp2_tm), asmp1_tm);
    thm th17 = gen(parse_term("l : (num#num)list"), gen(parse_term("dl : (addr#addr)list"), 
                gen(parse_term("i : num"), gen(parse_term("v : num#num"), 
                gen(parse_term("addr : addr"), gen(parse_term("order : num"), 
                gen(parse_term("maxorder : num"), th16)))))));
    thm th18 = disch(th17, goal);
    thm step = gen(parse_term("h : addr#addr"), gen(hl, th18));

    thm th = mp(list_INDUCT, conjunct(basis, step));

    return th;
}

/*
    (i2id i < lo) ==> (i < LENGTH l)
==> (free_area_repr (ifilter l) lo hi l' =
    free_area_repr (ifilter (modified l i (0, order))) lo hi l')
*/
thm far_lemma()
{   
    term l_ = parse_term("l' : (num#num)list");
    term goal = parse_term("! l i lo hi order. \
        (i2id i < lo) ==> (i < LENGTH l) \
        ==> (free_area_repr (ifilter l) lo hi l' -|- \
            free_area_repr (ifilter (modified l i (0, order))) lo hi l')");
    // show_induct_goal(l_, goal, list_INDUCT);

    term asmp1_tm = parse_term("i2id i < (lo : num)");
    term asmp2_tm = parse_term("i < LENGTH (l : (num#num)list)");
    thm asmp1 = rewrite_rule(I2ID_DEF, assume(asmp1_tm));
    thm asmp2 = assume(asmp2_tm);

    // basis
    term basis_goal = rewrite_term(parse_term("(l' : (num#num)list) = []"), goal);
    thm th1 = rewrite(FREE_AREA_REPR_DEF, basis_goal);
    thm basis = simp(th1);

    // step
    thm ind_asmp = assume(goal);
    term ind_goal = parse_term("free_area_repr (ifilter l) lo hi (CONS h l') -|- \
            free_area_repr (ifilter (modified l i (0, order))) lo hi (CONS h l')");
    thm th2 = rewrite(FREE_AREA_REPR_DEF, ind_goal);
    thm th3 = rewrite_after(IFILTER_DEF, th2);
    thm th4 = rewrite_after(ID2I_DEF, th3);
    term tm1 = parse_term("start + i < (lo : num) ==> ~(lo - start = i)");
    thm th5 = arith_rule(tm1);
    thm th6 = mp(mp(modified_mth(), asmp2), mp(th5, asmp1));
    thm th7 = rewrite_after(th6, th4);
    term tm2 = parse_term("i2id i < lo ==> i2id i < SUC lo");
    thm th8 = arith_rule(tm2);
    thm th9 = mp(mp(ind_asmp, mp(th8, assume(asmp1_tm))), asmp2);
    thm th10 = rewrite_after(th9, th7);
    thm th11 = simp(th10);
    thm th12 = disch(disch(th11, asmp2_tm), asmp1_tm);
    thm th13 = gen(parse_term("l : (num#num)list"), gen(parse_term("i : num"), 
                gen(parse_term("lo : num"), gen(parse_term("hi : num"), 
                gen(parse_term("order : num"), th12)))));
    thm th14 = disch(th13, goal);
    thm step = gen(parse_term("h : num#num"), gen(l_, th14));

    thm th = mp(list_INDUCT, conjunct(basis, step));

    return th;
}

/*
    start <= lo ==> lo <= i2id i ==> i2id i < hi
==> i < LENGTH l
==> ifilter l (i2id i)
==> nth l i = nth l' ((i2id i) - lo)
==> free_area_repr (ifilter l) lo hi l' = (
    free_area_repr (ifilter (modified l i (0, NO_ORDER))) lo hi l' **
    store_zero_array (id2vi (i2id i)) (PTR_SIZE * 2) (PAGE_SIZE * (2 EXP (ORD (nth l i)))) (PAGE_SIZE * (2 EXP (ORD (nth l i))) - PTR_SIZE * 2))
*/
thm far_split()
{
    term l_ = parse_term("l' : (num#num)list");
    term goal = parse_term("! (l : (num#num)list) lo hi i. \
        (start : num) <= lo ==> lo <= i2id i ==> i2id i < hi \
    ==> i < LENGTH l \
    ==> ifilter l (i2id i) \
    ==> nth l i = nth l' ((i2id i) - lo) \
    ==> free_area_repr (ifilter l) lo hi l' = ( \
        (free_area_repr (ifilter (modified l i (0, NO_ORDER))) lo hi l') ** \
        (store_zero_array (id2vi (i2id i)) (PTR_SIZE * 2) (PAGE_SIZE * (2 EXP (ORD (nth l i)))) (PAGE_SIZE * (2 EXP (ORD (nth l i))) - PTR_SIZE * 2)))");
    // show_induct_goal(l_, goal, list_INDUCT);

    term asmp1_tm = parse_term("(start : num) <= lo");
    term asmp2_tm = parse_term("(lo : num) <= i2id i");
    term asmp3_tm = parse_term("i2id i < (hi : num)");
    term asmp4_tm = parse_term("i < LENGTH (l : (num#num)list)");
    term asmp5_tm = parse_term("ifilter l (i2id i)");
    thm asmp1 = assume(asmp1_tm);
    thm asmp2 = assume(asmp2_tm);
    thm asmp3 = assume(asmp3_tm);
    thm asmp4 = assume(asmp4_tm);
    thm asmp5 = assume(asmp5_tm);

    // basis
    term tm1 = parse_term("nth (l : (num#num)list) i = nth l' ((i2id i) - lo) \
    ==> free_area_repr (ifilter l) lo hi l' = ( \
        (free_area_repr (ifilter (modified l i (0, NO_ORDER))) lo hi l') ** \
        (store_zero_array (id2vi (i2id i)) (PTR_SIZE * 2) (PAGE_SIZE * (2 EXP (ORD (nth l i)))) (PAGE_SIZE * (2 EXP (ORD (nth l i))) - PTR_SIZE * 2)))");
    term tm2 = rewrite_term(parse_term("(l' : (num#num)list) = []"), tm1);
    thm th1 = rewrite(FREE_AREA_REPR_DEF, tm2);
    term tm3 = parse_term("(lo : num) <= i2id i /\\ i2id i < hi ==> ~(lo = hi)");
    thm th2 = arith_rule(tm3);
    thm th3 = mp(th2, conjunct(asmp2, asmp3));
    thm th4 = rewrite_after(hfact_def, rewrite_after(th3, th1));
    thm th5 = rewrite_after(sepand_f, th4);
    thm th6 = rewrite_after(sepconj_f, th5);
    thm th7 = simp(th6);
    thm th8 = disch(disch(disch(disch(disch(th7, asmp5_tm), asmp4_tm), asmp3_tm), asmp2_tm), asmp1_tm);
    thm basis = gen(parse_term("l : (num#num)list"), gen(parse_term("lo : num"), 
                gen(parse_term("hi : num"), gen(parse_term("i : num"), th8))));
    
    // step
    term goal2 = parse_term("nth (l : (num#num)list) i == nth (CONS h l') ((i2id i) - lo) \
    ==> free_area_repr (ifilter l) lo hi (CONS h l') = ( \
        (free_area_repr (ifilter (modified l i (0, NO_ORDER))) lo hi (CONS h l')) ** \
        (store_zero_array (id2vi (i2id i)) (PTR_SIZE * 2) (PAGE_SIZE * (2 EXP (ORD (nth l i)))) (PAGE_SIZE * (2 EXP (ORD (nth l i))) - PTR_SIZE * 2)))");
    thm th9 = rewrite(FREE_AREA_REPR_DEF, goal2);
    
    term casep_tm = parse_term("(lo : num) = i2id i");
    term casen_tm = mk_comb(parse_term("~"), casep_tm);
    thm casep = assume(casep_tm);
    thm casen = assume(casen_tm);

    // casep
    thm th10 = rewrite_after(casep, th9);
    thm th11 = rewrite_after(asmp5, th10);
    thm th12 = rewrite_after(IFILTER_DEF, th11);
    thm th13 = rewrite_after(i2id2i(), th12);
    thm th14 = rewrite_after(mp(modified_nth(), asmp4), th13);
    thm th15 = rewrite_after(FREE_HEAD_DEF, th14);
    thm th16 = rewrite_after(ORD_DEF, th15);
    term tm4 = parse_term("(i2id i) - (i2id i) = 0");
    thm th17 = arith_rule(tm4);
    thm th18 = rewrite_after(th17, th16);
    thm th19 = rewrite_after(NTH_DEF, th18);
    thm th20 = rewrite_after(hsep_hemp_left, th19);
    // break into subgoals
    term tm5 = parse_term("nth l i = (h : num#num)");
    thm th21 = assume(tm5);
    term tm6 = parse_term("store_zero_array (id2vi (i2id i)) (PTR_SIZE * 2) \
        (PAGE_SIZE * 2 EXP SND (h : num#num)) \
        (PAGE_SIZE * 2 EXP SND (h : num#num) - PTR_SIZE * 2)");
    thm th22 = rewrite(symm(th21), tm6);
    term tm7 = parse_term("i2id i < SUC (i2id i)");
    thm th23 = arith_rule(tm7);
    thm th24 = mp(mp(far_lemma(), th23), asmp4);
    term tm8 = parse_term("free_area_repr (ifilter l) (SUC (i2id i)) hi l'");
    thm th25 = rewrite(th24, tm8);
    term tm9 = mk_comb(mk_comb(parse_term("**"), tm6), tm8);
    thm th26 = rewrite(th22, tm9);
    thm th27 = rewrite_after(th25, th26);
    thm th28 = rewrite_after(hsep_comm, th27);
    thm th29 = disch(th28, tm5);
    thm th30 = rewrite_after(th29, th20);
    thm thp = simp(th30);

    // casen
    thm th32 = rewrite_after(IFILTER_DEF, th9);
    thm th33 = rewrite_after(ID2I_DEF, th32);
    term tm10 = parse_term("(start : num) <= lo ==> ~(lo = start + i) ==> ~((lo - start) = i)");
    thm th34 = rewrite_rule(symm(I2ID_DEF), arith_rule(tm10));
    thm th35 = mp(mp(th34, asmp1), casen);
    thm th36 = mp(mp(modified_mth(), asmp4), th35);
    thm th37 = rewrite_after(th36, th33);
    term tm11 = parse_term("start <= lo ==> start <= SUC lo");
    thm th38 = arith_rule(tm11);
    thm asmp1_ = mp(th38, asmp1);
    term tm12 = parse_term("lo <= i2id i ==> ~(lo = i2id i) ==> SUC lo <= i2id i");
    thm th39 = arith_rule(tm12);
    thm asmp2_ = mp(mp(th39, asmp2), casen);
    thm th40 = mp(mp(mp(mp(mp(assume(goal), asmp1_), asmp2_), asmp3), asmp4), asmp5);
    term tm15 = parse_term("SUC lo <= i2id i ==> ((i2id i) - lo) = SUC ((i2id i) - SUC lo)");
    thm th47 = arith_rule(tm15);
    thm th48 = mp(th47, asmp2_);
    term tm13 = parse_term("nth (l : (num#num)list) i == nth (CONS h l') ((i2id i) - (lo : num))");
    thm th49 = rewrite_rule(th48, assume(tm13));
    thm th50 = rewrite_rule(NTH_DEF, th49);
    thm th41 = mp(th40, th50);
    term tm14 = dest_bin_fst_comb(dest_bin_snd_comb(dest_bin_snd_comb(concl(th37))));
    thm th42 = rewrite(th41, tm14);
    thm th43 = disch(th42, tm13);
    thm th44 = rewrite_after(hsep_assoc, th37);
    thm th45 = rewrite_after(th43, th44);
    thm thn = simp(th45);
    
    // merge
    thm th46 = merge_disj_cases(casep_tm, thp, thn);
    thm th52 = disch(disch(disch(disch(disch(th46, asmp5_tm), asmp4_tm), asmp3_tm), asmp2_tm), asmp1_tm);
    
    thm th53 = gen(parse_term("l : (num#num)list"), gen(parse_term("lo : num"), 
                gen(parse_term("hi : num"), gen(parse_term("i : num"), th52))));
    thm th54 = disch(th53, goal);
    thm step = gen(parse_term("h : num#num"), gen(l_, th54));

    thm th = mp(list_INDUCT, conjunct(basis, step));
    return th;
}

/*
    start <= lo ==> lo <= i2id i ==> i2id i < hi
==> i < LENGTH l
==> ~(ifilter l (i2id i))
==> ~(order = NO_ORDER)
==> (nth l i = nth l' ((i2id i) - lo))
==> (free_area_repr (ifilter l) lo hi l' **
    store_zero_array (id2vi (i2id i)) (PTR_SIZE * 2) (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order) - PTR_SIZE * 2)) = 
    free_area_repr (ifilter (modified l i (0, order))) lo hi (modified l' ((i2id i) - lo) (0, order)))
*/
thm far_merge()
{
    term l_ = parse_term("l' : (num#num)list");
    term goal = parse_term("! (l : (num#num)list) lo hi i. \
        (start : num) <= lo ==> lo <= i2id i ==> i2id i < hi \
    ==> i < LENGTH l \
    ==> ~(ifilter l (i2id i)) \
    ==> ~(order = NO_ORDER) \
    ==> nth l i = nth l' ((i2id i) - lo) \
    ==> (free_area_repr (ifilter l) lo hi l' ** \
        store_zero_array (id2vi (i2id i)) (PTR_SIZE * 2) (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order) - PTR_SIZE * 2)) = \
        free_area_repr (ifilter (modified l i (0, order))) lo hi (modified l' ((i2id i) - lo) (0, order))");
    // show_induct_goal(l_, goal, list_INDUCT);

    term asmp1_tm = parse_term("(start : num) <= lo");
    term asmp2_tm = parse_term("(lo : num) <= i2id i");
    term asmp3_tm = parse_term("i2id i < (hi : num)");
    term asmp4_tm = parse_term("i < LENGTH (l : (num#num)list)");
    term asmp5_tm = parse_term("~(ifilter l (i2id i))");
    term asmp6_tm = parse_term("~((order : num) = NO_ORDER)");
    thm asmp1 = assume(asmp1_tm);
    thm asmp2 = assume(asmp2_tm);
    thm asmp3 = assume(asmp3_tm);
    thm asmp4 = assume(asmp4_tm);
    thm asmp5 = assume(asmp5_tm);
    thm asmp6 = assume(asmp6_tm);

    // basis
    term tm1 = parse_term("nth l i = nth l' ((i2id i) - lo) \
    ==> (free_area_repr (ifilter l) lo hi l' ** \
        store_zero_array (id2vi (i2id i)) (PTR_SIZE * 2) (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order) - PTR_SIZE * 2)) = \
        free_area_repr (ifilter (modified l i (0, order))) lo hi (modified l' ((i2id i) - lo) (0, order))");
    term tm2 = rewrite_term(parse_term("(l' : (num#num)list) = []"), tm1);
    thm th1 = rewrite_after(FREE_AREA_REPR_DEF, rewrite(MODIFIED_DEF, tm2));
    term tm3 = parse_term("(lo : num) <= i2id i /\\ i2id i < hi ==> ~(lo = hi)");
    thm th2 = arith_rule(tm3);
    thm th3 = mp(th2, conjunct(asmp2, asmp3));
    thm th4 = rewrite_after(hfact_def, rewrite_after(th3, th1));
    thm th5 = rewrite_after(sepand_f, th4);
    thm th6 = rewrite_after(sepconj_f, th5);
    thm th7 = simp(th6);
    thm th8 = disch(disch(disch(disch(disch(disch(th7, asmp6_tm), asmp5_tm), asmp4_tm), asmp3_tm), asmp2_tm), asmp1_tm);
    thm basis = gen(parse_term("l : (num#num)list"), gen(parse_term("lo : num"), 
                gen(parse_term("hi : num"), gen(parse_term("i : num"), th8))));
    
    // step
    term goal2 = parse_term("nth l i = nth (CONS h l') ((i2id i) - lo) \
    ==> (free_area_repr (ifilter l) lo hi (CONS h l') ** \
        store_zero_array (id2vi (i2id i)) (PTR_SIZE * 2) (PAGE_SIZE * (2 EXP order)) (PAGE_SIZE * (2 EXP order) - PTR_SIZE * 2)) = \
        free_area_repr (ifilter (modified l i (0, order))) lo hi (modified (CONS h l') ((i2id i) - lo) (0, order))");
    
    term casep_tm = parse_term("(lo : num) = i2id i");
    term casen_tm = mk_comb(parse_term("~"), casep_tm);
    thm casep = assume(casep_tm);
    thm casen = assume(casen_tm);

    // casep
    thm th9 = rewrite(casep, goal2);
    term tm4 = parse_term("(i2id i) - (i2id i) = 0");
    thm th10 = arith_rule(tm4);
    thm th11 = rewrite_after(th10, th9);
    thm th12 = rewrite_after(MODIFIED_DEF, th11);
    thm th13 = rewrite_after(FREE_AREA_REPR_DEF, th12);    
    thm th14 = rewrite_after(asmp5, th13);
    thm th15 = rewrite_after(IFILTER_DEF, th14);
    thm th18 = rewrite_after(i2id2i(), th15);
    thm th19 = rewrite_after(mp(modified_nth(), asmp4), th18);
    thm th20 = rewrite_after(FREE_HEAD_DEF, th19);
    thm th21 = rewrite_after(REF_DEF, th20);
    thm th22 = rewrite_after(ORD_DEF, th21);
    thm th23 = rewrite_after(asmp6, th22);
    thm th24 = rewrite_after(NTH_DEF, th23);
    thm th25 = rewrite_after(hsep_hemp_left, th24);
    // break into subgoals
    term tm6 = parse_term("store_zero_array (id2vi (i2id i)) (PTR_SIZE * 2) \
        (PAGE_SIZE * 2 EXP order) \
        (PAGE_SIZE * 2 EXP order - PTR_SIZE * 2)");
    term tm7 = parse_term("i2id i < SUC (i2id i)");
    thm th26 = arith_rule(tm7);
    thm th27 = mp(mp(far_lemma(), th26), asmp4);
    term tm8 = parse_term("free_area_repr (ifilter l) (SUC (i2id i)) hi l'");
    thm th28 = rewrite(th27, tm8);
    term tm9 = mk_comb(mk_comb(parse_term("**"), tm8), tm6);
    thm th29 = rewrite(spec(tm8, hsep_comm), tm9);
    thm th30 = rewrite_after(th28, th29);
    thm th31 = rewrite_after(th30, th25);
    thm thp = simp(th31);

    // casen
    term tm10 = parse_term("(start : num) <= lo ==> ~(lo = start + i) ==> ~((lo - start) = i)");
    thm th32 = arith_rule(tm10);
    thm th33 = mp(mp(th32, asmp1), rewrite_rule(I2ID_DEF, casen));
    term tm11 = parse_term("start <= lo ==> start <= SUC lo");
    thm th34 = arith_rule(tm11);
    thm asmp1_ = mp(th34, asmp1);
    term tm12 = parse_term("lo <= i2id i ==> ~(lo = i2id i) ==> SUC lo <= i2id i");
    thm th35 = arith_rule(tm12);
    thm asmp2_ = mp(mp(th35, asmp2), casen);
    term tm13 = parse_term("SUC lo <= i2id i ==> ((i2id i) - lo) = SUC ((i2id i) - SUC lo)");
    thm th36 = arith_rule(tm13);
    thm th37 = mp(th36, asmp2_);
    thm th38 = rewrite(th37, goal2);
    thm th39 = rewrite_after(MODIFIED_DEF, th38);
    thm th40 = rewrite_after(FREE_AREA_REPR_DEF, th39);
    thm th41 = rewrite_after(IFILTER_DEF, th40);
    thm th42 = rewrite_after(ID2I_DEF, th41);
    thm th43 = mp(mp(modified_mth(), asmp4), th33);
    thm th44 = rewrite_after(th43, th42);
    thm th45 = rewrite_after(NTH_DEF, th44);
    thm th46 = mp(mp(mp(mp(mp(mp(assume(goal), asmp1_), asmp2_), asmp3), asmp4), asmp5), asmp6);
    term tm14 = dest_bin_fst_comb(dest_bin_snd_comb(dest_bin_snd_comb(concl(th45))));
    thm th47 = rewrite(hsep_assoc, tm14);
    thm th48 = rewrite_after(undisch(th46), th47);
    term tm15 = parse_term("nth (l : (num#num)list) i == nth l' ((i2id i) - SUC lo)");
    thm th49 = disch(th48, tm15);
    thm th50 = rewrite_after(th49, th45);
    thm thn = simp(th50);

    // merge
    thm th51 = merge_disj_cases(casep_tm, thp, thn);
    thm th52 = disch(disch(disch(disch(disch(disch(th51, asmp6_tm), asmp5_tm), asmp4_tm), asmp3_tm), asmp2_tm), asmp1_tm);
    thm th53 = gen(parse_term("l : (num#num)list"), gen(parse_term("lo : num"), 
                gen(parse_term("hi : num"), gen(parse_term("i : num"), th52))));
    thm th54 = disch(th53, goal);
    thm step = gen(parse_term("h : num#num"), gen(l_, th54));

    thm th = mp(list_INDUCT, conjunct(basis, step));
    return th;
}

/*
    store_zero_array (addr + &i) lo hi n =
    store_zero_array addr (lo + i) (hi + i) n
*/
thm store_array_addr()
{
    term n = parse_term("n : num");
    term goal = parse_term("! addr i lo hi. \
        store_zero_array (addr + &i) lo hi n = \
        store_zero_array addr (lo + i) (hi + i) n");
    // show_induct_goal(n, goal, num_INDUCTION);

    // basis
    term basis_goal = rewrite_term(parse_term("n = 0"), goal);
    thm th1 = rewrite(STORE_ZERO_ARRAY_DEF, basis_goal);
    term tm1 = parse_term("(lo + i) = (hi + i) <=> (lo : num) = hi");
    thm th2 = arith_rule(tm1);
    thm th3 = rewrite_after(th2, th1);
    thm basis = simp(th3);

    // step
    term tm2 = rewrite_term(parse_term("n = SUC m"), goal);
    term step_goal = rewrite_term(parse_term("SUC m = SUC n"), tm2);
    thm th4 = rewrite(STORE_ZERO_ARRAY_DEF, step_goal);
    term tm3 = parse_term("(addr + &i) + &lo = addr + &(lo + i)");
    thm th5 = arith_rule(tm3);
    thm th6 = rewrite_after(th5, th4);
    thm th7 = assume(goal);
    thm th8 = rewrite_after(th7, th6);
    term tm4 = parse_term("SUC lo + i = SUC (lo + i)");
    thm th9 = arith_rule(tm4);
    thm th10 = rewrite_after(th9, th8);
    thm th11 = simp(th10);
    thm th12 = disch(th11, goal);
    thm step = gen(n, th12);

    thm th = mp(num_INDUCTION, conjunct(basis, step));

    return th;
}

/*
    id2vi (pid + n) == id2vi pid + &(PAGE_SIZE * n)
*/
thm sza_merge_lemma()
{
    term tm1 = parse_term("id2vi (pid + n)");
    thm th1 = rewrite(ID2VI_DEF, tm1);
    thm th2 = rewrite_after(PH2VI_DEF, th1);
    thm th3 = rewrite_after(ID2PH_DEF, th2);
    term tm2 = parse_term("((pid + n) * PAGE_SIZE) = (pid * PAGE_SIZE) + (PAGE_SIZE * n)");
    thm th4 = arith_rule(tm2);
    term tm3 = parse_term("&((pid * PAGE_SIZE) + (PAGE_SIZE * n)) = &(pid * PAGE_SIZE) + &(PAGE_SIZE * n)");
    thm th5 = arith_rule(tm3);
    term tm4 = parse_term("(&(pid * PAGE_SIZE) + &(PAGE_SIZE * n)) - &offset = (&(pid * PAGE_SIZE) - &offset) + &(PAGE_SIZE * n)");
    thm th6 = arith_rule(tm4);
    thm th7 = rewrite_after(th4, th3);
    thm th8 = rewrite_after(th5, th7);
    thm th9 = rewrite_after(th6, th8);
    term tm5 = parse_term("id2vi pid + &(PAGE_SIZE * n)");
    thm th10 = rewrite(ID2VI_DEF, tm5);
    thm th11 = rewrite_after(PH2VI_DEF, th10);
    thm th12 = rewrite_after(ID2PH_DEF, th11);
    thm th13 = trans(th9, symm(th12));
    return th13;
}

/*
    (store_zero_array (id2vi pid) 0 (PAGE_SIZE * n) (PAGE_SIZE * n) **
    store_zero_array (id2vi (pid + n)) 0 (PAGE_SIZE * n) (PAGE_SIZE * n)) =
    store_zero_array (id2vi pid) 0 (PAGE_SIZE * (n * 2)) (PAGE_SIZE * (n * 2))
*/
thm sza_merge_lemma2()
{
    term rhs = parse_term("store_zero_array (id2vi pid) 0 (PAGE_SIZE * (n * 2)) (PAGE_SIZE * (n * 2))");
    thm th1 = mp(break_array_sepconj(), STORE_ZERO_ARRAY_DEF);
    term tm1 = parse_term("PAGE_SIZE * n <= PAGE_SIZE * (n * 2)");
    thm th2 = arith_rule(tm1);
    term tm2 = parse_term("PAGE_SIZE * (n * 2) <= PAGE_SIZE * (n * 2)");
    thm th3 = arith_rule(tm2);
    thm th4 = mp(mp(th1, th2), th3);
    term tm3 = parse_term("! (a : num). a - a = 0");
    thm th5 = arith_rule(tm3);
    term tm4 = parse_term("! (a : num). 0 + a = a");
    thm th6 = arith_rule(tm4);
    term tm5 = parse_term("PAGE_SIZE * n * 2 - PAGE_SIZE * n = PAGE_SIZE * n");
    thm th7 = arith_rule(tm5);
    thm th8 = rewrite_rule(th5, th4);
    thm th9 = rewrite_rule(th6, th8);
    thm th10 = rewrite_rule(th7, th9);
    
    term lhs2 = parse_term("store_zero_array (id2vi (pid + n)) 0 (PAGE_SIZE * n) (PAGE_SIZE * n)");
    thm th11 = rewrite(sza_merge_lemma(), lhs2);
    thm th12 = rewrite_after(store_array_addr(), th11);
    thm th13 = rewrite_after(th6, th12);
    term tm6 = parse_term("PAGE_SIZE * n + PAGE_SIZE * n = PAGE_SIZE * n * 2");
    thm th14 = arith_rule(tm6);
    thm th15 = rewrite_after(th14, th13);

    thm th16 = rewrite(th10, rhs);
    thm th17 = rewrite_after(symm(th15), th16);
    thm th = gen(parse_term("n : num"), gen(parse_term("pid : num"), symm(th17)));
    
    return th;
}

thm sza_merge()
{
    return new_axiom(parse_term(" \
    ! (i : num) (j : num) (ord : num). \
        (abs(&j - &i) = &(2 EXP ord)) \
    ==> ((store_zero_array (i2vi i) 0 (PAGE_SIZE * 2 EXP ord) (PAGE_SIZE * 2 EXP ord) ** \
        store_zero_array (i2vi j) 0 (PAGE_SIZE * 2 EXP ord) (PAGE_SIZE * 2 EXP ord)) \
    -|- store_zero_array (i2vi (MIN j i)) 0 (PAGE_SIZE * 2 EXP (SUC ord)) (PAGE_SIZE * 2 EXP (SUC ord))) \
    "));
}

/*
    id2i (i2id i) = i
*/
thm i2id2i()
{
    term tm = parse_term("id2i (i2id i)");
    thm ar = arith_rule(parse_term("! a : num. (start + a) - start = a"));
    thm thl[] = {ID2I_DEF, I2ID_DEF, ar, NULL};
    thm th = rewrite_after_term_list(thl, tm);
    return gen(parse_term("i : num"), th);
}

thm merge_head_body_axiom()
{
    return new_axiom(parse_term(" \
    ! (i : num) (sz : num) (order : num). \
        store_zero_array (i2vi i) (PTR_SIZE * 2) (PAGE_SIZE * 2 EXP order) (PAGE_SIZE * 2 EXP order - PTR_SIZE * 2) ** \
        data_at(i2vi i, Tptr, &0) ** \
        data_at(i2vi i + &PTR_SIZE, Tptr, &0) \
    -|- store_zero_array (i2vi i) 0 (PAGE_SIZE * 2 EXP order) (PAGE_SIZE * 2 EXP order) \
    "));
}







/* unused lemmas for future work */

/*
    dlist_head addr l dl order maxorder hl
==> dlist_head addr l dl order maxorder (modified hl order' (v, v))
*/
thm dh_hl_1()
{
    return TAKE_DEF;
}

/*
    ~(order = ORD (nth l (id2i lo))) \/ ~(F2 (nth hl order) = id2vi lo)
==> dlist_node_one addr l dl hl lo F1 F2
==> dlist_node_one addr l dl (modified hl order v) F1 F2
*/
thm dho_inv()
{
    return TAKE_DEF;
}

/*
    ~(ifilter new_l pid)
==> (NXT (nth hl order) = id2vi pid) 
==> (PRV (nth hl order) = id2vi pid)
==> dlist_node addr (ifilter new_l) l dl hl start end dl
==> dlist_node addr (ifilter new_l) l dl (modified hl order v) start end dl
*/
thm dn_hl_1()
{
    return TAKE_DEF;
}

/*
    NXT (nth dl (vi2i prev)) = pv
==> dlist_head_half addr l dl order h F1 F2
==> dlist_head addr l dl lo hi hl
==> dlist_head addr l (modified dl (vi2i prev) (next, _)) lo hi (modified hl (order - lo) (_, prev))
*/