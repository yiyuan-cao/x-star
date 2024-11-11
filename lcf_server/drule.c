#include "proof-user.h"
#include "proof-conv.h"
#include "def.h"
#include "drule.h"
#include <stdio.h>
#include <string.h>

thm disconj1;
thm impl_conj_mono_thm;
thm impl_disj_mono_thm;
thm impl_if_mono_thm;
thm hfact_true;
thm sepand_t;
thm sepand_f;
thm sepconj_f;
void load_axioms()
{
    disconj1 = new_axiom(parse_term("! A B. A ==> A \\/ B"));
    impl_conj_mono_thm = new_axiom(parse_term("! p1 p2 p3 p4. (p1 ==> p3) /\\ (p2 ==> p4) ==> ((p1 /\\ p2) ==> (p3 /\\ p4))"));
    impl_disj_mono_thm = new_axiom(parse_term("! p1 p2 p3 p4. (p1 ==> p3) /\\ (p2 ==> p4) ==> ((p1 \\/ p2) ==> (p3 \\/ p4))"));
    impl_if_mono_thm = new_axiom(parse_term("! P A B C D. (A ==> C) /\\ (B ==> D) ==> (if P then A else B) ==> (if P then C else D)"));
    hfact_true = new_axiom(parse_term("! hp. hfact T ** hp -|- hp"));
    sepand_t = new_axiom(parse_term("! hp. hpure T && hp -|- hp"));
    sepand_f = new_axiom(parse_term("! hp. hpure F && hp -|- hpure F"));
    sepconj_f = new_axiom(parse_term("! hp. hpure F ** hp -|- hpure F"));
}

thm give_up_fact()
{
    term p = parse_term("p : bool");
    term hp = parse_term("hp : hprop");
    thm th = mp(hfact_elim, disch(spec(hp, hentail_refl), p));
    return gen(p, gen(hp, th));
}
thm sepeq2sepent()
{
    term asmp = parse_term("hp1 -|- hp2");
    thm th1 = rewrite(assume(asmp), parse_term("hp1 |-- hp2"));
    thm th2 = rewrite_rule(hentail_refl, th1);
    thm th3 = gen(parse_term("hp1 : hprop"), gen(parse_term("hp2 : hprop"), disch(th2, asmp)));
    return th3;
}

/* pure logic */
thm impl_conj_mono(thm th1, thm th2)
{
    return mp(impl_conj_mono_thm, conjunct(th1, th2));
}
thm impl_disj_mono(thm th1, thm th2)
{
    return mp(impl_disj_mono_thm, conjunct(th1, th2));
}
thm impl_if_mono(term cond, thm thenth, thm elseth)
{
    return mp(spec(cond, impl_if_mono_thm), conjunct(thenth, elseth));
}
thm merge_disj_cases(term casep, thm pos, thm neg)
{
    return disj_cases(spec(casep, get_theorem("EXCLUDED_MIDDLE")), pos, neg);
}
// eq : a = b
// tm : f a
// res : f a = (\b. f b) a 
thm abs_term(term tm, term eq)
{
    term a = dest_bin_fst_comb(eq);
    term b = dest_bin_snd_comb(eq);
    term tm1 = rewrite_term(eq, tm);
    term tm2 = mk_comb(mk_abs(b, tm1), a);
    thm th = symm(rewrite(refl(parse_term("T")), tm2));
    return th;
}

/* separation logic */
thm eq2ent(thm th)
{
    return mp(sepeq2sepent(), th);
}
thm htrans(thm th1, thm th2)
{
    return mp(mp(hentail_trans, th1), th2);
}
thm htrans_list(thm thl[])
{
    thm th = thl[0];
    for(int i = 1; thl[i] != NULL; i++)
        th = htrans(th, thl[i]);
    return th;
}

/* rewrite related */
thm simp(thm th)
{
    return rewrite_rule(refl(parse_term("T")), th);
}
term rewrite_term(term th, term tm)
{
    return dest_bin_snd_comb(concl(rewrite(assume(th), tm)));
}
thm rewrite_after(thm th1, thm th2)
{
    return trans(th2, rewrite(th1, dest_bin_snd_comb(concl(th2))));
}
thm rewrite_after_list(thm thl[], thm th)
{
    for(int i = 0; thl[i] != NULL; i++)
        th = rewrite_after(thl[i], th);
    return th;
}
thm rewrite_after_term_list(thm thl[], term tm)
{
    thm th = rewrite(thl[0], tm);
    for(int i = 1; thl[i] != NULL; i++)
        th = rewrite_after(thl[i], th);
    return th;
}
thm rewrite_after_ent(thm th1, thm th2)
{
    return htrans(th2, mp(sepeq2sepent(), rewrite(th1, dest_bin_snd_comb(concl(th2)))));
}

/* state handler */
// facts to consume/keep
// pure theorem : asmps |- concl
// heap theorem : asmps |- hp1 |-- hp2
thm create_trans_auto(term cfactl[], term kfactl[], thm pthl[], thm hthl[])
{
    thm th = spec(parse_term("emp"), hentail_refl);
    for(int i = 0; hthl[i] != NULL; i++)
        th = mp(mp(hsep_monotone, hthl[i]), th);
    for(int i = 0; pthl[i] != NULL; i++)
        th = mp(mp(hfact_intro, pthl[i]), th);
    for(int i = 0; cfactl[i] != NULL; i++)
        th = mp(hfact_elim, disch(th, cfactl[i]));
    for(int i = 0; kfactl[i] != NULL; i++)
    {
        th = mp(mp(hfact_intro, assume(kfactl[i])), th);
        th = mp(hfact_elim, disch(th, kfactl[i]));
    }
    th = rewrite_rule(hsep_hemp_right, th);
    th = rewrite_rule(hsep_assoc, th);
    return th;
}
thm hexists_intro_auto__(term state, term eq)
{
    thm ent = spec(state, hentail_refl);
    term tm = dest_bin_snd_comb(concl(ent));
    thm absth = abs_term(tm, eq);
    thm thl[] = {ent, eq2ent(absth), NULL};
    thm th = htrans_list(thl);
    th = mp(hexists_intro, th);
    th = simp(th);
    return th;
}
thm hexists_intro_auto_(term state, term eq)
{
    if(is_binder("hexists", state))
    {
        term tm = binder_var("hexists", state);
        thm th = hexists_intro_auto_(binder_body("hexists", state), eq);
        th = mp(hexists_monotone, gen(tm, th));
        return th;
    }
    else return hexists_intro_auto__(state, eq);
}
// ent : hp |- hpx x
// eq : x = y
// return : hp |- exists y. hpx y
thm hexists_intro_auto(thm ent, term eq)
{
    term state = dest_bin_snd_comb(concl(ent));
    thm ent2 = hexists_intro_auto_(state, eq);
    return htrans(ent, ent2);
}
thm give_up_facts__(term tml[], term state)
{
    thm ent = spec(state, hentail_refl);
    term hfact = parse_term("hfact");
    for(int i = 0; tml[i] != NULL; i++)
    {
        state = dest_bin_snd_comb(concl(ent));
        thm th1 = sep_lift(mk_comb(hfact, tml[i]), state);
        ent = htrans(ent, eq2ent(th1));
        term p = dest_un_comb(dest_bin_fst_comb(dest_bin_snd_comb(concl(ent))));
        term hp = dest_bin_snd_comb(dest_bin_snd_comb(concl(ent)));
        ent = htrans(ent, spec(hp, spec(p, give_up_fact())));
    }
    return ent;
}
thm give_up_facts_(term tml[], term state)
{
    if(is_binder("hexists", state))
    {
        term tm = binder_var("hexists", state);
        thm th = give_up_facts_(tml, binder_body("hexists", state));
        th = mp(hexists_monotone, gen(tm, th));
        return th;
    }
    else return give_up_facts__(tml, state);
}
thm give_up_facts(term tml[], thm ent)
{
    term state = dest_bin_snd_comb(concl(ent));
    thm th = give_up_facts_(tml, state);
    th = htrans(ent, th);
    return th;
}

/* other helpers */
void show_induct_goal(term itype, term goal, thm ithm)
{
    term P = mk_abs(itype, goal);
    thm th = spec(P, ithm);                         
    thm sth = rewrite_rule(get_theorem("ABS_SIMP"), th);
    term cl = concl(sth);
    term igoal = dest_bin_fst_comb(cl);
    term igoal_basis = dest_bin_fst_comb(igoal);
    term igoal_step = dest_bin_snd_comb(igoal);
    printf("basis : %s\n", string_of_term(igoal_basis));
    printf("step : %s\n", string_of_term(igoal_step));
}
bool compare_hprop_(term hp1, term hp2)
{
    thm th = sep_cancel(hp1, hp2);
    if(strcmp(string_of_term(hp1), string_of_term(dest_bin_snd_comb(concl(th))))) 
    {
        printf("%s\n\n%s\n\n", string_of_term(hp1), string_of_term(dest_bin_snd_comb(concl(th))));
        return 0;
    }
    if(strcmp(string_of_term(hp2), string_of_term(dest_bin_fst_comb(concl(th))))) 
    {
        printf("%s\n\n%s\n\n", string_of_term(hp2), string_of_term(dest_bin_fst_comb(concl(th))));
        return 0;
    }
    printf("correct!\n");
    return 1;
}
bool compare_hprop(term hp1, term hp2)
{
    if(is_binder("hexists", hp1))
    {
        term tm1 = binder_var("hexists", hp1);
        term tm2 = binder_var("hexists", hp2);
        hp1 = binder_body("hexists", hp1);
        hp2 = binder_body("hexists", hp2);
        hp2 = subst(tm1, tm2, hp2);
        return compare_hprop(hp1, hp2);
    }
    else return compare_hprop_(hp1, hp2);
}
