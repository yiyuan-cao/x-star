#include "proof-user.h"
#include <stdio.h>
#include <string.h>

/** Auxilury functions. */
static thm hfalse_contradiction_aux(thm, term, term);

/** Term destructor. */

// Check if a term is a binary expression.
bool is_bin_op(term tm) {
  return is_comb(tm) && is_comb(fst_comb(tm)) 
     && !is_comb(fst_comb(fst_comb(tm)));
}

// The first operand of a binary expression.
term dest_bin_fst_comb(term tm) {
  if (!is_bin_op(tm)) return NULL;
  return snd_comb(fst_comb(tm));
}

// The second operand of a binary expression.
term dest_bin_snd_comb(term tm) {
  if (!is_bin_op(tm)) return NULL;
  return snd_comb(tm);
}

// The binary operator of a binary expression.
term dest_bin_op(term tm) {
  if (!is_bin_op(tm)) return NULL;
  return fst_comb(fst_comb(tm));
}

// Check if a term is a unary expression.
bool is_un_op(term tm) {
  return is_comb(tm) && !is_comb(fst_comb(tm));
}

// The operand of a unary expression.
term dest_un_comb(term tm) {
  if (!is_un_op(tm)) return NULL;
  return snd_comb(tm);
}

// The operand of a unary expression.
term dest_un_op(term tm) {
  if (!is_un_op(tm)) return NULL;
  return fst_comb(tm);
}

/** Additional User Interface for Pure Proof. */

// Rewrite a theorem
//
// ## Parameters
//   th1 : a theorem `a = b`
//   th2 : a theorem to rewrite
//
// ## Returns
//   a new theorem of th2 after rewriting by `a = b`
thm rewrite_thm(thm th1, thm th2) {
  term tm = conclusion(th2);
  return eq_mp(rewrite(th1, tm), th2);
}

// Rewrite using a theorem, then prove by reflexivity
//
// ## Parameters
//   th : a theorem
//   tm1: a term `a`
//   tm2: a term `b`
//
// ## Returns
//   a new theorem of `a == b` if success
thm rewrite_refl(thm th, term tm1, term tm2) {
  return (trans(rewrite(th, tm1), symm(rewrite(th, tm2))));
}

// Rewrites list of theorems.
//
// ## Parameters
//   rws: a list of rewrites_item of the form 
//        [th1,tm1; th2,tm2; ...; th(n),tm(n)] 
//        Tips: always th(n) = refl(tm(n))
//   len: length of rws
//
// ## Returns
//   a new theorem `tm1 == tm(n)` if 
//      forall k, tm(k) ==rewrite using th(k)== tm(k+1)
thm rewrites(rewrites_item rws[], int len) {
  thm result = GC_MALLOC(sizeof(struct Gc_Theorem*));

  result = rewrite(rws[0].th, rws[0].tm);
  for (int i = 1; i < len; ++i) {
    result = trans(result, rewrite(rws[i].th, rws[i].tm));
  }
  return result;
}

// Generalizes list of theorems.
//
// ## Parameters
//   tms: a list of generalized variables
//   len: length of tms
//
// ## Returns
//   a new generalized theorem 
thm gens(term tms[], int len, thm th) {
  thm result = GC_MALLOC(sizeof(struct Gc_Theorem*));

  result = th;
  for (int i = len - 1; i >= 0; --i) {
    result = gen(tms[i], result);
  }
  return result;
}

thm specs(thm th, term tml[])
{
  for(int i = 0; tml[i] != NULL; i++)
    th = spec(tml[i], th);
  return th;
}

thm mps(thm th, thm thl[])
{
  for(int i = 0; thl[i] != NULL; i++)
    th = mp(th, thl[i]);
  return th;
}

// General version of induction
//
// ## Parameters
//   i     : inductive datatype
//   basis : proof of base case 
//   step  : proof of induction step
//   goal  : induction goal
//
// ## Returns
//   a new theorem
thm induction_with_goal(indtype i, thm basis, thm step, term goal) {
  return mp(induction_aux(spec_all(i->ind), parse_term("!x. P x"), goal), conjunct(basis, step));
}

void show_induct_goal(term itype, term goal, thm ithm)
{
    term P = mk_abs(itype, goal);
    thm th = spec(P, ithm);                         
    thm sth = rewrite_rule(get_theorem("ABS_SIMP"), th);
    term cl = conclusion(sth);
    term igoal = dest_bin_fst_comb(cl);
    term igoal_basis = dest_bin_fst_comb(igoal);
    term igoal_step = dest_bin_snd_comb(igoal);
    printf("basis : %s\n", string_of_term(igoal_basis));
    printf("step : %s\n", string_of_term(igoal_step));
}

// Induction
//
// ## Parameters
//   i     : inductive datatype
//   basis : proof of base case 
//   step  : proof of induction step
//
// ## Returns
//   a new theorem (maybe fail in certain case)
thm induction(indtype i, thm basis, thm step) {
  return mp(i->ind, conjunct(basis, step));
}

thm add_assum(term tm, thm th) {
  return mp(disch(th, tm), assume(tm));
}

// ## Parameters
//   th1 : theorem `A1 /\ A2 /\ ... /\ Am`
//   n : ordinal number
// ## Returns
//   a new theorem `An`
thm conjunctn(thm th1, int n)
{
  thm res = th1;
  for(int i = 1; i < n; i++)
    res = conjunct2(res);
  term conj = dest_bin_op(conclusion(conjunct(assume(parse_term("a:bool = a")), assume(parse_term("b:bool = b")))));
  if(strcmp(string_of_term(dest_bin_op(conclusion(res))), string_of_term(conj)))
    return res;
  return conjunct1(res);
}

// ## Parameters
//   th1 : theorem `A1 ==> A2`
//   th1 : theorem `A3 ==> A4`
// ## Returns
//   a new theorem `(A1 /\ A3) ==> (A2 /\ A4)`
thm impl_conj_mono(thm th1, thm th2)
{
    return mp(taut(parse_term("! p1 p2 p3 p4. (p1 ==> p3) /\\ (p2 ==> p4) ==> ((p1 /\\ p2) ==> (p3 /\\ p4))")), conjunct(th1, th2));
}

// ## Parameters
//   th1 : theorem `A1 ==> A2`
//   th1 : theorem `A3 ==> A4`
// ## Returns
//   a new theorem `(A1 \/ A3) ==> (A2 \/ A4)`
thm impl_disj_mono(thm th1, thm th2)
{
    return mp(taut(parse_term("! p1 p2 p3 p4. (p1 ==> p3) /\\ (p2 ==> p4) ==> ((p1 \\/ p2) ==> (p3 \\/ p4))")), conjunct(th1, th2));
}

// ## Parameters
//   cond : term `P`
//   thenth : theorem `A1 ==> A2`
//   elseth : theorem `A3 ==> A4`
// ## Returns
//   a new theorem `!P. if P then A1 else A3 ==> if P then A2 else A4`
thm impl_if_mono(term cond, thm thenth, thm elseth)
{
    return mp(spec(cond, taut(parse_term("! P A B C D. (A ==> C) /\\ (B ==> D) ==> (if P then A else B) ==> (if P then C else D)"))), conjunct(thenth, elseth));
}

// ## Parameters
//   casep : term `P`
//   pos : theorem `A u {P} |- t`
//   neg : theorem `A u {~P} |- t`
// ## Returns
//   a new theorem `A |- t`
thm merge_disj_cases(term casep, thm pos, thm neg)
{
    return disj_cases(spec(casep, get_theorem("EXCLUDED_MIDDLE")), pos, neg);
}