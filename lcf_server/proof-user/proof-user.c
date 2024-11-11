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
  term tm = concl(th2);
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

/*  Logic Properties  */

// ## Returns
//   !A B. (A /\ B) = (B /\ A)
thm conj_comm_prop()
{
  thm th1 = conjunct1(assume(parse_term("A /\\ B")));
  thm th2 = conjunct2(assume(parse_term("A /\\ B")));
  thm th3 = conjunct(th2, th1);
  thm th4 = conjunct1(assume(parse_term("B /\\ A")));
  thm th5 = conjunct2(assume(parse_term("B /\\ A")));
  thm th6 = conjunct(th5, th4);
  thm th7 = deduct_antisym(th6, th3);
  thm th8 = gen(parse_term("A:bool"), gen(parse_term("B:bool"), th7));
  return th8;
}

// ## Parameters
//   tm1 : term `A`
//   tm2 : term `B`
//
// ## Returns
//   a new theorem `(A /\ B) = (B /\ A)`
thm conj_comm(term tm1, term tm2)
{
  return spec(tm2, spec(tm1, conj_comm_prop()));
}

// ## Returns
//   !A B C. (A /\ B) /\ C) = (A /\ (B /\ C))
thm conj_assoc_prop()
{
  term tm1 = parse_term("(A /\\ B) /\\ C");
  thm th1 = conjunct1(conjunct1(assume(tm1)));
  thm th2 = conjunct2(conjunct1(assume(tm1)));
  thm th3 = conjunct2(assume(tm1));
  thm th4 = conjunct(th1, conjunct(th2, th3));
  term tm2 = parse_term("A /\\ (B /\\ C)");
  thm th5 = conjunct1(assume(tm2));
  thm th6 = conjunct1(conjunct2(assume(tm2)));
  thm th7 = conjunct2(conjunct2(assume(tm2)));
  thm th8 = conjunct(conjunct(th5, th6), th7);
  thm th9 = deduct_antisym(th8, th4);
  thm th10 = gen(parse_term("A:bool"), gen(parse_term("B:bool"), gen(parse_term("C:bool"), th9)));
  return th10;
}

// ## Parameters
//   tm1 : term `A`
//   tm2 : term `B`
//   tm3 : term `C`
//
// ## Returns
//   a new theorem `(A /\ B) /\ C) = (A /\ (B /\ C))`
thm conj_assoc(term tm1, term tm2, term tm3)
{
  return spec(tm3, spec(tm2, spec(tm1, conj_assoc_prop())));
}

// ## Returns
//   !A B C. (A = B) ==> ((C /\ A) = (C /\ B))
thm eq_conj_l_prop()
{
  thm th1 = conjunct1(assume(parse_term("C /\\ A")));
  thm th2 = conjunct2(assume(parse_term("C /\\ A")));
  thm th3 = eq_mp(assume(parse_term("A <=> B")), th2);
  thm th4 = conjunct(th1, th3);
  thm th5 = conjunct1(assume(parse_term("C /\\ B")));
  thm th6 = conjunct2(assume(parse_term("C /\\ B")));
  thm th7 = eq_mp(symm(assume(parse_term("A <=> B"))), th6);
  thm th8 = conjunct(th5, th7);
  thm th9 = deduct_antisym(th8, th4);
  thm th10 = disch(th9, parse_term("A <=> B"));
  thm th11 = gen(parse_term("A:bool"), gen(parse_term("B:bool"), gen(parse_term("C:bool"), th10)));
  return th11;
}

// ## Parameters
//   tm1 : term `A`
//   tm2 : term `B`
//   tm3 : term `C`
//
// ## Returns
//   a new theorem `(A = B) ==> ((C /\ A) = (C /\ B))`
thm eq_conj_l(term tm1, term tm2, term tm3)
{
  return spec(tm3, spec(tm2, spec(tm1, eq_conj_l_prop())));
}

// ## Returns
//   !A B C. (A = B) ==> ((A /\ C) = (B /\ C))
thm eq_conj_r_prop()
{
  thm th1 = conjunct2(assume(parse_term("A /\\ C")));
  thm th2 = conjunct1(assume(parse_term("A /\\ C")));
  thm th3 = eq_mp(assume(parse_term("A <=> B")), th2);
  thm th4 = conjunct(th3, th1);
  thm th5 = conjunct2(assume(parse_term("B /\\ C")));
  thm th6 = conjunct1(assume(parse_term("B /\\ C")));
  thm th7 = eq_mp(symm(assume(parse_term("A <=> B"))), th6);
  thm th8 = conjunct(th7, th5);
  thm th9 = deduct_antisym(th8, th4);
  thm th10 = disch(th9, parse_term("A <=> B"));
  thm th11 = gen(parse_term("A:bool"), gen(parse_term("B:bool"), gen(parse_term("C:bool"), th10)));
  return th11;
}

// ## Parameters
//   tm1 : term `A`
//   tm2 : term `B`
//   tm3 : term `C`
//
// ## Returns
//   a new theorem `(A = B) ==> ((A /\ C) = (B /\ C))`
thm eq_conj_r(term tm1, term tm2, term tm3)
{
  return spec(tm3, spec(tm2, spec(tm1, eq_conj_r_prop())));
}

// ## Returns
//   !A B C. (A ==> B) ==> ((C /\ A) ==> (C /\ B))
thm impl_conj_l_prop()
{
  thm th1 = conjunct1(assume(parse_term("C /\\ A")));
  thm th2 = conjunct2(assume(parse_term("C /\\ A")));
  thm th3 = mp(assume(parse_term("A ==> B")), th2);
  thm th4 = conjunct(th1, th3);
  thm th5 = disch(th4, parse_term("C /\\ A"));
  thm th6 = disch(th5, parse_term("A ==> B"));
  thm th7 = gen(parse_term("A:bool"), gen(parse_term("B:bool"), gen(parse_term("C:bool"), th6)));
  return th7;
}

// ## Parameters
//   tm1 : term `A`
//   tm2 : term `B`
//   tm3 : term `C`
//
// ## Returns
//   a new theorem `(A ==> B) ==> ((C /\ A) ==> (C /\ B))`
thm impl_conj_l(term tm1, term tm2, term tm3)
{
  return spec(tm3, spec(tm2, spec(tm1, impl_conj_l_prop())));
}

// ## Returns
//   !A B C. (A ==> B) ==> ((A /\ C) ==> (B /\ C))
thm impl_conj_r_prop()
{
  thm th1 = conjunct2(assume(parse_term("A /\\ C")));
  thm th2 = conjunct1(assume(parse_term("A /\\ C")));
  thm th3 = mp(assume(parse_term("A ==> B")), th2);
  thm th4 = conjunct(th3, th1);
  thm th5 = disch(th4, parse_term("A /\\ C"));
  thm th6 = disch(th5, parse_term("A ==> B"));
  thm th7 = gen(parse_term("A:bool"), gen(parse_term("B:bool"), gen(parse_term("C:bool"), th6)));
  return th7;
}

// ## Parameters
//   tm1 : term `A`
//   tm2 : term `B`
//   tm3 : term `C`
//
// ## Returns
//   a new theorem `(A ==> B) ==> ((A /\ C) ==> (B /\ C))`
thm impl_conj_r(term tm1, term tm2, term tm3)
{
  return spec(tm3, spec(tm2, spec(tm1, impl_conj_r_prop())));
}

// ## Returns
//   !A B C. ((A ==> B) /\ (B ==> C)) ==> (A ==> C)
thm impl_trans_prop()
{
  term tm1 = parse_term("(A ==> B) /\\ (B ==> C)");
  thm th1 = conjunct1(assume(tm1));
  thm th2 = conjunct2(assume(tm1));
  thm th3 = mp(th1, assume(parse_term("A:bool")));
  thm th4 = mp(th2, th3);
  thm th5 = disch(th4, parse_term("A:bool"));
  thm th6 = disch(th5, tm1);
  thm th7 = gen(parse_term("A:bool"), gen(parse_term("B:bool"), gen(parse_term("C:bool"), th6)));
  return th7;
}

// ## Parameters
//   tm1 : term `A`
//   tm2 : term `B`
//   tm3 : term `C`
//
// ## Returns
//   a new theorem `((A ==> B) /\ (B ==> C)) ==> (A ==> C)`
thm impl_trans(thm th1, thm th2)
{
  return mp(impl_trans_prop(), conjunct(th1, th2));
}

// ## Parameters
//   th1 : theorem `A1 /\ A2 /\ ... /\ Am` (you can use "conj_assoc_prop" to get a form without bracket)
//   n : ordinal number
// ## Returns
//   a new theorem `An` (if n == m then there will be an error message)
thm conjunctn(thm th1, int n)
{
  thm res = th1;
  for(int i = 1; i < n; i++)
    res = conjunct2(res);
  if(conjunct2(res) == NULL) return res;
  return conjunct1(res);
}