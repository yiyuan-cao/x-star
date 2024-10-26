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

/* Deprecated Separation Logic */

// /** Separation Logic Property as Axiom. */
// void sl_init() {
//   new_type("hprop", 0);
//   new_type("loc", 0);
//   slval = define_type("slval", (const char *[]){"Vint int", "Vptr loc", NULL,});
// 
//   new_constant("null", parse_type(":loc"));
//   new_constant("emp", parse_type(":hprop"));
//   new_constant("hfalse", parse_type(":hprop"));
//   new_constant("pure", parse_type(":bool -> hprop"));
//   new_constant("sepconj", parse_type(":hprop -> hprop -> hprop"));
//   new_constant("pointsto", parse_type(":slval -> slval -> hprop"));
//   new_constant("undefpointsto", parse_type(":slval -> hprop"));
//   new_constant("fieldpointsto", parse_type(":slval -> num -> slval -> hprop"));
//   new_constant("hforall", parse_type(":(A -> hprop) -> hprop"));
//   new_constant("hexists", parse_type(":(A -> hprop) -> hprop"));
//   new_constant("entailment", parse_type(":hprop -> hprop -> bool"));
// 
//   himpl_refl_axiom = new_axiom(parse_term("!H:hprop. entailment H H"));
//   himpl_trans_axiom = new_axiom(parse_term(
//     "!H1 H2 H3. entailment H1 H2 ==> entailment H2 H3 ==> entailment H1 H3"
//   ));
//   himpl_antisym_axiom = new_axiom(parse_term(
//     "!H1 H2. entailment H1 H2 ==> entailment H2 H1 ==> H1 = H2"
//   ));
//   star_assoc_axiom = new_axiom(parse_term(
//     "!H1 H2 H3. sepconj (sepconj H1 H2) H3 = sepconj H1 (sepconj H2 H3)"
//   ));
//   star_comm_axiom = new_axiom(parse_term(
//     "!H1 H2. sepconj H1 H2 = sepconj H2 H1"
//   ));
//   star_monotone_axiom = new_axiom(parse_term(
//     "!H1 H2 H3 H4. (entailment H1 H3) ==> (entailment H2 H4) ==> (entailment (sepconj H1 H2) (sepconj H3 H4))"
//   ));
//   star_neutral_l_axiom = new_axiom(parse_term(
//     "!H. sepconj emp H = H"
//   ));
//   star_exists_axiom = new_axiom(parse_term(
//     "!(J:A->hprop) H. sepconj (hexists J) H = hexists (\\(x:A). (sepconj (J x) H))"
//   ));
//   star_forall_axiom = new_axiom(parse_term(
//     "!(J:A->hprop) H. entailment (sepconj (hforall J) H) (hforall (\\x. (sepconj (J x) H)))"
//   ));
//   frame_rule_l_axiom = new_axiom(parse_term(
//     "!H1 H2 H3. (entailment H1 H2) ==> entailment (sepconj H1 H3) (sepconj H2 H3)"
//   ));
//   single_not_null_axiom = new_axiom(parse_term(
//     "!p v. entailment (pointsto p v) (sepconj (pointsto p v) (pure (~(p = Vptr null))))"
//   ));
//   single_conflict_axiom = new_axiom(parse_term(
//     "!p v1 v2. entailment (sepconj (pointsto p v1) (pointsto p v2)) hfalse"
//   ));
//   field_not_null_axiom = new_axiom(parse_term(
//     "!p f v. entailment (fieldpointsto p f v) (sepconj (fieldpointsto p f v) (pure (~(p = Vptr null))))"
//   ));
//   field_conflict_axiom = new_axiom(parse_term(
//     "!p f v1 v2. entailment (sepconj (fieldpointsto p f v1) (fieldpointsto p f v2)) hfalse"
//   ));
//   pure_l_axiom = new_axiom(parse_term(
//     "!P H1 H2. (P ==> entailment H1 H2) ==> entailment (sepconj (pure P) H1) H2"
//   ));
//   pure_r_axiom = new_axiom(parse_term(
//     "!P H1 H2. P ==> entailment H1 H2 ==> entailment H1 (sepconj (pure P) H2)"
//   ));
//   exists_l_axiom = new_axiom(parse_term(
//     "!J H. (!x:A. entailment (J x) H) ==> entailment (hexists J) H"
//   ));
//   exists_r_axiom = new_axiom(parse_term(
//     "!(x:A) J H. entailment H (J x) ==> entailment H (hexists J)"
//   ));
//   exists_monotone_axiom = new_axiom(parse_term(
//     "!(J1:A->hprop) J2. (!(x:A). entailment (J1 x) (J2 x)) ==> entailment (hexists J1) (hexists J2)"
//   ));
//   forall_l_axiom = new_axiom(parse_term(
//     "!(x:A) J H. entailment (J x) H ==> entailment (hforall J) H"
//   ));
//   forall_r_axiom = new_axiom(parse_term(
//     "!(J:A->hprop) H. (!(x:A). entailment H (J x)) ==> entailment H (hforall J)"
//   ));
//   forall_monotone_axiom = new_axiom(parse_term(
//     "!(J1:A->hprop) J2. (!(x:A). entailment (J1 x) (J2 x)) ==> entailment (hforall J1) (hforall J2)"
//   ));
//   false_explosion_axiom = new_axiom(parse_term("!H. entailment hfalse H"));
//   false_elim_l_axiom = new_axiom(parse_term(
//     "!H. entailment (sepconj hfalse H) hfalse"
//   ));
//   false_def_axiom = new_axiom(parse_term("hfalse = pure F"));
//   himpl_sym_l_axiom = new_axiom(parse_term(
//     "!H1 H2. H1 = H2 ==> entailment H1 H2"
//   ));
//   pure_contradiction_axiom = new_axiom(parse_term(
//     "!P. ~P /\\ P = F"
//   ));
//   pure_distri_axiom = new_axiom(parse_term(
//     "!P1 P2. sepconj (pure P1) (pure P2) = pure (P1 /\\ P2)"
//   ));
//   undefpointsto_def_axiom = new_axiom(parse_term(
//     "!p. undefpointsto p = hexists (\\(q:slval). pointsto p q)"
//   ));
//   
//   // Added temporarily
//   disj_split_axiom = new_axiom(parse_term(
//     "!A. (A \\/ ~(A))"
//   ));
//   int_le_axiom = new_axiom(parse_term(
//     "!(a:int) (b:int). ~(a <= b) ==> (b <= a)"
//   ));
// }
// 
// // ## Parameters
// //   tm: term `H`
// //
// // ## Returns
// //   a new theorem `H |-- H`
// thm himpl_refl(term tm) {
//   return spec(tm, himpl_refl_axiom);
// }
// 
// // ## Parameters
// //   th1: theorem `H1 |-- H2`
// //   th2: theorem `H2 |-- H3`
// //
// // ## Returns
// //   a new theorem `H1 |-- H3`
// thm himpl_trans(thm th1, thm th2) {
//   return mp(mp(himpl_trans_axiom, th1), th2);
// }
// 
// // ## Parameters
// //   th1: theorem `H1 |-- H2`
// //   th2: theorem `H2 |-- H1`
// //
// // ## Returns
// //   a new theorem `H1 == H2`
// thm himpl_antisym(thm th1, thm th2) {
//   return mp(mp(himpl_antisym_axiom, th1), th2);
// }
// 
// // ## Parameters
// //   tm1: term `H1`
// //   tm2: term `H2`
// //   tm3: term `H3`
// //
// // ## Returns
// //   a new theorem `(H1 * H2) * H3 = H1 * (H2 * H3)`
// thm star_assoc(term tm1, term tm2, term tm3) {
//   return spec(tm3, spec(tm2, spec(tm1, star_assoc_axiom)));
// }
// 
// // ## Parameters
// //   tm1: term `H1`
// //   tm2: term `H2`
// //
// // ## Returns
// //   a new theorem `H1 * H2 = H2 * H1`
// thm star_comm(term tm1, term tm2) {
//   return spec(tm2, spec(tm1, star_comm_axiom));
// }
// 
// // ## Parameters
// //   th1: theorem `H1 |-- H3`
// //   th2: theorem `H2 |-- H4`
// //
// // ## Returns
// //   a new theorem `H1 * H2 |-- H3 * H4`
// thm star_monotone(thm th1, thm th2) {
//   return mp(mp(star_monotone_axiom, th1), th2);
// }
// 
// // ## Parameters
// //   tm: term `H`
// // 
// // ## Returns
// //   a new theorem `[] * H = H`
// thm star_neutral_l(term tm) {
//   return spec(tm, star_neutral_l_axiom);
// }
// 
// // ## Parameters
// //   tm: term `H` 
// //
// // ## Returns
// //   a new theorem `H * [] = H`
// thm star_neutral_r(term tm) {
//   return trans(star_comm(tm, parse_term("emp")), star_neutral_l(tm));
// }
// 
// // ## Parameters
// //   tm1: term `hexists J`
// //   tm2: term `H` 
// //
// // ## Returns
// //   a new theorem `(hexists J) * H = hexists (\x. J x * H)`
// thm star_exists(term tm1, term tm2) {
//   term tm_j = dest_un_comb(tm1);
//   return rewrite_thm(refl(tm1), spec(tm2, spec(tm_j, star_exists_axiom)));
// }
// 
// // ## Parameters
// //    tm1: term `hforall J`
// //    tm2: term `H`
// //
// // ## Returns
// //    a new theorem `(hforall J) * H |-- hforall (\x. J x * H)`
// thm star_forall(term tm1, term tm2) {
//   term tm_j = dest_un_comb(tm1);
//   return rewrite_thm(refl(tm1), spec(tm2, spec(tm_j, star_forall_axiom)));
// }
// 
// // ## Parameters
// //   th: theorem `H1 |-- H2`
// //   tm: term `H3`
// //
// // ## Returns
// //   a new theorem `H1 * H3 |-- H2 * H3`
// thm frame_rule_l(thm th, term tm) {
//   return spec(tm, mp(frame_rule_l_axiom, th));
// }
// 
// // ## Parameters
// //   th: theorem `H1 |-- H2`
// //   tm: term `H3`
// //
// // ## Returns
// //   a new theorem `H3 * H1 |-- H3 * H2`
// thm frame_rule_r(thm th, term tm) {
//   term h1 = dest_bin_fst_comb(concl(th));
//   term h2 = dest_bin_snd_comb(concl(th));
//   thm th1 = himpl_sym_l(star_comm(tm, h1));
//   thm th2 = himpl_sym_l(star_comm(h2, tm));
//   return himpl_trans(th1, himpl_trans(frame_rule_l(th, tm), th2));
// }
// 
// // ## Parameters
// //   tm1: term `p:slval`
// //   tm2: term `v:slval`
// //
// // ## Returns
// //   a new theorem `p ~> v |--- p ~> v * [p != NULL]
// thm single_not_null(term tm1, term tm2) {
//   return spec(tm2, spec(tm1, single_not_null_axiom));
// }
// 
// // ## Parameters
// //   tm1: term `p:slval` 
// //   tm2: term `v1:slval`
// //   tm3: term `v2:slval`
// //
// // ## Returns
// //   a new theorem `p ~> v1 * p ~> v2 |-- [F]`
// thm single_conflict(term tm1, term tm2, term tm3) {
//   return spec(tm3, spec(tm2, spec(tm1, single_conflict_axiom)));
// } 
// 
// // ## Parameters
// //   th: theorem `P ==> (H1 |-- H2)`
// //
// // ## Returns
// //   a new theorem `[P] * H1 |-- H2`
// thm pure_l(thm th) {
//   return mp(pure_l_axiom, th);
// } 
// 
// // ## Parameters
// //   th1: theorem `P`
// //   th2: theorem `H1 |-- H2`
// //
// // ## Returns
// //   a new theorem `H1 |-- [P] * H2`
// thm pure_r(thm th1, thm th2) {
//   return mp(mp(pure_r_axiom, th1), th2);
// }
// 
// // ## Parameters
// //   th: theorem `!x. (J x |-- H)`
// //
// // ## Returns
// //   a new theorem `hexists J |-- H`
// thm exists_l(thm th) {
//   return mp(exists_l_axiom, th);
// }
// 
// // ## Parameters
// //   th: theorem `H |-- J a`
// //   tm1: term `a`
// //   tm2: term `x`
// //
// // ## Returns
// //   a new theorem `H |-- hexists J` (the form of `J` is `\x. J x`)
// //
// // ## Tips
// //   If you find problem instantiating, see `exists_r_aux()`
// thm exists_r(thm th, term tm1, term tm2) {
//   term tm0 = concl(th);
//   if (is_bin_op(tm0) && 
//       !strcmp(string_of_term(dest_bin_op(tm0)), "entailment")) {
//     term tm_post = dest_bin_snd_comb(tm0);
//     term tm_app = mk_comb(fst_comb(tm0), mk_comb(mk_abs(tm2, subst(tm2, tm1, tm_post)), tm1));
//     thm app_eq1 = symm(rewrite(refl(tm2), tm_app));
//     thm app_eq2 = rewrite(refl(tm2), tm0);
//     thm th_app = eq_mp(app_eq1, eq_mp(app_eq2, th));
//     return mp(exists_r_axiom, th_app);
//   }
//   return mp(spec(tm2, exists_r_axiom), th);
// }
// 
// // ## Parameters
// //   th: theorem `H |-- J a`
// //   tm1: term `a`
// //   tm2: term `x`
// //   tm3: term `hexists J` (the form of `J` is `\x. J x`)
// //
// // ## Returns
// //   a new theorem `H |-- hexists J` 
// thm exists_r_aux (thm th, term tm1, term tm2, term tm3) {
//   term tm0 = concl(th);
//   if (is_bin_op(tm0) && 
//       !strcmp(string_of_term(dest_bin_op(tm0)), "entailment")) {
//     term tm_post = dest_bin_snd_comb(tm0);
//     term tm_app = mk_comb(fst_comb(tm0), mk_comb(snd_comb(tm3), tm1));
//     thm app_eq1 = symm(rewrite(refl(tm2), tm_app));
//     thm app_eq2 = rewrite(refl(tm2), tm0);
//     thm th_app = eq_mp(app_eq1, eq_mp(app_eq2, th));
//     return mp(exists_r_axiom, th_app);
//   }
//   return mp(spec(tm2, exists_r_axiom), th);
// }
// 
// // ## Parameters
// //   th: theorem `!x. (J1 x |-- J2 x)`
// //
// // ## Returns
// //   a new theorem `hexists J1 |-- hexists J2`
// thm exists_monotone(thm th) {
//   return mp(exists_monotone_axiom, th);
// }
// 
// // ## Parameters
// //   th: theorem `J a |-- H`
// //   tm1: term `a`
// //   tm2: term `x`
// //
// // ## Returns
// //   a new theorem `hforall J |- H` (the form of `J` is `\x. J x`)
// //
// // ## Tips
// //   If you find problem instantiating, see `forall_l_aux()`
// thm forall_l(thm th, term tm1, term tm2) {
//   term tm0 = concl(th);
//   if (is_bin_op(tm0) && 
//       !strcmp(string_of_term(dest_bin_op(tm0)), "entailment")) {
//     term tm_pre = dest_bin_fst_comb(tm0);
//     term tm_j_a = mk_comb(mk_abs(tm2, subst(tm2, tm1, tm_pre)), tm1);
//     term tm_app = mk_comb(mk_comb(dest_bin_op(tm0), tm_j_a), dest_bin_snd_comb(tm0));
//     thm app_eq1 = symm(rewrite(refl(tm2), tm_app));
//     thm app_eq2 = rewrite(refl(tm2), tm0);
//     thm th_app = eq_mp(app_eq1, eq_mp(app_eq2, th));
//     return mp(forall_l_axiom, th_app);
//   }
//   return mp(spec(tm2, forall_l_axiom), th);
// }
// 
// // ## Parameters
// //   th: theorem `J a |-- H`
// //   tm1: term `a`
// //   tm2: term `x`
// //   tm3: term `hforall J` (the form of `J` is `\x. J x`)
// //
// // ## Returns
// //   a new theorem `hforall J |- H` 
// thm forall_l_aux(thm th, term tm1, term tm2, term tm3) {
//   term tm0 = concl(th);
//   if (is_bin_op(tm0) && 
//       !strcmp(string_of_term(dest_bin_op(tm0)), "entailment")) {
//     term tm_pre = dest_bin_fst_comb(tm0);
//     term tm_j_a = mk_comb(snd_comb(tm3), tm1);
//     term tm_app = mk_comb(mk_comb(dest_bin_op(tm0), tm_j_a), dest_bin_snd_comb(tm0));
//     thm app_eq1 = symm(rewrite(refl(tm2), tm_app));
//     thm app_eq2 = rewrite(refl(tm2), tm0);
//     thm th_app = eq_mp(app_eq1, eq_mp(app_eq2, th));
//     return mp(forall_l_axiom, th_app);
//   }
//   return mp(spec(tm2, forall_l_axiom), th);
// }
// 
// // ## Parameters
// //   th: theorem `!x. (H |-- J x)`
// //
// // ## Returns
// //   a new theorem `H |-- hforall J`
// thm forall_r(thm th) {
//   return mp(forall_r_axiom, th);
// }
// 
// // ## Parameters
// //   th: theorem `!x. (J1 x |-- J2 x)`
// //
// // ## Returns
// //   a new theorem `hforall J1 |-- hforall J2`
// thm forall_monotone(thm th) {
//   return mp(forall_monotone_axiom, th);
// }
// 
// // ## Parameters
// //   p: term `p:slval`
// //   f: term `f:num`
// //   v: term `v:slval`
// //
// // ## Returns
// //   a new theorem `p.f ~> v |--- p.f ~> v * [p != NULL]
// thm field_not_null(term p, term f, term v) {
//   return spec(v, spec(f, spec(p, field_not_null_axiom)));
// }
// 
// // ## Parameters
// //   p: term `p:slval` 
// //   f: term `f:num`
// //   v1: term `v1:slval`
// //   v2: term `v2:slval`
// //
// // ## Returns
// //   a new theorem `p.f ~> v1 * p.f ~> v2 |-- [F]`
// thm field_conflict(term p, term f, term v1, term v2) {
//   return spec(v2, spec(v1, spec(f, spec(p, field_conflict_axiom))));
// }
// 
// // ## Parameters
// //   p: term `p:slval`
// //
// // ## Returns
// //   a new theorem `p ~> _ == hexists(q; p ~> q)`
// thm undefpointsto_def(term p) {
//   return spec(p, undefpointsto_def_axiom);
// }
// 
// // ## Parameters
// //   tm : term `H`
// //
// // ## Returns
// //   a new theorem `[F] |-- H`
// thm hfalse_explosion(term tm) {
//   return spec(tm, false_explosion_axiom);
// }
// 
// // ## Returns
// //   a definition of [hfalse]
// thm hfalse_def() {
//   return false_def_axiom;
// }
// 
// // ## Parameters
// //   tm : term `H`
// //
// // ## Returns
// //   a new theorem `[F] * H |-- [F]`
// thm hfalse_elim_l(term tm) {
//   return spec(tm, false_elim_l_axiom);
// }
// 
// // ## Parameters
// //   tm : term `H`
// //
// // ## Returns
// //   a new theorem `H * [F] |-- [F]`
// thm hfalse_elim_r(term tm) {
//   return himpl_trans(himpl_sym_l(star_comm(tm, parse_term("hfalse"))), hfalse_elim_l(tm));
// }
// 
// /** Additional Separation Logic Property Currently as Axiom. */
// 
// // ## Parameters
// //   th : theorem `H1 = H2`
// //
// // ## Returns
// //   a new theorem `H1 |-- H2`
// thm himpl_sym_l(thm th) {
//   return mp(himpl_sym_l_axiom, th);
// }
// 
// // ## Parameters
// //   th : theorem `H1 = H2`
// //
// // ## Returns
// //   a new theorem `H2 |-- H1`
// thm himpl_sym_r(thm th) {
//   return himpl_sym_l(symm(th));
// }
// 
// // ## Parameters
// //   tm1 : term `f:num`
// //   tm2 : term `p:slval`
// //
// // ## Returns
// //   a new theorem `NULL.f ~> p |-- [F]`
// thm fieldpointer_invalid(term f, term p) {
//   thm th1 = field_not_null(parse_term("Vptr null"), parse_term("f:num"), parse_term("p:slval"));
//   thm th2 = rewrite_thm(symm(hfalse_def()), th1);
//   term tm_post = dest_bin_snd_comb(concl(th2));
//   thm contra = hfalse_contradiction(himpl_refl(parse_term("hfalse")), tm_post);
//   thm th3 = gen(parse_term("f:num"), 
//     gen(parse_term("p:slval"), himpl_trans(th2, contra)));
//   return spec(p, spec(f, th3));
// }
// 
// // ## Parameters
// //   tm1 : term `P1`
// //   tm2 : term `P2`
// // 
// // ## Returns
// //   a new theorem `[P1] * [P2] = [P1 /\ P2]`
// thm pure_distri(term tm1, term tm2) {
//   return spec(tm2, spec(tm1, pure_distri_axiom));
// }
// 
// // ## Parameters
// //   tm : term `P`
// //
// // ## Returns
// //   a new theorem `~P /\ P = F`
// thm pure_contradiction(term tm) {
//   return spec(tm, pure_contradiction_axiom);
// }
// 
// /** Additional User Interface for Separation Logic Entailment Proof. */
// thm entails(rewrites_item hps[], int len) {
//   thm result = GC_MALLOC(sizeof(struct Gc_Theorem*));
// 
//   result = hps[0].th;
//   for (int i = 1; i < len; ++i) {
//     result = himpl_trans(result, hps[i].th);
//   }
//   return result;
// }
// 
// // ## Parameters
// //   th : theorem `H |- [F]`
// //   tm : term `A` in form of separating conjunctions
// //
// // ## Returns
// //   a new theorem `A |- [F]` if H is in A, `NULL` on failure.
// thm hfalse_contradiction(thm th, term tm) {
//   term tmc = concl(th);
//   if (strcmp(string_of_term(dest_bin_snd_comb(tmc)), "hfalse") ||
//       strcmp(string_of_term(dest_bin_op(tmc)), "entailment")) {
//         return NULL;
//       }
//   term tm0 = dest_bin_fst_comb(tmc);
//   return hfalse_contradiction_aux(th, tm0, tm);
// }
// 
// // ## Parameters
// //   th : theorem `H |- [F]`
// //
// // ## Returns
// //   a new theorem `H == [F]`
// thm hfalse_antisym(thm th) {
//   term tm = concl(th);
//   if (is_bin_op(tm)) {
//     term op = dest_bin_op(tm);
//     term tm1 = dest_bin_fst_comb(tm);
//     term tm2 = dest_bin_snd_comb(tm);
// 
//     if (strcmp(string_of_term(op), "entailment")) {
//       return NULL;
//     }
// 
//     thm hfalse_sym = hfalse_explosion(tm1);
//     return himpl_antisym(th, hfalse_sym);
//   }
//   return NULL;
// }
// 
// static thm hfalse_contradiction_aux(thm th, term tm0, term tm) {
//   // th = `H |- [False]`
//   // tm = `.. * .. * H * ..`
//   if (is_bin_op(tm)) {
//     term op = dest_bin_op(tm);
//     term tm1 = dest_bin_fst_comb(tm);
//     term tm2 = dest_bin_snd_comb(tm);
// 
//     if (strcmp(string_of_term(op), "sepconj")) {
//       return NULL;
//     }
// 
//     if (!strcmp(string_of_term(tm1), string_of_term(tm0))) {
//       return himpl_trans(frame_rule_l(th, tm2), hfalse_elim_l(tm2));
//     } else if (!strcmp(string_of_term(tm2), string_of_term(tm0))) {
//       return himpl_trans(frame_rule_r(th, tm1), hfalse_elim_r(tm1));
//     } else {
//       thm th1 = hfalse_contradiction_aux(th, tm0, tm1);
//       thm th2 = hfalse_contradiction_aux(th, tm0, tm2);
//       if (th1 != NULL) {
//         return himpl_trans(frame_rule_l(th1, tm2), hfalse_elim_l(tm2));
//       } else if (th2 != NULL) {
//         return himpl_trans(frame_rule_r(th2, tm1), hfalse_elim_r(tm1));
//       } else {
//         return NULL;
//       }
//     }
//   }
//   return NULL;
// }





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

/*  Added temporarily  */

// (A \/ ~(A))
thm disj_split(term tm1)
{
  return spec(tm1, disj_split_axiom);
}

// ~(a <= b) ==> (b <= a)
thm int_le(term tm1, term tm2)
{
  return spec(tm2, spec(tm1, int_le_axiom));
}