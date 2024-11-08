#include <proof-conv.h>
#include <string.h>
#include <stdio.h>

#define N 100

/// Suppose `thl` end with `NULL`.
thm rewrite_list(thm thl[], term tm) {
  if (thl[0] == NULL) return refl(tm);
  thm result = rewrite(thl[0], tm);
  for (int i = 1; ; ++i) {
    if (thl[i] == NULL) break;
    result = trans(result, rewrite(thl[i], snd_comb(conclusion(result))));
  }
  return result;
}

/// Suppose `thl` end with `NULL`.
thm trans_list(thm thl[]) {
  if (thl[0] == NULL) return NULL;
  thm result = thl[0];
  for (int i = 1; ; ++i) {
    if (thl[i] == NULL) break;
    result = trans(result, thl[i]);
  }
  return result;
}

/// Suppose `thl` end with `NULL`.
thm rewrite_rule_list(thm thl[], thm th) {
  if (thl[0] == NULL) return NULL;
  thm result = rewrite_rule(thl[0], th);
  for (int i = 1; ; ++i) {
    if (thl[i] == NULL) break;
    result = rewrite_rule(thl[i], result);
  }
  return result;
}

thm hentail_trans_list(thm thl[]) {
  thm hentail_trans = get_theorem("hentail_trans");
  thm result = thl[0];

  for (int i = 1; ; ++i) {
    if (thl[i] == NULL) break;
    result = mp(mp(hentail_trans, result), thl[i]);
  }
  return result;
}


bool has_typ(thm th) {
  return !equals_thm(new_axiom(conclusion(th)), th);
}

term normalize(term septerm) {
  return consequent(conclusion(sep_normalize(septerm)));
}

thm sep_normalize_(term septerm) {
  if (is_binop(parse_term("hsep"), septerm)) {
    term l = fst_binop(parse_term("hsep"), septerm), r = snd_binop(parse_term("hsep"), septerm);
    if (is_comb(r) && equals_term(fst_comb(r), parse_term("hfact"))) {
      thm th1 = once_rewrite(get_theorem("hsep_hfact_comm"), septerm);
      septerm = snd_comb(conclusion(th1));
      r = snd_comb(septerm);
      thm th2 = once_rewrite(sep_normalize_(r), septerm);
      return trans(th1, th2);
    } else {
      return once_rewrite(sep_normalize_(l), septerm);
    } 
  } else {
    return refl(septerm);
  }
}

thm sep_normalize(term septerm) {
  thm th1 = rewrite_list( 
    (thm[]) { get_theorem("hand_assoc"), 
              symm(get_theorem("hfact_hpure")),
              get_theorem("hfact_hpure_right"),
              symm(get_theorem("hsep_assoc")),
              get_theorem("hsep_hemp_left"),
              get_theorem("hsep_hemp_right"),
              NULL }, septerm);
  septerm = consequent(conclusion(th1));
  thm th2 = sep_normalize_(septerm);
  septerm = consequent(conclusion(th2));
  thm th3 = rewrite(get_theorem("hsep_assoc"), septerm);
  return trans_list((thm[]){th1, th2, th3, NULL});
}

thm sep_normalize_rule(thm th) {
  term septerm = conclusion(th);
  if (is_binop(parse_term("hentail"), septerm)) {
    term l = fst_binop(parse_term("hentail"), septerm), r = snd_binop(parse_term("hentail"), septerm);
    th = rewrite_rule(sep_normalize(l), th);
    th = rewrite_rule(sep_normalize(r), th);
    return th;
  } else {
    return th;
  }
}

thm sep_lift_(term lft, term septerm) {
  thm lem1 = spec(lft, get_theorem("hsep_comm_left_part"));

  if (is_binop(parse_term("hsep"), septerm)) {
    term l = fst_binop(parse_term("hsep"), septerm), r = snd_binop(parse_term("hsep"), septerm);
    if (equals_term(l, lft)) {
      return once_rewrite(lem1, septerm);
    } else {
      if (is_binop(parse_term("hsep"), r)) {
        thm th1 = once_rewrite(sep_lift_(lft, r), septerm);
        septerm = consequent(conclusion(th1));
        thm th2 = once_rewrite(lem1, septerm);
        return trans(th1, th2);
      } else {
        return once_rewrite(symm(get_theorem("hsep_comm")), septerm);
      }
    }
  } else {
    return refl(septerm);
  }
}

thm sep_lift(term lft, term septerm) {
  if (is_binop(parse_term("hsep"), lft)) {
    term l = fst_binop(parse_term("hsep"), lft), r = snd_binop(parse_term("hsep"), lft);
    thm th1 = sep_lift(r, septerm);
    septerm = consequent(conclusion(th1));
    thm th2 = sep_lift_(l, septerm);
    septerm = consequent(conclusion(th2));
    thm th3 = once_rewrite(symm(get_theorem("hsep_assoc")), septerm);
    return trans_list((thm[]){th1, th2, th3, NULL});
  } else {
    return sep_lift_(lft, septerm);
  }
}

thm sep_cancel(term lft, term septerm) {
  if (is_binop(parse_term("hsep"), lft)) {
    term l = fst_binop(parse_term("hsep"), lft);
    term r = snd_binop(parse_term("hsep"), lft);
    thm th1 = once_rewrite(sep_lift_(l, septerm), septerm);
    septerm = consequent(conclusion(th1));
    thm th2 = once_rewrite(sep_cancel(r, snd_comb(septerm)), septerm);
    return trans(th1, th2);
  } else {
    return refl(lft);
  }
}

thm which_implies(term state, thm th) {
  /// `state` is in the form of `hexists x1..xn. Q1 ** ... ** Qx.
  /// `th` is in the form of `P1 ==> (.. (Pn ==> (Q1 ** ... ** Qm |-- R1 ** ... ** Rs)))`.
  /// suppose pre- and post-condition of `th` are not `emp`.

  // Destruct `hexists` and record the binders in `exists_list`.
  term exists_list[N];
  int exists_count = 0;
  while (is_binder("hexists", state)) {
    exists_list[++exists_count] = binder_var("hexists", state);
    state = binder_body("hexists", state);
  }

  /*  Handling hypotheses. 
    Note: Because we don't have exception handling in C, it may raise "OCaml exception: {}" 
    when we call a function with return value `Failure _` in OCaml. In CStar, we can 
    figure this out by check if the return value is `NULL`, and (temporarily) ignore 
    the error information raised by OCaml (actually Rust). 
  */
  while (is_binop(parse_term("==>"), conclusion(th))) {
    thm tmp = undisch(th);
    if (tmp == NULL) break;
    th = undisch(th);
  }
  while (has_typ(th)) {
    term hyp = hypth(th);
    if (hyp == NULL) break;
    th = disch(th, hyp);
    th = mp(get_theorem("hfact_elim_dup"), th);
  }
  th = sep_normalize_rule(th);
  term th_pre = fst_binop(parse_term("hentail"), conclusion(th));
  term th_post = snd_binop(parse_term("hentail"), conclusion(th));
  /*  Apply `trans` theorem .
    First normalize `state` to a form `(trans_pre) * (other)`. Then apply `hsep_cancel_right` 
    rule to get a theorem `(trans_pre) * (other) |-- (trans_post) * (other)`. Finally return 
    the normalized post condition of this entailment. 
  */ 
  thm th1 = sep_normalize(state);
  state = consequent(conclusion(th1));
  term old_state = state;
  thm th2 = sep_lift(th_pre, state);
  state = consequent(conclusion(th2));
  
  thm entail = spec(snd_binop(parse_term("hsep"), state), mp(get_theorem("hsep_cancel_right"), th));
  entail = sep_normalize_rule(entail);

  
  thm th_pre_norm = sep_cancel(old_state, fst_binop(parse_term("hentail"), conclusion(entail)));
  entail = once_rewrite_rule(th_pre_norm, entail);

  // Construct `hexists` with binders (in order) in `exists_list`.
  for (int i = exists_count; i > 0; --i) {
    entail = gen(exists_list[i], entail);
    entail = mp(get_theorem("hexists_monotone"), entail);
  }

  return entail;
}

// [[cstar::function(
// thm hfact_auto(term pres[], term posts[]) {
//   thm result = spec(`emp`, get_theorem("hentail_refl")); // emp |-- emp
//   term pre_conj = `T`;
// 
//   int i = 0;
//   while (1) {
//     if (pres[i] == NULL) break;
//     term pre = pres[i];
//     pre_conj = `(${pre_conj:bool}) /\ (${pre:bool})`;
//     i = i + 1;
//   }
// 
//   i = 0;
//   while (1) {
//     if (posts[i] == NULL) break;
//     term post = posts[i];
//     term check_post_i = `${pre_conj:bool} ==> ${post:bool}`;
//     thm arith = arith_rule(check_post_i);
//     if (equals_term(conclusion(arith), check_post_i)) {
//       result = mp(mp(get_theorem("hfact_intro"), mp(arith, assume(pre_conj))), result);
//     }
//     i = i + 1;
//   }
// 
//   puts("hfact_auto");
//   puts(string_of_thm(result));
// 
//   i = 0;
//   while (1) {
//     if (pres[i] == NULL) break;
//     int j = 0;
//     while (1) {
//       if (posts[j] == NULL) break;
//       if (equals_term(pres[i], posts[j])) {
// 
//       }
//       j = j + 1;
//     }
//     i = i + 1;
//   }
// 
//   return sep_normalize_rule(result);
// }
// )]];