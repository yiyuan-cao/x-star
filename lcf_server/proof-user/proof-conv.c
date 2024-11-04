#include <proof-conv.h>
#include <string.h>
#include <stdio.h>

bool equal(term tm1, term tm2) {
  return !strcmp(string_of_term(tm1), string_of_term(tm2));
}

thm sep_normalize_(term septerm) {
  if (is_binop(parse_term("hsep"), septerm)) {
    term l = fst_binop(parse_term("hsep"), septerm), r = snd_binop(parse_term("hsep"), septerm);
    if (is_comb(r) && equal(fst_comb(r), parse_term("hfact"))) {
      thm th1 = once_rewrite(get_theorem("hsep_hfact_comm"), septerm);
      septerm = snd_comb(concl(th1));
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

/// Suppose `thl` end with `NULL`.
thm rewrite_list(thm thl[], term tm) {
  if (thl[0] == NULL) return refl(tm);
  thm result = rewrite(thl[0], tm);
  for (int i = 1; ; ++i) {
    if (thl[i] == NULL) break;
    result = trans(result, rewrite(thl[i], snd_comb(concl(result))));
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

thm sep_normalize(term septerm) {
  thm th1 = rewrite_list( 
    (thm[]) { get_theorem("hand_assoc"), 
              symm(get_theorem("hfact_hpure")),
              get_theorem("hfact_hpure_right"),
              symm(get_theorem("hsep_assoc")),
              get_theorem("hsep_hemp_left"),
              get_theorem("hsep_hemp_right"),
              NULL }, septerm);
  septerm = snd_comb(concl(th1));
  thm th2 = sep_normalize_(septerm);
  septerm = snd_comb(concl(th2));
  thm th3 = rewrite(get_theorem("hsep_assoc"), septerm);
  return trans_list((thm[]){th1, th2, th3, NULL});
}

thm sep_normalize_rule(thm th) {
  term septerm = concl(th);
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
    term l = snd_comb(fst_comb(septerm)), r = snd_comb(septerm);
    if (equal(l, lft)) {
      return once_rewrite(lem1, septerm);
    } else {
      if (is_binop(parse_term("hsep"), r)) {
        thm th1 = once_rewrite(sep_lift_(lft, r), septerm);
        septerm = snd_comb(concl(th1));
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
    term l = snd_comb(fst_comb(lft)), r = snd_comb(lft);
    thm th1 = sep_lift(r, septerm);
    septerm = snd_comb(concl(th1));
    thm th2 = sep_lift_(l, septerm);
    septerm = snd_comb(concl(th2));
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
    thm th1 = sep_lift_(l, septerm);
    septerm = snd_comb(concl(th1));
    thm th2 = once_rewrite(sep_cancel(r, snd_comb(septerm)), septerm);
    return trans(th1, th2);
  } else {
    return refl(lft);
  }
}

#define N 100
term exists_list[N];
int exists_count = 0;
#undef N 

thm which_implies(term state, thm th) {
  /// `state` is in the form of `hexists x1..xn. Q1 ** ... ** Qn.
  /// `th` is in the form of `P1 ==> (.. (Pn ==> (Q1 ** ... ** Qn |-- R1 ** ... ** Rn)))`.

  // Destruct `hexists` and record the binders in `exists_list`.
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
  while (1) {
    thm tmp = undisch(th);
    if (tmp == NULL) break;
    th = undisch(th);
  }
  while (1) {
    term hyp = hypth(th);
    if (hyp == NULL) break;
    th = disch(th, hyp);
    th = mp(get_theorem("hfact_elim"), th);
  }
  th = sep_normalize_rule(th);
  term th_pre = fst_binop(parse_term("hentail"), concl(th));
  term th_post = snd_binop(parse_term("hentail"), concl(th));
  
  /*  Apply `trans` theorem .
    First normalize `state` to a form `(trans_pre) * (other)`. Then apply `hsep_cancel_right` 
    rule to get a theorem `(trans_pre) * (other) |-- (trans_post) * (other)`. Finally return 
    the normalized post condition of this entailment. 
  */ 
  term old_state = state;
  thm th1 = sep_normalize(state);
  state = snd_comb(concl(th1));
  thm th2 = sep_lift(th_pre, state);
  state = snd_comb(concl(th2));

  thm entail = spec(snd_binop(parse_term("hsep"), state), mp(get_theorem("hsep_cancel_right"), th));
  entail = sep_normalize_rule(entail);
  thm th_pre_norm = sep_cancel(state, fst_binop(parse_term("hentail"), concl(entail)));
  entail = once_rewrite_rule(th_pre_norm, entail);

  // Construct `hexists` with binders (in order) in `exists_list`.
  for (int i = exists_count; i > 0; --i) {
    entail = gen(exists_list[i], entail);
    entail = mp(get_theorem("hexists_monotone"), entail);
  }

  return entail;
}

