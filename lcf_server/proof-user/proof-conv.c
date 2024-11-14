#include <proof-conv.h>
#include <string.h>
#include <stdio.h>

#define N 100

thm simp(thm th)
{
    return rewrite_rule(refl(parse_term("T")), th);
}

thm once_rewrite_list(thm thl[], term tm) {
  if (thl[0] == NULL) return refl(tm);
  thm result = once_rewrite(thl[0], tm);
  for (int i = 1; ; ++i) {
    if (thl[i] == NULL) break;
    result = trans(result, once_rewrite(thl[i], consequent(conclusion(result))));
  }
  return result;
}

thm once_rewrite_rule_list(thm thl[], thm th) {
  if (thl[0] == NULL) return NULL;
  thm result = once_rewrite_rule(thl[0], th);
  for (int i = 1; ; ++i) {
    if (thl[i] == NULL) break;
    result = once_rewrite_rule(thl[i], result);
  }
  return result;
}

/// Suppose `thl` end with `NULL`.
thm rewrite_list(thm thl[], term tm) {
  if (thl[0] == NULL) return refl(tm);
  thm result = rewrite(thl[0], tm);
  for (int i = 1; ; ++i) {
    if (thl[i] == NULL) break;
    result = trans(result, rewrite(thl[i], consequent(conclusion(result))));
  }
  return result;
}

thm rewrite_rhs(thm th1, thm th2)
{
    return trans(th2, rewrite(th1, consequent(conclusion(th2))));
}

/// Suppose `thl` end with `NULL`.
thm rewrite_list_rhs(thm thl[], thm th) {
  thm result = th;
  for (int i = 0; thl[i] != NULL; ++i) {
    result = rewrite_rhs(thl[i], result);
  }
  return result;
}

term rewrite_term(term th, term tm)
{
    return dest_bin_snd_comb(conclusion(rewrite(assume(th), tm)));
}

thm eq2ent(thm th)
{
    return mp(get_theorem("hentail_sym_left"), th);
}

thm rewrite_after_ent(thm th1, thm th2)
{
    return hent_trans(th2, eq2ent(rewrite(th1, consequent(conclusion(th2)))));
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

thm hent_trans(thm th1, thm th2)
{
    return mp(mp(get_theorem("hentail_trans"), th1), th2);
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

thm hentail_trans_auto(thm th1, thm th2) {
  th1 = sep_normalize_rule(th1);
  th2 = sep_normalize_rule(th2);
  term th1_post = snd_binop(parse_term("hentail"), conclusion(th1));
  term th2_pre = fst_binop(parse_term("hentail"), conclusion(th2));
  thm eq = sep_reorder(th2_pre, th1_post);
  return hentail_trans_list((thm[]){th1, mp(get_theorem("hentail_sym_left"), eq), th2, NULL});
}

thm hentail_trans_auto_list(thm thl[]) {
  thm result = hentail_trans_auto(thl[0], thl[1]);

  for (int i = 2; ; ++i) {
    if (thl[i] == NULL) break;
    result = hentail_trans_auto(result, thl[i]);
  }
  return result;
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

thm sep_reorder(term lft, term septerm) {
  if (is_binop(parse_term("hsep"), lft)) {
    term l = fst_binop(parse_term("hsep"), lft);
    term r = snd_binop(parse_term("hsep"), lft);
    thm th1 = once_rewrite(sep_lift_(l, septerm), septerm);
    septerm = consequent(conclusion(th1));
    thm th2 = once_rewrite(sep_reorder(r, snd_comb(septerm)), septerm);
    return trans(th1, th2);
  } else {
    return refl(lft);
  }
}

// facts to consume/keep
// pure theorem : asmps |- concl
// heap theorem : asmps |- hp1 |-- hp2
// assert all asumps are in cfacts or kfacts
// return : {cfacts} ** {kfacts} ** {hp1s} |-- {kfacts} ** {concls} ** {hp2s}
thm create_trans_auto(term cfactl[], term kfactl[], thm pthl[], thm hthl[])
{
  thm hsep_monotone = get_theorem("hsep_monotone");
  thm hfact_intro = get_theorem("hfact_intro");
  thm hfact_elim = get_theorem("hfact_elim");
  thm hsep_hemp_right = get_theorem("hsep_hemp_right");
  thm hsep_assoc = get_theorem("hsep_assoc");
    thm th = spec(parse_term("emp"), get_theorem("hentail_refl"));
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
  
  thm th_pre_norm = sep_reorder(old_state, fst_binop(parse_term("hentail"), conclusion(entail)));
  entail = once_rewrite_rule(th_pre_norm, entail);

  entail = once_rewrite_rule(
    rewrite_list(
      (thm[]){get_theorem("hfalse_absorb_left"),
              get_theorem("hfalse_absorb_right"), NULL},
      snd_binop(parse_term("hentail"), conclusion(entail))), 
    entail);

  // Construct `hexists` with binders (in order) in `exists_list`.
  for (int i = exists_count; i > 0; --i) {
    entail = gen(exists_list[i], entail);
    entail = mp(get_theorem("hexists_monotone"), entail);
  }

  return entail;
}

thm hfact_auto(term pres[], term posts[], thm helpers[]) {
  thm result = spec(parse_term("emp"), get_theorem("hentail_refl"));
  term hyps[N];
  int hyp_cnt = 0;
  int i = 0;
  while (1) {
    if (pres[ i ] == NULL) break;
    term pre = pres[ i ];
    _Bool in_post = false;
    _Bool in_match = false;
    int j = 0;
    while (1) {
      if (posts[ j ] == NULL) break;
      term post = posts[ j ];
      if (equals_term(pre, post)) {
        in_post = true;
        posts[ j ] = parse_term("F:bool");
        continue;
      }
      term
        t =
        subst(post,
          parse_term("post:bool"),
          subst(pre, parse_term("pre:bool"), parse_term("pre ==> post")));
      thm arith = arith_rule(t);
      int k = 0;
      while (1) {
        if (helpers[k] == NULL) break;
        thm helper = helpers[k];
        if (equals_term(t, conclusion(helper))) arith = helper;
        k = k + 1;
      }
      if (equals_term(conclusion(arith), t)) {
        in_match = true;
        result = mp(mp(get_theorem("hfact_intro"), mp(arith, assume(pre))),
          result);
        posts[ j ] = parse_term("F:bool");
      }
      j = j + 1;
    }
    if (in_post) { hyps[ hyp_cnt ] = pre; hyp_cnt = hyp_cnt + 1; }
    else
      if (in_match) {
        result = mp(get_theorem("hfact_elim"), disch(result, hypth(result)));
      }
      else {
        result = add_assum(pre, result);
        result = mp(get_theorem("hfact_elim"), disch(result, hypth(result)));
      }
    i = i + 1;
  }
  i = 0;
  while (i < hyp_cnt) { result = add_assum(hyps[ i ], result); i = i + 1; }
  return sep_normalize_rule(result);
}

// ent : hp |- hpx x
// eq : x = y
// return : hp |- exists y. hpx y
thm hexists_intro_auto(thm ent, term eq)
{
    term state = dest_bin_snd_comb(conclusion(ent));
    term exists_list[N];
    int exists_count = 0;
    while (is_binder("hexists", state)) {
        exists_list[++exists_count] = binder_var("hexists", state);
        state = binder_body("hexists", state);
    }

    thm th = spec(state, get_theorem("hentail_refl"));
    thm absth = abs_term(state, eq);
    th = hentail_trans_list((thm[]){th, eq2ent(absth), NULL});
    th = mp(get_theorem("hexists_intro"), th);
    th = simp(th);
    
    for (int i = exists_count; i > 0; --i) {
        th = gen(exists_list[i], th);
        th = mp(get_theorem("hexists_monotone"), th);
    }
    return hent_trans(ent, th);
}

bool compare_hprop_(term hp1, term hp2)
{
    thm th = sep_reorder(hp1, hp2);
    if(strcmp(string_of_term(hp1), string_of_term(dest_bin_snd_comb(conclusion(th))))) 
    {
        printf("Fail to match!\n");
        printf("%s\n\n%s\n\n", string_of_term(hp1), string_of_term(dest_bin_snd_comb(conclusion(th))));
        return 0;
    }
    if(strcmp(string_of_term(hp2), string_of_term(dest_bin_fst_comb(conclusion(th))))) 
    {
        printf("Fail to match!\n");
        printf("%s\n\n%s\n\n", string_of_term(hp2), string_of_term(dest_bin_fst_comb(conclusion(th))));
        return 0;
    }
    printf("Match!\n");
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

thm unfold(term hp, thm def)
{
    thm th = rewrite(def, hp);
    return eq2ent(th);
}
thm fold(term hp, thm def)
{
    thm th = rewrite(def, hp);
    return eq2ent(symm(th));
}

thm use_fact_rewrite(term fact, term target)
{
    thm th = assume(fact);
    th = rewrite(th, target);
    th = eq2ent(th);
    return th;
}
thm use_fact_symm_rewrite(term fact, term target)
{
    thm th = symm(assume(fact));
    th = rewrite(th, target);
    th = eq2ent(th);
    return th;
}