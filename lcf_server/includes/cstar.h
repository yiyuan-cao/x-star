#ifndef CSTAR_HEADER
#define CSTAR_HEADER
#pragma GCC diagnostic ignored "-Wunknown-attributes"
#include <stddef.h>
#include <stdio.h>
#include <proof-kernel.h>
#include <proof-user.h>
#include <proof-conv.h>

#define N 100

// Global variables for temporary terms, goals, and theorems
term tmp_term, tmp_term1, tmp_term2, tmp_term3, tmp_term4;
term tmp_goal;
thm tmp_thm;
term __state, __transform; 

thm array_at_zero_length(term t1, term t2, term t3) { 
  thm array_at_zero_length = symm(get_theorem("array_at_replicate_zero_length"));
  return spec(t3, spec(t2, spec(t1, array_at_zero_length)));
}

thm add_emp_equiv_right(thm th, term state) {
  thm hentail_sym_left = get_theorem("hentail_sym_left");
  thm hsep_hemp_right = spec(state, symm(get_theorem("hsep_hemp_right")));
  thm result = mp(hentail_sym_left, hsep_hemp_right);
  result = sep_normalize_rule(rewrite_rule(th, result));
  return result;
}

thm array_at_last_split(term t1, term t2, term t3, term t4) {
  return spec(t4, spec(t3, spec(t2, spec(t1, get_theorem("array_at_last_split")))));
}

thm undef_array_at_select_first(term t1, term t2, term t3) {
  thm undef_array_at_rec_def = get_theorem("undef_array_at_rec_def");
  thm result = spec(t3, spec(t2, spec(t1, undef_array_at_rec_def)));
  result = mp(get_theorem("hentail_sym_left"), undisch(result));
  return disch(result, hypth(result));
}

thm hsep_monotone(thm th1, thm th2) {
  return sep_normalize_rule(mp(mp(get_theorem("hsep_monotone"), th1), th2));
}

thm undef_array_at_zero_length(term t1, term t2) {
  return mp(get_theorem("hentail_sym_left"), 
      spec(t2, spec(t1, get_theorem("undef_array_at_zero_length"))));
}

thm hentail_trans_auto(thm th1, thm th2) {
  th1 = sep_normalize_rule(th1);
  th2 = sep_normalize_rule(th2);
  term th1_post = snd_binop(parse_term("hentail"), conclusion(th1));
  term th2_pre = fst_binop(parse_term("hentail"), conclusion(th2));
  thm eq = sep_cancel(th2_pre, th1_post);

  if (!equals_term(th1_post, fst_binop(parse_term("(=):hprop->hprop->bool"), conclusion(eq)))) puts("1!!!");
  if (!equals_term(th2_pre, snd_binop(parse_term("(=):hprop->hprop->bool"), conclusion(eq)))) puts("2!!!");
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

/* Symbolic execution. */
term get_symbolic_state() { return __state; }
void set_symbolic_state(thm th) { 
  __state = snd_binop(parse_term("hentail"), conclusion(th));
  printf("%s\n\n", string_of_term(__state));
}

#endif