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
