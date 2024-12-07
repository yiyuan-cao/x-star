#include <cstar.h>
#include <stdlib.h>
#include <string.h>
FILE* fp = NULL;
char buf[10000];

;

;

thm array_at_zero_length(term t1, term t2, term t3) {
  thm
    array_at_zero_length =
    symm(get_theorem("array_at_replicate_zero_length")); 
fputs(strcat(strcat(strcpy(buf,"5#8#\""), string_of_thm(array_at_zero_length)), "\"\n"), fp);
  return spec(t3, spec(t2, spec(t1, array_at_zero_length)));
}

thm add_emp_equiv_right(thm th, term state) {
  thm
    hentail_sym_left =
    get_theorem("hentail_sym_left"); 
fputs(strcat(strcat(strcpy(buf,"12#8#\""), string_of_thm(hentail_sym_left)), "\"\n"), fp);
  thm
    hsep_hemp_right =
    spec(state, symm(get_theorem("hsep_hemp_right"))); 
fputs(strcat(strcat(strcpy(buf,"13#8#\""), string_of_thm(hsep_hemp_right)), "\"\n"), fp);
  thm
    result =
    mp(hentail_sym_left, hsep_hemp_right); 
fputs(strcat(strcat(strcpy(buf,"14#8#\""), string_of_thm(result)), "\"\n"), fp);
  result = sep_normalize_rule(rewrite_rule(th, result));
  return result;
}

thm array_at_last_split(term t1, term t2, term t3, term t4) {
  return spec(t4,
    spec(t3, spec(t2, spec(t1, get_theorem("array_at_last_split")))));
}

thm undef_array_at_select_first(term t1, term t2, term t3) {
  thm
    undef_array_at_rec_def =
    get_theorem("undef_array_at_rec_def"); 
fputs(strcat(strcat(strcpy(buf,"28#8#\""), string_of_thm(undef_array_at_rec_def)), "\"\n"), fp);
  thm
    result =
    spec(t3, spec(t2, spec(t1, undef_array_at_rec_def))); 
fputs(strcat(strcat(strcpy(buf,"29#8#\""), string_of_thm(result)), "\"\n"), fp);
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

thm hfact_manual(term pre1, term pre2, term post) {
  thm
    arith =
    undisch(undisch(arith_rule(subst(post,
            parse_term("post:bool"),
            subst(pre2,
              parse_term("pre2:bool"),
              subst(pre1,
                parse_term("pre1:bool"),
                parse_term("pre1 ==> pre2 ==> post"))))))); 
fputs(strcat(strcat(strcpy(buf,"50#8#\""), string_of_thm(arith)), "\"\n"), fp);
  thm
    result =
    spec(parse_term("emp"), get_theorem("hentail_refl")); 
fputs(strcat(strcat(strcpy(buf,"51#8#\""), string_of_thm(result)), "\"\n"), fp);
  result = mp(mp(get_theorem("hfact_intro"), arith), result);
  result = mp(get_theorem("hfact_elim"), disch(result, hypth(result)));
  result = mp(get_theorem("hfact_elim"), disch(result, hypth(result)));
  return sep_normalize_rule(result);
}

void clear() {
  term
    unmodified =
    parse_term("data_at(&\"to\", Tptr, to_pre) **\n                       data_at(&\"len\", Tint, n)"); 
fputs(strcat(strcat(strcpy(buf,"65#10#\""), string_of_term(unmodified)), "\"\n"), fp);
  __state = subst(unmodified,
    parse_term("unmodified:hprop"),
    parse_term("\n      fact(n >= &0) **\n      unmodified **\n      undef_array_at(to_pre, Tchar, n) \n  "));
  __state = subst(unmodified,
    parse_term("unmodified:hprop"),
    parse_term("\n    fact(n >= &0) ** \n    data_at(&\"i\", Tint, &0) **\n    unmodified **\n    undef_array_at(to_pre, Tchar, n)\n  "));
  {
    term
      pre_state =
      get_symbolic_state(); 
fputs(strcat(strcat(strcpy(buf,"86#12#\""), string_of_term(pre_state)), "\"\n"), fp);
    thm
      emp_equiv_thm =
      array_at_zero_length(parse_term("to_pre:int"),
        parse_term("Tchar"),
        parse_term("&0:int")); 
fputs(strcat(strcat(strcpy(buf,"87#12#\""), string_of_thm(emp_equiv_thm)), "\"\n"), fp);
    thm
      final_thm =
      add_emp_equiv_right(emp_equiv_thm, pre_state); 
fputs(strcat(strcat(strcpy(buf,"89#12#\""), string_of_thm(final_thm)), "\"\n"), fp);
    set_symbolic_state(sep_normalize_rule(final_thm));
  }
  __state = subst(unmodified,
    parse_term("unmodified:hprop"),
    parse_term("\n    fact(n >= &0) ** \n    data_at(&\"i\", Tint, &0) **\n    unmodified **\n    undef_array_at(to_pre, Tchar, n) **\n    array_at(to_pre, Tchar, replicate(&0, &0))\n  "));
  {
    term
      pre_state =
      get_symbolic_state(); 
fputs(strcat(strcat(strcpy(buf,"105#12#\""), string_of_term(pre_state)), "\"\n"), fp);
    thm
      hfact_thm =
      hfact_auto((term[]){ parse_term("n >= &0"), NULL },
        (term[]){
          parse_term("n >= &0"),
          parse_term("&0 <= &0"),
          parse_term("&0 <= n"),
          NULL
        },
        (thm[]){ NULL }); 
fputs(strcat(strcat(strcpy(buf,"106#12#\""), string_of_thm(hfact_thm)), "\"\n"), fp);
    thm
      undef_array_simpl =
      mp(get_theorem("hentail_sym_left"),
        symm(rewrite_list((thm[]){
              arith_rule(parse_term("to_pre + &0 * sizeof(Tchar) = to_pre")),
              arith_rule(parse_term("n - &0 = n")),
              NULL
            },
            parse_term("undef_array_at(to_pre + &0 * sizeof(Tchar), Tchar, n - &0)")))); 
fputs(strcat(strcat(strcpy(buf,"109#12#\""), string_of_thm(undef_array_simpl)), "\"\n"), fp);
    thm
      hsep_mono =
      hsep_monotone(hfact_thm, undef_array_simpl); 
fputs(strcat(strcat(strcpy(buf,"115#12#\""), string_of_thm(hsep_mono)), "\"\n"), fp);
    thm
      final_thm =
      local_apply(pre_state, hsep_mono); 
fputs(strcat(strcat(strcpy(buf,"116#12#\""), string_of_thm(final_thm)), "\"\n"), fp);
    set_symbolic_state(final_thm);
  }
  __state = subst(unmodified,
    parse_term("unmodified:hprop"),
    parse_term("\n    fact(&0 <= &0) ** fact(&0 <= n) **\n    fact(n >= &0) **\n    data_at(&\"i\", Tint, &0) **\n    unmodified **\n    array_at(to_pre, Tchar, replicate(&0, &0)) **\n    undef_array_at(to_pre + &0 * sizeof(Tchar), Tchar, n - &0)\n  "));
  __state = subst(unmodified,
    parse_term("unmodified:hprop"),
    parse_term("\n        exists (i_v:int).\n        fact(&0 <= i_v) ** fact(i_v <= n) **\n        data_at(&\"i\", Tint, i_v) **\n        unmodified **\n        array_at(to_pre, Tchar, replicate(i_v, &0)) ** \n        undef_array_at(to_pre + i_v * sizeof(Tchar), Tchar, n - i_v)\n    "));
  {
    __state = subst(unmodified,
      parse_term("unmodified:hprop"),
      parse_term("\n        exists (i_v:int).\n        fact(i_v < n) ** \n        fact(&0 <= i_v) ** fact(i_v <= n) ** \n        fact(n >= &0) **\n        data_at(&\"i\", Tint, i_v) **\n        unmodified **\n        array_at(to_pre, Tchar, replicate(i_v, &0)) **\n        undef_array_at(to_pre + i_v * sizeof(Tchar), Tchar, n - i_v)\n    "));
    {
      thm
        dest_undef_array =
        undef_array_at_select_first(parse_term("to + i * sizeof(Tchar)"),
          parse_term("Tchar"),
          parse_term("len - i")); 
fputs(strcat(strcat(strcpy(buf,"153#14#\""), string_of_thm(dest_undef_array)), "\"\n"), fp);
      thm
        *arith_facts =
        (thm[]){
          arith_rule(parse_term("len - i > &0 <=> i < len")),
          arith_rule(parse_term("len - i - 1 == len - (i + &1)")),
          arith_rule(parse_term("(to + i * sizeof(Tchar)) + sizeof(Tchar) ==\n                        to + (i + &1) * sizeof(Tchar)")),
          NULL
        };
      dest_undef_array = rewrite_rule_list(arith_facts, dest_undef_array);
      thm
        final_thm =
        local_apply(get_symbolic_state(), dest_undef_array); 
fputs(strcat(strcat(strcpy(buf,"169#14#\""), string_of_thm(final_thm)), "\"\n"), fp);
      set_symbolic_state(final_thm);
    }
    __state = subst(unmodified,
      parse_term("unmodified:hprop"),
      parse_term("\n        exists (i_v:int).\n        fact(i_v < n) ** \n        fact(&0 <= i_v) ** fact(i_v <= n) ** \n        fact(n >= &0) **\n        data_at(&\"i\", Tint, i_v) **\n        unmodified ** \n        array_at(to_pre, Tchar, replicate(i_v, &0)) **\n        undef_data_at(to_pre + i_v * sizeof(Tchar), Tchar) **\n        undef_array_at(to_pre + (i_v + &1) * sizeof(Tchar), Tchar, n - (i_v + 1))\n    "));
    __state = subst(unmodified,
      parse_term("unmodified:hprop"),
      parse_term("\n        exists (i_v:int).\n        fact(i_v < n) ** \n        fact(&0 <= i_v) ** fact(i_v <= n) ** \n        fact(n >= &0) **\n        data_at(&\"i\", Tint, i_v) **\n        unmodified ** \n        array_at(to_pre, Tchar, replicate(i_v, &0)) **\n        data_at(to_pre + i_v * sizeof(Tchar), Tchar, &0) **\n        undef_array_at(to_pre + (i_v + &1) * sizeof(Tchar), Tchar, n - (i_v + &1))\n    "));
    __state = subst(unmodified,
      parse_term("unmodified:hprop"),
      parse_term("\n        exists (i_v:int).\n        fact(i_v < n) ** \n        fact(&0 <= i_v) ** fact(i_v <= n) ** \n        fact(n >= &0) **\n        data_at(&\"i\", Tint, i_v + &1) **\n        unmodified ** \n        array_at(to_pre, Tchar, replicate(i_v, &0)) **\n        data_at(to_pre + i_v * sizeof(Tchar), Tchar, &0) **\n        undef_array_at(to_pre + (i_v + &1) * sizeof(Tchar), Tchar, n - (i_v + &1))\n    "));
    {
      term
        pre_state =
        get_symbolic_state(); 
fputs(strcat(strcat(strcpy(buf,"218#14#\""), string_of_term(pre_state)), "\"\n"), fp);
      thm
        array_at_last =
        array_at_last_split(parse_term("to_pre:int"),
          parse_term("Tchar"),
          parse_term("&0"),
          parse_term("i_v:int")); 
fputs(strcat(strcat(strcpy(buf,"219#14#\""), string_of_thm(array_at_last)), "\"\n"), fp);
      array_at_last = rewrite_rule(arith_rule(parse_term("(i_v >= &0) <=> (&0 <= i_v)")),
        array_at_last);
      thm
        final_thm =
        local_apply(pre_state, array_at_last); 
fputs(strcat(strcat(strcpy(buf,"221#14#\""), string_of_thm(final_thm)), "\"\n"), fp);
      set_symbolic_state(final_thm);
    }
    __state = subst(unmodified,
      parse_term("unmodified:hprop"),
      parse_term("\n        exists (i_v:int).\n        fact(i_v < n) ** \n        fact(&0 <= i_v) ** fact(i_v <= n) ** \n        fact(n >= &0) **\n        data_at(&\"i\", Tint, i_v + &1) **\n        unmodified ** \n        array_at(to_pre, Tchar, replicate(i_v + &1, &0)) **\n        undef_array_at(to_pre + (i_v + &1) * sizeof(Tchar), Tchar, n - (i_v + &1))\n    "));
    {
      term
        pre_state =
        get_symbolic_state(); 
fputs(strcat(strcat(strcpy(buf,"239#14#\""), string_of_term(pre_state)), "\"\n"), fp);
      thm
        hfact_thm =
        hfact_auto((term[]){
            parse_term("n >= &0"),
            parse_term("i_v < n"),
            parse_term("&0 <= i_v"),
            parse_term("i_v <= n"),
            NULL
          },
          (term[]){
            parse_term("n >= &0"),
            parse_term("i_v + &1 <= n"),
            parse_term("&0 <= i_v + &1"),
            NULL
          },
          (thm[]){ NULL }); 
fputs(strcat(strcat(strcpy(buf,"240#14#\""), string_of_thm(hfact_thm)), "\"\n"), fp);
      thm
        final_thm =
        local_apply(pre_state, hfact_thm); 
fputs(strcat(strcat(strcpy(buf,"243#14#\""), string_of_thm(final_thm)), "\"\n"), fp);
      set_symbolic_state(final_thm);
    }
    __state = subst(unmodified,
      parse_term("unmodified:hprop"),
      parse_term("\n        exists (i_v:int).\n        fact(&0 <= i_v + &1) ** (i_v + &1 <= n) **\n        fact(n >= &0) **\n        data_at(&\"i\", Tint, i_v + &1) **\n        unmodified ** \n        array_at(to_pre, Tchar, replicate(i_v + &1, &0)) **\n        undef_array_at(to_pre + (i_v + &1) * sizeof(Tchar), Tchar, n - (i_v + 1))\n    "));
  }
  __state = subst(unmodified,
    parse_term("unmodified:hprop"),
    parse_term("\n      exists (i_v:int).\n      fact(i_v >= (n:int)) ** \n      fact(&0 <= i_v) ** fact(i_v <= n) ** \n      fact(n >= &0) **\n      data_at(&\"i\", Tint, i_v) **\n      unmodified ** \n      array_at(to_pre, Tchar, replicate(i_v, &0)) **\n      undef_array_at(to_pre + i_v * sizeof(Tchar), Tchar, n - i_v)\n  "));
  tmp_term = normalize(subst(unmodified,
      parse_term("unmodified:hprop"),
      parse_term("fact(n >= &0) ** fact (&0 <= i_v) **\n        data_at(&\"i\", Tint, i_v) **\n        unmodified ** \n        array_at(to_pre, Tchar, replicate(i_v, &0)) **\n        undef_array_at(to_pre + i_v * sizeof(Tchar), Tchar, n - i_v)")));
  {
    term
      pre_state =
      get_symbolic_state(); 
fputs(strcat(strcat(strcpy(buf,"279#12#\""), string_of_term(pre_state)), "\"\n"), fp);
    thm
      hfact1 =
      hfact_manual(parse_term("(i_v:int) >= n"),
        parse_term("(i_v:int) <= n"),
        parse_term("(i_v:int) == n")); 
fputs(strcat(strcat(strcpy(buf,"280#12#\""), string_of_thm(hfact1)), "\"\n"), fp);
    hfact1 = local_apply(normalize(binder_body("hexists", pre_state)), hfact1);
    thm
      subst_i_v =
      mp(get_theorem("hentail_sym_left"),
        rewrite(assume(parse_term("(i_v:int) = n")), tmp_term)); 
fputs(strcat(strcat(strcpy(buf,"283#12#\""), string_of_thm(subst_i_v)), "\"\n"), fp);
    subst_i_v = mp(get_theorem("hfact_elim"),
      disch(subst_i_v, hypth(subst_i_v)));
    thm
      hfact2 =
      hfact_auto((term[]){ parse_term("n >= &0"), parse_term("&0 <= n"), NULL },
        (term[]){ parse_term("n >= &0"), NULL },
        (thm[]){ NULL }); 
fputs(strcat(strcat(strcpy(buf,"287#12#\""), string_of_thm(hfact2)), "\"\n"), fp);
    hfact2 = local_apply(consequent(conclusion(subst_i_v)), hfact2);
    thm
      without_exists =
      hentail_trans_auto_list((thm[]){ hfact1, subst_i_v, hfact2, NULL }); 
fputs(strcat(strcat(strcpy(buf,"291#12#\""), string_of_thm(without_exists)), "\"\n"), fp);
    thm
      final_thm =
      mp(get_theorem("hexists_elim"),
        gen(parse_term("i_v:int"), without_exists)); 
fputs(strcat(strcat(strcpy(buf,"292#12#\""), string_of_thm(final_thm)), "\"\n"), fp);
    set_symbolic_state(final_thm);
  }
  __state = subst(unmodified,
    parse_term("unmodified:hprop"),
    parse_term("\n      fact(n >= &0) **\n      data_at(&\"i\", Tint, n) **\n      unmodified ** \n      array_at(to_pre, Tchar, replicate(n, &0)) **\n      undef_array_at(to_pre + n * sizeof(Tchar), Tchar, n - n)\n  "));
  {
    term
      pre_state =
      get_symbolic_state(); 
fputs(strcat(strcat(strcpy(buf,"307#12#\""), string_of_term(pre_state)), "\"\n"), fp);
    thm
      undef_array_elim =
      undef_array_at_zero_length(parse_term("to_pre + n * sizeof(Tchar)"),
        parse_term("Tchar")); 
fputs(strcat(strcat(strcpy(buf,"308#12#\""), string_of_thm(undef_array_elim)), "\"\n"), fp);
    undef_array_elim = rewrite_rule(arith_rule(parse_term("&0 = (n:int) - n")),
      undef_array_elim);
    thm
      final_thm =
      local_apply(pre_state, undef_array_elim); 
fputs(strcat(strcat(strcpy(buf,"310#12#\""), string_of_thm(final_thm)), "\"\n"), fp);
    set_symbolic_state(final_thm);
  }
  __state = subst(unmodified,
    parse_term("unmodified:hprop"),
    parse_term("\n      fact(n >= &0) **\n      data_at(&\"i\", Tint, n) **\n      unmodified ** \n      array_at(to_pre, Tchar, replicate(n, &0))\n  "));
}
int main() { cst_init(); char path[100]="./";
char filename[30];
sscanf(__BASE_FILE__, "%[^.]", filename);
fp = fopen(strcat(strcat(path, filename),"_log.csv"), "w");
clear();
fclose(fp);
 return 0; }