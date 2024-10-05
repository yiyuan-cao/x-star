#include <stdint.h>
#include <stdio.h>
#include "host.h"
#include "sl.h"

// extracted from reverse.c
indtype i32_list;
thm is_nil, is_cons, head, tail;
thm append, reverse, i32_ll_repr;

void ghost_function() {
  i32_list = define_type("i32_list = nil | cons int i32_list");

  // constructors
  new_constant("is_nil", parse_type("i32_list->bool"));
  is_nil = new_axiom(parse_term(
    "(is_nil nil = true) && (is_nil (cons h t) = false)"
  ));
  // discriminators
  new_constant("is_cons", parse_type("i32_list->bool"));
  is_cons = new_axiom(parse_term(
    "(is_cons nil = false) && (is_cons (cons h t) = true)"
  ));
  new_constant("head", parse_type("i32_list->int"));
  head = new_axiom(parse_term(
    "head (cons h t) = h"
  ));
  new_constant("tail", parse_type("i32_list->i32_list"));
  tail = new_axiom(parse_term(
    "tail (cons h t) = t"
  ));

  // ghost functions
  new_constant("append", parse_type("i32_list->i32_list->i32_list"));
  append = new_axiom(parse_term(
    "append l1 l2 = \
      if (is_nil l1) then l2 else \
        (cons (head l1) (append (tail l1) l2))"
  ));

  new_constant("reverse", parse_type("i32_list->i32_list"));
  reverse = new_axiom(parse_term(
    "reverse l = \
      if (is_nil l) then nil else \
        let h = head l in \
        let rev_t = reverse (tail l) in \
          (append rev_t (cons h nil))"
  ));

  // data_at : ptr -> (t: c_type) -> reprtype(t) -> hprop
  new_constant("data_at_int", parse_type("ptr#int->hprop"));
  new_constant("data_at_ptr", parse_type("ptr#ptr->hprop"));
  new_constant("data_at_struct_int_ll_node", parse_type("ptr#(int#ptr)->hprop"));
  new_constant("i32_ll_repr", parse_type("ptr->i32_list->hprop"));
  i32_ll_repr = new_axiom(parse_term(
    "i32_ll_repr p l = \
      if (is_nil l) then (PURE (p = Pnull)) SEPAND EMP else \
        let h = head l in \
        let t = tail l in \
        hexists value. data_at_int(fieldaddr(p,0), value) SEP \
        hexists next. data_at_ptr(fieldaddr(p,1), next) SEP \
          (PURE (value = h)) SEPAND (i32_ll_repr next t)"
  ));
  printf("%s\n", string_of_thm(i32_ll_repr));
}

term eq_r(thm t) {
  return dest_comb_snd(concl(t));
}

thm app_nil_r_base() {
  thm th1 = ONCE_REWRITE_CONV1(append, parse_term("append nil nil"));
  thm th2 = ONCE_REWRITE_CONV1(is_nil, eq_r(th1));
  return TRANS(TRANS(th1, th2), CONDS_ELIM_CONV(eq_r(th2)));
}

thm app_nil_r_induct() {
  thm th1 = ONCE_REWRITE_CONV1(append, parse_term("append (cons a0 a1) nil"));
  thm th2 = ONCE_REWRITE_CONV1(is_nil, eq_r(th1));
  thm th3 = TRANS(TRANS(th1, th2), CONDS_ELIM_CONV(eq_r(th2)));
  thm th4 = ONCE_REWRITE_CONV2(head, tail, eq_r(th3));
  thm th5 = ONCE_REWRITE_CONV1(ASSUME(parse_term("append a1 nil = a1")), eq_r(th4));
  thm th6 = TRANS(th3, TRANS(th4, th5));
  return GEN(parse_term("a0:int"), GEN(parse_term("a1:i32_list"), 
      DISCH(parse_term("append a1 nil = a1"), th6)));
}

thm app_nil_r() {
  thm th1 = app_nil_r_base();
  printf("%s\n", string_of_thm(th1));
  return th1;
  thm th2 = app_nil_r_induct();

  thm aux = ISPEC(parse_term("\\l. append l nil = l"), i32_list.induct);
  thm i32_list_induction = EQ_MP(ONCE_REWRITE_CONV0(concl(aux)), aux);
  return MATCH_MP(i32_list_induction, CONJ(th1, th2));
}

int main() {
  hol_init();
  sl_init();
  ghost_function();

  thm th1 = app_nil_r();
  printf("%s\n", string_of_thm(th1));
  return 0;
}