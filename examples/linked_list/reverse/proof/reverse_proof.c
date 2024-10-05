// linked with LCF lib, extracted from reverse.c.
#include <stdint.h>
#include <stdio.h>
#include <host.h>
#include <sl.h>

struct i32_ll_node {
  int32_t value;
  struct i32_ll_node *next;
};

// extracted from reverse.c
indtype i32_list;
thm is_nil, is_cons, head, tail;
thm append, reverse, i32_ll_repr;

void ghost_function() {
  i32_list = define_type("i32_list = nil | cons int i32_list");

  is_nil = define(parse_term("is_nil nil = T /\\ is_nil (cons h t) = F"));
  is_cons = define(parse_term("is_cons nil = F /\\ is_cons (cons h t) = T"));
  head = define(parse_term("head (cons h t) = h"));
  tail = define(parse_term("tail (cons h t) = t"));

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

  new_constant("i32_ll_repr", parse_type("pval->i32_list->hprop"));
  i32_ll_repr = new_axiom(parse_term(
    "i32_ll_repr p l = \
      if (is_nil l) then (pure (p = Vptr(&0))) &&& emp else \
        let h = head l in \
        let t = tail l in \
        hexists value. data_at(field_addr(p, 0), Vint value) ** \
        hexists next. data_at(field_addr(p, 1), next) ** \
          (pure (value = h)) &&& (i32_ll_repr next t)"
  ));
}

// written in reverse_proof.c
void app_nil_r() {
  // ...
}

int main() {
  hol_init();
  sl_init();

  ghost_function();
  return 0;
}

// prove which-implies #1
thm p1() {
  // 
}