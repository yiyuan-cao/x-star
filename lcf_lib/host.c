#include "host.h"
#include "caml.h"
#include "caml/alloc.h"
#include <string.h>

void hol_init() {
  const char *hol_light_dir = getenv("HOLLIGHT_DIR");
  if (hol_light_dir == NULL) {
    hol_light_dir = "hol-light";
  }

  caml_start();

  value preludes[] = {
      caml_alloc_sprintf("#directory \"%s\";;", hol_light_dir),
      caml_alloc_sprintf("#use \"hol.ml\";;"),
  };
  caml_init(sizeof(preludes) / sizeof(value), preludes);

  printf("*********************\n"
         "HOL Light Initialized\n"
         "*********************\n");
}

term parse_term(const char *s) {
  LOAD_FUNCTION(parse_term);
  value inner = caml_callback(*function_parse_term, caml_copy_string(s));
  return (term){caml_forget(inner)};
}

hol_type parse_type(const char *s) {
  LOAD_FUNCTION(parse_type);
  value inner = caml_callback(*function_parse_type, caml_copy_string(s));
  return (hol_type){caml_forget(inner)};
}

char *string_of_term(term t) {
  LOAD_FUNCTION(string_of_term);
  value result = caml_callback(*function_string_of_term, (value)t.inner);
  return caml_read_string(result);
}

char *string_of_type(hol_type ty) {
  LOAD_FUNCTION(string_of_type);
  value result = caml_callback(*function_string_of_type, (value)ty.inner);
  return caml_read_string(result);
}

char *string_of_thm(thm th) {
  LOAD_FUNCTION(string_of_thm);
  value result = caml_callback(*function_string_of_thm, (value)th.inner);
  return caml_read_string(result);
}

void parse_as_infix(const char *op, int prec, const char *assoc) {
  LOAD_FUNCTION(parse_as_infix_helper);
  caml_callback3(*function_parse_as_infix_helper, caml_copy_string(op), caml_copy_int32(prec), caml_copy_string(assoc));
}

void parse_as_binder(const char *op) {
  LOAD_FUNCTION(parse_as_binder);
  caml_callback(*function_parse_as_binder, caml_copy_string(op));
}

void override_interface(const char *op1, term op2) {
  LOAD_FUNCTION(override_interface_helper);
  caml_callback2(*function_override_interface_helper, caml_copy_string(op1), (value)op2.inner);
}

void new_type(const char *s, int n) {
  LOAD_FUNCTION(new_type_helper);
  caml_callback2(*function_new_type_helper, caml_copy_string(s), caml_copy_int32(n));
}

void new_constant(const char *s, hol_type ty) {
  LOAD_FUNCTION(new_constant_helper);
  caml_callback2(*function_new_constant_helper, caml_copy_string(s), (value)ty.inner);
}

thm new_axiom(term t) {
  LOAD_FUNCTION(new_axiom);
  value inner = caml_callback(*function_new_axiom, (value)t.inner);
  return (thm){caml_forget(inner)};
}

term concl(thm th) {
  LOAD_FUNCTION(concl);
  value inner = caml_callback(*function_concl, (value)th.inner);
  return (term){caml_forget(inner)};
}

term dest_comb_fst(term t) {
  LOAD_FUNCTION(dest_comb);
  void *temp = caml_forget(caml_callback(*function_dest_comb, (value)t.inner));
  LOAD_FUNCTION(fst);
  value inner = caml_callback(*function_fst, (value)temp);
  return (term){caml_forget(inner)};
}

term dest_comb_snd(term t) {
  LOAD_FUNCTION(dest_comb);  
  void *temp = caml_forget(caml_callback(*function_dest_comb, (value)t.inner));
  LOAD_FUNCTION(snd);
  value inner = caml_callback(*function_snd, (value)temp);
  return (term){caml_forget(inner)};
}

indtype define_type(const char *s) {
  LOAD_FUNCTION(define_type);
  LOAD_FUNCTION(fst);
  LOAD_FUNCTION(snd);
  void *temp = caml_forget(caml_callback(*function_define_type, caml_copy_string(s)));
  value ind = caml_callback(*function_fst, (value)temp);
  value rec = caml_callback(*function_snd, (value)temp);
  return (indtype){(thm){caml_forget(ind)}, (thm){caml_forget(rec)}};
}

thm REFL(term t) {
  LOAD_FUNCTION(REFL);
  value inner = caml_callback(*function_REFL, (value)t.inner);
  return (thm){caml_forget(inner)};
}

thm ASSUME(term t) {
  LOAD_FUNCTION(ASSUME);
  value inner = caml_callback(*function_ASSUME, (value)t.inner);
  return (thm){caml_forget(inner)};
}

thm TRANS(thm th1, thm th2) {
  LOAD_FUNCTION(TRANS);
  value inner = caml_callback2(*function_TRANS, (value)th1.inner, (value)th2.inner);
  return (thm){caml_forget(inner)};
}

thm EQ_MP(thm th1, thm th2) {
  LOAD_FUNCTION(EQ_MP);
  value inner = caml_callback2(*function_EQ_MP, (value)th1.inner, (value)th2.inner);
  return (thm){caml_forget(inner)};
}

thm GEN(term t, thm th) {
  LOAD_FUNCTION(GEN);
  value inner = caml_callback2(*function_GEN, (value)t.inner, (value)th.inner);
  return (thm){caml_forget(inner)};
}

thm DISCH(term t, thm th) {
  LOAD_FUNCTION(DISCH);
  value inner = caml_callback2(*function_DISCH, (value)t.inner, (value)th.inner);
  return (thm){caml_forget(inner)};
}

thm CONJ(thm th1, thm th2) {
  LOAD_FUNCTION(CONJ);
  value inner = caml_callback2(*function_CONJ, (value)th1.inner, (value)th2.inner);
  return (thm){caml_forget(inner)};
}

thm MATCH_MP(thm th1, thm th2) {
  LOAD_FUNCTION(MATCH_MP);
  value inner = caml_callback2(*function_MATCH_MP, (value)th1.inner, (value)th2.inner);
  return (thm){caml_forget(inner)};
}

thm ISPEC(term t, thm th) {
  LOAD_FUNCTION(ISPEC);
  value inner = caml_callback2(*function_ISPEC, (value)t.inner, (value)th.inner);
  return (thm){caml_forget(inner)};
}

thm ONCE_REWRITE_CONV0(term t) {
  LOAD_FUNCTION(ONCE_REWRITE_CONV0);
  value inner = caml_callback(*function_ONCE_REWRITE_CONV0, (value)t.inner);
  return (thm){caml_forget(inner)};
}

thm ONCE_REWRITE_CONV1(thm th, term t) {
  LOAD_FUNCTION(ONCE_REWRITE_CONV1);
  value inner = caml_callback2(*function_ONCE_REWRITE_CONV1, (value)th.inner, (value)t.inner);
  return (thm){caml_forget(inner)};
}

thm ONCE_REWRITE_CONV2(thm th1, thm th2, term t) {
  LOAD_FUNCTION(ONCE_REWRITE_CONV2);
  value inner = caml_callback3(*function_ONCE_REWRITE_CONV2, (value)th1.inner, (value)th2.inner, (value)t.inner);
  return (thm){caml_forget(inner)};
}

thm CONDS_ELIM_CONV(term t) {
  LOAD_FUNCTION(CONDS_ELIM_CONV);
  value inner = caml_callback(*function_CONDS_ELIM_CONV, (value)t.inner);
  return (thm){caml_forget(inner)};
}