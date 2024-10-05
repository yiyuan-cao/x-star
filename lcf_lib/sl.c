#include "host.h"
#include "sl.h"
#include <stdio.h>

static indtype ptr;
static indtype c_val;

static thm himpl_refl;

void sl_init() {
  override_interface("true", parse_term("T"));
  override_interface("false", parse_term("F"));
  parse_as_infix("&&", 22, "left");
  parse_as_infix("||", 22, "left");
  override_interface("&&", parse_term("(/\\)"));
  override_interface("||", parse_term("(\\/)"));
  
  new_type("hprop", 0);
  ptr = define_type("ptr = Pnull | Pptr num");
  c_val = define_type("c_val = Vbool bool | Vint int | Vptr ptr");
  
  new_constant("fieldaddr", parse_type("ptr#num->ptr"));
  new_axiom(parse_term("fieldaddr(Ptr p, ofs) = Ptr(p+ofs)"));

  new_constant("EMP", parse_type("hprop"));
  new_constant("PURE", parse_type("bool->hprop"));

  // separating conjunction
  new_constant("SEP", parse_type("hprop->hprop->hprop"));
  parse_as_infix("SEP", 22, "right");

  // separation logic AND
  new_constant("SEPAND", parse_type("hprop->hprop->hprop"));
  parse_as_infix("SEPAND", 22, "right");

  // entailment
  new_constant("|--", parse_type("hprop->hprop->bool"));
  parse_as_infix("|--", 22, "right");

  // separation logic quantifiers
  new_constant("hforall", parse_type("(A->hprop)->hprop"));
  parse_as_binder("hforall");
  new_constant("hexists", parse_type("(A->hprop)->hprop"));
  parse_as_binder("hexists");

  himpl_refl = new_axiom(parse_term("!H. H |-- H"));
}

thm HIMPL_REFL(term t) {
  return ISPEC(t, himpl_refl);
}