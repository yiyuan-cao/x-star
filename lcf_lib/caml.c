#include "caml.h"
#include "caml/alloc.h"
#include <string.h>

#define LOAD_CLOSEURE(name)                                                    \
  static const value *closure_##name = NULL;                                   \
  if (closure_##name == NULL) {                                                \
    closure_##name = caml_named_value(#name);                                  \
  }

void caml_start() {
  char *argv[] = {"ocaml", NULL};
  caml_startup(argv);
}

void caml_init(int cmdn, value cmds[]) {
  LOAD_CLOSEURE(run_toplevel);
  for (int i = 0; i < cmdn; i++) {
    caml_callback(*closure_run_toplevel, cmds[i]);
  }
}

const value *caml_from_toplevel(const char *name) {
  LOAD_CLOSEURE(expose_toplevel);
  const value *named = caml_named_value(name);
  if (named == NULL) {
    caml_callback(*closure_expose_toplevel, caml_copy_string(name));
    named = caml_named_value(name);
  }
  return named;
}

void *caml_forget(const value v) {
  value* p = malloc(sizeof(value));
  *p = v; 
  caml_register_generational_global_root(p);
  return (void *)v;
}

char *caml_read_string(value v) {
  size_t len = caml_string_length(v);

  char *result = malloc(len + 1);
  memcpy(result, String_val(v), len);
  result[len] = '\0';
  return result;
}
