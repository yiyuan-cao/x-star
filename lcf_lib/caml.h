#ifndef HOL_CAML_H
#define HOL_CAML_H

#include <caml/alloc.h>
#include <caml/callback.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

void caml_start();
void caml_init(int cmdn, value cmds[]);
const value *caml_from_toplevel(const char *name);

#define LOAD_FUNCTION(name)                                                    \
  static const value *function_##name = NULL;                                  \
  if (function_##name == NULL) {                                               \
    function_##name = caml_from_toplevel(#name);                               \
  }

void *caml_forget(value v);
char* caml_read_string(value v);

#endif
