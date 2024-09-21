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

char *string_of_term(term t) {
  LOAD_FUNCTION(string_of_term);
  value result = caml_callback(*function_string_of_term, (value)t.inner);
  return caml_read_string(result);
}
