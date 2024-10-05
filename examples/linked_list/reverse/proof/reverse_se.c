// VST-IDE Annotated C code for symbolic execution (with ghost code). extracted from reverse.c by the C* compiler.

#include "reverse_se.h"
#include <stddef.h>

/*@ Extern Coq (i32_list: *)
               (i32_ll_repr: val -> i32_list -> Assertion) */

struct i32_ll_node {
  int32_t value;
  struct i32_ll_node *next;
};

typedef struct i32_ll_node *i32_ll;

// TODO: (to fix) ghost localval/command.
i32_ll i32_ll_reverse(i32_ll p, i32_list l)
/*@ Require i32_ll_repr(p, l) 
    Ensure i32_ll_repr(__return, reverse(l)) 
*/
{
    i32_ll rev_prefix = (void *)0, rem_suffix = p;
    i32_list l1 = nil(), l2 = l; // [[ghost::localvar]]
    
    /*@ Inv i32_list_eq(l, append(reverse(l1), l2)) && 
            i32_ll_repr(rev_prefix, l1) * i32_ll_repr(rem_suffix, l2) *
            undef_data_at(&p)
      */
    while (rem_suffix != NULL) {
        i32_ll t;
        assert(is_cons(l2)); // [[ghost::assert]]
        t = rem_suffix->next;
        rem_suffix->next = rev_prefix;
        rev_prefix = rem_suffix;
        l1 = cons(rem_suffix->value, l1); // [[ghost::command]]
        rem_suffix = t;
        l2 = tail(l2); // [[ghost::command]]
    }
    return rev_prefix;
}