// VST-IDE Annotated C code for symbolic execution (with ghost code). extracted from reverse.c by the C* compiler.

#include "reverse_se.h"
#include <stddef.h>

struct list_cell {
    int head;
    struct list_cell *tail;
};

// TODO
struct list_cell *reverse(struct list_cell *p)
    [[ghost::parameter(List l)]]
    [[ghost::require(list_repr(p, l))]]
    [[ghost::ensure(list_repr(p, list_reverse(l)))]]
{
    struct list_cell *rev_prefix = NULL, *rem_suffix = p;
    [[ghost::localvar(List l1 = list_nil(), l2 = l)]]; // ghost local variable, must be initialized
    [[ghost::invariant((PURE(list_equal(list_append(list_reverse(l1), l2), l))
                            SEPAND(list_repr(rev_prefix, l1) SEP list_repr(rem_suffix, l2) SEP DATA_AT_ANY(&p))))]] // no `;`, attached to the while loop below
    while (rem_suffix != NULL) {
        struct list_cell *t;
        [[ghost::assert(rem_suffix != NULL)]]; // Possible hint: tell VST-IDE that rem_suffix is not NULL (unfold the cell)
        t = rem_suffix->tail;
        rem_suffix->tail = rev_prefix;
        rev_prefix = rem_suffix;
        [[ghost::command(l1 = list_cons(rem_suffix->head, l1))]];
        rem_suffix = t;
        [[ghost::command(l2 = list_cons_tail(l2))]];
    }
    return rev_prefix;
}