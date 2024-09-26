// run with dynamically checked ghost code

// newly added header files
#include "cstar_test.h"
#include "reverse_datatype.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
// #include <stdlib.h> // WHY THIS ISN'T ALLOWED?

struct i32_ll_node {
    int32_t value;
    struct i32_ll_node *next;
};

typedef struct i32_ll_node *i32_ll;

hprop i32_ll_repr(i32_ll p, i32_list l) { // Here p actually serve as a pair of a Ptr and an
                                        // field offset mapping for struct list_cell (used in field acesssing)
    if (is_nil(l)) {
        return PURE(p == NULL)
            SEPAND EMP; // code is generated after type checking the reverse.c ghost code by C* compiler
    } else {
        i32 h = head(l);
        i32_list t = tail(l);
        LET_DATA_AT(&p->value, i32 value)
        LET_DATA_AT(&p->next, i32_ll next)
        return PURE(value == h) SEPAND i32_ll_repr(next, t);
    }
}

i32_list append(i32_list l1, i32_list l2) {
    return is_nil(l1) ? l2 : cons(head(l1), append(tail(l1), l2));
}

i32_list reverse(i32_list l) {
    if (is_nil(l)) {
        return l;
    } else {
        i32 h = head(l);
        i32_list rev_tail = reverse(tail(l));
        return append(rev_tail, cons(h, nil()));
    }
}

// a possible substitute for list_reverse
i32_list reverse_with_local_var_and_for_loop(i32_list list) {
    i32_list rev_list = nil();
    i32_list rem_list = list;
    for (; is_cons(rem_list);) {
        i32 h = head(rem_list);
        rem_list = tail(rem_list);
        rev_list = cons(h, rev_list);
    }
    return rev_list;
}
void print_i32_ll(i32_ll p) {
    while (p != NULL) {
        printf("%d ", p->value);
        p = p->next;
    }
    printf("\n");
}

i32_ll i32_ll_reverse_orig(i32_ll p, i32_list l) {
    i32_ll rev_prefix = NULL, rem_suffix = p;
    i32_list l1 = nil(), l2 = l;
#define INV                                                                                      \
    (PURE(i32_list_eq(append(reverse(l1), l2), l)) SEPAND                                        \
    (i32_ll_repr(rev_prefix, l1) SEP                                                             \
     i32_ll_repr(rem_suffix, l2) SEP                                                             \
     DATA_AT_ANY(&p)))
    for (assert(INV); rem_suffix != NULL; assert(INV)) {
        // Trick: using for-loop to ensure invariant is checked at the begining and at the end of each loop body
#undef INV
        i32_ll t;
        assert(is_cons(l2));
        t = rem_suffix->next;
        rem_suffix->next = rev_prefix;
        rev_prefix = rem_suffix;
        l1 = cons(rem_suffix->value, l1);
        rem_suffix = t;
        l2 = tail(l2);
    }
    return rev_prefix;
}

i32_ll i32_ll_reverse(i32_ll p, i32_list l) {
    require(i32_ll_repr(p, l));
    i32_ll __result = i32_ll_reverse_orig(p, l);
    // construst a wrapper for executable functions because ensure clause must be checked for all
    // possible exit points
    ensure(i32_ll_repr(__result, reverse(l)));
    return __result;
}

// debug only
void test_reverse() {
    i32_list l1 = cons(1, cons(2, cons(3, nil())));
    i32_list l1_rev = cons(3, cons(2, cons(1, nil())));
    i32_list l2 = reverse(l1);
    assert(i32_list_eq(l1_rev, l2));
    i32_list_print(l1_rev);
    i32_list_print(l2);
}

int main() {
    test_reverse(); // debug only
    i32_ll p = &(struct i32_ll_node){1, &(struct i32_ll_node){2, &(struct i32_ll_node){3, NULL}}};
    print_i32_ll(p);
    i32_list l = cons(1, cons(2, cons(3, nil())));
    i32_list_print(l);
    i32_ll q;
    q = i32_ll_reverse(p, l);
    print_i32_ll(q);
    return 0;
}
