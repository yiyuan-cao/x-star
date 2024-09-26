// This is the C* source code for the `reverse` example, the only source file the PROGRAMMER writes.
//   - C* source code = C + ghost code (also written in C language)
//   - Ghost code is used for executable specifications and imperative-style proof hints.
//   - This file can be extracted in two ways: testing mode and proof mode.
//   - This file is also directly compilable by C2X compatible compilers because all ghost code is embedded in [[attribute]] syntax.

// TODO: Requirements and syntax for ghost code.

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

struct i32_ll_node {
    int32_t value;
    struct i32_ll_node *next;
};

typedef struct i32_ll_node *i32_ll;

[[ghost::datatype(
    i32_list(), // a list of type variables (empty for monomorphic types)
    nil(), // empty list
    cons(int32_t head, i32_list tail) // generates accessors `head` and `tail` and constructors `nil` and `cons`
)]];
// Generates structural equality (`i32_list_eq`), accessors, constructors, and discriminators (`is_nil`, `is_cons`) that can be used in ghost code.
// - In testing, the datatype is implemented as tagged unions using `enum`, `union`, and `struct` in C.
//     - Generates `i32_list_print` for debugging purposes.
// - In symbolic execution, values of a ghost datatype is deemed as primitive program values in ghost code.
//   - Constructors are primitive data constructors.
//   - Accessors and discriminators have (pure) pre/post-specifications.
// - In proof, the datatype is translated to HOL inductive type definition.
//   - Accessors (partially-defined total functions) and discriminators are translated to HOL functions with respect to the inductive type.

[[ghost::representation( // signifies the return type is `hprop` for extraction to proof mode.
bool i32_ll_repr(i32_ll p, i32_list l) {
    // We will do type checking before extracting to reverse_proof.c
    if (is_nil(l)) {
        return (p == NULL) && EMP;
        // PURE is automatically added; && is the same as SEPAND in this context (write SEPAND explicitly for disambiguation).
        // `==` compares primitive program values. (Use generated `i32_list_eq` for comparing ghost datatypes.)
        // return FACT(p == NULL); // This is another way to write `PURE(p == NULL) SEPAND EMP`.
    } else {
        int32_t h = head(l); // similar to a LET-binding
        i32_list t = tail(l);
        // introduce the `LET_DATA_AT` syntax for claiming the ownership of struct fields at the addresses `&p->value` and `&p->next`
        // bind them to existentially quantified variables `p_value` and `p_next`
        LET_DATA_AT(&p->value, int32_t value)
        LET_DATA_AT(&p->next, i32_ll next)
        return (value == h) && i32_ll_repr(next, t); // programmer can also use SEP for explicit separation; SEP has the same precedence as SEPAND.
    }
}
)]];

// For the basic extraction support of ghost functions, we require purely functional code and no loops.
// - Each execution branch must have a return statement.

// For future support
// - `while` loop and `for` iteration
// - `if` without `else`
// - `return` in other places
// - mutable local variables
//   - note that mutation of a local var is just a `let`-rebind without single branch `if` and loops
// other data structures (arrays, structs, etc.)

// In principle, any C code that is observationally pure can be extracted to proof mode.
//   - Observationally pure: the output of the function is a pure function of the input (if no errors occur) and no divergence.
//     Moreover, the code must not interfere with original program code. (This is also a requirement for ghost commands.)

// Two ways to extract function definitions:
// 1. Similar to an SMT encoding or Characteristic Formula
// 2. Multiple functions for each program point

[[ghost::function(
i32_list append(i32_list l1, i32_list l2) {
    return is_nil(l1) ? l2 : cons(head(l1), append(tail(l1), l2)); // support the ternary operator `?:`
}
)]];

[[ghost::function(
i32_list reverse(i32_list l) {
    if (is_nil(l)) {
        return l;
    } else {
        int32_t h = head(l);
        i32_list rev_t = reverse(tail(l));
        return append(rev_t, cons(h, nil()));
    }
}
)]];

// Another version of reverse, possibly supported in the future.
[[ghost::function(
i32_list reverse_with_local_var_and_for_loop(i32_list l) {
    i32_list rev_list = nil();
    i32_list rem_list = l;
    for (; is_cons(rem_list);) {
        int32_t head = head(rem_list);
        rem_list = tail(rem_list);
        rev_list = cons(head, rev_list);
    }
    return rev_list;
}
)]];

void print_i32_ll(i32_ll p) {
    while (p != NULL) {
        printf("%d ", p->value);
        p = p->next;
    }
    printf("\n");
}

i32_ll i32_ll_reverse(i32_ll p)
    [[ghost::parameter(i32_list l)]]
    [[ghost::require(i32_ll_repr(p, l))]]
    [[ghost::ensure(i32_ll_repr(__result, reverse(l)))]]
{
    i32_ll rev_prefix = NULL, rem_suffix = p;
    [[ghost::localvar(i32_list l1 = nil(), l2 = l)]];
    // ghost local variable must be initialized
    [[ghost::invariant(
        (i32_list_eq(append(reverse(l1), l2), l)) &&
        (i32_ll_repr(rev_prefix, l1) SEP
         i32_ll_repr(rem_suffix, l2) SEP
         DATA_AT_ANY(&p)))]] // no `;` so this invariant is attached to the while loop below
    while (rem_suffix != NULL) {
        i32_ll t;
        [[ghost::assert(is_cons(l2))]]; // Programmer hint to tell VST-IDE that rem_suffix is not NULL.
        t = rem_suffix->next;
        rem_suffix->next = rev_prefix;
        rev_prefix = rem_suffix;
        [[ghost::command(l1 = cons(rem_suffix->value, l1))]];
        rem_suffix = t;
        [[ghost::command(l2 = tail(l2))]];
    }
    return rev_prefix;
}

[[ghost::debug(
void test_reverse() {
    i32_list l1 = cons(1, cons(2, cons(3, nil())));
    i32_list l1_rev = cons(3, cons(2, cons(1, nil())));
    i32_list l2 = reverse(l1);
    assert(i32_list_eq(l1_rev, l2));
    i32_list_print(l1_rev);
    i32_list_print(l2);
}
)]];

#define DEBUG

int main() {
    [[ghost::debug(test_reverse())]]; // debug only
    i32_ll p =
        &(struct i32_ll_node){1, &(struct i32_ll_node){2, &(struct i32_ll_node){3, NULL}}};
#ifdef DEBUG
    print_i32_ll(p);
#endif
    [[ghost::localvar(i32_list l = cons(1, cons(2, cons(3, nil()))))]];
    [[ghost::debug(i32_list_print(l))]];
    i32_ll q;
    // attached to the function call, used to pass ghost arguments
    [[ghost::argument(l)]] q = i32_ll_reverse(p);
#ifdef DEBUG
    print_i32_ll(q);
#endif
    return 0;
}
