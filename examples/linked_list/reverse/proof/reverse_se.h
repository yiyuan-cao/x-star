// provides external datatype manipulation functions with Separation logic
// specifications for help with the symbolic execution of the annotated C code
// in reverse_proof.c

// NOTE: GHOST C DATA TYPES COULD BE SHARED (SUPPORT OF READ-ONLY/FRACTIONAL
// ASSERTION NEEDED).

#include <stdbool.h>
#include <stdint.h>

struct list_block;
typedef struct list_block *i32_list;

// (trivial) logical representation of List
/*@ Extern Coq (_i32_list: *)   
               (_nil: _i32_list)                         
               (_cons: Z -> _i32_list -> _i32_list) 
               (_append: _i32_list -> _i32_list -> _i32_list)
               (_reverse: _i32_list -> _i32_list)
               (_i32_ll_repr: i32_list -> _i32_list -> Assertion) 
                */

/** constructors with specifications for symbolic executing ghost code */
i32_list nil();
/*@ Require emp */
/*@ Ensure _i32_ll_repr(__return, _nil) */

i32_list cons(int32_t head, i32_list tail);
/*@ With (t:_i32_list) */
/*@ Require _i32_ll_repr(tail, t) */
/*@ Ensure _i32_ll_repr(__return, _cons(head, t)) */

/** accessors */
int32_t head(i32_list list);
/*@ With (h:Z) (t:_i32_list) */
/*@ Require _i32_ll_repr(list, _cons(h, t)) */
/*@ Ensure __return == h && _i32_ll_repr(list, _cons(h, t)) */

i32_list tail(i32_list list);
/*@ With (h:Z) (t:_i32_list) */
/*@ Require _i32_ll_repr(list, _cons(h, t)) */
/*@ Ensure _i32_ll_repr(__return, t) */

/** discriminators */
bool is_nil(i32_list list);
/*@ Require _i32_ll_repr(list, _nil) */
/*@ Ensure __return == true */

bool is_cons(i32_list list);
/*@ Require exists(head, tail), _i32_ll_repr(list, _cons(head, tail)) */
/*@ Ensure __return == true */

/** equality */
bool i32_list_eq(i32_list list1, i32_list list2);
/*@ With (l1:_i32_list) (l2: _i32_list) */
/*@ Require _i32_ll_repr(list1, l1) * _i32_ll_repr(list2, l2) */
/*@ Ensure __return == (l1 == l2) */

i32_list append(i32_list list1, i32_list list2);
/*@ With (l1: _i32_list) (l2: _i32_list)*/
/*@ Require _i32_ll_repr(list1, l1) * _i32_ll_repr(list2, l2) */
/*@ Ensure _i32_ll_repr(__return, _append(l1, l2)) */

i32_list reverse(i32_list list);
/*@ With (l: _i32_list) */
/*@ Require _i32_ll_repr(list, l) */
/*@ Ensure _i32_ll_repr(__return, _reverse(l)) */
