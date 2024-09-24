// provides external datatype manipulation functions with Separation logic
// specifications for help with the symbolic execution of the annotated C code
// in reverse_proof.c

// NOTE: GHOST C DATA TYPES COULD BE SHARED (SUPPORT OF READ-ONLY/FRACTIONAL
// ASSERTION NEEDED).

#include <stdbool.h>
#include <stdint.h>

struct list_block;
typedef struct list_block *List;

// (trivial) logical representation of List
/*@ _List : *                 */
/*@ _nil : _List               */
/*@ _cons : Z -> _List -> _List */
/*@ _list_repr : List -> _List -> HProp */

/** constructors with specifications for symbolic executing ghost code */
List list_nil();
/*@ requires: emp */
/*@ ensures: _list_repr(__result, _nil) */

List list_cons(int64_t head, List tail);
/*@ with: t:_List */
/*@ requires: _list_repr(tail, t) */
/*@ ensures: _list_repr(__result, _cons(head, t)) */

/** accessors */
int64_t list_cons_head(List list);
/*@ with: head:Z, tail:_List */
/*@ requires: _list_repr(list, _cons(head, tail)) */
/*@ ensures: __result = head && _list_repr(list, _cons(head, tail)) */

List list_cons_tail(List list);
/*@ with: head:Z, tail:_List */
/*@ requires: _list_repr(list, _cons(head, tail)) */
/*@ ensures: _list_repr(__result, tail) */

/** discriminators */
bool list_is_nil(List list);
/*@ requires: _list_repr(list, _nil) */
/*@ ensures: __result = true */

bool list_is_cons(List list);
/*@ requires: exists(head, tail), _list_repr(list, _cons(head, tail)) */
/*@ ensures: __result = true */

/** equality */
bool list_equal(List list1, List list2);
/*@ requires: _list_repr(list1, l1) * _list_repr(list2, l2) */
/*@ ensures: __result = (l1 = l2) */

/** debug only */
void list_println_sexp(List list);

// representation of linked lists
/*@ list_repr : PTR -> _List -> HProp */