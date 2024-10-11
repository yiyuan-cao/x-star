// V20241008

/*@ Import Coq Import naive_C_Rules */
/*@ Import Coq Require Import lib */

/*@ Extern Coq addr := Z */

/*@ Extern Coq
  (UINT_MAX : Z)
*/

/*@ Extern Coq
  (nil : {A} -> list A)
  (Z_to_nat : Z -> nat)
  (repeat : {A} -> A -> nat -> list A)
*/

/*@ Extern Coq
  (undef_store_char : addr -> Z -> Assertion)
  (store_char : addr -> Z -> Z -> Assertion)
  (store_undef_array_rec : (addr -> Z -> Assertion) ->
                           addr -> Z -> Z -> nat -> Assertion)
  (store_undef_array : (addr -> Z -> Assertion) ->
                       addr -> Z -> Assertion)
  (store_array : {A} -> (addr -> Z -> A -> Assertion) ->
                 addr -> Z -> list A -> Assertion)
*/
