// V20241030

/*@ Import Coq Import naive_C_Rules */
/*@ Import Coq Require Import lib */

/*@ Extern Coq addr := Z */

/*@ Extern Coq
  (False : Prop)
  (map : {A} {B} -> (A -> B) -> list A -> list B)
  (Zrepeat : {A} -> A -> Z -> list A)
  (Znth : {A} -> Z -> list A -> A -> A)
  (sublist : {A} -> Z -> Z -> list A -> list A)
  (Zadd : Z -> Z -> Z)
  (undef_store_char : addr -> Z -> Assertion)
  (store_char : addr -> Z -> Z -> Assertion)
  (store_int : addr -> Z -> Z -> Assertion)
  (store_undef_array : (addr -> Z -> Assertion) ->
                       addr -> Z -> Assertion)
  (store_array : {A} -> (addr -> Z -> A -> Assertion) ->
                 addr -> Z -> list A -> Assertion)
*/

void abort()
/*@
With
  (P : Assertion)
Require
  False &&
  emp
Ensure
  P
*/
;

/*@ include strategies "common.strategies" */
