// https://github.com/verifast/verifast/blob/b351656ae5b89afe0539be4c3c2703af8dc94c90/examples/address_of_local.c

#include "vst_ide.h"

void inc(int* i)
/*@
With
  (v : Z)
Require
  data_at(i, int, v)
Ensure
  data_at(i@pre, int, v + 1)
*/
{
  /*@ Assert
    data_at(&i, int*, i@pre) *
    data_at(i, int, v)
  */
  (*i) = (*i) + 1;
  /*@ Assert
    data_at(&i, int*, i@pre) *
    data_at(i, int, v + 1)
  */
}

void address_of_param(int x)
/*@
Require
  emp
Ensure
  emp
*/
{
    /*@ Assert
      data_at(&x, int, x@pre)
    */
    x = 5;
    /*@ Assert
      data_at(&x, int, 5)
    */
    int* ptr = &x;
    /*@ Assert
      data_at(&x, int, 5) *
      data_at(&ptr, int*, &x)
    */
    inc(ptr) /*@ where v = 5 */;
    /*@ Assert
      data_at(&x, int, 5 + 1) *
      data_at(&ptr, int*, &x)
    */
    // address_of_param_entail_wit_5
    /*@ Assert
      data_at(&x, int, 6) *
      data_at(&ptr, int*, &x)
    */
    int z = x;
    /*@ Assert
      data_at(&x, int, 6) *
      data_at(&ptr, int*, &x) *
      data_at(&z, int*, 6)
    */
    // address_of_param_safety_wit_3
    if (z == 6) {
    } else {
      abort();
    }
}

void address_of_local()
/*@
Require
  emp
Ensure
  emp
*/
{
  /*@ Assert
    emp
  */
  int x = 0;
  /*@ Assert
    data_at(&x, int, 0)
  */
  {
    /*@ Assert
      data_at(&x, int, 0)
    */
    int* ptr = &x;
    /*@ Assert
      data_at(&x, int, 0) *
      data_at(&ptr, int*, &x)
    */
    {
      /*@ Assert
        data_at(&x, int, 0) *
        data_at(&ptr, int*, &x)
      */
      int** ptrptr = &ptr;
      /*@ Assert
        data_at(&x, int, 0) *
        data_at(&ptr, int*, &x) *
        data_at(&ptrptr, int**, &ptr)
      */
      inc(*ptrptr) /*@ where v = 0 */;
      /*@ Assert
        data_at(&x, int, 0 + 1) *
        data_at(&ptr, int*, &x) *
        data_at(&ptrptr, int**, &ptr)
      */
      // address_of_local_entail_wit_8
      /*@ Assert
        data_at(&x, int, 1) *
        data_at(&ptr, int*, &x) *
        data_at(&ptrptr, int**, &ptr)
      */
      int z = x;
      /*@ Assert
        data_at(&x, int, 1) *
        data_at(&ptr, int*, &x) *
        data_at(&ptrptr, int**, &ptr) *
        data_at(&z, int, 1)
      */
      // address_of_local_safety_wit_3
      if (z == 1) {
      } else {
        abort();
      }
    }
    /*@ Assert
        data_at(&x, int, 1) *
        data_at(&ptr, int*, &x)
    */
  }
  /*@ Assert
      data_at(&x, int, 1)
  */
}
