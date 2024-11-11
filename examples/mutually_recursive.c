#include "mutually_recursive.h"

int is_even(int x)
/*@
Require
  x >= 0
Ensure
  x@pre % 2 == 0 && __return == 1 ||
  x@pre % 2 != 0 && __return == 0
*/
{
  /*@ Assert
    x@pre >= 0 &&
    data_at(&x, int, x@pre)
  */
  if (x == 0) {
    /*@ Assert
      x@pre == 0 &&
      x@pre >= 0 &&
      data_at(&x, int, x@pre)
    */
    return 1;
    // is_even_return_wit_1 : [| x@pre = 0 |] && emp |--
    //                        [| x@pre % 2 = 0 |] && [| 1 = 1 |] && emp ||
    //                        [| x@pre % 2 <> 0 |] && [| 1 = 0 |] && emp.
  } else {
    /*@ Assert
      x@pre != 0 &&
      x@pre >= 0 &&
      data_at(&x, int, x@pre)
    */
    // is_even_entail_wit_4
    /*@ Assert
      x@pre - 1 >= 0 &&
      data_at(&x, int, x@pre)
    */
    return is_odd(x - 1);
    // is_even_return_wit_2_1 : forall retval,
    //                          [| (x@pre - 1) % 2 = 0 |] && [| retval = 0 |] && [| x@pre - 1 >= 0 |] && emp |--
    //                          [| x@pre % 2 = 0 |] && [| retval = 1 |] && emp ||
    //                          [| x@pre % 2 <> 0 |] && [| retval = 0 |] && emp.
    // is_even_return_wit_2_2 : forall retval,
    //                          [| (x@pre - 1) % 2 <> 0 |] && [| retval = 1 |] && [| x@pre - 1 >= 0 |] && emp |--
    //                          [| x@pre % 2 = 0 |] && [| retval = 1 |] && emp ||
    //                          [| x@pre % 2 <> 0 |] && [| retval = 0 |] && emp.
  }
}

int is_odd(int x)
/*@
Require
  x >= 0
Ensure
  x@pre % 2 != 0 && __return == 1 ||
  x@pre % 2 == 0 && __return == 0
*/
{
  /*@ Assert
    x@pre >= 0 &&
    data_at(&x, int, x@pre)
  */
  if (x == 0) {
    /*@ Assert
      x@pre == 0 &&
      x@pre >= 0 &&
      data_at(&x, int, x@pre)
    */
    return 0;
    // is_odd_return_wit_1 : [| x@pre = 0 |] && emp |--
    //                       [| x@pre % 2 <> 0 |] && [| 0 = 1 |] && emp ||
    //                       [| x@pre % 2 = 0 |] && [| 1 = 1 |] && emp.
  } else {
    /*@ Assert
      x@pre != 0 &&
      x@pre >= 0 &&
      data_at(&x, int, x@pre)
    */
    // is_odd_entail_wit_4
    /*@ Assert
      x@pre - 1 >= 0 &&
      data_at(&x, int, x@pre)
    */
    return is_even(x - 1);
    // is_odd_return_wit_2_1 : forall retval,
    //                         [| (x@pre - 1) % 2 <> 0 |] && [| retval = 0 |] && [| x@pre - 1 >= 0 |] && emp |--
    //                         [| x@pre % 2 <> 0 |] && [| retval = 1 |] && emp ||
    //                         [| x@pre % 2 = 0 |] && [| retval = 0 |] && emp.
    // is_odd_return_wit_2_2 : forall retval,
    //                         [| (x@pre - 1) % 2 = 0 |] && [| retval = 1 |] && [| x@pre - 1 >= 0 |] && emp |--
    //                         [| x@pre % 2 <> 0 |] && [| retval = 1 |] && emp ||
    //                         [| x@pre % 2 = 0 |] && [| retval = 0 |] && emp.
  }
}
