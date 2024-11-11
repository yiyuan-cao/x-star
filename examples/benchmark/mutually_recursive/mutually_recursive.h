#include "vst_ide.h"

int is_even(int x)
/*@
Require
  x >= 0
Ensure
  x@pre % 2 == 0 && __return == 1 ||
  x@pre % 2 != 0 && __return == 0
*/
;

int is_odd(int x)
/*@
Require
  x >= 0
Ensure
  x@pre % 2 != 0 && __return == 1 ||
  x@pre % 2 == 0 && __return == 0
*/
;