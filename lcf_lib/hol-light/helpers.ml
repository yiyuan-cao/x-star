let new_type_helper typ arity = 
  new_type(typ, Int32.to_int arity);;

let new_constant_helper const typ = 
  new_constant(const, typ);;

let parse_as_infix_helper op prec assoc = 
  parse_as_infix(op, (Int32.to_int prec, assoc));;

let extend_basic_rewrite th = 
  extend_basic_rewrites [th];;

let override_interface_helper op1 op2 = 
  override_interface (op1, op2);;

let ONCE_REWRITE_CONV0 t = ONCE_REWRITE_CONV[] t;;
let ONCE_REWRITE_CONV1 th t = ONCE_REWRITE_CONV[th] t;;
let ONCE_REWRITE_CONV2 th1 th2 t = ONCE_REWRITE_CONV[th1;th2] t;;

let fst (x, y) = x;;
let snd (x, y) = y;;
