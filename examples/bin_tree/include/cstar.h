#ifndef CSTAR_H
#define CSTAR_H

[[ghost::extraction(
    TYPE,       // considering the extraction of types
    TEST,       // if it's dynamic check mode
    Integer,    // then a integer ghost value type
    big_number, // gets translated to a big number C data structure type
    )]];

[[ghost::extraction(
    TYPE,    // considering the extraction of types
    PROOF,   // if it's static proving mode
    Integer, // then a integer ghost value type
    int,     // gets translated to the integer type in HOL Light
)]];

[[ghost::extraction(
    OP,    // considering the extraction of operators
    PROOF, // if it's static proving mode
    (==) : Integer->Integer->boolean,
    (=) : int->int->bool,
)]];

[[ghost::extraction(
    OP, 
    TEST, 
    (==) : Integer->Integer->boolean, 
    eq_big_number : big_number->big_number->bool, 
)]];

[[ghost::representation(
    boolean repr(int32_t v, Integer n) { return VAL(v) == = n; }
    // VAL(v) gets the mathematical primitive C value of a stack variable v
    //    - (identity function when testing)
    // === is the polymorphic mathematical equality operator
    //    - for primitive values, same as == in testing
    //    - for other data structures, it translates to a recursively defined
    //      equality function for that type (generated when that datatype is
    //      defined using [[ghost::datatype]])
)]];

[[ghost::model(
    Integer getmodel(int32_t v) { return VAL(v); }
    // get the model of a program variable (if possible)
    // ensures that the model is a valid representation of the program
    // variable, i.e. repr(v, getmodel(v)) holds
    // this could be done only when the representation predicate is
    // deterministic and total viewed as a function from the program variable
    // value domain to the ghost value domain
)]];

#endif // CSTAR_H