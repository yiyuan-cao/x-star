// Generated from cstar_std.config

#ifndef CSTAR_H
#define CSTAR_H

#include <stdbool.h> // for the `bool` type
#include <assert.h>
#include <stdint.h>

// Run-time correspondence of logical layer entities to C entities
#define VAL(v) ((Z)(v)) // identity function when testing
#define Z int64_t
#define Ptr size_t
#define Bool bool
#define HProp bool
#define PURE(p) (p) // embed a pure logical assertion as a separation logic assertion with no constraints on heaps
#define EQ ==
#define SEP &&
#define SEPAND &&

#define LET_SEP(type, x, y) type x = (y);
#define DATA_AT_EXISTS(x) (true)

#define require assert
#define ensure assert

// proposal: delete these macros and overload `if`, `?:`, `&&`, `||`, and `!` to work on `Bool`
#define AND &&
#define OR ||
#define NOT !






















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
    boolean repr(int32_t v, Integer n) { return VAL(v) === VInt(repr(n)); }
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
