#include "cstar.h"

[[ghost::datatype(BinTree<>, // type name (and optional: support type variable lists in angle brackets)
                             // polymorphic type can be implemented using void* and indirection
                             // types not checked at runtime (UB should be deemed as error execution)
                  Leaf(), // constructor syntax: Uppercase constructor name with
                          // named arguments in parentheses
                  Node(Integer value, BinTree left, BinTree right))]];

[[ghost::function(BinTree reverse(BinTree tree) {
    if (is_Leaf(tree)) {
        return tree;
        // g1 = !tree. is_Leaf tree => reverse tree = tree
    }
    if (is_Node(tree)) {
        BinTree left_reversed = reverse(left(tree));
        BinTree right_reversed = reverse(right(tree));
        return Node(value(tree), right_reversed, left_reversed);
        // g2 = !tree. is_Node tree =>
        //       !left_reversed. left_reversed = reverse(left(tree)) =>
        //             !right_reversed. right_reversed = reverse(right(tree)) =>
        //                              reverse tree = Node(value(tree),
        //                              right_reversed, left_reversed)
    }
}
                  // ?reverse. g1 /\ g2
                  )]]

    // int main() { return 0; }