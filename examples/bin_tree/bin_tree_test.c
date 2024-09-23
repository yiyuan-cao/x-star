#include "bin_tree_datatype.h"

#define is_Leaf(tree) BinTree_is_Leaf(tree)
#define is_Node(tree) BinTree_is_Node(tree)
#define node(value, left, right) BinTree_Node(value, left, right)
#define leaf() BinTree_Leaf()
#define left(tree) BinTree_Node_left(tree)
#define right(tree) BinTree_Node_right(tree)
#define value(tree) BinTree_Node_value(tree)
#define equal(tree1, tree2) BinTree_equal(tree1, tree2)

bool ascending(BinTree tree) {
    if (is_Leaf(tree)) {
        return true;
    }
    if (is_Node(tree)) {
        return ascending(left(tree)) && ascending(right(tree)) &&
               value(tree) > value(left(tree)) &&
               value(tree) < value(right(tree));
    }
    return false;
}

bool descending(BinTree tree) {
    if (is_Leaf(tree)) {
        return true;
    }
    if (is_Node(tree)) {
        return descending(left(tree)) && descending(right(tree)) &&
               value(tree) < value(left(tree)) &&
               value(tree) > value(right(tree));
    }
    return false;
}

BinTree bst_ascending_insert(BinTree tree, int value) {
    if (is_Leaf(tree)) {
        return node(value, leaf(), leaf());
    }
    if (is_Node(tree)) {
        if (value < value(tree)) {
            return node(value(tree), bst_ascending_insert(left(tree), value),
                        right(tree));
        } else {
            return node(value(tree), left(tree),
                        bst_ascending_insert(right(tree), value));
        }
    }
    return tree;
}

int main() {
    BinTree tree = BinTree_Node(1, BinTree_Leaf(), BinTree_Leaf());
    BinTree_println(tree);
    return 0;
}