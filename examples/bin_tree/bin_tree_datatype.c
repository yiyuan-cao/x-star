#include "bin_tree_datatype.h"
#include <stdio.h>
#include <stdlib.h>

struct BinTreeBlock {
    enum { Leaf, Node } tag;
    union {
        struct {
            [[maybe_unused]] char Leaf_dummy;
        };
        struct {
            int Node_value;
            BinTree Node_left;
            BinTree Node_right;
        };
    };
};

BinTree BinTree_Leaf() {
    BinTree tree = (BinTree)malloc(sizeof(struct BinTreeBlock));
    *tree = (struct BinTreeBlock){.tag = Leaf, .Leaf_dummy = 0};
    return tree;
}
BinTree BinTree_Node(int value, BinTree left, BinTree right) {
    BinTree tree = (BinTree)malloc(sizeof(struct BinTreeBlock));
    *tree = (struct BinTreeBlock){.tag = Node,
                                  .Node_value = value,
                                  .Node_left = left,
                                  .Node_right = right};
    return tree;
}

BinTree BinTree_Node_left(BinTree tree) { return tree->Node_left; }
BinTree BinTree_Node_right(BinTree tree) { return tree->Node_right; }
int BinTree_Node_value(BinTree tree) { return tree->Node_value; }

bool BinTree_is_Leaf(BinTree tree) { return tree->tag == Leaf; }
bool BinTree_is_Node(BinTree tree) { return tree->tag == Node; }

bool BinTree_equal(BinTree tree1, BinTree tree2) {
    if (tree1->tag != tree2->tag) {
        return false;
    }
    if (tree1->tag == Leaf) {
        return true;
    }
    return tree1->Node_value == tree2->Node_value &&
           BinTree_equal(tree1->Node_left, tree2->Node_left) &&
           BinTree_equal(tree1->Node_right, tree2->Node_right);
}

void BinTree_print(BinTree tree) {
    if (tree->tag == Leaf) {
        printf("Leaf");
    } else {
        printf("Node(");
        BinTree_print(tree->Node_left);
        printf(", %d, ", tree->Node_value);
        BinTree_print(tree->Node_right);
        printf(")");
    }
}

void BinTree_println(BinTree tree) {
    BinTree_print(tree);
    printf("\n");
}