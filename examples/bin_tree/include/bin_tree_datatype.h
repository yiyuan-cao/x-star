#ifndef BIN_TREE_DATATYPE_H
#define BIN_TREE_DATATYPE_H

#include <stdbool.h>

/** datatype */
struct BinTreeBlock;
typedef struct BinTreeBlock *BinTree;

/** constructors */
BinTree BinTree_Leaf();
BinTree BinTree_Node(int value, BinTree left, BinTree right);

/** accessors */
BinTree BinTree_Node_left(BinTree tree);
BinTree BinTree_Node_right(BinTree tree);
int BinTree_Node_value(BinTree tree);

/** discriminators */
bool BinTree_is_Leaf(BinTree tree);
bool BinTree_is_Node(BinTree tree);

/** equality */
bool BinTree_equal(BinTree tree1, BinTree tree2);

/** debug only */
void BinTree_println(BinTree tree);

#endif