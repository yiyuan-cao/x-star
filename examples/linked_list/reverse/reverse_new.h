// header file for reverse_new.c

#ifndef REVERSE_NEW_H
#define REVERSE_NEW_H

#include <stdlib.h>

struct TreeCell;
typedef struct TreeCell *Tree;

Tree Leaf();
Tree Node(int value, Tree left, Tree right);

void print_tree(Tree tree);
void print_tree_depth(Tree tree, int depth);
Tree reverse_tree(Tree tree);

struct TreeCell {
    enum { LEAF, NODE } tag;
    union {
        struct {
            char dummy;
        };
        struct {
            int value;
            Tree left;
            Tree right;
        };
    };
};

Tree Leaf() {
    Tree leaf = malloc(sizeof(struct TreeCell));
    leaf->tag = LEAF;
    return leaf;
}
Tree Node(int value, Tree left, Tree right) {
    Tree node = malloc(sizeof(struct TreeCell));
    node->tag = NODE;
    node->value = value;
    node->left = left;
    node->right = right;
    return node;
}

#endif