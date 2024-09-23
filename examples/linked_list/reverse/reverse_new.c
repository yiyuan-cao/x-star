#include "reverse_new.h"
#include <stdio.h>
#include <stdlib.h>

struct TreeCell {
    enum { LEAF, NODE } tag;
    union {
        struct {
            char dummy; // No additional data for LEAF
        };
        struct {
            int value;
            struct TreeCell *left;
            struct TreeCell *right;
        };
    };
};

// Function to create a leaf
Tree Leaf() {
    Tree leaf = malloc(sizeof(struct TreeCell));
    leaf->tag = LEAF;
    return leaf;
}

// Function to create a node
Tree Node(int value, Tree left, Tree right) {
    Tree node = malloc(sizeof(struct TreeCell));
    node->tag = NODE;
    node->value = value;
    node->left = left;
    node->right = right;
    return node;
}

// Function to print the tree, with indentation to show depth, left to right
void print_tree_depth(Tree tree, int depth) {
    if (tree == NULL) {
        return;
    }

    // Print right subtree
    print_tree(tree->right, depth + 1);

    // Print current node
    for (int i = 0; i < depth; i++) {
        printf("         "); // Indentation for depth
    }
    if (tree->tag == LEAF) {
        printf("Leaf\n");
    } else {
        printf("Node(%d)\n", tree->value);
    }

    // Print left subtree
    print_tree(tree->left, depth + 1);
}

void print_tree(Tree tree) {
    print_tree_depth(tree, 0);
}

Tree reverse_tree(Tree tree) {
    switch (tree->tag) {
    case LEAF:
        return tree;
    case NODE: {
        Tree new_left = reverse_tree(tree->right);
        Tree new_right = reverse_tree(tree->left);
        Tree new_node = Node(tree->value, new_left, new_right);
        return new_node;
    }
    }
}

int main() {
    Tree tree = Node(1, Node(2, Leaf(), Leaf()),
                     Node(3, Node(4, Leaf(), Leaf()), Node(5, Leaf(), Leaf())));
    print_tree(tree, 0);
    printf("\n");
    Tree reversed_tree = reverse_tree(tree);
    print_tree(reversed_tree, 0);
    return 0;
}