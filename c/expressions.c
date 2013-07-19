/*
 * Main developer: Nico Van Cleemput
 * In collaboration with: Craig Larson
 * 
 * Copyright (C) 2013 Ghent University.
 * Licensed under the GNU GPL, read the file LICENSE.txt for details.
 */

#include <stdlib.h>
#include <stdio.h>
#include <getopt.h>

typedef int boolean;
#define TRUE 1
#define FALSE 0

#define MAX_UNARY_COUNT 10
#define MAX_BINARY_COUNT 10

#define MAX_TREE_DEPTH MAX_UNARY_COUNT + MAX_BINARY_COUNT
#define MAX_TREE_LEVEL_WIDTH MAX_BINARY_COUNT + 1
#define MAX_NODES_USED MAX_UNARY_COUNT + 2*MAX_BINARY_COUNT + 1

int verbose = FALSE;

int targetUnary;
int targetBinary;

typedef struct node {
    struct node *left;
    struct node *right;
    
    int type; //i.e., number of children
    int depth;
    
    char *content;
} NODE;

const NODE DEFAULT_NODE = {NULL, NULL, 0, 0, NULL};

void addChildToNode(NODE *parent, NODE *child){
    if(parent->left == NULL){
        parent->left = child;
        parent->type = 1;
        child->depth = parent->depth + 1;
    } else if(parent->right == NULL){
        parent->right = child;
        parent->type = 2;
        child->depth = parent->depth + 1;
    } else {
        fprintf(stderr, "ERROR: Parent already has two children.\n");
        exit(EXIT_FAILURE);
    }
}

NODE *removeChildFromNode(NODE *parent){
    if(parent->right != NULL){
        NODE *child = parent->right;
        parent->right = NULL;
        parent->type = 1;
        return child;
    } else if(parent->left != NULL){
        NODE *child = parent->left;
        parent->left = NULL;
        parent->type = 0;
        return child;
    } else {
        fprintf(stderr, "ERROR: Parent has no children.\n");
        exit(EXIT_FAILURE);
    }
}

typedef struct tree {
    struct node *root;
    
    struct node *unusedStack[MAX_NODES_USED - 1]; //-1 because root is never unused
    int unusedStackSize;
    
    struct node *nodesAtDepth[MAX_TREE_DEPTH+1][MAX_TREE_LEVEL_WIDTH];
    int levelWidth[MAX_TREE_DEPTH+1];
    int depth;
    
    int unaryCount;
    int binaryCount;
} TREE;

void initTree(TREE *tree){
    int i;
    for(i=0; i<MAX_NODES_USED - 1; i++){
        tree->unusedStack[i] = malloc(sizeof(NODE));
        tree->unusedStack[i]->left = tree->unusedStack[i]->right = NULL;
        tree->unusedStack[i]->depth = 0;
        tree->unusedStack[i]->type = 0;
        tree->unusedStack[i]->content = NULL;
    }
    tree->unusedStackSize = MAX_NODES_USED - 1;
    
    for(i=0; i<MAX_TREE_DEPTH+1; i++){
        tree->levelWidth[i]=0;
    }
    
    tree->binaryCount = tree->unaryCount = 0;
    tree->depth = 0;
    
    //create the root
    NODE *root = malloc(sizeof(NODE));
    root->left = root->right = NULL;
    root->depth = 0;
    root->type = 0;
    root->content = NULL;
    
    //set the root
    tree->root = root;
    tree->levelWidth[0] = 1;
    tree->nodesAtDepth[0][0] = tree->root;
}

void freeTree(TREE *tree){
    int i;
    for(i=0; i<MAX_NODES_USED - 1; i++){
        free(tree->unusedStack[i]);
    }
    free(tree->root);
}

/* 
 * Returns non-zero value if the tree satisfies the current target counts
 * for unary and binary operators. Returns 0 in all other cases.
 */
boolean isComplete(TREE *tree){
    return tree->unaryCount == targetUnary && tree->binaryCount == targetBinary;
}

//===================================================================
// Usage methods
//===================================================================
void help(char *name){
    fprintf(stderr, "The program %s constructs expression based on provided parameters.\n\n", name);
    fprintf(stderr, "Usage\n=====\n");
    fprintf(stderr, " %s [options]\n", name);
    fprintf(stderr, "       <description>.\n");
    fprintf(stderr, "\n\n");
    fprintf(stderr, "Valid options\n=============\n");
    fprintf(stderr, "* Various options\n");
    fprintf(stderr, "    -h, --help\n");
    fprintf(stderr, "       Print this help and return.\n");
    fprintf(stderr, "    -v, --verbose\n");
    fprintf(stderr, "       Make the program more verbose.\n");
}

void usage(char *name){
    fprintf(stderr, "Usage: %s [options]\n", name);
    fprintf(stderr, "For more information type: %s -h \n\n", name);
}

/*
 * process any command-line options.
 */
int processOptions(int argc, char **argv) {
    int c;
    char *name = argv[0];
    static struct option long_options[] = {
        {"help", no_argument, NULL, 'h'},
        {"verbose", no_argument, NULL, 'v'}
    };
    int option_index = 0;

    while ((c = getopt_long(argc, argv, "hf:dvoF:", long_options, &option_index)) != -1) {
        switch (c) {
            case 0:
                //handle long option with no alternative
                switch(option_index) {
                    default:
                        fprintf(stderr, "Illegal option index %d.\n", option_index);
                        usage(name);
                        return EXIT_FAILURE;
                }
                break;
            case 'h':
                help(name);
                return EXIT_SUCCESS;
            case 'v':
                verbose = TRUE;
                break;
            case '?':
                usage(name);
                return EXIT_FAILURE;
            default:
                fprintf(stderr, "Illegal option %c.\n", c);
                usage(name);
                return EXIT_FAILURE;
        }
    }
    return -1;
}

int main(int argc, char *argv[]) {
    
    int po = processOptions(argc, argv);
    if(po != -1) return po;
    

    return 0;
}
