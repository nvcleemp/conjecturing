/*
 * Main developer: Nico Van Cleemput
 * In collaboration with: Craig Larson
 * 
 * Copyright (C) 2013 Ghent University.
 * Licensed under the GNU GPL, read the file LICENSE.txt for details.
 */

#ifndef BINTREES_H
#define	BINTREES_H
    
#include "limits.h"

typedef int boolean;
#define TRUE 1
#define FALSE 0

typedef struct node {
    struct node *left;
    struct node *right;
    
    int type; //i.e., number of children
    int depth;
    
    int pos;
    
    int contentLabel[2];
} NODE;

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


//------ Node operations -------

void addChildToNode(NODE *parent, NODE *child);

NODE *removeChildFromNode(NODE *parent);

void getOrderedNodes(NODE *node, NODE **orderedNodes, int *currentPosition);

//------ Tree operations -------

void initTree(TREE *tree);

void freeTree(TREE *tree);

void addChildToNodeInTree(TREE *tree, NODE *parent);

void removeChildFromNodeInTree(TREE *tree, NODE *parent);

#endif	/* BINTREES_H */

