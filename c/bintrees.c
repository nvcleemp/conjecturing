/*
 * Main developer: Nico Van Cleemput
 * In collaboration with: Craig Larson
 * 
 * Copyright (C) 2013 Ghent University.
 * Licensed under the GNU GPL, read the file LICENSE.txt for details.
 */

#include <stdlib.h>
#include "bintrees.h"
#include "util.h"

//------ Node operations -------

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
        BAILOUT("Parent already has two children")
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
        BAILOUT("Parent has no children")
    }
}

void getOrderedNodes(NODE *node, NODE **orderedNodes, int *currentPosition){
    if(node->type==2){
        getOrderedNodes(node->left, orderedNodes, currentPosition);
        getOrderedNodes(node->right, orderedNodes, currentPosition);
        orderedNodes[*currentPosition] = node;
        node->pos = *currentPosition;
        (*currentPosition)++;
    } else if(node->type==1){
        getOrderedNodes(node->left, orderedNodes, currentPosition);
        orderedNodes[*currentPosition] = node;
        node->pos = *currentPosition;
        (*currentPosition)++;
    } else {
        orderedNodes[*currentPosition] = node;
        node->pos = *currentPosition;
        (*currentPosition)++;
    }
}

//------ Tree operations -------

void initTree(TREE *tree){
    int i;
    for(i=0; i<MAX_NODES_USED - 1; i++){
        tree->unusedStack[i] = malloc(sizeof(NODE));
        tree->unusedStack[i]->left = tree->unusedStack[i]->right = NULL;
        tree->unusedStack[i]->depth = 0;
        tree->unusedStack[i]->type = 0;
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

void addChildToNodeInTree(TREE *tree, NODE *parent){
    NODE *child = tree->unusedStack[--(tree->unusedStackSize)];
    addChildToNode(parent, child);
    if(child->depth > tree->depth) tree->depth = child->depth;
    
    if(parent->type==2){
        tree->unaryCount--;
        tree->binaryCount++;
    } else {
        tree->unaryCount++;
    }
    
    tree->nodesAtDepth[child->depth][(tree->levelWidth[child->depth])++] = child;
}

void removeChildFromNodeInTree(TREE *tree, NODE *parent){
    NODE *child = removeChildFromNode(parent);
    tree->unusedStack[tree->unusedStackSize] = child;
    (tree->unusedStackSize)++;
    tree->levelWidth[child->depth]--;
    
    if(tree->levelWidth[child->depth]==0){
        tree->depth--;
    }
    
    if(parent->type==1){
        tree->binaryCount--;
        tree->unaryCount++;
    } else {
        tree->unaryCount--;
    }
}
