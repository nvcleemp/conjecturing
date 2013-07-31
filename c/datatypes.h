/* 
 * File:   datatypes.h
 * Author: nvcleemp
 *
 * Created on July 31, 2013, 3:44 PM
 */

#ifndef DATATYPES_H
#define	DATATYPES_H

#ifdef	__cplusplus
extern "C" {
#endif
    
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
    char *content;
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


#ifdef	__cplusplus
}
#endif

#endif	/* DATATYPES_H */

