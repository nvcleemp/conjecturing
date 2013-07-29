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
#include <math.h>

typedef int boolean;
#define TRUE 1
#define FALSE 0

#define MAX_UNARY_COUNT 10
#define MAX_BINARY_COUNT 10

#define MAX_TREE_DEPTH MAX_UNARY_COUNT + MAX_BINARY_COUNT
#define MAX_TREE_LEVEL_WIDTH MAX_BINARY_COUNT + 1
#define MAX_NODES_USED MAX_UNARY_COUNT + 2*MAX_BINARY_COUNT + 1

#define MAX_INVARIANT_COUNT 100
#define MAX_UNARY_OPERATORS 20
#define MAX_COMM_BINARY_OPERATORS 20
#define MAX_NCOMM_BINARY_OPERATORS 20

#define MAX_ENTITY_COUNT 1000

#define INVARIANT_LABEL 0
#define UNARY_LABEL 1
#define COMM_BINARY_LABEL 2
#define NON_COMM_BINARY_LABEL 3

int verbose = FALSE;

int targetUnary; //number of unary nodes in the generated trees
int targetBinary; //number of binary nodes in the generated trees

int invariantCount;
boolean invariantsUsed[MAX_INVARIANT_COUNT];

int mainInvariant;

#define LEQ 0 // i.e., MI <= expression
#define LESS 1 // i.e., MI < expression
#define GEQ 2 // i.e., MI >= expression
#define GREATER 3 // i.e., MI > expression

int inequality = LEQ;

int unaryOperatorCount = 7;
/* 
 * 1: x - 1
 * 2: x + 1
 * 3: x * 2
 * 4: x / 2
 * 5: x ** 2
 * 6: x * (-1)
 * 7: x ** (-1)
 */
int unaryOperators[MAX_UNARY_OPERATORS];

int commBinaryOperatorCount = 2;
/* 
 * 1: x + y
 * 2: x * y
 */
int commBinaryOperators[MAX_COMM_BINARY_OPERATORS];

int nonCommBinaryOperatorCount = 3;
/* 
 * 1: x - y
 * 2: x / y
 * 3: x ** y
 */
int nonCommBinaryOperators[MAX_NCOMM_BINARY_OPERATORS];

double invariantValues[MAX_ENTITY_COUNT][MAX_INVARIANT_COUNT];

int entityCount = 0;

unsigned long int treeCount = 0;
unsigned long int labeledTreeCount = 0;

boolean onlyUnlabeled = FALSE;
boolean onlyLabeled = FALSE;

typedef struct node {
    struct node *left;
    struct node *right;
    
    int type; //i.e., number of children
    int depth;
    
    int pos;
    
    int contentLabel[2];
    char *content;
} NODE;

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

double handleUnaryOperator(int id, double value){
    if(id==0){
        return value - 1;
    } else if(id==1){
        return value + 1;
    } else if(id==2){
        return value * 2;
    } else if(id==3){
        return value / 2;
    } else if(id==4){
        return value*value;
    } else if(id==5){
        return -value;
    } else if(id==6){
        return 1/value;
    } else {
        fprintf(stderr, "Unknown unary operator ID -- exiting\n");
        exit(EXIT_FAILURE);
    }
}

double handleCommutativeBinaryOperator(int id, double left, double right){
    if(id==0){
        return left + right;
    } else if(id==1){
        return left*right;
    } else {
        fprintf(stderr, "Unknown commutative binary operator ID -- exiting\n");
        exit(EXIT_FAILURE);
    }
}

double handleNonCommutativeBinaryOperator(int id, double left, double right){
    if(id==0){
        return left - right;
    } else if(id==1){
        return left/right;
    } else if(id==2){
        return pow(left, right);
    } else {
        fprintf(stderr, "Unknown non-commutative binary operator ID -- exiting\n");
        exit(EXIT_FAILURE);
    }
}

boolean handleComparator(double left, double right, int id){
    if(id==0){
        return left <= right;
    } else if(id==1){
        return left < right;
    } else if(id==2){
        return left >= right;
    } else if(id==3){
        return left > right;
    } else {
        fprintf(stderr, "Unknown comparator ID -- exiting\n");
        exit(EXIT_FAILURE);
    }
}

double evaluateNode(NODE *node, int entity){
    if (node->contentLabel[0]==INVARIANT_LABEL) {
        return invariantValues[entity][node->contentLabel[1]];
    } else if (node->contentLabel[0]==UNARY_LABEL) {
        return handleUnaryOperator(node->contentLabel[1], evaluateNode(node->left, entity));
    } else if (node->contentLabel[0]==NON_COMM_BINARY_LABEL){
        return handleNonCommutativeBinaryOperator(node->contentLabel[1],
                evaluateNode(node->left, entity), evaluateNode(node->right, entity));
    } else if (node->contentLabel[0]==COMM_BINARY_LABEL){
        return handleCommutativeBinaryOperator(node->contentLabel[1],
                evaluateNode(node->left, entity), evaluateNode(node->right, entity));
    } else {
        fprintf(stderr, "Unknown content label type -- exiting\n");
        exit(EXIT_FAILURE);
    }
}

boolean evaluateTree(TREE *tree){
    int i;
    int hitCount = 0;
    for(i=0; i<entityCount; i++){
        double expression = evaluateNode(tree->root, i);
        if(!handleComparator(invariantValues[i][mainInvariant], expression, inequality)){
            return FALSE;
        } else if(expression==invariantValues[i][mainInvariant]) {
            hitCount++;
        }
    }
    return TRUE;
}

void handleLabeledTree(TREE *tree){
    labeledTreeCount++;
}

boolean leftSideBiggest(NODE *node, NODE **orderedNodes){
    NODE *leftMost = node->left;
    while (leftMost->left != NULL) leftMost = leftMost->left;
    int startLeft = leftMost->pos;
    int startRight = node->left->pos+1;
    int lengthLeft = startRight - startLeft;
    int lengthRight = node->pos - startRight;
    
    if(lengthLeft > lengthRight){
        return TRUE;
    } else if (lengthLeft < lengthRight){
        return FALSE;
    } else {
        int i = 0;
        while (i<lengthLeft &&
                orderedNodes[startLeft + i]->contentLabel[0]==orderedNodes[startRight + i]->contentLabel[0] &&
                orderedNodes[startLeft + i]->contentLabel[1]==orderedNodes[startRight + i]->contentLabel[1]){
            i++;
        }
        return i==lengthLeft ||
                (orderedNodes[startLeft + i]->contentLabel[0] > orderedNodes[startRight + i]->contentLabel[0]) ||
                ((orderedNodes[startLeft + i]->contentLabel[0] == orderedNodes[startRight + i]->contentLabel[0]) &&
                 (orderedNodes[startLeft + i]->contentLabel[1] > orderedNodes[startRight + i]->contentLabel[1]));
    }
}

void generateLabeledTree(TREE *tree, NODE **orderedNodes, int pos){
    int i;
    
    if (pos == targetUnary + 2*targetBinary + 1){
        handleLabeledTree(tree);
    } else {
        NODE *currentNode = orderedNodes[pos];
        if (currentNode->type == 0){
            currentNode->contentLabel[0] = INVARIANT_LABEL;
            for (i=0; i<invariantCount; i++){
                if (!invariantsUsed[i]){
                    currentNode->contentLabel[1] = i;
                    invariantsUsed[i] = TRUE;
                    generateLabeledTree(tree, orderedNodes, pos+1);
                    invariantsUsed[i] = FALSE;
                }
            }
        } else if (currentNode->type == 1){
            currentNode->contentLabel[0] = UNARY_LABEL;
            for (i=0; i<unaryOperatorCount; i++){
                currentNode->contentLabel[1] = unaryOperators[i];
                generateLabeledTree(tree, orderedNodes, pos+1);
            }
        } else { // currentNode->type == 2
            //first try non-commutative binary operators
            currentNode->contentLabel[0] = NON_COMM_BINARY_LABEL;
            for (i=0; i<nonCommBinaryOperatorCount; i++){
                currentNode->contentLabel[1] = nonCommBinaryOperators[i];
                generateLabeledTree(tree, orderedNodes, pos+1);
            }
            
            //then try commutative binary operators
            if (leftSideBiggest(currentNode, orderedNodes)){
                currentNode->contentLabel[0] = COMM_BINARY_LABEL;
                for (i=0; i<commBinaryOperatorCount; i++){
                    currentNode->contentLabel[1] = commBinaryOperators[i];
                    generateLabeledTree(tree, orderedNodes, pos+1);
                }
            }
        }
    }
}

void handleTree(TREE *tree){
    treeCount++;
    if(onlyUnlabeled) return;
    
    //start by ordering nodes
    NODE *orderedNodes[targetUnary + 2*targetBinary + 1];
    
    int pos = 0;
    getOrderedNodes(tree->root, orderedNodes, &pos);
    
    //mark all invariants as unused
    int i;
    for (i=0; i<invariantCount; i++){
        invariantsUsed[i] = FALSE;
    }
    
    generateLabeledTree(tree, orderedNodes, 0);
}

void generateTreeImpl(TREE *tree){
    int i, start;
    
    if(tree->unaryCount > targetUnary + 1 || tree->binaryCount > targetBinary)
        return;
    
    if(isComplete(tree)){
        handleTree(tree);
        return;
    }
    
    start = tree->levelWidth[tree->depth-1]-1;
    while(start>=0 && tree->nodesAtDepth[tree->depth-1][start]->type==0){
        start--;
    }
    if(start>=0 && tree->nodesAtDepth[tree->depth-1][start]->type==1){
        start--;
    }
    
    for(i=start+1; i<tree->levelWidth[tree->depth-1]; i++){
        NODE *parent = tree->nodesAtDepth[tree->depth-1][i];
        addChildToNodeInTree(tree, parent);
        generateTreeImpl(tree);
        removeChildFromNodeInTree(tree, parent);
    }
    
    for(i=0; i<tree->levelWidth[tree->depth]; i++){
        NODE *parent = tree->nodesAtDepth[tree->depth][i];
        addChildToNodeInTree(tree, parent);
        generateTreeImpl(tree);
        removeChildFromNodeInTree(tree, parent);
    }
}

void generateTree(int unary, int binary){
    TREE tree;
    targetUnary = unary;
    targetBinary = binary;
    initTree(&tree);
    
    if (unary==0 && binary==0){
        handleTree(&tree);
    } else {
        addChildToNodeInTree(&tree, tree.root);
        generateTreeImpl(&tree);
        removeChildFromNodeInTree(&tree, tree.root);
    }
    
    freeTree(&tree);
}
//===================================================================
// Usage methods
//===================================================================
void help(char *name){
    fprintf(stderr, "The program %s constructs expressions based on provided parameters.\n\n", name);
    fprintf(stderr, "Usage\n=====\n");
    fprintf(stderr, " %s [options] -u unary binary\n", name);
    fprintf(stderr, "       Generates expression trees with the given number of unary and\n");
    fprintf(stderr, "       binary operators.\n");
    fprintf(stderr, " %s [options] -l unary binary invariants\n", name);
    fprintf(stderr, "       Generates labeled expression trees with the given number of unary\n");
    fprintf(stderr, "       and binary operators and the given number of invariants.\n");
    fprintf(stderr, "\n\n");
    fprintf(stderr, "Valid options\n=============\n");
    fprintf(stderr, "* Generated types\n");
    fprintf(stderr, "    -u, --unlabeled\n");
    fprintf(stderr, "       Generate unlabeled expression trees.\n");
    fprintf(stderr, "    -l, --labeled\n");
    fprintf(stderr, "       Generate labeled expression trees.\n");
    fprintf(stderr, "\n");
    fprintf(stderr, "* Parameters\n");
    fprintf(stderr, "    --unary n\n");
    fprintf(stderr, "       The number of unary operators used during the generation of labeled\n");
    fprintf(stderr, "       expression trees. This value is ignored when generating valid\n");
    fprintf(stderr, "       expressions.\n");
    fprintf(stderr, "    --commutative n\n");
    fprintf(stderr, "       The number of commutative binary operators used during the generation\n");
    fprintf(stderr, "       of labeled expression trees. This value is ignored when generating valid\n");
    fprintf(stderr, "       expressions.\n");
    fprintf(stderr, "    --non-commutative n\n");
    fprintf(stderr, "       The number of non-commutative binary operators used during the\n");
    fprintf(stderr, "       generation of labeled expression trees. This value is ignored when\n");
    fprintf(stderr, "       generating valid expressions.\n");
    fprintf(stderr, "\n");
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
        {"unary", required_argument, NULL, 0},
        {"commutative", required_argument, NULL, 0},
        {"non-commutative", required_argument, NULL, 0},
        {"help", no_argument, NULL, 'h'},
        {"verbose", no_argument, NULL, 'v'},
        {"unlabeled", no_argument, NULL, 'u'},
        {"labeled", no_argument, NULL, 'l'}
    };
    int option_index = 0;

    while ((c = getopt_long(argc, argv, "hvul", long_options, &option_index)) != -1) {
        switch (c) {
            case 0:
                //handle long option with no alternative
                switch(option_index) {
                    case 0:
                        unaryOperatorCount = strtol(optarg, NULL, 10);
                        break;
                    case 1:
                        commBinaryOperatorCount = strtol(optarg, NULL, 10);
                        break;
                    case 2:
                        nonCommBinaryOperatorCount = strtol(optarg, NULL, 10);
                        break;
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
            case 'u':
                onlyUnlabeled = TRUE;
                break;
            case 'l':
                onlyLabeled = TRUE;
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
    
    // check the non-option arguments
    if (onlyUnlabeled && argc - optind != 2) {
        usage(name);
        return EXIT_FAILURE;
    }
    
    if (onlyLabeled && argc - optind != 3) {
        usage(name);
        return EXIT_FAILURE;
    }
    
    return -1;
}

int main(int argc, char *argv[]) {
    
    int po = processOptions(argc, argv);
    if(po != -1) return po;
    
    int unary = strtol(argv[optind], NULL, 10);
    int binary = strtol(argv[optind+1], NULL, 10);
    if(!onlyUnlabeled) {
        invariantCount = strtol(argv[optind+2], NULL, 10);
    }
    
    //set the operator labels
    /* TODO: this is only temporarily. Once we are generating
     * actual expressions the labels will not be consecutively
     * but will refer to the actual operators being used. This
     * code however will be retained for when just labeled trees
     * are being generated.
     */
    if(!onlyUnlabeled) {
        int i;
        for (i=0; i<unaryOperatorCount; i++) {
            unaryOperators[i] = i;
        }
        for (i=0; i<commBinaryOperatorCount; i++) {
            commBinaryOperators[i] = i;
        }
        for (i=0; i<nonCommBinaryOperatorCount; i++) {
            nonCommBinaryOperators[i] = i;
        }
    }
    
    generateTree(unary, binary);
    
    if(onlyUnlabeled){
        fprintf(stderr, "Found %lu unlabeled trees.\n", treeCount);
    } else if(onlyLabeled) {
        fprintf(stderr, "Found %lu unlabeled trees.\n", treeCount);
        fprintf(stderr, "Found %lu labeled trees.\n", labeledTreeCount);
    }
    
    return 0;
}
