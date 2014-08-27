/*
 * Main developer: Nico Van Cleemput
 * In collaboration with: Craig Larson
 * 
 * Copyright (C) 2014 Nico Van Cleemput.
 * Licensed under the GNU GPL, read the file LICENSE.txt for details.
 */

#include "bintrees.h"
#include "util.h"
#include "printing_pb.h"

#define INVARIANT_LABEL 0
#define UNARY_LABEL 1
#define COMM_BINARY_LABEL 2
#define NON_COMM_BINARY_LABEL 3

void printComparator_propertyBased(int id, FILE *f){
    if(id==0){
        fprintf(f, "<=");
    } else if(id==2){
        fprintf(f, ">=");
    } else {
        BAILOUT("Unknown comparator ID")
    }
}

void printUnaryOperator_left_propertyBased(int id, FILE *f){
    if(id==0){
        fprintf(f, "!(");
    } else {
        BAILOUT("Unknown unary operator ID")
    }
}

void printUnaryOperator_right_propertyBased(int id, FILE *f){
    if(id==0){
        fprintf(f, ")");
    } else {
        BAILOUT("Unknown unary operator ID")
    }
}

void printCommutativeBinaryOperator_left_propertyBased(int id, FILE *f){
    if(id==0 || id==1 || id==2){
        fprintf(f, "(");
    } else {
        BAILOUT("Unknown commutative binary operator ID")
    }
}

void printCommutativeBinaryOperator_middle_propertyBased(int id, FILE *f){
    if(id==0){
        fprintf(f, ") & (");
    } else if(id==1){
        fprintf(f, ") | (");
    } else if(id==2){
        fprintf(f, ") ^ (");
    } else {
        BAILOUT("Unknown commutative binary operator ID")
    }
}

void printCommutativeBinaryOperator_right_propertyBased(int id, FILE *f){
    if(id==0 || id==1 || id==2){
        fprintf(f, ")");
    } else {
        BAILOUT("Unknown commutative binary operator ID")
    }
}

void printNonCommutativeBinaryOperator_left_propertyBased(int id, FILE *f){
    if(id==0){
        fprintf(f, "(");
    } else {
        BAILOUT("Unknown commutative binary operator ID")
    }
}

void printNonCommutativeBinaryOperator_middle_propertyBased(int id, FILE *f){
    if(id==0){
        fprintf(f, ") => (");
    } else {
        BAILOUT("Unknown commutative binary operator ID")
    }
}

void printNonCommutativeBinaryOperator_right_propertyBased(int id, FILE *f){
    if(id==0){
        fprintf(f, ")");
    } else {
        BAILOUT("Unknown commutative binary operator ID")
    }
}

void printNode_propertyBased(NODE *node, FILE *f, char **invariantNamePointers){
    int type = node->contentLabel[0];
    int id = node->contentLabel[1];
    if (type==INVARIANT_LABEL) {
        if(invariantNamePointers==NULL){
            fprintf(f, "I%d", id + 1);
        } else {
            fprintf(f, "%s", invariantNamePointers[id]);
        }
    } else if (type==UNARY_LABEL) {
        printUnaryOperator_left_propertyBased(id, f);
        printNode_propertyBased(node->left, f, invariantNamePointers);
        printUnaryOperator_right_propertyBased(id, f);
    } else if (type==NON_COMM_BINARY_LABEL){
        printNonCommutativeBinaryOperator_left_propertyBased(id, f);
        printNode_propertyBased(node->left, f, invariantNamePointers);
        printNonCommutativeBinaryOperator_middle_propertyBased(id, f);
        printNode_propertyBased(node->right, f, invariantNamePointers);
        printNonCommutativeBinaryOperator_right_propertyBased(id, f);
    } else if (type==COMM_BINARY_LABEL){
        printCommutativeBinaryOperator_left_propertyBased(id, f);
        printNode_propertyBased(node->left, f, invariantNamePointers);
        printCommutativeBinaryOperator_middle_propertyBased(id, f);
        printNode_propertyBased(node->right, f, invariantNamePointers);
        printCommutativeBinaryOperator_right_propertyBased(id, f);
    } else {
        BAILOUT("Unknown content label type")
    }
}

void printUnaryOperator_single_propertyBased(int id, FILE *f){
    if(id==0){
        fprintf(f, "!");
    } else {
        BAILOUT("Unknown unary operator ID")
    }
}

void printCommutativeBinaryOperator_single_propertyBased(int id, FILE *f){
    if(id==0){
        fprintf(f, "&"); //AND
    } else if(id==1){
        fprintf(f, "|"); //OR
    } else if(id==2){
        fprintf(f, "^"); //XOR
    } else {
        BAILOUT("Unknown commutative binary operator ID")
    }
}

void printNonCommutativeBinaryOperator_single_propertyBased(int id, FILE *f){
    if(id==0){
        fprintf(f, "=>");
    } else {
        BAILOUT("Unknown commutative binary operator ID")
    }
}

void printSingleNode_propertyBased(NODE *node, FILE *f, char **invariantNamePointers){
    int type = node->contentLabel[0];
    int id = node->contentLabel[1];
    if (type==INVARIANT_LABEL) {
        if(invariantNamePointers==NULL){
            fprintf(f, "I%d", id + 1);
        } else {
            fprintf(f, "%s", invariantNamePointers[id]);
        }
    } else if (type==UNARY_LABEL) {
        printUnaryOperator_single_propertyBased(id, f);
    } else if (type==NON_COMM_BINARY_LABEL){
        printNonCommutativeBinaryOperator_single_propertyBased(id, f);
    } else if (type==COMM_BINARY_LABEL){
        printCommutativeBinaryOperator_single_propertyBased(id, f);
    } else {
        BAILOUT("Unknown content label type")
    }
}
