/*
 * Main developer: Nico Van Cleemput
 * In collaboration with: Craig Larson
 * 
 * Copyright (C) 2013 Ghent University.
 * Licensed under the GNU GPL, read the file LICENSE.txt for details.
 */

#include "bintrees.h"
#include "util.h"
#include "printing.h"

#define INVARIANT_LABEL 0
#define UNARY_LABEL 1
#define COMM_BINARY_LABEL 2
#define NON_COMM_BINARY_LABEL 3

void printComparator(int id, FILE *f){
    if(id==0){
        fprintf(f, "<=");
    } else if(id==1){
        fprintf(f, "<");
    } else if(id==2){
        fprintf(f, ">=");
    } else if(id==3){
        fprintf(f, ">");
    } else {
        BAILOUT("Unknown comparator ID")
    }
}

void printUnaryOperator_left(int id, FILE *f){
    if(id==0 || id==1 || id==2 || id==3 || id==4){
        fprintf(f, "(");
    } else if(id==5){
        fprintf(f, "(-");
    } else if(id==6){
        fprintf(f, "(1 / ");
    } else if(id==7){
        fprintf(f, "(sqrt");
    } else if(id==8){
        fprintf(f, "(ln");
    } else if(id==9){
        fprintf(f, "(log10");
    } else {
        BAILOUT("Unknown unary operator ID")
    }
}

void printUnaryOperator_right(int id, FILE *f){
    if(id==0){
        fprintf(f, " - 1)");
    } else if(id==1){
        fprintf(f, " + 1)");
    } else if(id==2){
        fprintf(f, " * 2)");
    } else if(id==3){
        fprintf(f, " / 2)");
    } else if(id==4){
        fprintf(f, " ^ 2)");
    } else if(id==5 || id==6 || id==7 || id==8 || id==9){
        fprintf(f, ")");
    } else {
        BAILOUT("Unknown unary operator ID")
    }
}

void printCommutativeBinaryOperator_left(int id, FILE *f){
    if(id==0 || id==1){
        fprintf(f, "(");
    } else {
        BAILOUT("Unknown commutative binary operator ID")
    }
}

void printCommutativeBinaryOperator_middle(int id, FILE *f){
    if(id==0){
        fprintf(f, " + ");
    } else if(id==1){
        fprintf(f, " * ");
    } else {
        BAILOUT("Unknown commutative binary operator ID")
    }
}

void printCommutativeBinaryOperator_right(int id, FILE *f){
    if(id==0 || id==1){
        fprintf(f, ")");
    } else {
        BAILOUT("Unknown commutative binary operator ID")
    }
}

void printNonCommutativeBinaryOperator_left(int id, FILE *f){
    if(id==0 || id==1 || id==2){
        fprintf(f, "(");
    } else {
        BAILOUT("Unknown commutative binary operator ID")
    }
}

void printNonCommutativeBinaryOperator_middle(int id, FILE *f){
    if(id==0){
        fprintf(f, " - ");
    } else if(id==1){
        fprintf(f, " / ");
    } else if(id==2){
        fprintf(f, " ^ ");
    } else {
        BAILOUT("Unknown commutative binary operator ID")
    }
}

void printNonCommutativeBinaryOperator_right(int id, FILE *f){
    if(id==0 || id==1 || id==2){
        fprintf(f, ")");
    } else {
        BAILOUT("Unknown commutative binary operator ID")
    }
}

void printNode(NODE *node, FILE *f, char **invariantNamePointers){
    int type = node->contentLabel[0];
    int id = node->contentLabel[1];
    if (type==INVARIANT_LABEL) {
        if(invariantNamePointers==NULL){
            fprintf(f, "(I%d)", id + 1);
        } else {
            fprintf(f, "(%s)", invariantNamePointers[id]);
        }
    } else if (type==UNARY_LABEL) {
        printUnaryOperator_left(id, f);
        printNode(node->left, f, invariantNamePointers);
        printUnaryOperator_right(id, f);
    } else if (type==NON_COMM_BINARY_LABEL){
        printNonCommutativeBinaryOperator_left(id, f);
        printNode(node->left, f, invariantNamePointers);
        printNonCommutativeBinaryOperator_middle(id, f);
        printNode(node->right, f, invariantNamePointers);
        printNonCommutativeBinaryOperator_right(id, f);
    } else if (type==COMM_BINARY_LABEL){
        printCommutativeBinaryOperator_left(id, f);
        printNode(node->left, f, invariantNamePointers);
        printCommutativeBinaryOperator_middle(id, f);
        printNode(node->right, f, invariantNamePointers);
        printCommutativeBinaryOperator_right(id, f);
    } else {
        BAILOUT("Unknown content label type")
    }
}

void printUnaryOperator_single(int id, FILE *f){
    if(id==0){
        fprintf(f, "-1");
    } else if(id==1){
        fprintf(f, "+1");
    } else if(id==2){
        fprintf(f, "*2");
    } else if(id==3){
        fprintf(f, "/2");
    } else if(id==4){
        fprintf(f, "^2");
    } else if(id==5){
        fprintf(f, "-()");
    } else if(id==6){
        fprintf(f, "1/");
    } else if(id==7){
        fprintf(f, "sqrt");
    } else if(id==8){
        fprintf(f, "ln");
    } else if(id==9){
        fprintf(f, "log10");
    } else {
        BAILOUT("Unknown unary operator ID")
    }
}

void printCommutativeBinaryOperator_single(int id, FILE *f){
    if(id==0){
        fprintf(f, "+");
    } else if(id==1){
        fprintf(f, "*");
    } else {
        BAILOUT("Unknown commutative binary operator ID")
    }
}

void printNonCommutativeBinaryOperator_single(int id, FILE *f){
    if(id==0){
        fprintf(f, "-");
    } else if(id==1){
        fprintf(f, "/");
    } else if(id==2){
        fprintf(f, "^");
    } else {
        BAILOUT("Unknown commutative binary operator ID")
    }
}

void printSingleNode(NODE *node, FILE *f, char **invariantNamePointers){
    int type = node->contentLabel[0];
    int id = node->contentLabel[1];
    if (type==INVARIANT_LABEL) {
        if(invariantNamePointers==NULL){
            fprintf(f, "I%d", id + 1);
        } else {
            fprintf(f, "%s", invariantNamePointers[id]);
        }
    } else if (type==UNARY_LABEL) {
        printUnaryOperator_single(id, f);
    } else if (type==NON_COMM_BINARY_LABEL){
        printNonCommutativeBinaryOperator_single(id, f);
    } else if (type==COMM_BINARY_LABEL){
        printCommutativeBinaryOperator_single(id, f);
    } else {
        BAILOUT("Unknown content label type")
    }
}
