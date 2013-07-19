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

int verbose = FALSE;

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
    } else if(parent->right == NULL){
        parent->right = child;
        parent->type = 2;
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
