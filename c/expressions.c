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
#include <ctype.h>
#include <string.h>
#include <signal.h>
#include <unistd.h>
#include <float.h>
#include <malloc.h>

#include "bintrees.h"
#include "util.h"
#include "printing.h"
#include "printing_pb.h"

#define INVARIANT_LABEL 0
#define UNARY_LABEL 1
#define COMM_BINARY_LABEL 2
#define NON_COMM_BINARY_LABEL 3

//UNDEFINED is used for undefined values when making property based conjectures
#define UNDEFINED -1

int verbose = FALSE;

char outputType = 'h';

int targetUnary; //number of unary nodes in the generated trees
int targetBinary; //number of binary nodes in the generated trees

int invariantCount;
boolean *invariantsUsed;

int mainInvariant;

boolean allowMainInvariantInExpressions = FALSE;
boolean useInvariantNames = FALSE;

float allowedPercentageOfSkips = 0.2f;

char **invariantNames;
char **invariantNamesPointers;

#define LEQ 0 // i.e., MI <= expression
#define LESS 1 // i.e., MI < expression
#define GEQ 2 // i.e., MI >= expression
#define GREATER 3 // i.e., MI > expression

#define SUFFICIENT 0 // i.e., MI <= expression
#define NECESSARY 2 // i.e., MI => expression

int inequality = LEQ; // == SUFFICIENT

int unaryOperatorCount = 27;
/* 
 * 1: x - 1
 * 2: x + 1
 * 3: x * 2
 * 4: x / 2
 * 5: x ** 2
 * 6: x * (-1)
 * 7: x ** (-1)
 * 8: sqrt(x)
 * 9: ln(x)
 * 10: log_10(x)
 * 11: exp(x)
 * 12: 10 ** x
 * 13: ceil(x)
 * 14: floor(x)
 * 15: abs(x)
 * 16: sin(x)
 * 17: cos(x)
 * 18: tan(x)
 * 19: asin(x)
 * 20: acos(x)
 * 21: atan(x)
 * 22: sinh(x)
 * 23: cosh(x)
 * 24: tanh(x)
 * 25: asinh(x)
 * 26: acosh(x)
 * 27: atanh(x)
 */
int unaryOperators[MAX_UNARY_OPERATORS];

int commBinaryOperatorCount = 4;
/* 
 * 1: x + y
 * 2: x * y
 * 3: max(x,y)
 * 4: min(x,y)
 */
int commBinaryOperators[MAX_COMM_BINARY_OPERATORS];

int nonCommBinaryOperatorCount = 3;
/* 
 * 1: x - y
 * 2: x / y
 * 3: x ** y
 */
int nonCommBinaryOperators[MAX_NCOMM_BINARY_OPERATORS];

double **invariantValues;
boolean **invariantValues_propertyBased;

double *knownTheory;
boolean *knownTheory_propertyBased;

int objectCount = 0;

unsigned long int treeCount = 0;
unsigned long int labeledTreeCount = 0;
unsigned long int validExpressionsCount = 0;

unsigned long int timeOut = 0;
boolean timeOutReached = FALSE;

boolean userInterrupted = FALSE;
boolean terminationSignalReceived = FALSE;

boolean heuristicStoppedGeneration = FALSE;

boolean onlyUnlabeled = FALSE;
boolean onlyLabeled = FALSE;
boolean generateExpressions = FALSE;
boolean doConjecturing = FALSE;
boolean propertyBased = FALSE;
boolean theoryProvided = FALSE;

boolean printValidExpressions = FALSE;

#define GRINVIN_NEXT_OPERATOR_COUNT 0

int nextOperatorCountMethod = GRINVIN_NEXT_OPERATOR_COUNT;

FILE *operatorFile = NULL;
boolean closeOperatorFile = FALSE;
FILE *invariantsFile = NULL;
boolean closeInvariantsFile = FALSE;

#define NO_HEURISTIC -1
#define DALMATIAN_HEURISTIC 0
#define GRINVIN_HEURISTIC 1

int selectedHeuristic = NO_HEURISTIC;

boolean (*heuristicStopConditionReached)() = NULL;
void (*heuristicInit)() = NULL;
void (*heuristicPostProcessing)() = NULL;

//function declarations

void outputExpression(TREE *tree, FILE *f);
void printExpression(TREE *tree, FILE *f);
boolean handleComparator(double left, double right, int id);

void printExpression_propertyBased(TREE *tree, FILE *f);
boolean handleComparator_propertyBased(boolean left, boolean right, int id);

/* 
 * Returns non-zero value if the tree satisfies the current target counts
 * for unary and binary operators. Returns 0 in all other cases.
 */
boolean isComplete(TREE *tree){
    return tree->unaryCount == targetUnary && tree->binaryCount == targetBinary;
}

//----------- Heuristics -------------

//dalmatian heuristic

boolean dalmatianFirst = TRUE;

double **dalmatianCurrentConjectureValues;
boolean **dalmatianCurrentConjectureValues_propertyBased;

int *dalmatianBestConjectureForObject;

boolean *dalmatianObjectInBoundArea; //only for property based conjectures

boolean *dalmatianConjectureInUse;

TREE *dalmatianConjectures;

int dalmatianHitCount = 0;

inline void dalmatianUpdateHitCount(){
    dalmatianHitCount = 0;
    int i;
    for(i=0; i<objectCount; i++){
        double currentBest = 
        dalmatianCurrentConjectureValues[dalmatianBestConjectureForObject[i]][i];
        if(currentBest == invariantValues[i][mainInvariant]){
            dalmatianHitCount++;
        }
    }
    
}

void dalmatianHeuristic(TREE *tree, double *values){
    int i;
    //this heuristic assumes the expression was true for all objects
    
    //if known theory is provided, we check that first
    boolean isMoreSignificant = FALSE;
    if(theoryProvided){
        for(i=0; i<objectCount; i++){
            if(!handleComparator(knownTheory[i], values[i], inequality)){
                if(verbose){
                    fprintf(stderr, "Conjecture is more significant than known theory for object %d.\n", i+1);
                    fprintf(stderr, "%11.6lf vs. %11.6lf\n", knownTheory[i], values[i]);
                }
                isMoreSignificant = TRUE;
            }
        }

        //check if there is at least one object for which this bound is more significant than the known theory
        if(!isMoreSignificant) return;
    }
    
    //if this is the first conjecture, we just store it and return
    if(dalmatianFirst){
        if(verbose){
            fprintf(stderr, "Saving expression\n");
            printExpression(tree, stderr);
        }
        memcpy(dalmatianCurrentConjectureValues[0], values, 
                sizeof(double)*objectCount);
        for(i=0; i<objectCount; i++){
            dalmatianBestConjectureForObject[i] = 0;
        }
        dalmatianConjectureInUse[0] = TRUE;
        copyTree(tree, dalmatianConjectures + 0);
        dalmatianFirst = FALSE;
        dalmatianUpdateHitCount();
        return;
    }
    
    //check the significance
    //----------------------
    
    //find the objects for which this bound is better
    isMoreSignificant = FALSE; //the conjecture is not necessarily more significant than the other conjectures
    int conjectureFrequency[objectCount];
    memset(conjectureFrequency, 0, objectCount*sizeof(int));
    for(i=0; i<objectCount; i++){
        double currentBest = 
        dalmatianCurrentConjectureValues[dalmatianBestConjectureForObject[i]][i];
        if(handleComparator(currentBest, values[i], inequality)){
            conjectureFrequency[dalmatianBestConjectureForObject[i]]++;
        } else {
            if(verbose){
                fprintf(stderr, "Conjecture is more significant for object %d.\n", i+1);
                fprintf(stderr, "%11.6lf vs. %11.6lf\n", currentBest, values[i]);
            }
            dalmatianBestConjectureForObject[i] = objectCount;
            isMoreSignificant = TRUE;
        }
    }
    
    //check if there is at least one object for which this bound is more significant
    if(!isMoreSignificant) return;

    if(verbose){
        fprintf(stderr, "Saving expression\n");
        printExpression(tree, stderr);
    }
    
    //if we get here, then the current bound is at least for one object more significant
    //we store the values and that conjecture
    int smallestAvailablePosition = 0;
    
    while(smallestAvailablePosition < objectCount &&
            conjectureFrequency[smallestAvailablePosition]>0){
        smallestAvailablePosition++;
    }
    if(smallestAvailablePosition == objectCount){
        BAILOUT("Error when handling dalmatian heuristic")
    }
    
    for(i=smallestAvailablePosition+1; i<objectCount; i++){
        if(conjectureFrequency[i]==0){
            dalmatianConjectureInUse[i] = FALSE;
        }
    }
    
    memcpy(dalmatianCurrentConjectureValues[smallestAvailablePosition], values, 
            sizeof(double)*objectCount);
    for(i=0; i<objectCount; i++){
        if(dalmatianBestConjectureForObject[i] == objectCount){
            dalmatianBestConjectureForObject[i] = smallestAvailablePosition;
        }
    }
    copyTree(tree, dalmatianConjectures + smallestAvailablePosition);
    dalmatianConjectureInUse[smallestAvailablePosition] = TRUE;
    
    dalmatianUpdateHitCount();
    
}

boolean dalmatianHeuristicStopConditionReached(){
    return dalmatianHitCount == objectCount;
}

void dalmatianHeuristicInit_shared_pre(){
    int i;
    
    dalmatianBestConjectureForObject = (int *)malloc(sizeof(int) * objectCount);
    if(dalmatianBestConjectureForObject == NULL){
        fprintf(stderr, "Initialisation of Dalmatian heuristic failed: insufficient memory -- exiting!\n");
        exit(EXIT_FAILURE);
    }
    
    dalmatianConjectureInUse = (boolean *)malloc(sizeof(boolean) * (objectCount + 1));
    if(dalmatianConjectureInUse == NULL){
        fprintf(stderr, "Initialisation of Dalmatian heuristic failed: insufficient memory -- exiting!\n");
        exit(EXIT_FAILURE);
    }
    for(i = 0; i <= objectCount; i++){
        dalmatianConjectureInUse[i] = FALSE;
    }
    
    dalmatianConjectures = (TREE *)malloc(sizeof(TREE) * (objectCount+1));
    if(dalmatianConjectures == NULL){
        fprintf(stderr, "Initialisation of Dalmatian heuristic failed: insufficient memory -- exiting!\n");
        exit(EXIT_FAILURE);
    }
}

void dalmatianHeuristicInit_shared_post(){
    int i;
    for(i=0;i<=objectCount;i++){
        initTree(dalmatianConjectures+i);
    }
}

void dalmatianHeuristicInit(){
    int i;
    dalmatianHeuristicInit_shared_pre();
    
    dalmatianCurrentConjectureValues  = (double **)malloc(sizeof(double *) * (objectCount + 1));
    if(dalmatianCurrentConjectureValues == NULL){
        fprintf(stderr, "Initialisation of Dalmatian heuristic failed: insufficient memory -- exiting!\n");
        exit(EXIT_FAILURE);
    }
    dalmatianCurrentConjectureValues[0] = (double *)malloc(sizeof(double) * (objectCount + 1) * objectCount);
    if(dalmatianCurrentConjectureValues[0] == NULL){
        fprintf(stderr, "Initialisation of Dalmatian heuristic failed: insufficient memory -- exiting!\n");
        exit(EXIT_FAILURE);
    }
 
    for(i = 0; i <= objectCount; i++)
        dalmatianCurrentConjectureValues[i] = (*dalmatianCurrentConjectureValues + objectCount * i);
    
    dalmatianHeuristicInit_shared_post();
}

void dalmatianHeuristicInit_propertyBased(){
    int i;
    dalmatianHeuristicInit_shared_pre();

    dalmatianObjectInBoundArea = (boolean *)malloc(sizeof(boolean) * (objectCount + 1));
    if(dalmatianObjectInBoundArea == NULL){
        fprintf(stderr, "Initialisation of Dalmatian heuristic failed: insufficient memory -- exiting!\n");
        exit(EXIT_FAILURE);
    }
    for(i = 0; i <= objectCount; i++){
        dalmatianObjectInBoundArea[i] = FALSE;
    }
    
    dalmatianCurrentConjectureValues_propertyBased  = (boolean **)malloc(sizeof(double *) * (objectCount + 1));
    if(dalmatianCurrentConjectureValues_propertyBased == NULL){
        fprintf(stderr, "Initialisation of Dalmatian heuristic failed: insufficient memory -- exiting!\n");
        exit(EXIT_FAILURE);
    }
    dalmatianCurrentConjectureValues_propertyBased[0] = (boolean *)malloc(sizeof(double) * (objectCount + 1) * objectCount);
    if(dalmatianCurrentConjectureValues_propertyBased[0] == NULL){
        fprintf(stderr, "Initialisation of Dalmatian heuristic failed: insufficient memory -- exiting!\n");
        exit(EXIT_FAILURE);
    }
 
    for(i = 0; i <= objectCount; i++)
        dalmatianCurrentConjectureValues_propertyBased[i] = (*dalmatianCurrentConjectureValues_propertyBased + objectCount * i);


    dalmatianHeuristicInit_shared_post();
}

void dalmatianHeuristicPostProcessing(){
    int i;
    for(i=0;i<=objectCount;i++){
        if(dalmatianConjectureInUse[i]){
            outputExpression(dalmatianConjectures+i, stdout);
        }
        freeTree(dalmatianConjectures+i);
    }
}

inline void dalmatianUpdateHitCount_propertyBased(){
    dalmatianHitCount = 0;
    int i;
    for(i=0; i<objectCount; i++){
        if(invariantValues_propertyBased[i][mainInvariant] == UNDEFINED){
            continue;
        }
        if(dalmatianObjectInBoundArea[i]){
            dalmatianHitCount++;
        }
    }
    
}

void dalmatianHeuristic_propertyBased(TREE *tree, boolean *values){
    int i;
    //this heuristic assumes the expression was true for all objects
    
    //if known theory is provided, we check that first
    boolean isMoreSignificant = FALSE;
    if(theoryProvided){
        for(i=0; i<objectCount; i++){
            if(inequality == SUFFICIENT){
                if(invariantValues_propertyBased[i][mainInvariant] == UNDEFINED ||
                        !(invariantValues_propertyBased[i][mainInvariant])){
                    //we're only looking at object that have the main property to decide
                    //the significance.
                    continue;
                }
            } else if(inequality == NECESSARY){
                if(invariantValues_propertyBased[i][mainInvariant] == UNDEFINED ||
                        (invariantValues_propertyBased[i][mainInvariant])){
                    //we're only looking at object that do not have the main property
                    //to decide the significance.
                    continue;
                }
            } else {
                BAILOUT("Error when handling dalmatian heuristic: unknown inequality")
            }
            
            if(!handleComparator_propertyBased(knownTheory_propertyBased[i],
                values[i], inequality)){
                if(verbose){
                    fprintf(stderr, "Conjecture is more significant than known theory for object %d.\n", i+1);
                }
                isMoreSignificant = TRUE;
            }
        }

        //check if there is at least one object for which this bound is more significant than the known theory
        if(!isMoreSignificant) return;
    }
    
    //if this is the first conjecture, we just store it and return
    if(dalmatianFirst){
        if(verbose){
            fprintf(stderr, "Saving expression\n");
            printExpression_propertyBased(tree, stderr);
        }
        memcpy(dalmatianCurrentConjectureValues_propertyBased[0], values, 
                sizeof(double)*objectCount);
        for(i=0; i<objectCount; i++){
            if(values[i] == UNDEFINED){
                continue;
        }
            if(values[i]){
                dalmatianObjectInBoundArea[i] = TRUE;
            }
        }
        dalmatianConjectureInUse[0] = TRUE;
        copyTree(tree, dalmatianConjectures + 0);
        dalmatianFirst = FALSE;
        dalmatianUpdateHitCount_propertyBased();
        return;
    }
    
    //check the significance
    //----------------------
    
    //find the objects for which this bound is better
    isMoreSignificant = FALSE; //the conjecture is not necessarily more significant than the other conjectures
    for(i=0; i<objectCount; i++){
        if(inequality == SUFFICIENT){
            if(invariantValues_propertyBased[i][mainInvariant] == UNDEFINED ||
                    !(invariantValues_propertyBased[i][mainInvariant])){
                //we're only looking at object that have the main property to decide
                //the significance.
                continue;
            }
        } else if(inequality == NECESSARY){
            if(invariantValues_propertyBased[i][mainInvariant] == UNDEFINED ||
                    (invariantValues_propertyBased[i][mainInvariant])){
                //we're only looking at object that do not have the main property
                //to decide the significance.
                continue;
            }
        } else {
            BAILOUT("Error when handling dalmatian heuristic: unknown inequality")
        }
        
        if(!handleComparator_propertyBased(dalmatianObjectInBoundArea[i],
                values[i], inequality)){
            if(verbose){
                fprintf(stderr, "Conjecture is more significant for object %d.\n", i+1);
            }
            isMoreSignificant = TRUE;
        }
    }
    
    //check if there is at least one object for which this bound is more significant
    if(!isMoreSignificant) return;

    if(verbose){
        fprintf(stderr, "Saving expression\n");
        printExpression_propertyBased(tree, stderr);
    }
    
    //if we get here, then the current bound is at least for one object more significant
    //we store the values and that conjecture
    int smallestAvailablePosition = 0;
    
    while(smallestAvailablePosition <= objectCount &&
            dalmatianConjectureInUse[smallestAvailablePosition]){
        smallestAvailablePosition++;
    }
    if(smallestAvailablePosition == objectCount + 1){
        BAILOUT("Error when handling dalmatian heuristic")
    }
    
    memcpy(dalmatianCurrentConjectureValues_propertyBased[smallestAvailablePosition],
            values, sizeof(boolean)*objectCount);    
    copyTree(tree, dalmatianConjectures + smallestAvailablePosition);
    dalmatianConjectureInUse[smallestAvailablePosition] = TRUE;
    
    //update bounded area
    if(inequality == SUFFICIENT){
        for(i = 0; i < objectCount; i++){
            if(values[i] == UNDEFINED){
                continue;
            }
            dalmatianObjectInBoundArea[i] = 
                    dalmatianObjectInBoundArea[i] || values[i];
        }
    } else if(inequality == NECESSARY){
        for(i = 0; i < objectCount; i++){
            if(values[i] == UNDEFINED){
                continue;
            }
            dalmatianObjectInBoundArea[i] = 
                    dalmatianObjectInBoundArea[i] && values[i];
        }
    } else {
        BAILOUT("Error when handling dalmatian heuristic: unknown inequality")
    }
    
    dalmatianUpdateHitCount_propertyBased();
    
    //prune conjectures
    /* We just loop through the conjectures and remove the ones that are no longer
     * significant. At the moment we avoid doing anything special like looking for
     * the best set of conjectures to prune.
     * 
     * By definition, this pruning will not influence the bounding area (and the
     * hit count).
     */
    int j, k;
    
    if(inequality == SUFFICIENT){
        for(i = 0; i <= objectCount; i++){
            if(dalmatianConjectureInUse[i]){
                isMoreSignificant = FALSE;
                for(j = 0; j < objectCount; j++){
                    if(invariantValues_propertyBased[j][mainInvariant] == UNDEFINED ||
                            !(invariantValues_propertyBased[j][mainInvariant])){
                        //we're only looking at object that have the main property to decide
                        //the significance.
                        continue;
                    }
                    
                    //first we check whether the object is in the bound area
                    boolean localObjectInBoundArea = FALSE;
                    
                    for(k = 0; k <= objectCount; k++){
                        if(dalmatianConjectureInUse[k] && k!=i){
                            if(dalmatianCurrentConjectureValues_propertyBased[k][j] ==
                                    UNDEFINED){
                                continue;
                            }
                            localObjectInBoundArea =
                                    localObjectInBoundArea ||
                                    dalmatianCurrentConjectureValues_propertyBased[k][j];
                        }
                    }
                    
                    //then we check whether this conjecture is still significant
                    if(!handleComparator_propertyBased(localObjectInBoundArea,
                            dalmatianCurrentConjectureValues_propertyBased[i][j],
                            inequality)){
                        if(verbose){
                            fprintf(stderr, "Conjecture %d is more significant for object %d.\n", i+1, j+1);
                        }
                        isMoreSignificant = TRUE;
                        break;
                    }
                }
                //we only keep the conjecture if it is still more significant
                //for at least one object.
                dalmatianConjectureInUse[i] = isMoreSignificant;
            }
        }
    } else if(inequality == NECESSARY){
        for(i = 0; i <= objectCount; i++){
            if(dalmatianConjectureInUse[i]){
                isMoreSignificant = FALSE;
                for(j = 0; j < objectCount; j++){
                    if(invariantValues_propertyBased[j][mainInvariant] == UNDEFINED ||
                            (invariantValues_propertyBased[j][mainInvariant])){
                        //we're only looking at object that do not have the main property to decide
                        //the significance.
                        continue;
                    }
                    
                    //first we check whether the object is in the bound area
                    boolean localObjectInBoundArea = TRUE;
                    
                    for(k = 0; k <= objectCount; k++){
                        if(dalmatianConjectureInUse[k] && k!=i){
                            if(dalmatianCurrentConjectureValues_propertyBased[k][j] ==
                                    UNDEFINED){
                                continue;
                            }
                            localObjectInBoundArea =
                                    localObjectInBoundArea &&
                                    dalmatianCurrentConjectureValues_propertyBased[k][j];
                        }
                    }
                    
                    //then we check whether this conjecture is still significant
                    if(!handleComparator_propertyBased(localObjectInBoundArea,
                            dalmatianCurrentConjectureValues_propertyBased[i][j],
                            inequality)){
                        if(verbose){
                            fprintf(stderr, "Conjecture %d is more significant for object %d.\n", i+1, j+1);
                        }
                        isMoreSignificant = TRUE;
                        break;
                    }
                }
                //we only keep the conjecture if it is still more significant
                //for at least one object.
                dalmatianConjectureInUse[i] = isMoreSignificant;
            }
        }
    } else {
        BAILOUT("Error when handling dalmatian heuristic: unknown inequality")
    }
}
    
boolean dalmatianHeuristicStopConditionReached_propertyBased(){
    int pCount = 0; //i.e., the number of object that have the main property
    int i;
    
    for(i = 0; i < objectCount; i++){
        if(invariantValues_propertyBased[i][mainInvariant] == UNDEFINED){
            continue;
}
        if(invariantValues_propertyBased[i][mainInvariant]){
            pCount++;
        }
    }

    /* If we specified sufficient conditions, then the variable dalmatianHitCount
     * contains the number of objects in the intersection of all conditions.
     * If we specified necessary conditions, then the variable dalmatianHitCount
     * contains the number of objects in the union of all conditions.
     */
    return dalmatianHitCount == pCount;
}

void (* const dalmatianHeuristicPostProcessing_propertyBased)(void) = 
        dalmatianHeuristicPostProcessing;

//grinvin heuristic

double grinvinBestError = DBL_MAX;
TREE grinvinBestExpression;

double grinvinValueError(double *values){
    double result = 0.0;
    int i;
    
    for(i=0; i<objectCount; i++){
        double diff = values[i] - invariantValues[mainInvariant][i];
        result += (diff*diff);
    }
    return result;
}

void grinvinHeuristic(TREE *tree, double *values){
    //this heuristic assumes the expression was true for all objects
    double valueError = grinvinValueError(values);
    if(valueError < grinvinBestError){
        grinvinBestError = valueError;
        copyTree(tree, &grinvinBestExpression);
    }
}

boolean grinvinHeuristicStopConditionReached(){
    return (1 << (2*targetBinary + targetUnary)) * objectCount >= grinvinBestError;
}

void grinvinHeuristicInit(){
    initTree(&grinvinBestExpression);
}

void grinvinHeuristicPostProcessing(){
    outputExpression(&grinvinBestExpression, stdout);
    freeTree(&grinvinBestExpression);
}

//------ Stop generation -------

boolean shouldGenerationProcessBeTerminated(){
    if(heuristicStopConditionReached!=NULL){
        if(heuristicStopConditionReached()){
            heuristicStoppedGeneration = TRUE;
            return TRUE;
        }
    }
    if(timeOutReached || userInterrupted || terminationSignalReceived){
        return TRUE;
    }
    
    return FALSE;
}

void handleAlarmSignal(int sig){
    if(sig==SIGALRM){
        timeOutReached = TRUE;
    } else {
        fprintf(stderr, "Handler called with wrong signal -- ignoring!\n");
    }
}

void handleInterruptSignal(int sig){
    if(sig==SIGINT){
        userInterrupted = TRUE;
    } else {
        fprintf(stderr, "Handler called with wrong signal -- ignoring!\n");
    }
}

void handleTerminationSignal(int sig){
    if(sig==SIGTERM){
        terminationSignalReceived = TRUE;
    } else {
        fprintf(stderr, "Handler called with wrong signal -- ignoring!\n");
    }
}

//------ Expression operations -------

void outputExpressionStack(TREE *tree, FILE *f){
    int i, length;
    if(useInvariantNames){
        fprintf(f, "%s\n", invariantNames[mainInvariant]);
    } else {
        fprintf(f, "I%d\n", mainInvariant + 1);
    }
    
    //start by ordering nodes
    NODE *orderedNodes[tree->unaryCount + 2*(tree->binaryCount) + 1];
    
    length = 0;
    getOrderedNodes(tree->root, orderedNodes, &length);
    
    for(i=0; i<length; i++){
        printSingleNode(orderedNodes[i], f, 
            useInvariantNames ? invariantNamesPointers : NULL);
        fprintf(f, "\n");
    }
    printComparator(inequality, f);
    fprintf(f, "\n\n");
}

void outputExpressionStack_propertyBased(TREE *tree, FILE *f){
    int i, length;
    if(useInvariantNames){
        fprintf(f, "%s\n", invariantNames[mainInvariant]);
    } else {
        fprintf(f, "I%d\n", mainInvariant + 1);
    }
    
    //start by ordering nodes
    NODE *orderedNodes[tree->unaryCount + 2*(tree->binaryCount) + 1];
    
    length = 0;
    getOrderedNodes(tree->root, orderedNodes, &length);
    
    for(i=0; i<length; i++){
        printSingleNode_propertyBased(orderedNodes[i], f, 
            useInvariantNames ? invariantNamesPointers : NULL);
        fprintf(f, "\n");
    }
    printComparator_propertyBased(inequality, f);
    fprintf(f, "\n\n");
}

void printExpression(TREE *tree, FILE *f){
    if(useInvariantNames){
        fprintf(f, "%s ", invariantNames[mainInvariant]);
    } else {
        fprintf(f, "I%d ", mainInvariant + 1);
    }
    printComparator(inequality, f);
    fprintf(f, " ");
    printNode(tree->root, f, 
            useInvariantNames ? invariantNamesPointers : NULL);
    fprintf(f, "\n");
}

void printExpression_propertyBased(TREE *tree, FILE *f){
    if(useInvariantNames){
        fprintf(f, "%s ", invariantNames[mainInvariant]);
    } else {
        fprintf(f, "I%d ", mainInvariant + 1);
    }
    printComparator_propertyBased(inequality, f);
    fprintf(f, " ");
    printNode_propertyBased(tree->root, f, 
            useInvariantNames ? invariantNamesPointers : NULL);
    fprintf(f, "\n");
}

void outputExpression(TREE *tree, FILE *f){
    if(propertyBased){
        if(outputType=='h'){
            printExpression_propertyBased(tree, f);
        } else if(outputType=='s'){
            outputExpressionStack_propertyBased(tree, f);
        }
    } else {
        if(outputType=='h'){
            printExpression(tree, f);
        } else if(outputType=='s'){
            outputExpressionStack(tree, f);
        }
    }
}

void handleExpression(TREE *tree, double *values, int calculatedValues, int hitCount, int skipCount){
    validExpressionsCount++;
    if(printValidExpressions){
        printExpression(tree, stderr);
    }
    if(doConjecturing){
        if(selectedHeuristic==DALMATIAN_HEURISTIC){
            if(skipCount > allowedPercentageOfSkips * objectCount){
                return;
            }
            dalmatianHeuristic(tree, values);
        } else if(selectedHeuristic==GRINVIN_HEURISTIC){
            if(skipCount > allowedPercentageOfSkips * objectCount){
                return;
            }
            grinvinHeuristic(tree, values);
        }
    }
}

void handleExpression_propertyBased(TREE *tree, boolean *values, int calculatedValues, int hitCount, int skipCount){
    validExpressionsCount++;
    if(printValidExpressions){
        printExpression_propertyBased(tree, stderr);
    }
    if(doConjecturing){
        if(selectedHeuristic==DALMATIAN_HEURISTIC){
            if(skipCount > allowedPercentageOfSkips * objectCount){
                return;
            }
            dalmatianHeuristic_propertyBased(tree, values);
        } else if(selectedHeuristic==GRINVIN_HEURISTIC){
            BAILOUT("Grinvin heuristic is not defined for property-based conjectures.")
        }
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
    } else if(id==7){
        return sqrt(value);
    } else if(id==8){
        return log(value);
    } else if(id==9){
        return log10(value);
    } else if(id==10){
        return exp(value);
    } else if(id==11){
        return pow(10, value);
    } else if(id==12){
        return ceil(value);
    } else if(id==13){
        return floor(value);
    } else if(id==14){
        return fabs(value);
    } else if(id==15){
        return sin(value);
    } else if(id==16){
        return cos(value);
    } else if(id==17){
        return tan(value);
    } else if(id==18){
        return asin(value);
    } else if(id==19){
        return acos(value);
    } else if(id==20){
        return atan(value);
    } else if(id==21){
        return sinh(value);
    } else if(id==22){
        return cosh(value);
    } else if(id==23){
        return tanh(value);
    } else if(id==24){
        return asinh(value);
    } else if(id==25){
        return acosh(value);
    } else if(id==26){
        return atanh(value);
    } else {
        BAILOUT("Unknown unary operator ID")
    }
}

void writeUnaryOperatorExample(FILE *f){
    fprintf(f, "U  0    x - 1\n");
    fprintf(f, "U  1    x + 1\n");
    fprintf(f, "U  2    x * 2\n");
    fprintf(f, "U  3    x / 2\n");
    fprintf(f, "U  4    x ^ 2\n");
    fprintf(f, "U  5    -x\n");
    fprintf(f, "U  6    1 / x\n");
    fprintf(f, "U  7    sqrt(x)\n");
    fprintf(f, "U  8    ln(x)\n");
    fprintf(f, "U  9    log_10(x)\n");
    fprintf(f, "U 10    exp(x)\n");
    fprintf(f, "U 11    10 ^ x\n");
    fprintf(f, "U 12    ceil(x)\n");
    fprintf(f, "U 13    floor(x)\n");
    fprintf(f, "U 14    |x|\n");
    fprintf(f, "U 15    sin(x)\n");
    fprintf(f, "U 16    cos(x)\n");
    fprintf(f, "U 17    tan(x)\n");
    fprintf(f, "U 18    asin(x)\n");
    fprintf(f, "U 19    acos(x)\n");
    fprintf(f, "U 20    atan(x)\n");
    fprintf(f, "U 21    sinh(x)\n");
    fprintf(f, "U 22    cosh(x)\n");
    fprintf(f, "U 23    tanh(x)\n");
    fprintf(f, "U 24    asinh(x)\n");
    fprintf(f, "U 25    acosh(x)\n");
    fprintf(f, "U 26    atanh(x)\n");
}

double handleCommutativeBinaryOperator(int id, double left, double right){
    if(id==0){
        return left + right;
    } else if(id==1){
        return left*right;
    } else if(id==2){
        return left < right ? right : left;
    } else if(id==3){
        return left < right ? left : right;
    } else {
        BAILOUT("Unknown commutative binary operator ID")
    }
}

void writeCommutativeBinaryOperatorExample(FILE *f){
    fprintf(f, "C 0    x + y\n");
    fprintf(f, "C 1    x * y\n");
    fprintf(f, "C 2    max(x,y)\n");
    fprintf(f, "C 3    min(x,y)\n");
}

double handleNonCommutativeBinaryOperator(int id, double left, double right){
    if(id==0){
        return left - right;
    } else if(id==1){
        return left/right;
    } else if(id==2){
        return pow(left, right);
    } else {
        BAILOUT("Unknown non-commutative binary operator ID")
    }
}

void writeNonCommutativeBinaryOperatorExample(FILE *f){
    fprintf(f, "N 0    x - y\n");
    fprintf(f, "N 1    x / y\n");
    fprintf(f, "N 2    x ^ y\n");
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
        BAILOUT("Unknown comparator ID")
    }
}

double evaluateNode(NODE *node, int object){
    if (node->contentLabel[0]==INVARIANT_LABEL) {
        return invariantValues[object][node->contentLabel[1]];
    } else if (node->contentLabel[0]==UNARY_LABEL) {
        return handleUnaryOperator(node->contentLabel[1], evaluateNode(node->left, object));
    } else if (node->contentLabel[0]==NON_COMM_BINARY_LABEL){
        return handleNonCommutativeBinaryOperator(node->contentLabel[1],
                evaluateNode(node->left, object), evaluateNode(node->right, object));
    } else if (node->contentLabel[0]==COMM_BINARY_LABEL){
        return handleCommutativeBinaryOperator(node->contentLabel[1],
                evaluateNode(node->left, object), evaluateNode(node->right, object));
    } else {
        BAILOUT("Unknown content label type")
    }
}

boolean handleUnaryOperator_propertyBased(int id, boolean value){
    if(value==UNDEFINED){
        return UNDEFINED;
    }
    if(id==0){
        return !value;
    } else {
        BAILOUT("Unknown unary operator ID")
    }
}

void writeUnaryOperatorExample_propertyBased(FILE *f){
    fprintf(f, "U 0    !x\n");
}

boolean handleCommutativeBinaryOperator_propertyBased(int id, boolean left, boolean right){
    if(left==UNDEFINED || right==UNDEFINED){
        return UNDEFINED;
    }
    if(id==0){
        return left && right;
    } else if(id==1){
        return left || right;
    } else if(id==2){
        return (!left) != (!right); //XOR
    } else {
        BAILOUT("Unknown commutative binary operator ID")
    }
}

void writeCommutativeBinaryOperatorExample_propertyBased(FILE *f){
    fprintf(f, "C 0    x & y\n");
    fprintf(f, "C 1    x | y\n");
    fprintf(f, "C 2    x ^ y (XOR)\n");
}

boolean handleNonCommutativeBinaryOperator_propertyBased(int id, boolean left, boolean right){
    if(left==UNDEFINED || right==UNDEFINED){
        return UNDEFINED;
    }
    if(id==0){
        return (!left) || right;
    } else {
        BAILOUT("Unknown non-commutative binary operator ID")
    }
}

void writeNonCommutativeBinaryOperatorExample_propertyBased(FILE *f){
    fprintf(f, "N 0    x => y\n");
}

boolean handleComparator_propertyBased(boolean left, boolean right, int id){
    if(left==UNDEFINED || right==UNDEFINED){
        return UNDEFINED;
    }
    if(id==0){
        return (!right) || left;
    } else if(id==2){
        return (!left) || right;
    } else {
        BAILOUT("Unknown comparator ID")
    }
}

boolean evaluateNode_propertyBased(NODE *node, int object){
    if (node->contentLabel[0]==INVARIANT_LABEL) {
        return invariantValues_propertyBased[object][node->contentLabel[1]];
    } else if (node->contentLabel[0]==UNARY_LABEL) {
        return handleUnaryOperator_propertyBased(node->contentLabel[1],
                evaluateNode_propertyBased(node->left, object));
    } else if (node->contentLabel[0]==NON_COMM_BINARY_LABEL){
        return handleNonCommutativeBinaryOperator_propertyBased(node->contentLabel[1],
                evaluateNode_propertyBased(node->left, object),
                evaluateNode_propertyBased(node->right, object));
    } else if (node->contentLabel[0]==COMM_BINARY_LABEL){
        return handleCommutativeBinaryOperator_propertyBased(node->contentLabel[1],
                evaluateNode_propertyBased(node->left, object),
                evaluateNode_propertyBased(node->right, object));
    } else {
        BAILOUT("Unknown content label type")
    }
}

boolean evaluateTree(TREE *tree, double *values, int *calculatedValues, int *hits, int *skips){
    int i;
    int hitCount = 0;
    int skipCount = 0;
    for(i=0; i<objectCount; i++){
        if(isnan(invariantValues[i][mainInvariant])){
            skipCount++;
            continue; //skip NaN
        }
        double expression = evaluateNode(tree->root, i);
        values[i] = expression;
        if(isnan(expression)){
            skipCount++;
            continue; //skip NaN
        }
        if(!handleComparator(invariantValues[i][mainInvariant], expression, inequality)){
            *calculatedValues = i+1;
            *hits = hitCount;
            *skips = skipCount;
            return FALSE;
        } else if(expression==invariantValues[i][mainInvariant]) {
            hitCount++;
        }
    }
    *hits = hitCount;
    *skips = skipCount;
    *calculatedValues = objectCount;
    if(skipCount == objectCount){
        return FALSE;
    }
    return TRUE;
}

boolean evaluateTree_propertyBased(TREE *tree, boolean *values, int *calculatedValues, int *hits, int *skips){
    int i;
    int hitCount = 0;
    int skipCount = 0;
    for(i=0; i<objectCount; i++){
        if(invariantValues_propertyBased[i][mainInvariant]==UNDEFINED){
            skipCount++;
            continue; //skip undefined values
        }
        boolean expression = evaluateNode_propertyBased(tree->root, i);
        values[i] = expression;
        if(expression == UNDEFINED){
            skipCount++;
            continue; //skip NaN
        }
        if(!handleComparator_propertyBased(invariantValues_propertyBased[i][mainInvariant], expression, inequality)){
            *calculatedValues = i+1;
            *hits = hitCount;
            *skips = skipCount;
            return FALSE;
        } else if(!(expression) == !(invariantValues_propertyBased[i][mainInvariant])) {
            hitCount++;
        }
    }
    *hits = hitCount;
    *skips = skipCount;
    *calculatedValues = objectCount;
    if(skipCount == objectCount){
        return FALSE;
    }
    return TRUE;
}

void checkExpression(TREE *tree){
    double values[objectCount];
    int calculatedValues = 0;
    int hitCount = 0;
    int skipCount = 0;
    if (evaluateTree(tree, values, &calculatedValues, &hitCount, &skipCount)){
        handleExpression(tree, values, objectCount, hitCount, skipCount);
    }
}

void checkExpression_propertyBased(TREE *tree){
    boolean values[objectCount];
    int calculatedValues = 0;
    int hitCount = 0;
    int skipCount = 0;
    if (evaluateTree_propertyBased(tree, values, &calculatedValues, &hitCount, &skipCount)){
        handleExpression_propertyBased(tree, values, objectCount, hitCount, skipCount);
    }
}

//------ Labeled tree generation -------

void handleLabeledTree(TREE *tree){
    labeledTreeCount++;
    if(generateExpressions || doConjecturing){
        if(propertyBased){
            checkExpression_propertyBased(tree);
        } else {
            checkExpression(tree);
        }
    }
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
                if(shouldGenerationProcessBeTerminated()){
                    return;
                }
            }
        } else if (currentNode->type == 1){
            currentNode->contentLabel[0] = UNARY_LABEL;
            for (i=0; i<unaryOperatorCount; i++){
                currentNode->contentLabel[1] = unaryOperators[i];
                generateLabeledTree(tree, orderedNodes, pos+1);
                if(shouldGenerationProcessBeTerminated()){
                    return;
                }
            }
        } else { // currentNode->type == 2
            //first try non-commutative binary operators
            currentNode->contentLabel[0] = NON_COMM_BINARY_LABEL;
            for (i=0; i<nonCommBinaryOperatorCount; i++){
                currentNode->contentLabel[1] = nonCommBinaryOperators[i];
                generateLabeledTree(tree, orderedNodes, pos+1);
                if(shouldGenerationProcessBeTerminated()){
                    return;
                }
            }
            
            //then try commutative binary operators
            if (leftSideBiggest(currentNode, orderedNodes)){
                currentNode->contentLabel[0] = COMM_BINARY_LABEL;
                for (i=0; i<commBinaryOperatorCount; i++){
                    currentNode->contentLabel[1] = commBinaryOperators[i];
                    generateLabeledTree(tree, orderedNodes, pos+1);
                    if(shouldGenerationProcessBeTerminated()){
                        return;
                    }
                }
            }
        }
    }
}

//------ Unlabeled tree generation -------

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
    
    if(!allowMainInvariantInExpressions){
        invariantsUsed[mainInvariant] = TRUE;
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
        if(shouldGenerationProcessBeTerminated()){
            return;
        }
    }
    
    for(i=0; i<tree->levelWidth[tree->depth]; i++){
        NODE *parent = tree->nodesAtDepth[tree->depth][i];
        addChildToNodeInTree(tree, parent);
        generateTreeImpl(tree);
        removeChildFromNodeInTree(tree, parent);
        if(shouldGenerationProcessBeTerminated()){
            return;
        }
    }
}

void generateTree(int unary, int binary){
    if(verbose){
        fprintf(stderr, "Generating trees with %d unary node%s and %d binary node%s.\n",
                unary, unary == 1 ? "" : "s", binary, binary == 1 ? "" : "s");
    }
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
    
    if(verbose && doConjecturing){
        fprintf(stderr, "Status: %lu unlabeled tree%s, %lu labeled tree%s, %lu expression%s\n",
                treeCount, treeCount==1 ? "" : "s",
                labeledTreeCount, labeledTreeCount==1 ? "" : "s",
                validExpressionsCount, validExpressionsCount==1 ? "" : "s");
    }
}

//------ conjecturing functions -------

void getNextOperatorCount(int *unary, int *binary){
    if(nextOperatorCountMethod == GRINVIN_NEXT_OPERATOR_COUNT){
        if((*binary)==0){
            if((*unary)%2==0){
                (*binary) = (*unary)/2;
                (*unary) = 1;
            } else {
                (*binary) = (*unary + 1)/2;
                (*unary) = 0;
            }
        } else {
            (*binary)--;
            (*unary)+=2;
        }
    } else {
        BAILOUT("Unknown method to determine next operator count")
    }
}

void conjecture(int startUnary, int startBinary){
    int unary = startUnary;
    int binary = startBinary;
    int availableInvariants = invariantCount - (allowMainInvariantInExpressions ? 0 : 1);
    
    generateTree(unary, binary);
    getNextOperatorCount(&unary, &binary);
    while(!shouldGenerationProcessBeTerminated()) {
        if(unary <= MAX_UNARY_COUNT && 
           binary <= MAX_BINARY_COUNT &&
           availableInvariants >= binary+1)
            generateTree(unary, binary);
        getNextOperatorCount(&unary, &binary);
    }
}

//------ Various functions -------

void readOperators(){
    //set operator counts to zero
    unaryOperatorCount = commBinaryOperatorCount = nonCommBinaryOperatorCount = 0;
    
    //read the operators from the file
    int i;
    int operatorCount = 0;
    char line[1024]; //array to temporarily store a line
    if(fgets(line, sizeof(line), operatorFile)){
        if(sscanf(line, "%d", &operatorCount) != 1) {
            BAILOUT("Error while reading operators")
        }
    } else {
        BAILOUT("Error while reading operators")
    }
    for(i=0; i<operatorCount; i++){
        if(fgets(line, sizeof(line), operatorFile)){
            //read operator
            char operatorType = 'E'; //E for Error
            int operatorNumber = -1;
            if(sscanf(line, "%c %d", &operatorType, &operatorNumber) != 2) {
                BAILOUT("Error while reading operators")
            }
            //process operator
            if(operatorType=='U'){
                unaryOperators[unaryOperatorCount++] = operatorNumber;
            } else if(operatorType=='C'){
                commBinaryOperators[commBinaryOperatorCount++] = operatorNumber;
            } else if(operatorType=='N'){
                nonCommBinaryOperators[nonCommBinaryOperatorCount++] = operatorNumber;
            } else {
                fprintf(stderr, "Unknown operator type '%c' -- exiting!\n", operatorType);
                exit(EXIT_FAILURE);
            }
        } else {
            BAILOUT("Error while reading operators")
        }
    }
}

char *trim(char *str){
    //http://stackoverflow.com/questions/122616/how-do-i-trim-leading-trailing-whitespace-in-a-standard-way
    char *end;
    
    // Trim leading space
    while(isspace(*str)) str++;

    if(*str == 0)  // All spaces?
        return str;

    // Trim trailing space
    end = str + strlen(str) - 1;
    while(end > str && isspace(*end)) end--;

    // Write new null terminator
    *(end+1) = 0;

    return str;
}

void allocateMemory_onlyLabeled(){
    if(invariantCount <= 0){
        fprintf(stderr, "Illegal value for invariant count: %d -- exiting!\n", invariantCount);
        exit(EXIT_FAILURE);
    }
    
    invariantsUsed = (boolean *)malloc(sizeof(boolean) * invariantCount);
    if(invariantsUsed == NULL){
        fprintf(stderr, "Initialisation failed: insufficient memory -- exiting!\n");
        exit(EXIT_FAILURE);
    }    
}

void allocateMemory_shared(){
    int i;
    if(invariantCount <= 0){
        fprintf(stderr, "Illegal value for invariant count: %d -- exiting!\n", invariantCount);
        exit(EXIT_FAILURE);
    }
    if(objectCount <= 0){
        fprintf(stderr, "Illegal value for object count: %d -- exiting!\n", objectCount);
        exit(EXIT_FAILURE);
    }
    
    invariantsUsed = (boolean *)malloc(sizeof(boolean) * invariantCount);
    if(invariantsUsed == NULL){
        fprintf(stderr, "Initialisation failed: insufficient memory -- exiting!\n");
        exit(EXIT_FAILURE);
    }
    
    invariantNames = (char **)malloc(sizeof(char *) * invariantCount);
    if(invariantNames == NULL){
        fprintf(stderr, "Initialisation failed: insufficient memory -- exiting!\n");
        exit(EXIT_FAILURE);
    }
    invariantNames[0] = (char *)malloc(sizeof(char) * invariantCount * 1024);
    if(invariantNames[0] == NULL){
        fprintf(stderr, "Initialisation failed: insufficient memory -- exiting!\n");
        exit(EXIT_FAILURE);
    }
    for(i = 0; i < invariantCount; i++){
        invariantNames[i] = (*invariantNames + 1024 * i);
    }
    
    invariantNamesPointers = (char **)malloc(sizeof(char *) * invariantCount);
    if(invariantNamesPointers == NULL){
        fprintf(stderr, "Initialisation failed: insufficient memory -- exiting!\n");
        exit(EXIT_FAILURE);
    }
    
}

void allocateMemory_invariantBased(){
    int i;
    
    allocateMemory_shared();

    invariantValues = (double **)malloc(sizeof(double *) * objectCount);
    if(invariantValues == NULL){
        fprintf(stderr, "Initialisation failed: insufficient memory -- exiting!\n");
        exit(EXIT_FAILURE);
    }
    invariantValues[0] = (double *)malloc(sizeof(double) * objectCount * invariantCount);
    if(invariantValues[0] == NULL){
        fprintf(stderr, "Initialisation failed: insufficient memory -- exiting!\n");
        exit(EXIT_FAILURE);
    }
    for(i = 0; i < objectCount; i++){
        invariantValues[i] = (*invariantValues + invariantCount * i);
    }
    
    knownTheory = (double *)malloc(sizeof(double) * objectCount);
    if(knownTheory == NULL){
        fprintf(stderr, "Initialisation failed: insufficient memory -- exiting!\n");
        exit(EXIT_FAILURE);
    }
            
}

void allocateMemory_propertyBased(){
    int i;
    
    allocateMemory_shared();

    invariantValues_propertyBased = (boolean **)malloc(sizeof(boolean *) * objectCount);
    if(invariantValues_propertyBased == NULL){
        fprintf(stderr, "Initialisation failed: insufficient memory -- exiting!\n");
        exit(EXIT_FAILURE);
    }
    invariantValues_propertyBased[0] = (boolean *)malloc(sizeof(boolean) * objectCount * invariantCount);
    if(invariantValues_propertyBased[0] == NULL){
        fprintf(stderr, "Initialisation failed: insufficient memory -- exiting!\n");
        exit(EXIT_FAILURE);
    }
    for(i = 0; i < objectCount; i++){
        invariantValues_propertyBased[i] = (*invariantValues_propertyBased + invariantCount * i);
    }
    
    knownTheory_propertyBased = (boolean *)malloc(sizeof(boolean) * objectCount);
    if(knownTheory_propertyBased == NULL){
        fprintf(stderr, "Initialisation failed: insufficient memory -- exiting!\n");
        exit(EXIT_FAILURE);
    }

}

void readInvariantsValues(){
    int i,j;
    char line[1024]; //array to temporarily store a line
    
    //first read number of invariants and number of entities
    if(fgets(line, sizeof(line), invariantsFile)){
        if(sscanf(line, "%d %d %d", &objectCount, &invariantCount, &mainInvariant) != 3) {
            BAILOUT("Error while reading invariants")
        }
        mainInvariant--; //internally we work zero-based
    } else {
        BAILOUT("Error while reading invariants")
    }
    
    allocateMemory_invariantBased();
    
    //maybe read invariant names
    if(useInvariantNames){
        for(j=0; j<invariantCount; j++){
            if(fgets(line, sizeof(line), invariantsFile)){
                char *name = trim(line);
                strcpy(invariantNames[j], name);
                invariantNamesPointers[j] = invariantNames[j];
            } else {
                BAILOUT("Error while reading invariant names")
            }
        }
    }
    
    if(theoryProvided){
        //first read the known theory
        for(i=0; i<objectCount; i++){
            if(fgets(line, sizeof(line), invariantsFile)){
                double value = 0.0;
                if(sscanf(line, "%lf", &value) != 1) {
                    BAILOUT("Error while reading known theory")
                }
                knownTheory[i] = value;
            } else {
                BAILOUT("Error while reading known theory")
            }
        }
    }
    
    //start reading the individual values
    for(i=0; i<objectCount; i++){
        for(j=0; j<invariantCount; j++){
            if(fgets(line, sizeof(line), invariantsFile)){
                double value = 0.0;
                if(sscanf(line, "%lf", &value) != 1) {
                    BAILOUT("Error while reading invariants")
                }
                invariantValues[i][j] = value;
            } else {
                BAILOUT("Error while reading invariants")
            }
        }
    }
}

void readInvariantsValues_propertyBased(){
    int i,j;
    char line[1024]; //array to temporarily store a line
    
    //first read number of invariants and number of entities
    if(fgets(line, sizeof(line), invariantsFile)){
        if(sscanf(line, "%d %d %d", &objectCount, &invariantCount, &mainInvariant) != 3) {
            BAILOUT("Error while reading invariants")
        }
        mainInvariant--; //internally we work zero-based
    } else {
        BAILOUT("Error while reading invariants")
    }
    
    allocateMemory_propertyBased();
    
    //maybe read invariant names
    if(useInvariantNames){
        for(j=0; j<invariantCount; j++){
            if(fgets(line, sizeof(line), invariantsFile)){
                char *name = trim(line);
                strcpy(invariantNames[j], name);
                invariantNamesPointers[j] = invariantNames[j];
            } else {
                BAILOUT("Error while reading invariant names")
            }
        }
    }
    
    if(theoryProvided){
        //first read the known theory
        for(i=0; i<objectCount; i++){
            if(fgets(line, sizeof(line), invariantsFile)){
                boolean value = UNDEFINED;
                if(sscanf(line, "%d", &value) != 1) {
                    BAILOUT("Error while reading known theory")
                }
                if(value == UNDEFINED ||
                        value == FALSE ||
                        value == TRUE){
                    knownTheory_propertyBased[i] = value;
                } else {
                    BAILOUT("Error while reading known theory")
                }
            } else {
                BAILOUT("Error while reading known theory")
            }
        }
    }
    
    //start reading the individual values
    for(i=0; i<objectCount; i++){
        for(j=0; j<invariantCount; j++){
            if(fgets(line, sizeof(line), invariantsFile)){
                boolean value = UNDEFINED;
                if(sscanf(line, "%d", &value) != 1) {
                    BAILOUT("Error while reading invariants")
                }
                if(value == UNDEFINED ||
                        value == FALSE ||
                        value == TRUE){
                    invariantValues_propertyBased[i][j] = value;
                } else {
                    BAILOUT("Error while reading invariants")
                }
            } else {
                BAILOUT("Error while reading invariants")
            }
        }
    }
}

boolean checkKnownTheory(){
    if(!theoryProvided) return TRUE;
    int i;
    int hitCount = 0;
    for(i=0; i<objectCount; i++){
        if(isnan(invariantValues[i][mainInvariant])){
            continue; //skip NaN
        }
        if(isnan(knownTheory[i])){
            continue; //skip NaN
        }
        if(!handleComparator(invariantValues[i][mainInvariant], knownTheory[i], inequality)){
            return FALSE;
        } else if(invariantValues[i][mainInvariant] == knownTheory[i]){
            hitCount++;
        }
    }
    if(hitCount==objectCount){
        fprintf(stderr, "Warning: can not improve on known theory using these objects.\n");
    }
    return TRUE;
}

boolean checkKnownTheory_propertyBased(){
    if(!theoryProvided) return TRUE;
    int i;
    int hitCount = 0;
    for(i=0; i<objectCount; i++){
        if(invariantValues_propertyBased[i][mainInvariant]==UNDEFINED){
            continue; //skip undefined values
        }
        if(knownTheory_propertyBased[i] == UNDEFINED){
            continue; //skip NaN
        }
        if(!handleComparator_propertyBased(
                invariantValues_propertyBased[i][mainInvariant],
                knownTheory_propertyBased[i], inequality)){
            return FALSE;
        } else if(!(knownTheory_propertyBased[i]) ==
                !(invariantValues_propertyBased[i][mainInvariant])) {
            hitCount++;
        }
    }
    if(hitCount==objectCount){
        fprintf(stderr, "Warning: can not improve on known theory using these objects.\n");
    }
    return TRUE;
}

void printInvariantValues(FILE *f){
    int i, j;
    //header row
    fprintf(f, "     ");
    if(theoryProvided){
        fprintf(f, "Known theory  ");
    }
    for(j=0; j<invariantCount; j++){
        fprintf(f, "Invariant %2d  ", j+1);
    }
    fprintf(f, "\n");
    //table
    for(i=0; i<objectCount; i++){
        fprintf(f, "%3d) ", i+1);
        if(theoryProvided){
            fprintf(f, "%11.6lf   ", knownTheory[i]);
        }
        for(j=0; j<invariantCount; j++){
            fprintf(f, "%11.6lf   ", invariantValues[i][j]);
        }
        fprintf(f, "\n");
    }
}

void printInvariantValues_propertyBased(FILE *f){
    int i, j;
    //header row
    fprintf(f, "     ");
    if(theoryProvided){
        fprintf(f, "Known theory  ");
    }
    for(j=0; j<invariantCount; j++){
        fprintf(f, "Invariant %2d  ", j+1);
    }
    fprintf(f, "\n");
    //table
    for(i=0; i<objectCount; i++){
        fprintf(f, "%3d) ", i+1);
        if(theoryProvided){
            if(knownTheory_propertyBased[i] == UNDEFINED){
                fprintf(f, " UNDEFINED    ");
            } else if(knownTheory_propertyBased[i]){
                fprintf(f, "   TRUE       ");
            } else {
                fprintf(f, "   FALSE      ");
            }
        }
        for(j=0; j<invariantCount; j++){
            if(invariantValues_propertyBased[i][j] == UNDEFINED){
                fprintf(f, " UNDEFINED    ");
            } else if(invariantValues_propertyBased[i][j]){
                fprintf(f, "   TRUE       ");
            } else {
                fprintf(f, "   FALSE      ");
            }
        }
        fprintf(f, "\n");
    }
}

//===================================================================
// Usage methods
//===================================================================
void help(char *name){
    fprintf(stderr, "The program %s constructs expressions based on provided parameters.\n\n", name);
    fprintf(stderr, "\e[1mUsage\n=====\e[21m\n");
    fprintf(stderr, " %s [options] -u unary binary\n", name);
    fprintf(stderr, "       Generates expression trees with the given number of unary and\n");
    fprintf(stderr, "       binary operators.\n");
    fprintf(stderr, " %s [options] -l unary binary invariants\n", name);
    fprintf(stderr, "       Generates labeled expression trees with the given number of unary\n");
    fprintf(stderr, "       and binary operators and the given number of invariants.\n");
    fprintf(stderr, " %s [options] -e unary binary\n", name);
    fprintf(stderr, "       Generates valid expressions with the given number of unary and\n");
    fprintf(stderr, "       binary operators.\n");
    fprintf(stderr, " %s [options] -c [unary binary]\n", name);
    fprintf(stderr, "       Use heuristics to make conjectures.\n");
    fprintf(stderr, "\n\n");
    fprintf(stderr, "\e[1mValid options\n=============\e[21m\n");
    fprintf(stderr, "\e[1m* Generated types\e[21m (exactly one of these four should be used)\n");
    fprintf(stderr, "    -u, --unlabeled\n");
    fprintf(stderr, "       Generate unlabeled expression trees.\n");
    fprintf(stderr, "    -l, --labeled\n");
    fprintf(stderr, "       Generate labeled expression trees.\n");
    fprintf(stderr, "    -e, --expressions\n");
    fprintf(stderr, "       Generate true expressions.\n");
    fprintf(stderr, "    -c, --conjecture\n");
    fprintf(stderr, "       Use heuristics to make conjectures.\n");
    fprintf(stderr, "\n");
    fprintf(stderr, "\e[1m* Parameters\e[21m\n");
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
    fprintf(stderr, "    --allow-main-invariant\n");
    fprintf(stderr, "       Allow the main invariant to appear in the generated expressions.\n");
    fprintf(stderr, "    --all-operators\n");
    fprintf(stderr, "       Use all the available operators. This flag will only be used when\n");
    fprintf(stderr, "       generating expressions or when in conjecturing mode. The result is\n");
    fprintf(stderr, "       that no operators are read from the input.\n");
    fprintf(stderr, "    -t, --theory\n");
    fprintf(stderr, "       Known theory will be supplied. When using this flag, you need to\n");
    fprintf(stderr, "       give the best known value for each object: after specifying the\n");
    fprintf(stderr, "       number objects, invariants and the main invariant (and possibly\n");
    fprintf(stderr, "       the invariant names), and before specifying the invariant values.\n");
    fprintf(stderr, "       It is verified whether this known theory is indeed consistent with\n");
    fprintf(stderr, "       the selected main invariant.\n");
    fprintf(stderr, "    --leq\n");
    fprintf(stderr, "       Use the comparator <= when constructing conjectures. The conjectures will\n");
    fprintf(stderr, "       be of the form 'main invariant <= f(invariants)'. This is the default\n");
    fprintf(stderr, "       comparator.\n");
    fprintf(stderr, "    --less\n");
    fprintf(stderr, "       Use the comparator < when constructing conjectures. The conjectures will\n");
    fprintf(stderr, "       be of the form 'main invariant < f(invariants)'.\n");
    fprintf(stderr, "    --geq\n");
    fprintf(stderr, "       Use the comparator >= when constructing conjectures. The conjectures will\n");
    fprintf(stderr, "       be of the form 'main invariant >= f(invariants)'.\n");
    fprintf(stderr, "    --greater\n");
    fprintf(stderr, "       Use the comparator > when constructing conjectures. The conjectures will\n");
    fprintf(stderr, "       be of the form 'main invariant > f(invariants)'.\n");
    fprintf(stderr, "    -p, --property\n");
    fprintf(stderr, "       Make property based conjecture instead of the default invariant based\n");
    fprintf(stderr, "       conjectures.\n");
    fprintf(stderr, "    --sufficient\n");
    fprintf(stderr, "       Create sufficient conditions when constructing property based\n");
    fprintf(stderr, "       conjectures. The conjectures will be of the form 'main property <- \n");
    fprintf(stderr, "       f(properties)'. This is the default for property based conjectures.\n");
    fprintf(stderr, "    --necessary\n");
    fprintf(stderr, "       Create necessary conditions when constructing property based conjectures.\n");
    fprintf(stderr, "       The conjectures will be of the form 'main property -> f(properties)'.\n");
    fprintf(stderr, "\n");
    fprintf(stderr, "\e[1m* Heuristics\e[21m\n");
    fprintf(stderr, "    --dalmatian\n");
    fprintf(stderr, "       Use the dalmatian heuristic to make conjectures.\n");
    fprintf(stderr, "    --grinvin\n");
    fprintf(stderr, "       Use the heuristic from Grinvin to make conjectures.\n");
    fprintf(stderr, "\n");
    fprintf(stderr, "\e[1m* Various options\e[21m\n");
    fprintf(stderr, "    -h, --help\n");
    fprintf(stderr, "       Print this help and return.\n");
    fprintf(stderr, "    -v, --verbose\n");
    fprintf(stderr, "       Make the program more verbose.\n");
    fprintf(stderr, "    --example\n");
    fprintf(stderr, "       Print an example of an input file for the operators. It is advised to\n");
    fprintf(stderr, "       use this example as a starting point for your own file.\n");
    fprintf(stderr, "    --limits name\n");
    fprintf(stderr, "       Print the limit for the given name to stdout. Possible names are: all,\n");
    fprintf(stderr, "       MAX_OBJECT_COUNT, MAX_INVARIANT_COUNT.\n");
    fprintf(stderr, "    --time t\n");
    fprintf(stderr, "       Stops the generation after t seconds. Zero seconds means that the\n");
    fprintf(stderr, "       generation won't be stopped. The default is 0.\n");
    fprintf(stderr, "    --operators filename\n");
    fprintf(stderr, "       Specifies the file containing the operators to be used. Defaults to\n");
    fprintf(stderr, "       stdin.\n");
    fprintf(stderr, "    --invariants filename\n");
    fprintf(stderr, "       Specifies the file containing the invariant values. Defaults to stdin.\n");
    fprintf(stderr, "    --print-valid-expressions\n");
    fprintf(stderr, "       Causes all valid expressions that are found to be printed to stderr.\n");
    fprintf(stderr, "\n\n");
    fprintf(stderr, "\e[1mInput format\n============\e[21m\n");
    fprintf(stderr, "The operators that should be used and the invariant values are read from an in-\n");
    fprintf(stderr, "put file. By default these are both read from stdin. In this case the operators\n");
    fprintf(stderr, "are read first and then the invariants. If the option \e[4m--all-operators\e[24m is speci-\n");
    fprintf(stderr, "fied then reading the operators is skipped and all operators are used.\n");
    fprintf(stderr, "We will now describe the format of these input files. A general rule is that\n");
    fprintf(stderr, "the maximum length of each line is 1024 characters and after each input you can\n");
    fprintf(stderr, "add comments (respecting the 1024 character limit).\n\n");
    fprintf(stderr, "\e[1m* Operators\e[21m\n");
    fprintf(stderr, "   The first line gives the number of operators that will follow. After that\n");
    fprintf(stderr, "   line each line starts with a character followed by whitespace followed by\n");
    fprintf(stderr, "   a number.\n");
    fprintf(stderr, "   The character is one of:\n");
    fprintf(stderr, "     - U: unary operator\n");
    fprintf(stderr, "     - C: commutative binary operator\n");
    fprintf(stderr, "     - U: non-commutative binary operator\n");
    fprintf(stderr, "   The number specifies which operator is meant. An overview of the operators\n");
    fprintf(stderr, "   can be obtained by running the program with the option \e[4m--example\e[24m. This out-\n");
    fprintf(stderr, "   puts an exemplary input file which selects all operators.\n\n");
    fprintf(stderr, "\e[1m* Invariants\e[21m\n");
    fprintf(stderr, "   The first line contains the number of objects, the number of invariants and\n");
    fprintf(stderr, "   the number of the main invariant seperated by spaces. In case you are using\n");
    fprintf(stderr, "   the option \e[4m--invariant-names\e[24m you first have to specify the invariant names.\n");
    fprintf(stderr, "   Each invariant name is written on a single line without any comments. The\n");
    fprintf(stderr, "   whole line is used as the invariant name (white spaces at the beginning and\n");
    fprintf(stderr, "   end of the line are removed). After that the invariant values follow. One\n");
    fprintf(stderr, "   invariant value per line in this order: 1st value of 1st object, 2nd value of\n");
    fprintf(stderr, "   1st object,..., 1st value of 2nd object,...\n");
    fprintf(stderr, "   We give an example from graph theory to illustrate the input of invariant\n");
    fprintf(stderr, "   values. We have 4 invariants: number of vertices, number of edges, maximum\n");
    fprintf(stderr, "   and minimum degree. We have 3 objects: C3, C5 and K5. So we have these\n");
    fprintf(stderr, "   invariant values:\n");
    fprintf(stderr, "   \n");
    fprintf(stderr, "            #vertices   #edges   max. degree   min. degree\n");
    fprintf(stderr, "      C3        3          3         2              2\n");
    fprintf(stderr, "      C5        5          5         2              2\n");
    fprintf(stderr, "      K5        5         10         4              4\n");
    fprintf(stderr, "   \n");
    fprintf(stderr, "   If you want to find upper bounds for the number of edges, then the invariant\n");
    fprintf(stderr, "   values input file would like like this:\n");
    fprintf(stderr, "   \e[2m\n");
    fprintf(stderr, "   3 4 2\n");
    fprintf(stderr, "   Number of vertices\n");
    fprintf(stderr, "   Number of edges\n");
    fprintf(stderr, "   Maximum degree\n");
    fprintf(stderr, "   Minimum degree\n");
    fprintf(stderr, "   3\n   3\n   2\n   2\n");
    fprintf(stderr, "   5\n   5\n   2\n   2\n");
    fprintf(stderr, "   5\n   10\n   4\n   4\n");
    fprintf(stderr, "   \e[22m\n");
    fprintf(stderr, "   The example above assumes you are using the option \e[4m--invariant-names\e[24m. If this\n");
    fprintf(stderr, "   is not the case, then you can skip the second until fifth line.\n");
    fprintf(stderr, "\n\n");
    fprintf(stderr, "\e[1mHeuristics\n==========\e[21m\n");
    fprintf(stderr, "This program allows the heuristic used to select bounds to be altered. Currently\n");
    fprintf(stderr, "there are two heuristics implemented. We will give a brief description of each\n");
    fprintf(stderr, "of the heuristics.\n");
    fprintf(stderr, "\e[1m* Dalmatian\e[21m\n");
    fprintf(stderr, "   The Dalmatian heuristic, developed by Siemion Fajtlowicz, is used in Graffiti\n");
    fprintf(stderr, "   and Graffiti.pc. It selects bounds based on truth and significance.\n");
    fprintf(stderr, "   A bound is accepted if it is true for all objects in the considered database\n");
    fprintf(stderr, "   and if it is tighter than all the other bounds for at least one object in the\n");
    fprintf(stderr, "   considered database. This implies that there are at most as many bounds as\n");
    fprintf(stderr, "   there are objects in the considered database.\n");
    fprintf(stderr, "\e[1m* Grinvin\e[21m\n");
    fprintf(stderr, "   This is the heuristic that is used by default in Grinvin. It selects bounds\n");
    fprintf(stderr, "   based on truth and relative complexity.\n");
    fprintf(stderr, "   A bound is accepted if it is true for all objects in the considered database\n");
    fprintf(stderr, "   and if it has the smallest value error. The value error is defined as the sum\n");
    fprintf(stderr, "   of the squares of the differences between the values and the bounds for all\n");
    fprintf(stderr, "   objects in the database. This heuristic keeps generating expressions while\n");
    fprintf(stderr, "   the product of the number of objects in the considered database and two to\n");
    fprintf(stderr, "   the power number of unary plus twice the number of binary operators is less\n");
    fprintf(stderr, "   than the best value error up to that point.\n");
    fprintf(stderr, "\n\n");
    fprintf(stderr, "Please mail  \e[4mnico [DOT] vancleemput [AT] gmail [DOT] com\e[24m in case of trouble.\n");
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
        {"example", no_argument, NULL, 0},
        {"time", required_argument, NULL, 0},
        {"allow-main-invariant", no_argument, NULL, 0},
        {"all-operators", no_argument, NULL, 0},
        {"dalmatian", no_argument, NULL, 0},
        {"grinvin", no_argument, NULL, 0},
        {"invariant-names", no_argument, NULL, 0},
        {"operators", required_argument, NULL, 0},
        {"invariants", required_argument, NULL, 0},
        {"leq", no_argument, NULL, 0},
        {"less", no_argument, NULL, 0},
        {"geq", no_argument, NULL, 0},
        {"greater", no_argument, NULL, 0},
        {"limits", required_argument, NULL, 0},
        {"allowed-skips", required_argument, NULL, 0},
        {"print-valid-expressions", no_argument, NULL, 0},
        {"sufficient", no_argument, NULL, 0},
        {"necessary", no_argument, NULL, 0},
        {"help", no_argument, NULL, 'h'},
        {"verbose", no_argument, NULL, 'v'},
        {"unlabeled", no_argument, NULL, 'u'},
        {"labeled", no_argument, NULL, 'l'},
        {"expressions", no_argument, NULL, 'e'},
        {"conjecture", no_argument, NULL, 'c'},
        {"output", required_argument, NULL, 'o'},
        {"property", no_argument, NULL, 'p'},
        {"theory", no_argument, NULL, 't'}
    };
    int option_index = 0;

    while ((c = getopt_long(argc, argv, "hvuleco:pt", long_options, &option_index)) != -1) {
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
                    case 3:
                        writeUnaryOperatorExample(stdout);
                        writeCommutativeBinaryOperatorExample(stdout);
                        writeNonCommutativeBinaryOperatorExample(stdout);
                        return EXIT_SUCCESS;
                        break;
                    case 4:
                        timeOut = strtoul(optarg, NULL, 10);
                        break;
                    case 5:
                        allowMainInvariantInExpressions = TRUE;
                        break;
                    case 6:
                        operatorFile = NULL;
                        closeOperatorFile = FALSE;
                        break;
                    case 7:
                        selectedHeuristic = DALMATIAN_HEURISTIC;
                        if(propertyBased){
                            heuristicInit = dalmatianHeuristicInit_propertyBased;
                            heuristicStopConditionReached = dalmatianHeuristicStopConditionReached_propertyBased;
                            heuristicPostProcessing = dalmatianHeuristicPostProcessing_propertyBased;
                        } else {
                            heuristicInit = dalmatianHeuristicInit;
                            heuristicStopConditionReached = dalmatianHeuristicStopConditionReached;
                            heuristicPostProcessing = dalmatianHeuristicPostProcessing;
                        }
                        break;
                    case 8:
                        selectedHeuristic = GRINVIN_HEURISTIC;
                        heuristicInit = grinvinHeuristicInit;
                        heuristicStopConditionReached = grinvinHeuristicStopConditionReached;
                        heuristicPostProcessing = grinvinHeuristicPostProcessing;
                        break;
                    case 9:
                        useInvariantNames = TRUE;
                        break;
                    case 10:
                        operatorFile = fopen(optarg, "r");
                        closeOperatorFile = TRUE;
                        break;
                    case 11:
                        invariantsFile = fopen(optarg, "r");
                        closeInvariantsFile = TRUE;
                        break;
                    case 12:
                        inequality = LEQ;
                        break;
                    case 13:
                        inequality = LESS;
                        break;
                    case 14:
                        inequality = GEQ;
                        break;
                    case 15:
                        inequality = GREATER;
                        break;
                    case 16:
                        fprintf(stderr, "Limits are no longer supported.\n");
                        return EXIT_SUCCESS;
                        break;
                    case 17:
                        allowedPercentageOfSkips = strtof(optarg, NULL);
                        break;
                    case 18:
                        printValidExpressions = TRUE;
                        break;
                    case 19:
                        inequality = SUFFICIENT;
                        break;
                    case 20:
                        inequality = NECESSARY;
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
            case 'e':
                generateExpressions = TRUE;
                break;
            case 'c':
                doConjecturing = TRUE;
                break;
            case 'o':
                switch(optarg[0]) {
                    case 's':
                    case 'h':
                        outputType = optarg[0];
                        break;
                    default:
                        fprintf(stderr, "Illegal output type %s.\n", optarg);
                        usage(name);
                        return EXIT_FAILURE;
                }
                break;
            case 'p':
                propertyBased = TRUE;
                //heuristic needs to be chosen after switching to property based conjecturing
                selectedHeuristic = NO_HEURISTIC;
                unaryOperatorCount = 1;
                /*
                 * 1: not
                 */
                commBinaryOperatorCount = 3;
                /*
                 * 1: and
                 * 2: or
                 * 3: xor
                 */
                nonCommBinaryOperatorCount = 1;
                /* 
                 * 1: implication
                 */
                break;
            case 't':
                theoryProvided = TRUE;
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
    
    if(onlyLabeled + onlyUnlabeled +
            generateExpressions + doConjecturing != TRUE){
        fprintf(stderr, "Please select one type to be generated.\n");
        usage(name);
        return EXIT_FAILURE;
    }
    
    if(doConjecturing && selectedHeuristic==NO_HEURISTIC){
        fprintf(stderr, "Please select a heuristic to make conjectures.\n");
        usage(name);
        return EXIT_FAILURE;
    }
    
    // check the non-option arguments
    if ((onlyUnlabeled || generateExpressions) && argc - optind != 2) {
        usage(name);
        return EXIT_FAILURE;
    }
    
    if (onlyLabeled && argc - optind != 3) {
        usage(name);
        return EXIT_FAILURE;
    }
    
    if (doConjecturing && !((argc == optind) || (argc - optind == 2))) {
        usage(name);
        return EXIT_FAILURE;
    }
    
    // check comparator for property-based conjectures
    if (propertyBased && 
            !((inequality == SUFFICIENT) || (inequality == NECESSARY))){
        fprintf(stderr, "For property-based conjectures you can only use --sufficient or --necessary.\n");
        usage(name);
        return EXIT_FAILURE;
    }
    
    
    return -1;
}

int main(int argc, char *argv[]) {
    
    operatorFile = stdin;
    invariantsFile = stdin;
    
    int po = processOptions(argc, argv);
    if(po != -1) return po;
    
    int unary = 0;
    int binary = 0;
    if(!doConjecturing){
        unary = strtol(argv[optind], NULL, 10);
        binary = strtol(argv[optind+1], NULL, 10);
        if(onlyLabeled) {
            invariantCount = strtol(argv[optind+2], NULL, 10);
        }
    } else if(argc - optind == 2) {
        unary = strtol(argv[optind], NULL, 10);
        binary = strtol(argv[optind+1], NULL, 10);
    }

    //set the operator labels
    if(onlyLabeled) {
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
        allocateMemory_onlyLabeled();
    } else if (!onlyUnlabeled){
        if(operatorFile==NULL){
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
        } else {
            readOperators();
        }
        if(propertyBased){
            readInvariantsValues_propertyBased();
            if(verbose) printInvariantValues_propertyBased(stderr);
            if(!checkKnownTheory_propertyBased()){
                BAILOUT("Known theory is not consistent with main invariant")
            }
        } else {
            readInvariantsValues();
            if(verbose) printInvariantValues(stderr);
            if(!checkKnownTheory()){
                BAILOUT("Known theory is not consistent with main invariant")
            }
        }
    }
    
    if(closeOperatorFile){
        fclose(operatorFile);
    }
    if(closeInvariantsFile){
        fclose(invariantsFile);
    }
    
    //do heuristic initialisation
    if(heuristicInit!=NULL){
        heuristicInit();
    }
    
    //register handlers for signals
    signal(SIGALRM, handleAlarmSignal);
    signal(SIGINT, handleInterruptSignal);
    signal(SIGTERM, handleTerminationSignal);
    
    //if timeOut is non-zero: start alarm
    if(timeOut) alarm(timeOut);
    
    //start actual generation process
    if(doConjecturing){
        conjecture(unary, binary);
    } else {
        generateTree(unary, binary);
    }
    
    //give information about the reason why the program halted
    if(heuristicStoppedGeneration){
        fprintf(stderr, "Generation process was stopped by the conjecturing heuristic.\n");
    } else if(timeOutReached){
        fprintf(stderr, "Generation process was stopped because the maximum time was reached.\n");
    } else if(userInterrupted){
        fprintf(stderr, "Generation process was interrupted by user.\n");
    } else if(terminationSignalReceived){
        fprintf(stderr, "Generation process was killed.\n");
    }
    
    //print some statistics
    if(onlyUnlabeled){
        fprintf(stderr, "Found %lu unlabeled trees.\n", treeCount);
    } else if(onlyLabeled) {
        fprintf(stderr, "Found %lu unlabeled trees.\n", treeCount);
        fprintf(stderr, "Found %lu labeled trees.\n", labeledTreeCount);
    } else if(generateExpressions || doConjecturing) {
        fprintf(stderr, "Found %lu unlabeled trees.\n", treeCount);
        fprintf(stderr, "Found %lu labeled trees.\n", labeledTreeCount);
        fprintf(stderr, "Found %lu valid expressions.\n", validExpressionsCount);
    }
    
    //do some heuristic-specific post-processing like outputting the conjectures
    if(heuristicPostProcessing!=NULL){
        heuristicPostProcessing();
    }
    
    return 0;
}
