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
#include <time.h>
#include <limits.h>
//#include <malloc.h>

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

int invariantCount = 0;
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

unsigned long int complexity = 0;
boolean report_maximum_complexity_reached = FALSE;

unsigned long int timeOut = 0;
boolean timeOutReached = FALSE;

boolean userInterrupted = FALSE;
boolean terminationSignalReceived = FALSE;

boolean heuristicStoppedGeneration = FALSE;
unsigned long int complexity_limit = (INT_MAX) ;
boolean complexity_limit_reached = FALSE;

boolean onlyUnlabeled = FALSE;
boolean onlyLabeled = FALSE;
boolean generateExpressions = FALSE;
boolean generateAllExpressions = FALSE;
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
#define SAM_HEURISTIC 2
#define RL_HEURISTIC  3 

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

void dalmatianHeuristic(TREE *tree, double *values, int skipCount){
    int i;
    //this heuristic assumes the expression was true for all objects
    if(skipCount > allowedPercentageOfSkips * objectCount){
      return;
    }
    
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
        if(handleComparator(currentBest, values[i], inequality+1)){
            conjectureFrequency[dalmatianBestConjectureForObject[i]]++;
        } else if (handleComparator(values[i], currentBest, inequality+1) ) {
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
            conjectureFrequency[smallestAvailablePosition]>0){  // checking whether an expression is dropped
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

void dalmatianHeuristic_propertyBased(TREE *tree, boolean *values, int skipCount){
    int i;
    //this heuristic assumes the expression was true for all objects
    if(skipCount > allowedPercentageOfSkips * objectCount){
      return;
    }
    
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

/* ===================== SAM heuristic (dynamic top-k, alpha, beta, lambda) ===================== */

typedef struct samConjecture {
    TREE   *tree;     // deep copy we own
    double  score;    // lower is better
    boolean in_use;   // slot actually populated
} samConjecture;

/* Globals with defaults (you can wire CLI options later) */
static int    sam_top_k  = 10;      /* --sam-top-k <int> */
static double sam_alpha = 1;    /* --sam-alpha <double> */
static double sam_lambda = 0.2;    /* --sam-lambda <double> */
static double sam_beta   = 0.05;   /* --sam-beta <double> */

static samConjecture *samConjectures = NULL;
static int samUsed = 0;

static void samFreeEntry(samConjecture *e){
    if (e->in_use && e->tree){
        freeTree(e->tree);
        free(e->tree);
    }
    e->tree = NULL;
    e->in_use = FALSE;
    e->score = 0.0;
}

static int compareSamConjectures(const void *a, const void *b) {
    const samConjecture *pa = (const samConjecture*)a;
    const samConjecture *pb = (const samConjecture*)b;

    // push unused to the end
    if (!pa->in_use && !pb->in_use) return 0;
    if (!pa->in_use) return 1;
    if (!pb->in_use) return -1;

    // ascending by score (best first)
    if (pa->score < pb->score) return -1;
    if (pa->score > pb->score) return  1;
    return 0;
}

static inline double samViolation(double actual, double pred, int ineq) {
    // non-negative hinge violations based on comparator
    switch (ineq) {
        case LEQ:      /* actual <= pred  */ return fmax(actual - pred, 0.0);
        case LESS:     /* actual <  pred  */ return fmax(actual - pred, 0.0);
        case GEQ:      /* actual >= pred  */ return fmax(pred   - actual, 0.0);
        case GREATER:  /* actual >  pred  */ return fmax(pred   - actual, 0.0);
        default: return 0.0;
    }
}

static void samInsertCandidate(TREE *tree, double score){
    // deep copy the tree we’re keeping
    TREE *cpy = (TREE*)malloc(sizeof(TREE));
    if (!cpy){ fprintf(stderr, "Out of memory\n"); exit(EXIT_FAILURE); }
    initTree(cpy);
    copyTree(tree, cpy);

    samConjecture cand = { cpy, score, TRUE };

    if (samUsed < sam_top_k) {
        samConjectures[samUsed++] = cand;
        qsort(samConjectures, samUsed, sizeof(samConjectures[0]), compareSamConjectures);
        return;
    }

    // full: replace worst if better
    qsort(samConjectures, sam_top_k, sizeof(samConjectures[0]), compareSamConjectures);
    if (cand.score < samConjectures[sam_top_k-1].score) {
        samFreeEntry(&samConjectures[sam_top_k-1]);
        samConjectures[sam_top_k-1] = cand;
        qsort(samConjectures, sam_top_k, sizeof(samConjectures[0]), compareSamConjectures);
    } else {
        freeTree(cand.tree);
        free(cand.tree);
    }
}

static void samHeuristicInit(void){
    // allocate dynamic buffer
    if (sam_top_k <= 0) sam_top_k = 1;
    samConjectures = (samConjecture*)calloc((size_t)sam_top_k, sizeof(samConjecture));
    if (!samConjectures){ fprintf(stderr, "Out of memory\n"); exit(EXIT_FAILURE); }

    // initialize entries
    for (int i = 0; i < sam_top_k; ++i) {
        samConjectures[i].tree = NULL;
        samConjectures[i].in_use = FALSE;
        samConjectures[i].score = 0.0;
    }
    samUsed = 0;
}

static void samHeuristicPostProcessing(void){
    if (!samConjectures){
        fprintf(stderr, "SAM: no buffer.\n");
        return;
    }

    int stored = (samUsed < sam_top_k) ? samUsed : sam_top_k;
    if (stored == 0) {
        fprintf(stderr, "SAM: no conjectures collected.\n");
    } else {
        qsort(samConjectures, stored, sizeof(samConjectures[0]), compareSamConjectures);

        if (verbose) fprintf(stderr, "SAM top-%d (lower is better):\n", stored);

        for (int i = 0, rank = 1; i < stored; ++i) {
            if (!samConjectures[i].in_use || !samConjectures[i].tree || !samConjectures[i].tree->root) continue;

            if (verbose) {
                fprintf(stderr, "[%2d] score = %.6f :: ", rank++, samConjectures[i].score);
                printExpression(samConjectures[i].tree, stderr);
            }
            // Output the conjecture to STDOUT
            outputExpression(samConjectures[i].tree, stdout);
        }
    }

    // free all slots and the array
    for (int i = 0; i < sam_top_k; ++i) samFreeEntry(&samConjectures[i]);
    free(samConjectures);
    samConjectures = NULL;
    samUsed = 0;
}

/* Core scoring: call this from handleExpression when selectedHeuristic==SAM_HEURISTIC */
void samHeuristic(TREE *tree, double *values, int skipCount){
    if (skipCount > allowedPercentageOfSkips * objectCount) return;

    double sumViol = 0.0;         // average hinge violation (primary)
    double sumTight = 0.0;        // average tightness among non-violators (secondary)
    int n_eff = 0;                // # usable objects
    int n_feasible = 0;           // # non-violating objects

    for (int i = 0; i < objectCount; ++i) {
        double actual = invariantValues[i][mainInvariant];
        double pred   = values[i];
        if (isnan(actual) || isnan(pred)) continue;

        double v = samViolation(actual, pred, inequality);
        sumViol += v;
        n_eff++;

        // Only measure tightness when the inequality is satisfied
        if (v == 0.0) {
            double tight;
            if (inequality == LEQ || inequality == LESS) {
                // want actual ≤ pred; smaller (pred - actual) is tighter
                tight = fmax(pred - actual, 0.0);
            } else { // GEQ or GREATER
                // want actual ≥ pred; smaller (actual - pred) is tighter
                tight = fmax(actual - pred, 0.0);
            }
            sumTight += tight;   // could use tight^2 if desired
            n_feasible++;
        }
    }
    if (n_eff == 0) return;

    double avgViolation = sumViol / (double)n_eff;
    double avgTightness = (n_feasible ? sumTight / (double)n_feasible : 0.0);

    double complexityPenalty = (double)(targetUnary + 2 * targetBinary);
    
    double V = avgViolation; // (1.0 + avgViolation)
    double T = avgTightness; // (1.0 + avgTightness)
   // double Cmax = (double)complexity_limit;              // known constant
    double C = complexityPenalty; // (Cmax + 1e-12)    // in [0,1]
    //if (C > 1.0) C = 1.0                              // safety clamp

    double score = sam_alpha * V + sam_beta * T + sam_lambda * C;
    
    /* Reject non-finite scores (NaN or Inf) */
    if (!isfinite(score)) {
        return;
    }
    samInsertCandidate(tree, score);
}

/* ===================== SAM heuristic (ends) ===================== */

/* ========================================================================== */
/* Reinforcement Learning (REINFORCE) Heuristic                               */
/* Episodic training: θ persists, pool resets each episode                     */
/* CSV logging: rl_learning_curve.csv                                          */
/* Print ONLY when SWAP occurs (not append)                                    */
/* Suggestion: add a small KEEP penalty when KEEP does not produce a SWAP      */
/* ========================================================================== */

static int RL_EPISODES = 4;   /* default */

#ifndef RL_MAX_TOP_K
#define RL_MAX_TOP_K 10000
#endif

#ifndef RL_FEAT_DIM
#define RL_FEAT_DIM 8   /* [1, v, t, c, sim, aV, aC, fill] */
#endif

#ifndef RL_MAX_STEPS
#define RL_MAX_STEPS 50000  /* reservoir sample size */
#endif

#ifndef RL_ONE_SHOT
#define RL_ONE_SHOT 0
#endif

/* --- Suggested keep-penalty (discourages useless KEEP actions) ----------- */
/* Your swap rewards are typically ~1e-5..3e-4, so 1e-4 is a good default. */
#ifndef RL_KEEP_COST
#define RL_KEEP_COST 1e-4
#endif

/*------------ Tunables -----------------------------------------------------*/
static double rl_alpha_viol     = 1.0;
static double rl_beta_tight     = 0.2;
static double rl_lambda_comp    = 0.05;
static double rl_rho_redund     = 0.05;
static double rl_lr             = 0.05;
static double rl_gamma          = 0.95;
static double rl_baseline_alpha = 0.05;
static int    rl_top_k          = 10;
static unsigned rl_seed         = 0;
static int rl_debug __attribute__((unused)) = 0;
char rl_sim_name[256];

/* logging controls */
static int rl_log_every = 5000;          /* heartbeat every N candidates (0=off) */
static unsigned long rl_seen = 0;
static unsigned long rl_kept = 0;
static unsigned long rl_swaps = 0;       /* SWAPS only (not appends) */
static int rl_theta_initialized = 0;

/* episode state */
static int rl_episode = 1;              /* current episode index (1..RL_EPISODES) */
static FILE *rl_curve_fp = NULL;

/* reward tracking (episode) */
static double rl_reward_sum = 0.0;
static unsigned long rl_reward_n = 0;

/* --- Target-based normalization (advisor fix) --------------------------- */
static double rl_y_min = NAN;
static double rl_y_max = NAN;
static double rl_eps   = 1e-12;

static void rlComputeTargetMinMax(void){
    double mn = INFINITY, mx = -INFINITY;
    int cnt = 0;
    for (int i = 0; i < objectCount; ++i) {
        double y = invariantValues[i][mainInvariant];
        if (!isfinite(y)) continue;
        if (y < mn) mn = y;
        if (y > mx) mx = y;
        cnt++;
    }
    if (cnt == 0) { rl_y_min = 0.0; rl_y_max = 1.0; return; }
    rl_y_min = mn; rl_y_max = mx;
    if (!isfinite(rl_y_min) || !isfinite(rl_y_max) || rl_y_min == rl_y_max) {
        rl_y_min = 0.0; rl_y_max = 1.0;
    }
}

/* --------------------------- Data structures ----------------------------- */
typedef struct {
    double avgViol;
    double avgTight;
    double complexity;
} rlCandMetrics;

typedef struct {
    TREE  *tree;
    rlCandMetrics m;
    unsigned char *invBits;
    int in_use;
} rlPoolEntry;

/* Policy θ and features ϕ */
static double rl_theta[RL_FEAT_DIM];
static double rlPhi[RL_FEAT_DIM];

/* Experience buffer (reservoir sample) */
#if !RL_ONE_SHOT
typedef struct { double phi[RL_FEAT_DIM]; int a; double p; double r; } rlStep;
static rlStep rlBuffer[RL_MAX_STEPS];
static int    rlBufSize = 0;
static unsigned long rlStepsSeen = 0;
static double rlBaseline = 0.0;
static int    rlBaselineInit = 0;
#endif

/* Pool */
static rlPoolEntry rlPool[RL_MAX_TOP_K];
static int rlPoolCount = 0;

/* ------------------------------- Utils ---------------------------------- */

/* Returns nonzero if x is finite (i.e., not NaN or ±Inf). */
static inline int is_finite(double x){
    return isfinite(x);
}

/* Clamps x to the closed interval [lo, hi]. */
static inline double clamp(double x, double lo, double hi){
    return x < lo ? lo : (x > hi ? hi : x);
}

/* Numerically stable sigmoid function with input clipping. */
static inline double rlSigmoidSafe(double z){
    if (!isfinite(z)) return 0.5;
    z = clamp(z, -30.0, 30.0);
    return 1.0/(1.0+exp(-z));
}

/* Returns a uniform random number in [0,1]. */
static inline double rlRand01(void){
    return (double)rand()/(double)RAND_MAX;
}

/* Computes the dot product of two length-n vectors. */
static inline double rlDot(const double *a, const double *b, int n){
    double s = 0.0;
    for(int i=0;i<n;i++) s += a[i]*b[i];
    return s;
}

/* Frees memory associated with a pool entry and resets its state. */
static void rlFreeExpr(rlPoolEntry *e){
    if (e->tree){
        freeTree(e->tree);
        free(e->tree);
        e->tree = NULL;
    }
    if (e->invBits){
        free(e->invBits);
        e->invBits = NULL;
    }
    e->in_use = 0;
}

/* Computes violation magnitude for a predicted bound under the given inequality. */
static inline double rlViolation(double actual, double pred, int ineq){
    switch(ineq){
        case LEQ:
        case LESS:
            return fmax(actual - pred, 0.0);
        case GEQ:
        case GREATER:
            return fmax(pred - actual, 0.0);
        default:
            return 0.0;
    }
}

/* -------------------------- Invariant bit utilities -------------------------- */

/* Recursively marks invariants used in a tree by setting corresponding bits. */
static void rlMarkInvsRec(NODE *node, unsigned char *bits){
    if (!node) return;

    if (node->contentLabel[0] == INVARIANT_LABEL) {
        int idx = node->contentLabel[1];
        if (0 <= idx && idx < invariantCount)
            bits[idx] = 1;
    }

    rlMarkInvsRec(node->left, bits);
    rlMarkInvsRec(node->right, bits);
}

/* Builds the invariant bitset representation for a tree. */
static void rlBuildInvBitsForTree(TREE *tree, unsigned char *bits){
    memset(bits, 0, (size_t)invariantCount);
    rlMarkInvsRec(tree->root, bits);
}

/* Computes the Jaccard similarity between two invariant bitsets. */
static double rlJaccard(const unsigned char *a, const unsigned char *b){
    int inter = 0, uni = 0;

    for(int i=0;i<invariantCount;i++){
        int aa = a[i] != 0;
        int bb = b[i] != 0;
        inter += (aa && bb);
        uni   += (aa || bb);
    }

    return (uni == 0) ? 0.0 : ((double)inter / (double)uni);
}

/* -------------------------- Metrics & Aggregates ------------------------ */
static rlCandMetrics rlComputeCandMetrics(double *values){
    rlCandMetrics m;
    m.avgViol  = 0.0;
    m.avgTight = 0.0;
    m.complexity = (double)(targetUnary + 2*targetBinary);

    int n_eff  = 0;
    int n_feas = 0;

    const double VCAP = 1e6;
    const double NCAP = 10.0;

    for (int i = 0; i < objectCount; i++) {
        double a = invariantValues[i][mainInvariant];
        double p = values[i];
        if (!is_finite(a) || !is_finite(p)) continue;

        double v_raw = rlViolation(a, p, inequality);
        if (!is_finite(v_raw)) continue;
        if (v_raw > VCAP) v_raw = VCAP;

        double tight_raw = 0.0;
        if (v_raw == 0.0) {
            tight_raw = (inequality==LEQ || inequality==LESS) ? fmax(p - a, 0.0)
                                                             : fmax(a - p, 0.0);
            if (!is_finite(tight_raw)) tight_raw = 0.0;
            if (tight_raw > VCAP) tight_raw = VCAP;
        }

        double v_base = 0.0, t_base = 0.0;
        if (inequality==LEQ || inequality==LESS) {
            v_base = fmax(a - rl_y_min, 0.0);
            t_base = fmax(rl_y_max - a, 0.0);
        } else {
            v_base = fmax(rl_y_max - a, 0.0);
            t_base = fmax(a - rl_y_min, 0.0);
        }

        double v_norm;
        if (v_base <= rl_eps) v_norm = (v_raw <= rl_eps) ? 0.0 : 1.0;
        else v_norm = v_raw / (v_base + rl_eps);
        v_norm = isfinite(v_norm) ? clamp(v_norm, 0.0, NCAP) : 0.0;

        m.avgViol += v_norm;
        n_eff++;

        if (v_raw == 0.0) {
            double t_norm;
            if (t_base <= rl_eps) t_norm = 0.0;
            else t_norm = tight_raw / (t_base + rl_eps);
            t_norm = isfinite(t_norm) ? clamp(t_norm, 0.0, NCAP) : 0.0;

            m.avgTight += t_norm;
            n_feas++;
        }
    }

    if (n_eff == 0) {
        m.avgViol = NAN; m.avgTight = NAN;
    } else {
        m.avgViol /= (double)n_eff;
        if (n_feas > 0) m.avgTight /= (double)n_feas;
        else m.avgTight = NCAP;
    }
    return m;
}

static void rlPoolAggregates(double *aV, double *aT, double *aC, double *aR){
    if (rlPoolCount==0){ *aV=0.0; *aT=0.0; *aC=0.0; *aR=0.0; return; }
    double sV=0.0, sT=0.0, sC=0.0, sR=0.0; int pairs=0;

    for(int i=0;i<rlPoolCount;i++){
        if (!rlPool[i].in_use) continue;
        if (is_finite(rlPool[i].m.avgViol))    sV += rlPool[i].m.avgViol;
        if (is_finite(rlPool[i].m.avgTight))   sT += rlPool[i].m.avgTight;
        if (is_finite(rlPool[i].m.complexity)) sC += rlPool[i].m.complexity;
        for(int j=i+1;j<rlPoolCount;j++){
            if (!rlPool[j].in_use) continue;
            double r = rlJaccard(rlPool[i].invBits, rlPool[j].invBits);
            if (is_finite(r)){ sR += r; pairs++; }
        }
    }
    int n = rlPoolCount;
    *aV = (n>0)? sV/(double)n : 0.0;
    *aT = (n>0)? sT/(double)n : 0.0;
    *aC = (n>0)? sC/(double)n : 0.0;
    *aR = (pairs>0)? sR/(double)pairs : 0.0;
}

static double rlPoolScore(void){
    double aV,aT,aC,aR; rlPoolAggregates(&aV,&aT,&aC,&aR);
    if (!isfinite(aV)) aV = 0.0;
    if (!isfinite(aT)) aT = 0.0;
    if (!isfinite(aC)) aC = 0.0;
    if (!isfinite(aR)) aR = 0.0;
    double sc = rl_alpha_viol * aV + rl_beta_tight * aT + rl_lambda_comp * aC + rl_rho_redund * aR;
    return isfinite(sc) ? sc : 1e12;
}

/* -------------------------- Pool insert / swap --------------------------- */
static TREE *rlCopyTree(TREE *src){
    TREE *t = (TREE*)malloc(sizeof(TREE));
    if (!t){ fprintf(stderr,"Out of memory\n"); exit(EXIT_FAILURE); }
    initTree(t); copyTree(src, t);
    return t;
}

typedef enum { RL_NOCHANGE=0, RL_APPEND=1, RL_SWAP=2 } rlChangeType;

/* RETURN RL_APPEND, RL_SWAP, or RL_NOCHANGE */
static rlChangeType rlInsertKeep(TREE *tree, const rlCandMetrics *m, const unsigned char *bits){
    rlPoolEntry e; memset(&e,0,sizeof(e));
    e.tree = rlCopyTree(tree);
    e.m    = *m;
    e.invBits = (unsigned char*)malloc((size_t)invariantCount);
    if(!e.invBits){ fprintf(stderr,"Out of memory\n"); exit(EXIT_FAILURE); }
    memcpy(e.invBits, bits, (size_t)invariantCount);
    e.in_use = 1;

    /* append while not full */
    if (rlPoolCount < rl_top_k){
        if (rlPoolCount < RL_MAX_TOP_K) {
            rlPool[rlPoolCount++] = e;
            return RL_APPEND;
        } else {
            rlFreeExpr(&e);
            return RL_NOCHANGE;
        }
    }

    /* pool full => best swap */
    double bestScore = INFINITY;
    int bestIdx = -1;
    double current = rlPoolScore();

    for(int i=0;i<rl_top_k;i++){
        rlPoolEntry saved = rlPool[i];
        rlPool[i] = e;
        double sc = rlPoolScore();
        rlPool[i] = saved;
        if (is_finite(sc) && sc < bestScore){ bestScore=sc; bestIdx=i; }
    }

    if (bestScore < current && bestIdx >= 0){
        rlFreeExpr(&rlPool[bestIdx]);
        rlPool[bestIdx] = e;
        return RL_SWAP;
    } else {
        rlFreeExpr(&e);
        return RL_NOCHANGE;
    }
}

/* ----------------------------- Features --------------------------------- */
static void rlBuildPhi(const rlCandMetrics *m, const unsigned char *candBits){
    double aV,aT,aC,aR; rlPoolAggregates(&aV,&aT,&aC,&aR);

    double sim = 0.0; int cnt=0;
    for(int i=0;i<rlPoolCount;i++){
        if (!rlPool[i].in_use) continue;
        double s = rlJaccard(candBits, rlPool[i].invBits);
        if (is_finite(s)){ sim += s; cnt++; }
    }
    sim = (cnt>0)? sim/(double)cnt : 0.0;

    double fillFrac = (rl_top_k>0)? ((double)rlPoolCount/(double)rl_top_k) : 0.0;

    double v = is_finite(m->avgViol)    ? m->avgViol    : 0.0;
    double t = is_finite(m->avgTight)   ? m->avgTight   : 0.0;
    double c = is_finite(m->complexity) ? m->complexity : 0.0;
    aV = is_finite(aV)? aV:0.0; aC = is_finite(aC)? aC:0.0;
    sim = is_finite(sim)? sim:0.0; fillFrac = is_finite(fillFrac)? fillFrac:0.0;

    int k=0;
    rlPhi[k++] = 1.0;
    rlPhi[k++] = v;
    rlPhi[k++] = t;
    rlPhi[k++] = c;
    rlPhi[k++] = sim;
    rlPhi[k++] = aV;
    rlPhi[k++] = aC;
    rlPhi[k++] = fillFrac;
}

/* ------------------- Reservoir store ------------------------------------- */
#if !RL_ONE_SHOT
static void rlReservoirStoreStep(const double *phi, int a, double p, double r){
    rlStepsSeen++;

    if (rlBufSize < RL_MAX_STEPS) {
        for (int j=0;j<RL_FEAT_DIM;j++) rlBuffer[rlBufSize].phi[j] = phi[j];
        rlBuffer[rlBufSize].a = a;
        rlBuffer[rlBufSize].p = p;
        rlBuffer[rlBufSize].r = r;
        rlBufSize++;
        return;
    }

    unsigned long j = (unsigned long)(rand() % (int)rlStepsSeen);
    if (j < (unsigned long)RL_MAX_STEPS) {
        int idx = (int)j;
        for (int d=0; d<RL_FEAT_DIM; d++) rlBuffer[idx].phi[d] = phi[d];
        rlBuffer[idx].a = a;
        rlBuffer[idx].p = p;
        rlBuffer[idx].r = r;
    }
}
#endif

/* ------------------- CSV logging ---------------------------------------- */
static void rlCurveOpenIfNeeded(void){
    if (rl_curve_fp) return;
    rl_curve_fp = fopen("rl_learning_curve.csv", "w");
    if (!rl_curve_fp) return;
    fprintf(rl_curve_fp, "episode,final_score,seen,kept,swaps,avg_reward\n");
    fflush(rl_curve_fp);
}
static void rlCurveAppend(int ep, double finalScore){
    rlCurveOpenIfNeeded();
    if (!rl_curve_fp) return;
    double avgR = (rl_reward_n > 0) ? (rl_reward_sum / (double)rl_reward_n) : 0.0;
    fprintf(rl_curve_fp, "%d,%.12g,%lu,%lu,%lu,%.12g\n",
            ep, finalScore, rl_seen, rl_kept, rl_swaps, avgR);
    fflush(rl_curve_fp);
}

/* ------------------- Heuristic entry points / lifecycle ----------------- */
static void rlHeuristicInit(void){
    if (!isfinite(rl_y_min) || !isfinite(rl_y_max)) rlComputeTargetMinMax();

    rl_seen = 0; rl_kept = 0; rl_swaps = 0;
    rl_reward_sum = 0.0; rl_reward_n = 0;

#if !RL_ONE_SHOT
    rlBufSize = 0;
    rlStepsSeen = 0;
    rlBaseline = 0.0;
    rlBaselineInit = 0;
#endif

    static int seeded = 0;
    if (!seeded) {
        if (rl_seed != 0) srand(rl_seed);
        else srand((unsigned int)time(NULL));
        seeded = 1;
    }

    if (!rl_theta_initialized) {
        for (int j=0;j<RL_FEAT_DIM;j++)
            rl_theta[j] = 0.01 * ((rand()/(double)RAND_MAX) - 0.5);
        rl_theta_initialized = 1;
    }

    rlPoolCount = 0;
    for (int i=0; i<RL_MAX_TOP_K; ++i) {
        rlPool[i].tree = NULL;
        rlPool[i].invBits = NULL;
        rlPool[i].in_use = 0;
    }

    fprintf(stderr, "\n[RL] === Episode %d / %d ===\n", rl_episode, RL_EPISODES);
}

void rlHeuristic(TREE *tree, double *values, int skipCount){
#if RL_ONE_SHOT
    (void)tree; (void)values; (void)skipCount;
    return;
#else
    if (skipCount > allowedPercentageOfSkips * objectCount) return;

    rlCandMetrics m = rlComputeCandMetrics(values);
    if (!is_finite(m.avgViol)) return;

    unsigned char *candBits = (unsigned char*)malloc((size_t)invariantCount);
    if (!candBits){ fprintf(stderr,"Out of memory\n"); exit(EXIT_FAILURE); }
    rlBuildInvBitsForTree(tree, candBits);

    rlBuildPhi(&m, candBits);

    double z = rlDot(rl_theta, rlPhi, RL_FEAT_DIM);
    double p = rlSigmoidSafe(z);

    int a = (rlRand01() < p) ? 1 : 0;

    double before = rlPoolScore();
    rlChangeType change = RL_NOCHANGE;

    if (a == 1) {
        rl_kept++;
        change = rlInsertKeep(tree, &m, candBits);
        if (change == RL_SWAP) rl_swaps++;
    }

    double after = rlPoolScore();

    const double RCLIP = 10.0;
    double reward = clamp(before - after, -RCLIP, RCLIP);
    if (!isfinite(reward)) reward = 0.0;

    /* --- Suggested change: penalize useless KEEP (KEEP but no swap) ------- */
    /* This makes the policy learn to reserve KEEP for candidates that improve
       the pool (especially once the pool is full). */
    if (a == 1 && change != RL_SWAP) {
        reward -= RL_KEEP_COST;
    }

    rl_reward_sum += reward;
    rl_reward_n++;

    rlReservoirStoreStep(rlPhi, a, p, reward);

    rl_seen++;

    if (change == RL_SWAP) {
        fprintf(stderr,
                "[RL-SWAP] ep=%d seen=%lu swaps=%lu score: %.9f -> %.9f r=%.3e p=%.3f z=%.3f "
                "cand(v=%.6g t=%.6g c=%.6g)\n",
                rl_episode, rl_seen, rl_swaps, before, after, reward, p, z,
                m.avgViol, m.avgTight, m.complexity);
    }

    if (rl_log_every > 0 && (rl_seen % (unsigned long)rl_log_every) == 0) {
        fprintf(stderr,
                "[RL] ep=%d seen=%lu kept=%lu swaps=%lu pool=%d/%d score=%.6g\n",
                rl_episode, rl_seen, rl_kept, rl_swaps, rlPoolCount, rl_top_k, rlPoolScore());
    }

    free(candBits);
#endif
}

#if !RL_ONE_SHOT
static void rlEndEpisodeUpdate(void){
    if (rlBufSize==0) {
        fprintf(stderr, "[RL] update skipped: empty reservoir\n");
        return;
    }

    double G[RL_MAX_STEPS];
    double running = 0.0;
    for(int t=rlBufSize-1; t>=0; --t){
        double rt = rlBuffer[t].r; if (!isfinite(rt)) rt = 0.0;
        running = rt + rl_gamma*running; if (!isfinite(running)) running = 0.0;
        G[t] = running;
    }

    if (!rlBaselineInit){
        double avg=0.0; int c=0;
        for(int t=0;t<rlBufSize;t++){ if (isfinite(G[t])){ avg+=G[t]; c++; } }
        rlBaseline = (c>0)? avg/(double)c : 0.0;
        rlBaselineInit = 1;
    }

    const double GRAD_CLIP = 1e3;
    for(int t=0; t<rlBufSize; t++){
        double adv = G[t] - rlBaseline; if (!isfinite(adv)) adv = 0.0;
        double coeff = (double)(rlBuffer[t].a) - rlBuffer[t].p; if (!isfinite(coeff)) coeff = 0.0;

        for(int j=0;j<RL_FEAT_DIM;j++){
            double g = rl_lr * adv * coeff * rlBuffer[t].phi[j];
            if (!isfinite(g)) g = 0.0;
            g = clamp(g, -GRAD_CLIP, GRAD_CLIP);
            rl_theta[j] += g;
            if (!isfinite(rl_theta[j])) rl_theta[j] = 0.0;
        }

        rlBaseline = (1.0-rl_baseline_alpha)*rlBaseline + rl_baseline_alpha*G[t];
        if (!isfinite(rlBaseline)) rlBaseline = 0.0;
    }

    fprintf(stderr, "[RL] policy updated (reservoir=%d stepsSeen=%lu)\n", rlBufSize, rlStepsSeen);

    rlBufSize = 0;
    rlStepsSeen = 0;
}

static int rlCmpIdxByScore(const void *a, const void *b){
    int ia = *(const int*)a;
    int ib = *(const int*)b;

    int ua = rlPool[ia].in_use;
    int ub = rlPool[ib].in_use;

    if (ua && !ub) return -1;
    if (!ua && ub) return 1;
    if (!ua && !ub) return 0;

    double sa = rlPool[ia].m.avgViol;
    double sb = rlPool[ib].m.avgViol;

    if (sa < sb) return -1;
    if (sa > sb) return 1;
    return 0;
}

static void rlHeuristicPostProcessing(void){
    rlEndEpisodeUpdate();

    double finalScore = rlPoolScore();

    /* append CSV row for plot */
    rlCurveAppend(rl_episode, finalScore);

    fprintf(stderr, "[RL] Episode %d done: final_score=%.6f seen=%lu kept=%lu swaps=%lu\n",
            rl_episode, finalScore, rl_seen, rl_kept, rl_swaps);

    /* print conjectures to stdout (same as before) */
    int should_print_pool = (rl_episode == RL_EPISODES);  /* only last episode */
    if (should_print_pool && rlPoolCount > 0 ) {
        int n = rlPoolCount;
        int *idx = (int*)malloc((size_t)n * sizeof(int));
        if (!idx) { fprintf(stderr, "Out of memory\n"); exit(EXIT_FAILURE); }
        for (int i = 0; i < n; ++i) idx[i] = i;
        qsort(idx, n, sizeof(int), rlCmpIdxByScore);

        for (int k = 0; k < n; ++k) {
            int i = idx[k];
            if (rlPool[i].in_use && rlPool[i].tree && rlPool[i].tree->root) {
                outputExpression(rlPool[i].tree, stdout);
            }
        }
        free(idx);
    }

    for (int i = 0; i < rlPoolCount; ++i) rlFreeExpr(&rlPool[i]);
    rlPoolCount = 0;
}
#endif

/* --------------------------------- END RL --------------------------------- */
//------ Stop generation -------

boolean shouldGenerationProcessBeTerminated(int complexity){
    if(heuristicStopConditionReached!=NULL){
        if(heuristicStopConditionReached()){
            heuristicStoppedGeneration = TRUE;
            return TRUE;
        }
    }
    if(timeOutReached || userInterrupted || terminationSignalReceived){
        return TRUE;
    }
    if (complexity > complexity_limit) {
        complexity_limit_reached = TRUE;
        complexity = complexity_limit;
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
    if (printValidExpressions) {
        printExpression(tree, stderr);
    }
    if (!doConjecturing) return;
    if (skipCount > allowedPercentageOfSkips * objectCount) return;

    switch (selectedHeuristic) {
        case DALMATIAN_HEURISTIC:
            dalmatianHeuristic(tree, values, skipCount);
            break;
        case GRINVIN_HEURISTIC:
            grinvinHeuristic(tree, values);
            break;
        case SAM_HEURISTIC:
            samHeuristic(tree, values, skipCount);
            break;
        case RL_HEURISTIC:
            rlHeuristic(tree, values, skipCount);
            break;
        default:
            break;
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
            dalmatianHeuristic_propertyBased(tree, values, skipCount);
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
    if ((isnan(left)) || isnan(right)) {
      return TRUE;
    }
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

    /* Evaluate; may stop early if candidate violates inequality */
    boolean ok = evaluateTree(tree, values, &calculatedValues, &hitCount, &skipCount);

    /* IMPORTANT: avoid garbage values for the unevaluated tail */
    for (int j = calculatedValues; j < objectCount; ++j) {
        values[j] = NAN;
    }

    /* If RL is the selected heuristic, feed it EVERYTHING (valid + invalid) */
    if (doConjecturing && selectedHeuristic == RL_HEURISTIC) {
        rlHeuristic(tree, values, skipCount);
        return;
    }

    /* Original behavior for other heuristics: only valid expressions */
    if (ok) {
        handleExpression(tree, values, calculatedValues, hitCount, skipCount);
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
    if(generateAllExpressions){
        return;
    }
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
                complexity = targetUnary + 2*targetBinary;
                if(shouldGenerationProcessBeTerminated(complexity)){
                    return;
                }
            }
        } else if (currentNode->type == 1){
            currentNode->contentLabel[0] = UNARY_LABEL;
            for (i=0; i<unaryOperatorCount; i++){
                currentNode->contentLabel[1] = unaryOperators[i];
                generateLabeledTree(tree, orderedNodes, pos+1);
                complexity = targetUnary + 2*targetBinary;
                if(shouldGenerationProcessBeTerminated(complexity)){
                    return;
                }
            }
        } else { // currentNode->type == 2
            //first try non-commutative binary operators
            currentNode->contentLabel[0] = NON_COMM_BINARY_LABEL;
            for (i=0; i<nonCommBinaryOperatorCount; i++){
                currentNode->contentLabel[1] = nonCommBinaryOperators[i];
                generateLabeledTree(tree, orderedNodes, pos+1);
                complexity = targetUnary + 2*targetBinary;
                if(shouldGenerationProcessBeTerminated(complexity)){
                    return;
                }
            }
            
            //then try commutative binary operators
            if (leftSideBiggest(currentNode, orderedNodes)){
                currentNode->contentLabel[0] = COMM_BINARY_LABEL;
                for (i=0; i<commBinaryOperatorCount; i++){
                    currentNode->contentLabel[1] = commBinaryOperators[i];
                    generateLabeledTree(tree, orderedNodes, pos+1);
                    complexity = targetUnary + 2*targetBinary;
                    if(shouldGenerationProcessBeTerminated(complexity)){
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
        complexity = targetUnary + 2*targetBinary;
        if(shouldGenerationProcessBeTerminated(complexity)){
            return;
        }
    }
    
    for(i=0; i<tree->levelWidth[tree->depth]; i++){
        NODE *parent = tree->nodesAtDepth[tree->depth][i];
        addChildToNodeInTree(tree, parent);
        generateTreeImpl(tree);
        removeChildFromNodeInTree(tree, parent);
        complexity = targetUnary + 2*targetBinary;
        if(shouldGenerationProcessBeTerminated(complexity)){
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
    complexity = unary + 2*binary;
    while(!shouldGenerationProcessBeTerminated(complexity)) {
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
    /* === NEW: compute RL normalization constants === */
    rlComputeTargetMinMax();
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
    fprintf(stderr, " %s [options] -a [unary binary] [invariants]\n", name);
    fprintf(stderr, "       Generates labeled expression trees.\n");
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
    fprintf(stderr, "    -a, --all-expressions\n");
    fprintf(stderr, "       Generate labeled expression trees as for conjecturing.\n");
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
    fprintf(stderr, "    --maximum-complexity\n");
    fprintf(stderr, "       Print the maximum complexity reached during the generation to stderr.\n");
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
    fprintf(stderr, "    --rl\n");
    fprintf(stderr, "       Use a REINFORCE policy (learned online) to keep/skip candidates.\n");
    fprintf(stderr, "       Reward = improvement in a multi-term pool score (violation/tightness/\n");
    fprintf(stderr, "       complexity/redundancy). Keeps top-%d and prints them at the end.\n", rl_top_k);

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
        {"sam", no_argument, NULL, 0},
        {"rl", no_argument, NULL, 0},
        {"invariant-names", no_argument, NULL, 0},
        {"operators", required_argument, NULL, 0},
        {"invariants", required_argument, NULL, 0},
        {"leq", no_argument, NULL, 0},
        {"less", no_argument, NULL, 0}, // don't use this option
        {"geq", no_argument, NULL, 0},
        {"greater", no_argument, NULL, 0}, // don't use this option
        {"limits", required_argument, NULL, 0},
        {"allowed-skips", required_argument, NULL, 0},
        {"print-valid-expressions", no_argument, NULL, 0},
        {"sufficient", no_argument, NULL, 0},
        {"necessary", no_argument, NULL, 0},
        {"maximum-complexity", no_argument, NULL, 0},
        {"complexity-limit", required_argument, NULL, 0},
        {"top-k", required_argument, NULL, 0},
        {"beta", required_argument, NULL, 0},
        {"lambda", required_argument, NULL, 0},
        {"alpha", required_argument, NULL, 0},
        {"gamma", required_argument, NULL, 0},
        {"learningrate", required_argument, NULL, 0},
        {"baselinealpha", required_argument, NULL, 0},
        {"sim", required_argument, NULL, 0},
        {"seed", required_argument, NULL, 0},
        {"rho", required_argument, NULL, 0},
        {"episodes", required_argument, NULL, 0},
        {"help", no_argument, NULL, 'h'},
        {"verbose", no_argument, NULL, 'v'},
        {"unlabeled", no_argument, NULL, 'u'},
        {"labeled", no_argument, NULL, 'l'},
        {"expressions", no_argument, NULL, 'e'},
        {"all-expressions", no_argument, NULL, 'a'},
        {"conjecture", no_argument, NULL, 'c'},
        {"output", required_argument, NULL, 'o'},
        {"property", no_argument, NULL, 'p'},
        {"theory", no_argument, NULL, 't'}
    };
    int option_index = 0;

    while ((c = getopt_long(argc, argv, "hvuleaco:pt", long_options, &option_index)) != -1) {
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
                    case 9: // 
                        selectedHeuristic = SAM_HEURISTIC;
                        heuristicInit = samHeuristicInit;
                        heuristicStopConditionReached = NULL;         // no early stop for SAM
                        heuristicPostProcessing = samHeuristicPostProcessing;
                        break;
                    case 10:
                        selectedHeuristic = RL_HEURISTIC;
                        heuristicInit = rlHeuristicInit;
                        heuristicStopConditionReached = NULL;   // no early stop
                        heuristicPostProcessing = rlHeuristicPostProcessing;
                        break;
                    case 11:
                        useInvariantNames = TRUE;
                        break;
                    case 12:
                        operatorFile = fopen(optarg, "r");
                        closeOperatorFile = TRUE;
                        break;
                    case 13:
                        invariantsFile = fopen(optarg, "r");
                        closeInvariantsFile = TRUE;
                        break;
                    case 14:
                        inequality = LEQ;
                        break;
                    case 15:
                        inequality = LESS;
                        break;
                    case 16:
                        inequality = GEQ;
                        break;
                    case 17:
                        inequality = GREATER;
                        break;
                    case 18:
                        fprintf(stderr, "Limits are no longer supported.\n");
                        return EXIT_SUCCESS;
                        break;
                    case 19:
                        allowedPercentageOfSkips = strtof(optarg, NULL);
                        break;
                    case 20:
                        printValidExpressions = TRUE;
                        break;
                    case 21:
                        inequality = SUFFICIENT;
                        break;
                    case 22:
                        inequality = NECESSARY;
                        break;
                    case 23:
                        report_maximum_complexity_reached = TRUE;
                        break;
                    case 24:
                        complexity_limit = strtoul(optarg, NULL, 10);
                        break;
                    case 25: /* --top-k */
                        rl_top_k = strtol(optarg, NULL, 10);
                        if (rl_top_k < 1) rl_top_k = 1;
                        if (rl_top_k > RL_MAX_TOP_K) rl_top_k = RL_MAX_TOP_K;
                        sam_top_k = rl_top_k;
                        break;
                    case 26:
                        sam_beta = strtod(optarg, NULL);
                        rl_beta_tight = sam_beta; /* if you reuse same name */
                        break;
                    case 27:
                        sam_lambda = strtod(optarg, NULL);
                        rl_lambda_comp  = sam_lambda;
                        break;
                    case 28:
                        rl_alpha_viol = strtod(optarg, NULL);
                        sam_alpha = rl_alpha_viol;
                        break;
                    case 29:
                        rl_gamma = strtod(optarg, NULL);
                        break;
                    case 30:
                        rl_lr= strtod(optarg, NULL);
                        break;
                    case 31:
                        rl_baseline_alpha= strtod(optarg, NULL);
                        break;
                    case 32:
                        strncpy(rl_sim_name, optarg, sizeof(rl_sim_name)-1);
                        rl_sim_name[sizeof(rl_sim_name)-1] = '\0';
                        break;
                    case 33:
                        rl_seed = (unsigned)strtoul(optarg, NULL, 10);
                        break;
                    case 34:
                        rl_rho_redund= strtod(optarg, NULL);
                        break;
                    case 35: /* --episodes */
                    RL_EPISODES = strtol(optarg, NULL, 10);
                    if (RL_EPISODES <= 0) {
                        fprintf(stderr, "--episodes must be positive\n");
                        exit(EXIT_FAILURE);
                    }
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
            case 'a':
                generateAllExpressions = TRUE;
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
            generateExpressions + generateAllExpressions + doConjecturing != TRUE){
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
    
    if (generateAllExpressions && (argc > optind + 3)) {
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
    
    time_t start, end;

    start = time(NULL);

    operatorFile = stdin;
    invariantsFile = stdin;
    
    int po = processOptions(argc, argv);
    if(po != -1) return po;
    
    int unary = 0;
    int binary = 0;
    if(!(doConjecturing || generateAllExpressions)){
        unary = strtol(argv[optind], NULL, 10);
        binary = strtol(argv[optind+1], NULL, 10);
        if(onlyLabeled) {
            invariantCount = strtol(argv[optind+2], NULL, 10);
        }
    } else if(generateAllExpressions && (argc - optind == 1)) {
        invariantCount = strtol(argv[optind], NULL, 10);
    } else if(generateAllExpressions && (argc - optind == 3)) {
        unary = strtol(argv[optind], NULL, 10);
        binary = strtol(argv[optind+1], NULL, 10);
        invariantCount = strtol(argv[optind+2], NULL, 10);
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
        if(generateAllExpressions && invariantCount>0){
            allocateMemory_onlyLabeled();
        } else {
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
    
/* ----------------- start actual generation process ----------------- */

    if (doConjecturing || generateAllExpressions) {
    
        if (doConjecturing && selectedHeuristic == RL_HEURISTIC) {
    
            for (rl_episode = 1; rl_episode <= RL_EPISODES; ++rl_episode) {
    
                /* reset termination flags for a fresh episode */
                timeOutReached = FALSE;
                userInterrupted = FALSE;
                terminationSignalReceived = FALSE;
                heuristicStoppedGeneration = FALSE;
                complexity_limit_reached = FALSE;
    
                /* optional: per-episode counters */
                treeCount = 0;
                labeledTreeCount = 0;
                validExpressionsCount = 0;
    
                /* reset “progress” */
                complexity = 0;
    
                /* re-arm per-episode timeout */
                if (timeOut) alarm((unsigned int)timeOut);
    
                /* init episode (pool reset; theta persists) */
                if (heuristicInit) heuristicInit();
    
                /* full pass over expressions */
                conjecture(unary, binary);
    
                /* stop timer so it doesn't spill into next episode */
                if (timeOut) alarm(0);
    
                /* update policy + log + print pool */
                if (heuristicPostProcessing) heuristicPostProcessing();
    
                /* stop early only for user kills */
                if (userInterrupted || terminationSignalReceived) break;
            }
    
        } else {
    
            /* non-RL original single run */
            timeOutReached = FALSE; /* Reset timeout flags */
            if (timeOut) alarm((unsigned int)timeOut);   /* Arm timeout once for entire run */
            if (heuristicInit) heuristicInit();
            conjecture(unary, binary);
    
            if (timeOut) alarm(0);
            if (heuristicPostProcessing) heuristicPostProcessing();
        }
    } else {    
        /* not conjecturing: original behavior */
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
    } else if(complexity_limit_reached){
        fprintf(stderr, "Generation process was stopped because the maximum complexity was explored.\n");
    }
    
    //print some statistics
    if(onlyUnlabeled){
        fprintf(stderr, "Found %lu unlabeled trees.\n", treeCount);
    } else if(onlyLabeled) {
        fprintf(stderr, "Found %lu unlabeled trees.\n", treeCount);
        fprintf(stderr, "Found %lu labeled trees.\n", labeledTreeCount);
    } else if(generateAllExpressions) {
        fprintf(stderr, "Found %lu unlabeled trees.\n", treeCount);
        fprintf(stderr, "Found %lu labeled trees.\n", labeledTreeCount);
    } else if(generateExpressions || doConjecturing) {
        fprintf(stderr, "Found %lu unlabeled trees.\n", treeCount);
        fprintf(stderr, "Found %lu labeled trees.\n", labeledTreeCount);
        fprintf(stderr, "Found %lu valid expressions.\n", validExpressionsCount);
    }
    fprintf(stderr, "Maximum complexity reached: %lu\n", complexity-1);
    end = time(NULL);
    fprintf(stderr, "Elapsed time: %ld seconds\n", end - start);
    
    return 0;
}
