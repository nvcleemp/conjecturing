/* 
 * File:   limits.h
 * Author: nvcleemp
 *
 * Created on July 31, 2013, 4:12 PM
 */

#ifndef LIMITS_H
#define	LIMITS_H

#ifdef	__cplusplus
extern "C" {
#endif

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

#ifdef	__cplusplus
}
#endif

#endif	/* LIMITS_H */

