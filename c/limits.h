/*
 * Main developer: Nico Van Cleemput
 * In collaboration with: Craig Larson
 * 
 * Copyright (C) 2013 Ghent University.
 * Licensed under the GNU GPL, read the file LICENSE.txt for details.
 */

#ifndef LIMITS_H
#define	LIMITS_H

#define MAX_UNARY_COUNT 50
#define MAX_BINARY_COUNT 20

#define MAX_TREE_DEPTH MAX_UNARY_COUNT + MAX_BINARY_COUNT
#define MAX_TREE_LEVEL_WIDTH MAX_BINARY_COUNT + 1
#define MAX_NODES_USED MAX_UNARY_COUNT + 2*MAX_BINARY_COUNT + 1

#define MAX_UNARY_OPERATORS 40
#define MAX_COMM_BINARY_OPERATORS 20
#define MAX_NCOMM_BINARY_OPERATORS 20

#endif	/* LIMITS_H */

