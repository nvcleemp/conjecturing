/*
 * Main developer: Nico Van Cleemput
 * In collaboration with: Craig Larson
 * 
 * Copyright (C) 2014 Nico Van Cleemput.
 * Licensed under the GNU GPL, read the file LICENSE.txt for details.
 */

#ifndef PRINTING_PB_H
#define	PRINTING_PB_H

void printComparator_propertyBased(int id, FILE *f);
void printNode_propertyBased(NODE *node, FILE *f, char **invariantNamePointers);
void printSingleNode_propertyBased(NODE *node, FILE *f, char **invariantNamePointers);

#endif	/* PRINTING_PB_H */

