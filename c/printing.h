/*
 * Main developer: Nico Van Cleemput
 * In collaboration with: Craig Larson
 * 
 * Copyright (C) 2013 Ghent University.
 * Licensed under the GNU GPL, read the file LICENSE.txt for details.
 */

#ifndef PRINTING_H
#define	PRINTING_H

void printComparator(int id, FILE *f);
void printNode(NODE *node, FILE *f, char **invariantNamePointers);
void printSingleNode(NODE *node, FILE *f, char **invariantNamePointers);

#endif	/* PRINTING_H */

