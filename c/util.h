/*
 * Main developer: Nico Van Cleemput
 * In collaboration with: Craig Larson
 * 
 * Copyright (C) 2013 Ghent University.
 * Licensed under the GNU GPL, read the file LICENSE.txt for details.
 */

#ifndef UTIL_H
#define	UTIL_H

#include <stdlib.h>
#include <stdio.h>

#define BAILOUT(msg) fprintf(stderr, "%s - %d: " msg " -- exiting!\n", __FILE__, __LINE__); exit(EXIT_FAILURE);

#endif	/* UTIL_H */

