#
# Makefile for expressions
#
#
# Main developer: Nico Van Cleemput
# In collaboration with: Craig Larson
# 
# Copyright (C) 2013 Ghent University.
# Licensed under the GNU GPL, read the file LICENSE.txt for details.
#

SHELL = /bin/sh

CC32 = gcc 
CC64 = gcc 
CFLAGS = -O4 -Wall
COMPLETE = build/expressions build/expressions-64 build/expressions-profile build/expressions-debug
SOURCES = expressions.c datatypes.h limits.h util.h Makefile COPYRIGHT.txt LICENSE.txt
CONJECTURING_SOURCES = expressions.c

all : 32bit

complete: $(COMPLETE)

32bit: build/expressions

64bit : build/expressions-64

profile : build/expressions-profile

debug : build/expressions-debug

build/expressions: $(CONJECTURING_SOURCES)
	mkdir -p build
	${CC32} $(CFLAGS) $(CONJECTURING_SOURCES) -o build/expressions -lm

build/expressions-64: $(CONJECTURING_SOURCES)
	mkdir -p build
	${CC64} $(CFLAGS) $(CONJECTURING_SOURCES) -o build/expressions-64 -lm

build/expressions-profile: $(CONJECTURING_SOURCES)
	mkdir -p build
	${CC32} -Wall -pg -g $(CONJECTURING_SOURCES) -o build/expressions-profile -lm 

build/expressions-debug: $(CONJECTURING_SOURCES)
	mkdir -p build
	${CC32} -Wall -rdynamic -g $(CONJECTURING_SOURCES) -o build/expressions-debug -lm

sources: dist/conjecturing-sources.zip dist/conjecturing-sources.tar.gz

dist/conjecturing-sources.zip: $(SOURCES)
	mkdir -p dist
	zip dist/conjecturing-sources $(SOURCES)

dist/conjecturing-sources.tar.gz: $(SOURCES)
	mkdir -p dist
	tar czf dist/conjecturing-sources.tar.gz $(SOURCES)

clean:
	rm -rf build
	rm -rf dist