Sage package
============

The Makefile in this directory can be used to create a Sage package that can be installed in Sage.
This Sage package is however not meant to be an official Sage package to be distributed. Each time
a new package is built we construct a new Mercurial repository instead of reusing that of a previous
package. The packages built by this Makefile are perfectly usable for local copies.

You build a Sage package by issueing the following command:

    make conjecturing-20130910

The date 20130910 can be chosen freely, and only serves as a way to distinguish between versions.

You can then install this newly created package by issueing the following command:

    sage -f conjecturing-20130910.spkg

Depending on the location where Sage is installed, you might need to add `sudo` at the beginning 
of that command.
