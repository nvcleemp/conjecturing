Sage package
============

These instructions describe how to install conjecturing as a Sage package.
First you need to locate the Sage installation into which you want to install
conjecturing. In case this is the system installation of Sage, you can find 
the location using the command `which`.

 * Copy the directory conjecturing into the directory SAGE_ROOT/build/pkgs.
 * Copy the file conjecturing-0.9.1.tar.gz into SAGE_ROOT/upstream.
 * Run the following command:
     $ sage -sh sage-fix-pkg-checksums
 * Install the package using the following command:
     $ sage -i conjecturing
