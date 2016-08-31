Sage package
============

These instructions describe how to install conjecturing as a Sage package in
Sage 7.3 or later.
First you need to locate the Sage installation into which you want to install
conjecturing. In case this is the system installation of Sage, you can find
the location using the command `which`.

 * Copy the directory conjecturing into the directory SAGE_ROOT/build/pkgs.
 * Copy the file conjecturing-0.11.1.tar.gz into SAGE_ROOT/upstream.
 * Run the following command:
     $ sage --package fix-checksum conjecturing
 * Install the package using the following command:
     $ sage -i conjecturing

Note that if you are using the system installation of Sage, you might need to
prepend sudo to the commands above. If you are not using the system installation
of Sage, it might be easier to change into SAGE_ROOT and replace the commands by
./sage. 
