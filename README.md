conjecturing
============

See the directory `spkg` for instructions on how to build and install a Sage package containing the expressions program.
Once you have built and installed such a Sage package, you can use the Python files in the directory `sage` to interact
with the package.

Open the directory `sage` in a terminal window and start Sage. Usually this is done using the following command:

    $ sage

Once Sage has started, you can load the file `conjecturing.py`:

    sage: attach('conjecturing.py')

You can also choose to load any of the other files, but this is not necessary.

An example run might look like this:

    sage: attach('conjecturing.py')
    sage: attach('numbertheory.py')
    sage: objects = [5, 10]
    sage: conjecture(objects, invariants, 1)

Note that loading the file `numbertheory.py` sets the variable `invariants` to a list of invariants used in number theory.
