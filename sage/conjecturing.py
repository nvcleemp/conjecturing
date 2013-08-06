import sys
sys.path.append(".") # Needed to pass Sage's automated testing

from sage.all import *

def conjecture(objects, invariants, mainInvariant):
    
    invariantsDict = {}
    names = []
    
    for pos, invariant in enumerate(invariants):
        if type(invariant) == tuple:
            name, invariant = invariant
        elif hasattr(invariant, '__name__'):
            if invariant.__name__ in invariantsDict:
                name = '{}_{}'.format(invariant.__name__, pos)
            else:
                name = invariant.__name__
        else:
            name = 'invariant_{}'.format(pos)
        invariantsDict[name] = invariant
        names.append(name)


    command = './expressions -c --dalmatian --all-operators --time 5 --invariant-names'

    import subprocess
    sp = subprocess.Popen(command, shell=True,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, close_fds=True)
    stdin = sp.stdin

    stdin.write('{} {} {}\n'.format(len(objects), len(invariants), mainInvariant))

    for invariant in names:
        stdin.write('{}\n'.format(invariant))
    for o in objects:
        for invariant in names:
            stdin.write('{}\n'.format(invariantsDict[invariant](o)))
    
    out = sp.stdout
    
    for l in out:
        print l.rstrip()

