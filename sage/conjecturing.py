import sys
sys.path.append(".") # Needed to pass Sage's automated testing

from sage.all import *

def conjecture(objects, invariants, mainInvariant, variableName='x'):

    command = './expressions -c --dalmatian --all-operators --time 5 --invariant-names'

    import subprocess
    sp = subprocess.Popen(command, shell=True,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, close_fds=True)
    stdin = sp.stdin

    stdin.write('{} {} {}\n'.format(len(objects), len(invariants), mainInvariant))

    for invariant in invariants:
        stdin.write('{}\n'.format(invariant.__name__))
    for o in objects:
        for invariant in invariants:
            stdin.write('{}\n'.format(invariant(o)))
    
    out = sp.stdout
    
    for l in out:
        print l.rstrip()

