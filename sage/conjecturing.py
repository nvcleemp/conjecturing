import sys
sys.path.append(".") # Needed to pass Sage's automated testing

from sage.all import *


class Conjecture(SageObject): #Based on GraphExpression from IndependenceNumberProject

    def __init__(self, stack, expression):
        """Constructs a new Conjecture from the given stack of functions."""
        self.stack = stack
        self.expression = expression
        super(Conjecture, self).__init__()

    def __eq__(self, other):
        return self.stack == other.stack and self.expression == other.expression

    def _repr_(self):
        return repr(self.expression)

    def _latex_(self):
        return latex(self.expression)

    def evaluate(self, g):
        stack = []
        for op, opType in self.stack:
            if opType==0:
                stack.append(op(g))
            elif opType==1:
                stack.append(op(stack.pop()))
            elif opType==2:
	        right = stack.pop()
	        left = stack.pop()
                if op == operator.truediv and right == 0:
                    if left > 0:
                        stack.append(float('inf'))
                    elif left < 0:
                        stack.append(float('-inf'))
                    else:
                        stack.append(float('NaN'))
                else:
                    stack.append(op(left, right))
        return stack.pop()

def wrapUnboundMethod(op, invariantsDict):
    return lambda obj: getattr(obj, invariantsDict[op].__name__)()

def wrapBoundMethod(op, invariantsDict):
    return lambda obj: invariantsDict[op](obj)

def _makeConjecture(inputList, variable, invariantsDict):
    import operator

    specials = {'-1', '+1', '*2', '/2', '^2', '-()', '1/', 'log10', 'max', 'min'}

    unaryOperators = {'sqrt': sqrt, 'ln': log}
    binaryOperators = {'+': operator.add, '*': operator.mul, '-': operator.sub, '/': operator.truediv, '^': operator.pow}
    comparators = {'<': operator.lt, '<=': operator.le, '>': operator.gt, '>=': operator.ge}
    expressionStack = []
    operatorStack = []

    for op in inputList:
        if op in invariantsDict:
            import types
            if type(invariantsDict[op]) in (types.BuiltinMethodType, types.MethodType):
                f = wrapUnboundMethod(op, invariantsDict)
            else:
                f = wrapBoundMethod(op, invariantsDict)
            expressionStack.append(function(op, variable))
            operatorStack.append((f,0))
        elif op in specials:
            _handleSpecialOperators(expressionStack, op)
            operatorStack.append(_getSpecialOperators(op))
        elif op in unaryOperators:
            expressionStack.append(unaryOperators[op](expressionStack.pop()))
            operatorStack.append((unaryOperators[op],1))
        elif op in binaryOperators:
            right = expressionStack.pop()
            left = expressionStack.pop()
            expressionStack.append(binaryOperators[op](left, right))
            operatorStack.append((binaryOperators[op],2))
        elif op in comparators:
            right = expressionStack.pop()
            left = expressionStack.pop()
            expressionStack.append(comparators[op](left, right))
            operatorStack.append((comparators[op],2))
        else:
            raise ValueError("Error while reading output from expressions. Unknown element: {}".format(op))

    return Conjecture(operatorStack, expressionStack.pop())

def _handleSpecialOperators(stack, op):
    if op == '-1':
        stack.append(stack.pop()-1)
    elif op == '+1':
        stack.append(stack.pop()+1)
    elif op == '*2':
        stack.append(stack.pop()*2)
    elif op == '/2':
        stack.append(stack.pop()/2)
    elif op == '^2':
        x = stack.pop()
        stack.append(x*x)
    elif op == '-()':
        stack.append(-stack.pop())
    elif op == '1/':
        stack.append(1/stack.pop())
    elif op == 'log10':
        stack.append(log(stack.pop(),10))
    elif op == 'max':
        stack.append(function('maximum',stack.pop(),stack.pop()))
    elif op == 'min':
        stack.append(function('minimum',stack.pop(),stack.pop()))
    else:
        raise ValueError("Unknown operator: {}".format(op))

def _getSpecialOperators(op):
    if op == '-1':
        return (lambda x: x-1), 1
    elif op == '+1':
        return (lambda x: x+1), 1
    elif op == '*2':
        return (lambda x: x*2), 1
    elif op == '/2':
        return (lambda x: x*0.5), 1
    elif op == '^2':
        return (lambda x: x*x), 1
    elif op == '-()':
        return (lambda x: -x), 1
    elif op == '1/':
        return (lambda x: float('inf') if x==0 else 1.0/x), 1
    elif op == 'log10':
        return (lambda x: log(x,10)), 1
    elif op == 'max':
        return max, 2
    elif op == 'min':
        return min, 2
    else:
        raise ValueError("Unknown operator: {}".format(op))

def allOperators():
    return { '-1', '+1', '*2', '/2', '^2', '-()', '1/', 'sqrt', 'ln', 'log10', '+', '*', 'max', 'min', '-', '/', '^'}

def conjecture(objects, invariants, mainInvariant, variableName='x', time=5, debug=False, verbose=False, upperBound=True,
                                                   operators=None):

    if len(invariants)<2 or len(objects)==0: return

    operatorDict = { '-1' : 'U 0', '+1' : 'U 1', '*2' : 'U 2', '/2' : 'U 3', '^2' : 'U 4', '-()' : 'U 5', '1/' : 'U 6',
                     'sqrt' : 'U 7', 'ln' : 'U 8', 'log10' : 'U 9', '+' : 'C 0', '*' : 'C 1', 'max' : 'C 2', 'min' : 'C 3',
                     '-' : 'N 0', '/' : 'N 1', '^' : 'N 2'}

    # check whether number of invariants and objects falls within the allowed bounds
    import subprocess
    sp = subprocess.Popen('expressions --limits all', shell=True,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, close_fds=True)

    limits = {key:int(value) for key, value in (l.split(':') for l in sp.stdout)}

    assert len(objects) <= limits['MAX_OBJECT_COUNT'], 'This version of expressions does not support that many objects.'
    assert len(invariants) <= limits['MAX_INVARIANT_COUNT'], 'This version of expressions does not support that many invariants.'

    # prepare the invariants to be used in conjecturing
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

    # call the conjecturing program
    command = 'expressions -c{} --dalmatian {}--time {} --invariant-names --output stack {}'
    command = command.format('v' if verbose and debug else '', '--all-operators ' if operators is None else '',
                             time, '--leq' if upperBound else '--geq')

    sp = subprocess.Popen(command, shell=True,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, close_fds=True)
    stdin = sp.stdin

    if operators is not None:
        stdin.write('{}\n'.format(len(operators)))
        for op in operators:
            stdin.write('{}\n'.format(operatorDict[op]))

    stdin.write('{} {} {}\n'.format(len(objects), len(invariants), mainInvariant))

    for invariant in names:
        stdin.write('{}\n'.format(invariant))
    for o in objects:
        for invariant in names:
            stdin.write('{}\n'.format(invariantsDict[invariant](o)))
    
    if debug:
        for l in sp.stderr:
            print '> ' + l.rstrip()
    
    # process the output
    out = sp.stdout
    
    variable = var(variableName)
    
    conjectures = []
    inputList = []
    
    for l in out:
        op = l.strip()
        if op:
            inputList.append(op)
        else:
            conjectures.append(_makeConjecture(inputList, variable, invariantsDict))
            inputList = []
    
    return conjectures
