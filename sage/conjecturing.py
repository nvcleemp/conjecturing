import sys
sys.path.append(".") # Needed to pass Sage's automated testing

from sage.all import *


class Conjecture(SageObject): #Based on GraphExpression from IndependenceNumberProject

    def __init__(self, stack, expression, invariantsDict):
        """Constructs a new Conjecture from the given stack of functions."""
        self.stack = stack
        self.expression = expression
        self.invariantsDict = invariantsDict
        super(Conjecture, self).__init__()

    def __eq__(self, other):
        return self.stack == other.stack and self.expression == other.expression

    def _repr_(self):
        return repr(self.expression)

    def _latex_(self):
        return latex(self.expression)

    def evaluate(self, g):
        stack = []
        for op, opType, opName in self.stack:
            if opType==0:
                stack.append(op(g))
            elif opType==1:
                stack.append(op(stack.pop()))
            elif opType==2:
	        right = stack.pop()
	        left = stack.pop()
                stack.append(op(left, right))
        
        return stack.pop()

def wrapUnboundMethod(op, invariantsDict):
    return lambda obj: getattr(obj, invariantsDict[op].__name__)()

def wrapBoundMethod(op, invariantsDict):
    return lambda obj: invariantsDict[op](obj)

def _makeConjecture(inputList, variable, invariantsDict):
    import operator

    specials = {'-1', '+1', '*2', '/2', '^2', '-()', '1/', 'log10'}

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
            expressionStack.append(function(op, variable, evalf_func=f))
            operatorStack.append((f,0,op))
        elif op in specials:
            _handleSpecialOperators(expressionStack, op)
            operatorStack.append(_getSpecialOperators(op))
        elif op in unaryOperators:
            expressionStack.append(unaryOperators[op](expressionStack.pop()))
            operatorStack.append((unaryOperators[op],1,op))
        elif op in binaryOperators:
            right = expressionStack.pop()
            left = expressionStack.pop()
            expressionStack.append(binaryOperators[op](left, right))
            operatorStack.append((binaryOperators[op],2,op))
        elif op in comparators:
            right = expressionStack.pop()
            left = expressionStack.pop()
            expressionStack.append(comparators[op](left, right))
            operatorStack.append((comparators[op],2,op))
        else:
            raise ValueError("Error while reading output from expressions. Unknown element: {}".format(op))

    return Conjecture(operatorStack, expressionStack.pop(), invariantsDict)

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
    else:
        raise ValueError("Unknown operator: {}".format(op))

def _getSpecialOperators(op):
    if op == '-1':
        return (lambda x: x-1), 1, '-1'
    elif op == '+1':
        return (lambda x: x+1), 1, '+1'
    elif op == '*2':
        return (lambda x: x*2), 1, '*2'
    elif op == '/2':
        return (lambda x: x*0.5), 1, '/2'
    elif op == '^2':
        return (lambda x: x*x), 1, '^2'
    elif op == '-()':
        return (lambda x: -x), 1, '-()'
    elif op == '1/':
        return (lambda x: 1.0/x), 1, '1/'
    elif op == 'log10':
        return (lambda x: log(x,10)), 1, 'log10'
    else:
        raise ValueError("Unknown operator: {}".format(op))

def conjecture(objects, invariants, mainInvariant, variableName='x', time=5, debug=False):
    
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
    command = './expressions -c{} --dalmatian --all-operators --time {} --invariant-names --output stack'
    command = command.format('v' if debug else '', time)

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
