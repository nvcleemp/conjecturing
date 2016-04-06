import sys
sys.path.append(".") # Needed to pass Sage's automated testing

from sage.all import *


class Conjecture(SageObject): #Based on GraphExpression from IndependenceNumberProject

    def __init__(self, stack, expression, pickling):
        """Constructs a new Conjecture from the given stack of functions."""
        self.stack = stack
        self.expression = expression
        self.pickling = pickling
        self.__name__ = ''.join(c for c in repr(self.expression) if c != ' ')
        super(Conjecture, self).__init__()

    def __eq__(self, other):
        return self.stack == other.stack and self.expression == other.expression

    def __reduce__(self):
        return (_makeConjecture, self.pickling)

    def _repr_(self):
        return repr(self.expression)

    def _latex_(self):
        return latex(self.expression)

    def __call__(self, g, returnBoundValue=False):
        return self.evaluate(g, returnBoundValue)

    def evaluate(self, g, returnBoundValue=False):
        stack = []
        if returnBoundValue:
            assert self.stack[-1][0] in {operator.le, operator.lt, operator.ge, operator.gt}, "Conjecture is not a bound"
        for op, opType in self.stack:
            if opType==0:
                stack.append(op(g))
            elif opType==1:
                stack.append(op(stack.pop()))
            elif opType==2:
                right = stack.pop()
                left = stack.pop()
                if type(left) == sage.symbolic.expression.Expression:
                    left = left.n()
                if type(right) == sage.symbolic.expression.Expression:
                    right = right.n()
                if op == operator.truediv and right == 0:
                    if left > 0:
                        stack.append(float('inf'))
                    elif left < 0:
                        stack.append(float('-inf'))
                    else:
                        stack.append(float('NaN'))
                elif op == operator.pow and (right == Infinity or right == float('inf')):
                    if left < -1 or left > 1:
                        stack.append(float('inf'))
                    elif -1 < left < 1:
                        stack.append(0)
                    else:
                        stack.append(1)
                elif op == operator.pow and (right == -Infinity or right == float('-inf')):
                    if left < -1 or left > 1:
                        stack.append(0)
                    elif -1 < left < 1:
                        stack.append(float('inf'))
                    else:
                        stack.append(1)
                elif op == operator.pow and left == 0 and right < 0:
                    stack.append(float('inf'))
                elif op == operator.pow and left == -Infinity and right not in ZZ: #mimic C function pow
                    stack.append(float('inf'))
                elif op == operator.pow and left < 0 and right not in ZZ: #mimic C function pow
                    stack.append(float('nan'))
                elif op == operator.pow and right > 2147483647: #prevent RuntimeError
                    stack.append(float('nan'))
                elif op in {operator.le, operator.lt, operator.ge, operator.gt}:
                    left = round(left, 6)
                    right = round(right, 6)
                    if returnBoundValue:
                        stack.append(right)
                    else:
                        stack.append(op(left, right))
                else:
                    stack.append(op(left, right))
        return stack.pop()

def wrapUnboundMethod(op, invariantsDict):
    return lambda obj: getattr(obj, invariantsDict[op].__name__)()

def wrapBoundMethod(op, invariantsDict):
    return lambda obj: invariantsDict[op](obj)

def _makeConjecture(inputList, variable, invariantsDict):
    import operator

    specials = {'-1', '+1', '*2', '/2', '^2', '-()', '1/', 'log10', 'max', 'min', '10^'}

    unaryOperators = {'sqrt': sqrt, 'ln': log, 'exp': exp, 'ceil': ceil, 'floor': floor,
                      'abs': abs, 'sin': sin, 'cos': cos, 'tan': tan, 'asin': arcsin,
                      'acos': arccos, 'atan': arctan, 'sinh': sinh, 'cosh': cosh,
                      'tanh': tanh, 'asinh': arcsinh, 'acosh': arccosh, 'atanh': arctanh}
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
            expressionStack.append(sage.symbolic.function_factory.function(op)(variable))
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

    return Conjecture(operatorStack, expressionStack.pop(), (inputList, variable, invariantsDict))

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
        stack.append(function('maximum')(stack.pop(),stack.pop()))
    elif op == 'min':
        stack.append(function('minimum')(stack.pop(),stack.pop()))
    elif op == '10^':
        stack.append(10**stack.pop())
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
    elif op == '10^':
        return (lambda x: 10**x), 1
    else:
        raise ValueError("Unknown operator: {}".format(op))

def allOperators():
    """
    Returns a set containing all the operators that can be used with the
    invariant-based conjecture method. This method can be used to quickly
    get a set from which to remove some operators or to just get an idea
    of how to write some operators.

    There are at the moment 34 operators available, including, e.g., addition.

        sage: len(allOperators())
        34
        sage: '+' in allOperators()
        True
    """
    return { '-1', '+1', '*2', '/2', '^2', '-()', '1/', 'sqrt', 'ln', 'log10',
       'exp', '10^', 'ceil', 'floor', 'abs', 'sin', 'cos', 'tan', 'asin',
       'acos', 'atan', 'sinh', 'cosh', 'tanh', 'asinh', 'acosh', 'atanh',
       '+', '*', 'max', 'min', '-', '/', '^'}

def conjecture(objects, invariants, mainInvariant, variableName='x', time=5, debug=False, verbose=False, upperBound=True,
                                                   operators=None, theory=None):

    if len(invariants)<2 or len(objects)==0: return
    if not theory: theory=None

    assert 0 <= mainInvariant < len(invariants), 'Illegal value for mainInvariant'

    operatorDict = { '-1' : 'U 0', '+1' : 'U 1', '*2' : 'U 2', '/2' : 'U 3',
                     '^2' : 'U 4', '-()' : 'U 5', '1/' : 'U 6',
                     'sqrt' : 'U 7', 'ln' : 'U 8', 'log10' : 'U 9',
                     'exp' : 'U 10', '10^' : 'U 11', 'ceil' : 'U 12',
                     'floor' : 'U 13', 'abs' : 'U 14', 'sin' : 'U 15',
                     'cos' : 'U 16', 'tan' : 'U 17', 'asin' : 'U 18',
                     'acos' : 'U 19', 'atan' : 'U 20', 'sinh': 'U 21',
                     'cosh' : 'U 22', 'tanh' : 'U 23', 'asinh': 'U 24',
                     'acosh' : 'U 25', 'atanh' : 'U 26',
                     '+' : 'C 0', '*' : 'C 1', 'max' : 'C 2', 'min' : 'C 3',
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
    command = 'expressions -c{}{} --dalmatian {}--time {} --invariant-names --output stack {} --allowed-skips 0'
    command = command.format('v' if verbose and debug else '', 't' if theory is not None else '',
                             '--all-operators ' if operators is None else '',
                             time, '--leq' if upperBound else '--geq')

    sp = subprocess.Popen(command, shell=True,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, close_fds=True)
    stdin = sp.stdin

    if operators is not None:
        stdin.write('{}\n'.format(len(operators)))
        for op in operators:
            stdin.write('{}\n'.format(operatorDict[op]))

    stdin.write('{} {} {}\n'.format(len(objects), len(invariants), mainInvariant + 1))

    for invariant in names:
        stdin.write('{}\n'.format(invariant))

    if theory is not None:
        for o in objects:
            if upperBound:
                try:
                    stdin.write('{}\n'.format(min(float(t(o)) for t in theory)))
                except:
                    stdin.write('NaN\n')
            else:
                try:
                    stdin.write('{}\n'.format(max(float(t(o)) for t in theory)))
                except:
                    stdin.write('NaN\n')

    for o in objects:
        for invariant in names:
            try:
                stdin.write('{}\n'.format(float(invariantsDict[invariant](o))))
            except:
                stdin.write('NaN\n')

    if debug:
        for l in sp.stderr:
            print '> ' + l.rstrip()

    # process the output
    out = sp.stdout

    variable = SR.var(variableName)

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

class PropertyBasedConjecture(SageObject):

    def __init__(self, expression, propertyCalculators, pickling):
        """Constructs a new Conjecture from the given stack of functions."""
        self.expression = expression
        self.propertyCalculators = propertyCalculators
        self.pickling = pickling
        self.__name__ = repr(self.expression)
        super(PropertyBasedConjecture, self).__init__()

    def __eq__(self, other):
        return self.expression == other.expression

    def __reduce__(self):
        return (_makePropertyBasedConjecture, self.pickling)

    def _repr_(self):
        return repr(self.expression)

    def _latex_(self):
        return latex(self.expression)

    def __call__(self, g):
        return self.evaluate(g)

    def evaluate(self, g):
        values = {prop: f(g) for (prop, f) in self.propertyCalculators.items()}
        return self.expression.evaluate(values)

def _makePropertyBasedConjecture(inputList, invariantsDict):
    import operator

    binaryOperators = {'&', '|', '^', '->'}

    expressionStack = []
    propertyCalculators = {}

    for op in inputList:
        if op in invariantsDict:
            import types
            if type(invariantsDict[op]) in (types.BuiltinMethodType, types.MethodType):
                f = wrapUnboundMethod(op, invariantsDict)
            else:
                f = wrapBoundMethod(op, invariantsDict)
            prop = ''.join([l for l in op if l.strip()])
            expressionStack.append(prop)
            propertyCalculators[prop] = f
        elif op == '<-':
            right = expressionStack.pop()
            left = expressionStack.pop()
            expressionStack.append('({})->({})'.format(right, left))
        elif op == '~':
            expressionStack.append('~({})'.format(expressionStack.pop()))
        elif op in binaryOperators:
            right = expressionStack.pop()
            left = expressionStack.pop()
            expressionStack.append('({}){}({})'.format(left, op, right))
        else:
            raise ValueError("Error while reading output from expressions. Unknown element: {}".format(op))

    import sage.logic.propcalc as propcalc
    return PropertyBasedConjecture(propcalc.formula(expressionStack.pop()), propertyCalculators, (inputList, invariantsDict))

def allPropertyBasedOperators():
    """
    Returns a set containing all the operators that can be used with the
    property-based conjecture method. This method can be used to quickly
    get a set from which to remove some operators or to just get an idea
    of how to write some operators.

    There are at the moment 5 operators available, including, e.g., AND.

        sage: len(allPropertyBasedOperators())
        5
        sage: '&' in allPropertyBasedOperators()
        True
    """
    return { '~', '&', '|', '^', '->'}

def propertyBasedConjecture(objects, invariants, mainInvariant, time=5, debug=False, verbose=False, sufficient=True,
                                                   operators=None, theory=None):

    if len(invariants)<2 or len(objects)==0: return
    if not theory: theory=None

    assert 0 <= mainInvariant < len(invariants), 'Illegal value for mainInvariant'

    operatorDict = { '~' : 'U 0', '&' : 'C 0', '|' : 'C 1', '^' : 'C 2', '->' : 'N 0'}

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
    command = 'expressions -pc{}{} --dalmatian {}--time {} --invariant-names --output stack {} --allowed-skips 0'
    command = command.format('v' if verbose and debug else '', 't' if theory is not None else '',
                             '--all-operators ' if operators is None else '',
                             time, '--sufficient' if sufficient else '--necessary')

    if verbose:
        print('Using the following command')
        print(command)

    sp = subprocess.Popen(command, shell=True,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, close_fds=True)
    stdin = sp.stdin

    if operators is not None:
        stdin.write('{}\n'.format(len(operators)))
        for op in operators:
            stdin.write('{}\n'.format(operatorDict[op]))

    stdin.write('{} {} {}\n'.format(len(objects), len(invariants), mainInvariant + 1))

    for invariant in names:
        stdin.write('{}\n'.format(invariant))

    if theory is not None:
        for o in objects:
            if sufficient:
                try:
                    stdin.write('{}\n'.format(max((1 if bool(t(o)) else 0) for t in theory)))
                except:
                    stdin.write('-1\n')
            else:
                try:
                    stdin.write('{}\n'.format(min((1 if bool(t(o)) else 0) for t in theory)))
                except:
                    stdin.write('-1\n')

    for o in objects:
        for invariant in names:
            try:
                stdin.write('{}\n'.format(1 if bool(invariantsDict[invariant](o)) else 0))
            except:
                stdin.write('-1\n')

    if debug:
        for l in sp.stderr:
            print '> ' + l.rstrip()

    # process the output
    out = sp.stdout

    conjectures = []
    inputList = []

    for l in out:
        op = l.strip()
        if op:
            inputList.append(op)
        else:
            conjectures.append(_makePropertyBasedConjecture(inputList, invariantsDict))
            inputList = []

    return conjectures
