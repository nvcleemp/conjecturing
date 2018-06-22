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

    There are at the moment 34 operators available, including, e.g., addition::

        >>> len(allOperators())
        34
        >>> '+' in allOperators()
        True
    """
    return { '-1', '+1', '*2', '/2', '^2', '-()', '1/', 'sqrt', 'ln', 'log10',
       'exp', '10^', 'ceil', 'floor', 'abs', 'sin', 'cos', 'tan', 'asin',
       'acos', 'atan', 'sinh', 'cosh', 'tanh', 'asinh', 'acosh', 'atanh',
       '+', '*', 'max', 'min', '-', '/', '^'}

def conjecture(objects, invariants, mainInvariant, variableName='x', time=5,
               debug=False, verbose=False, upperBound=True, operators=None,
               theory=None, precomputed=None):
    """
    Runs the conjecturing program for invariants with the provided objects,
    invariants and main invariant. This method requires the program ``expressions``
    to be in the current working directory of Sage.

    INPUT:

    -  ``objects`` - a list of objects about which conjectures should be made.
    -  ``invariants`` - a list of functions (callable objects) which take a
       single argument and return a numerical real value. Each function should
       be able to produce a value for each of the elements of objects.
    -  ``mainInvariant`` - an integer that is the index of one of the elements
       of invariants. All conjectures will then be a bound for the invariant that
       corresponds to this index.
    -  ``upperBound`` - if given, this boolean value specifies whether upper or
       lower bounds for the main invariant should be generated. If ``True``,
       then upper bounds are generated. If ``False``, then lower bounds are
       generated. The default value is ``True``
    -  ``time`` - if given, this integer specifies the number of seconds before
       the conjecturing program times out and returns the best conjectures it
       has at that point. The default value is 5.
    -  ``theory`` - if given, specifies a list of known bounds. If this is
       ``None``, then no known bounds are used. Otherwise each conjecture will
       have to be more significant than the bounds in this list. This implies
       that if each object obtains equality for any of the bounds in this list,
       then no conjectures will be made. The default value is ``None``.
    -  ``precomputed`` - if given, specifies a way to obtain precomputed invariant
       values for (some of) the objects. If this is ``None``, then no precomputed
       values are used. If this is a tuple, then it has to have length 3. The
       first element is then a dictionary, the second element is a function that
       returns a key for an object, and the third element is a function that
       returns a key for an invariant. When an invariant value for an object
       needs to be computed it will first be checked whether the key of the
       object is in the dictionary. If it is, then it should be associated with
       a dictionary and it will be checked whether the key of the invariant is
       in that dictionary. If it is, then the associated value will be taken as
       the invariant value, otherwise the invariant value will be computed. If
       ``precomputed`` is not a tuple, it is assumed to be a dictionary, and the
       same procedure as above is used, but the identity is used for both key
       functions.
    -  ``operators`` - if given, specifies a set of operators that can be used.
       If this is ``None``, then all known operators are used. Otherwise only
       the specified operators are used. It is advised to use the method
       ``allOperators()`` to get a set containing all operators and then
       removing the operators which are not needed. The default value is
       ``None``.
    -  ``variableName`` - if given, this name will be used to denote the objects
       in the produced conjectures. The default value is ``'x'``. This option
       only has a cosmetical purpose.
    -  ``debug`` - if given, this boolean value specifies whether the output of
       the program ``expressions`` to ``stderr`` is printed. The default value
       is ``False``.
    -  ``verbose`` - if given, this boolean value specifies whether the program
       ``expressions`` is ran in verbose mode. Note that this has nu purpose if
       ``debug`` is not also set to ``True``. The default value is ``False``.

    EXAMPLES::

    A very simple example defines just two functions that take an integer and
    return an integer, and then generates conjectures for these invariant Using
    the single integer 1. As we are specifying the index of the main invariant
    to be 0, all conjectures will be upper bounds for ``a``::

        >>> def a(n): return n
        >>> def b(n): return n + 1
        >>> conjecture([1], [a,b], 0)
        [a(x) <= b(x) - 1]

    We can also generate lower bound conjectures::

        >>> conjecture([1], [a,b], 0, upperBound=False)
        [a(x) >= b(x) - 1]

    In order to get more nicely printed conjectures, we can change the default
    variable name which is used in the conjectures::

        >>> conjecture([1], [a,b], 0, variableName='n')
        [a(n) <= b(n) - 1]

    Conjectures can be made for any kind of object::

        >>> def max_degree(g): return max(g.degree())
        >>> objects = [graphs.CompleteGraph(i) for i in range(3,6)]
        >>> invariants = [Graph.size, Graph.order, max_degree]
        >>> mainInvariant = invariants.index(Graph.size)
        >>> conjecture(objects, invariants, mainInvariant, variableName='G')
         [size(G) <= 2*order(G),
          size(G) <= max_degree(G)^2 - 1,
          size(G) <= 1/2*max_degree(G)*order(G)]

    In some cases there might be invariants that are slow to calculate for some
    objects. For these cases, the method ``conjecture`` provides a way to specify
    precomputed values for some objects::

        >>> o_key = lambda g: g.canonical_label().graph6_string()
        >>> i_key = lambda f: f.__name__
        >>> objects = [graphs.CompleteGraph(3), graphs.SchlaefliGraph()]
        >>> invariants = [Graph.chromatic_number, Graph.order]
        >>> main_invariant = invariants.index(Graph.chromatic_number)
        >>> precomputed = {o_key(graphs.SchlaefliGraph()) : {i_key(Graph.chromatic_number) : 9}}
        >>> conjecture(objects, invariants, main_invariant, precomputed=(precomputed, o_key, i_key))
        [chromatic_number(x) <= order(x), chromatic_number(x) <= 10^tanh(order(x)) - 1]

    In some cases strange conjectures might be produced or one conjecture you
    might be expecting does not show up. In this case you can use the ``debug``
    and ``verbose`` option to find out what is going on behind the scene. By
    enabling ``debug`` the program prints the reason it stopped generating
    conjectures (time limit, no better conjectures possible, ...) and gives some
    statistics about the number of conjectures it looked at::

        >>> conjecture([1], [a,b], 0, debug=True)
        > Generation process was stopped by the conjecturing heuristic.
        > Found 2 unlabeled trees.
        > Found 2 labeled trees.
        > Found 2 valid expressions.
        [a(x) <= b(x) - 1]

    By also enabling ``verbose``, you can discover which values are actually
    given to the program::

        >>> conjecture([1], [a,b], 0, debug=True, verbose=True)
        >      Invariant  1  Invariant  2
        >   1)    1.000000      2.000000
        > Generating trees with 0 unary nodes and 0 binary nodes.
        > Saving expression
        > a <= b
        > Status: 1 unlabeled tree, 1 labeled tree, 1 expression
        > Generating trees with 1 unary node and 0 binary nodes.
        > Conjecture is more significant for object 1.
        >    2.000000 vs.    1.000000
        > Saving expression
        > a <= (b) - 1
        > Status: 2 unlabeled trees, 2 labeled trees, 2 expressions
        > Generation process was stopped by the conjecturing heuristic.
        > Found 2 unlabeled trees.
        > Found 2 labeled trees.
        > Found 2 valid expressions.
        [a(x) <= b(x) - 1]

    """

    if len(invariants)<2 or len(objects)==0: return
    if not theory: theory=None
    if not precomputed:
        precomputed = None
    elif type(precomputed) == tuple:
        assert len(precomputed) == 3, 'The length of the precomputed tuple should be 3.'
        precomputed, object_key, invariant_key = precomputed
    else:
        object_key = lambda x: x
        invariant_key = lambda x: x

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
    command = './expressions -c{}{} --dalmatian {}--time {} --invariant-names --output stack {} --allowed-skips 0'
    command = command.format('v' if verbose and debug else '', 't' if theory is not None else '',
                             '--all-operators ' if operators is None else '',
                             time, '--leq' if upperBound else '--geq')

    if verbose:
        print('Using the following command')
        print(command)

    import subprocess
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

    def get_value(invariant, o):
        precomputed_value = None
        if precomputed:
            o_key = object_key(o)
            i_key = invariant_key(invariant)
            if o_key in precomputed:
                if i_key in precomputed[o_key]:
                    precomputed_value = precomputed[o_key][i_key]
        if precomputed_value is None:
            return invariant(o)
        else:
            return precomputed_value

    if theory is not None:
        if verbose:
            print "Started writing theory to expressions"
        for o in objects:
            if upperBound:
                try:
                    stdin.write('{}\n'.format(min(float(get_value(t, o)) for t in theory)))
                except:
                    stdin.write('NaN\n')
            else:
                try:
                    stdin.write('{}\n'.format(max(float(get_value(t, o)) for t in theory)))
                except:
                    stdin.write('NaN\n')
        if verbose:
            print "Finished writing theory to expressions"

    if verbose:
        print "Started computing and writing invariant values to expressions"

    for o in objects:
        for invariant in names:
            try:
                stdin.write('{}\n'.format(float(get_value(invariantsDict[invariant], o))))
            except:
                stdin.write('NaN\n')

    if verbose:
        print "Finished computing and writing invariant values to expressions"

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

    if verbose:
        print "Finished conjecturing"

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

    There are at the moment 5 operators available, including, e.g., AND::

        >>> len(allPropertyBasedOperators())
        5
        >>> '&' in allPropertyBasedOperators()
        True
    """
    return { '~', '&', '|', '^', '->'}

def propertyBasedConjecture(objects, properties, mainProperty, time=5, debug=False,
                            verbose=False, sufficient=True, operators=None,
                            theory=None, precomputed=None):
    """
    Runs the conjecturing program for properties with the provided objects,
    properties and main property. This method requires the program ``expressions``
    to be in the current working directory of Sage.

    INPUT:

    -  ``objects`` - a list of objects about which conjectures should be made.
    -  ``properties`` - a list of functions (callable objects) which take a
       single argument and return a boolean value. Each function should
       be able to produce a value for each of the elements of objects.
    -  ``mainProperty`` - an integer that is the index of one of the elements
       of properties. All conjectures will then be a bound for the property that
       corresponds to this index.
    -  ``sufficient`` - if given, this boolean value specifies whether sufficient
       or necessary conditions for the main property should be generated. If
       ``True``, then sufficient conditions are generated. If ``False``, then
       necessary conditions are generated. The default value is ``True``
    -  ``time`` - if given, this integer specifies the number of seconds before
       the conjecturing program times out and returns the best conjectures it
       has at that point. The default value is 5.
    -  ``theory`` - if given, specifies a list of known bounds. If this is
       ``None``, then no known bounds are used. Otherwise each conjecture will
       have to be more significant than the conditions in this list. The default
       value is ``None``.
    -  ``operators`` - if given, specifies a set of operators that can be used.
       If this is ``None``, then all known operators are used. Otherwise only
       the specified operators are used. It is advised to use the method
       ``allPropertyBasedOperators()`` to get a set containing all operators and
       then removing the operators which are not needed. The default value is
       ``None``.
    -  ``debug`` - if given, this boolean value specifies whether the output of
       the program ``expressions`` to ``stderr`` is printed. The default value
       is ``False``.
    -  ``verbose`` - if given, this boolean value specifies whether the program
       ``expressions`` is ran in verbose mode. Note that this has nu purpose if
       ``debug`` is not also set to ``True``. The default value is ``False``.

    EXAMPLES::

    A very simple example uses just two properties of integers and generates
    sufficient conditions for an integer to be prime based on the integer 3::

        >>> propertyBasedConjecture([3], [is_prime,is_even], 0)
        [(~(is_even))->(is_prime)]

    We can also generate necessary condition conjectures::

        >>> propertyBasedConjecture([3], [is_prime,is_even], 0, sufficient=False)
        [(is_prime)->(~(is_even))]

    In some cases strange conjectures might be produced or one conjecture you
    might be expecting does not show up. In this case you can use the ``debug``
    and ``verbose`` option to find out what is going on behind the scene. By
    enabling ``debug`` the program prints the reason it stopped generating
    conjectures (time limit, no better conjectures possible, ...) and gives some
    statistics about the number of conjectures it looked at::

        >>> propertyBasedConjecture([3], [is_prime,is_even], 0, debug=True)
        > Generation process was stopped by the conjecturing heuristic.
        > Found 2 unlabeled trees.
        > Found 2 labeled trees.
        > Found 2 valid expressions.
        [(~(is_even))->(is_prime)]

    By also enabling ``verbose``, you can discover which values are actually
    given to the program::

        >>> propertyBasedConjecture([3], [is_prime,is_even], 0, debug=True, verbose=True)
        Using the following command
        ./expressions -pcv --dalmatian --all-operators --time 5 --invariant-names --output stack --sufficient --allowed-skips 0
        >      Invariant  1  Invariant  2
        >   1)    TRUE          FALSE
        > Generating trees with 0 unary nodes and 0 binary nodes.
        > Saving expression
        > is_prime <- is_even
        > Status: 1 unlabeled tree, 1 labeled tree, 1 expression
        > Generating trees with 1 unary node and 0 binary nodes.
        > Conjecture is more significant for object 1.
        > Saving expression
        > is_prime <- ~(is_even)
        > Conjecture 2 is more significant for object 1.
        > Status: 2 unlabeled trees, 2 labeled trees, 2 expressions
        > Generation process was stopped by the conjecturing heuristic.
        > Found 2 unlabeled trees.
        > Found 2 labeled trees.
        > Found 2 valid expressions.
        [(~(is_even))->(is_prime)]
    """

    if len(properties)<2 or len(objects)==0: return
    if not theory: theory=None
    if not precomputed:
        precomputed = None
    elif type(precomputed) == tuple:
        assert len(precomputed) == 3, 'The length of the precomputed tuple should be 3.'
        precomputed, object_key, invariant_key = precomputed
    else:
        object_key = lambda x: x
        invariant_key = lambda x: x

    assert 0 <= mainProperty < len(properties), 'Illegal value for mainProperty'

    operatorDict = { '~' : 'U 0', '&' : 'C 0', '|' : 'C 1', '^' : 'C 2', '->' : 'N 0'}

    # prepare the invariants to be used in conjecturing
    propertiesDict = {}
    names = []

    for pos, property in enumerate(properties):
        if type(property) == tuple:
            name, property = property
        elif hasattr(property, '__name__'):
            if property.__name__ in propertiesDict:
                name = '{}_{}'.format(property.__name__, pos)
            else:
                name = property.__name__
        else:
            name = 'property_{}'.format(pos)
        propertiesDict[name] = property
        names.append(name)

    # call the conjecturing program
    command = './expressions -pc{}{} --dalmatian {}--time {} --invariant-names --output stack {} --allowed-skips 0'
    command = command.format('v' if verbose and debug else '', 't' if theory is not None else '',
                             '--all-operators ' if operators is None else '',
                             time, '--sufficient' if sufficient else '--necessary')

    if verbose:
        print('Using the following command')
        print(command)

    import subprocess
    sp = subprocess.Popen(command, shell=True,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, close_fds=True)
    stdin = sp.stdin

    if operators is not None:
        stdin.write('{}\n'.format(len(operators)))
        for op in operators:
            stdin.write('{}\n'.format(operatorDict[op]))

    stdin.write('{} {} {}\n'.format(len(objects), len(properties), mainProperty + 1))

    for property in names:
        stdin.write('{}\n'.format(property))

    def get_value(prop, o):
        precomputed_value = None
        if precomputed:
            o_key = object_key(o)
            p_key = invariant_key(prop)
            if o_key in precomputed:
                if p_key in precomputed[o_key]:
                    precomputed_value = precomputed[o_key][p_key]
        if precomputed_value is None:
            return prop(o)
        else:
            return precomputed_value

    if theory is not None:
        if verbose:
            print "Started writing theory to expressions"
        for o in objects:
            if sufficient:
                try:
                    stdin.write('{}\n'.format(max((1 if bool(get_value(t, o)) else 0) for t in theory)))
                except:
                    stdin.write('-1\n')
            else:
                try:
                    stdin.write('{}\n'.format(min((1 if bool(get_value(t, o)) else 0) for t in theory)))
                except:
                    stdin.write('-1\n')
        if verbose:
            print "Finished writing theory to expressions"

    if verbose:
        print "Started computing and writing property values to expressions"

    for o in objects:
        for property in names:
            try:
                stdin.write('{}\n'.format(1 if bool(get_value(propertiesDict[property], o)) else 0))
            except:
                stdin.write('-1\n')

    if verbose:
        print "Finished computing and writing property values to expressions"

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
            conjectures.append(_makePropertyBasedConjecture(inputList, propertiesDict))
            inputList = []

    if verbose:
        print "Finished conjecturing"

    return conjectures
