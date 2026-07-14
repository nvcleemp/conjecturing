import sys
sys.path.append(".") 

import numpy as np
from sympy import *
from sympy.core.relational import Relational
import types
import re
import warnings
import pandas as pd
import pulp    #for ip for dalmatian optimal subsetting 
import math
from itertools import combinations


def create_dummies(my_data, categorical_names, nan_is_level=True):
    # Counts the number of unique values for each 
    # categorical variable and creates a dummy variable for each, 
    # unless there are two, in which case one dummy variable is 
    # created.
    # 
    # It also names the target variable TARGET and, for a categorical
    # target, creates values TARGET_<value>.  If there are two levels
    # for target, only one TARGET_<value> is created 
    # 
    # Returns the new data frame, target property names, and property
    # names (the lists are empty if the target is an invariant).
    #
    # The option nan_is_level=True creates a dummy variable for 
    # missing values.

    property_names = []
    target_property_names = []
    for col in categorical_names:
        if col != "TARGET":
            if nan_is_level:
                unique_vals=list(my_data[col].unique())  # if nan is a level
            else:
                unique_vals=list(my_data[col].dropna().unique())  # if nan is not a level
            if len(unique_vals)==2: # just use one level for binary features
                property_names.append(col+"_"+str(unique_vals[1]))
            elif len(unique_vals) > 2: #one property for each level.
                for level in unique_vals:
                    property_names.append(col+"_"+str(level))
    
    
    if "TARGET" in categorical_names:
        if nan_is_level:
            unique_vals = list(my_data["TARGET"].unique()) # if nan is a level
        else:
            unique_vals = list(my_data["TARGET"].dropna().unique()) # if nan is not a level
        if len(unique_vals)==2:
            target_property_names.append("TARGET_"+str(unique_vals[1]))
        elif len(unique_vals) > 2:
            for level in unique_vals:
                target_property_names.append("TARGET_"+str(level))
                
    my_df = pd.get_dummies(my_data, 
                           columns=categorical_names,
                           dtype=np.uint8,
                           dummy_na=nan_is_level,  # False is the default.  If False, use dropna() above
                           drop_first=False) # False is the default
    
    my_df = my_df.rename(lambda col: col.replace('.0', ''), axis='columns')
    return (my_df, property_names, target_property_names)

def create_example_class(my_df, invariant_names, property_names, categorical_names,
                         target_property_names):
    # Creates the Example class with a method/attribute for each
    # invariant and property, including the target (levels).
    #
    # returns the Example class

    class Example():
        def __init__(self, name, my_df):
            self.name = name
            self.my_df = my_df
            
    for i in invariant_names:
        inv = build_inv(i)
        setattr(Example,inv.__name__,inv )
    
    for i in property_names:
        prop = build_prop(i)
        setattr(Example, prop.__name__,prop)
    
    if "TARGET" in categorical_names:
        for i in target_property_names:
            prop = build_prop(i)
            setattr(Example, prop.__name__, prop)
    else:
        target_invariant = invariant_names.index("TARGET")
        setattr(Example, "target_invariant", target_invariant)
    return Example

def get_invariants_properties(Example, invariant_names, 
                              property_names, categorical_names, 
                              target_property_names):
    # Returns the lists of invariant, property, and target_property
    # functions.

    invariants =[]
    for i in invariant_names:
        invariants.append(Example.__dict__[i])
    properties=[]
    for i in property_names:
        properties.append(Example.__dict__[i])
    target_properties=[]
    if "TARGET" in categorical_names:
        for i in target_property_names:
            target_properties.append(Example.__dict__[i])

    return(invariants, properties, target_properties)

def invariant_conjecturing(Example, train_examples, categorical_names, 
                           target_property_names, invariants, 
                           use_operators, my_complexity, my_time, 
                           my_skips, inv_file, debug=False, 
                           verbose=False, notebook_path = "./", 
                           output_path="./", heuristic='dalmatian',
                           params=None):

    inv_conjectures = []
    if "TARGET" in categorical_names:
        for value in target_property_names:
            print(value)
            target_property = Example.__dict__[value]
            my_examples = [example for example in train_examples if target_property(example) == True]
            for inv in invariants:
                print(invariants.index(inv), end=" ")
                sys.stdout.flush()
                inv_of_interest = invariants.index(inv)
                conjs = conjecture(my_examples, 
                                   invariants, 
                                   inv_of_interest, 
                                   operators=use_operators, 
                                   upperBound=True, 
                                   time=my_time,
                                   complexity_limit=my_complexity,
                                   debug=debug,
                                   verbose=verbose,
                                   skips=my_skips,
                                   notebook_path=notebook_path,
                                   heuristic=heuristic,
                                   params=params)
                #convert_conjecture_names(conjs)
                inv_conjectures += conjs
    
                conjs = conjecture(my_examples, 
                                   invariants, 
                                   inv_of_interest, 
                                   operators=use_operators, 
                                   upperBound=False, 
                                   time=my_time,
                                   complexity_limit=my_complexity,
                                   debug=debug,
                                   verbose=verbose,
                                   skips=my_skips,
                                   notebook_path=notebook_path,
                                   heuristic=heuristic,
                                   params=params)
                #convert_conjecture_names(conjs)
                inv_conjectures += conjs
        print("\nnumber of conjectures", len(inv_conjectures))
        if len(target_property_names) == 1:
            value = target_property_names[0]
            print(value + " False")
            target_property = Example.__dict__[value]
            my_examples = [example for example in train_examples if target_property(example) == False]
            for inv in invariants:
                print(invariants.index(inv), end=" ")
                sys.stdout.flush()
                inv_of_interest = invariants.index(inv)
                conjs = conjecture(my_examples, 
                                   invariants, 
                                   inv_of_interest, 
                                   operators=use_operators, 
                                   upperBound=True, 
                                   time=my_time,
                                   complexity_limit=my_complexity,
                                   debug=debug,
                                   verbose=verbose,
                                   skips=my_skips,
                                   notebook_path=notebook_path,
                                   heuristic=heuristic,
                                   params=params)
                #convert_conjecture_names(conjs)
                inv_conjectures += conjs
    
                conjs = conjecture(my_examples, 
                                   invariants, 
                                   inv_of_interest, 
                                   operators=use_operators, 
                                   upperBound=False, 
                                   time=my_time,
                                   complexity_limit=my_complexity,
                                   debug=debug,
                                   verbose=verbose,
                                   skips=my_skips,
                                   notebook_path=notebook_path,
                                   heuristic=heuristic,
                                   params=params)
                #convert_conjecture_names(conjs)
                inv_conjectures += conjs
    else: # target is an invariant
        my_examples = [example for example in train_examples]
        target_invariant = Example.target_invariant
        conjs = conjecture(my_examples, 
                           invariants, 
                           target_invariant, 
                           operators=use_operators, 
                           upperBound=True, 
                           time=my_time,
                           complexity_limit=my_complexity,
                           debug=debug,
                           verbose=verbose,
                           skips=my_skips,
                           notebook_path=notebook_path,
                           heuristic=heuristic,
                           params=params)
        #convert_conjecture_names(conjs)
        inv_conjectures += conjs
        conjs = conjecture(my_examples, 
                           invariants, 
                           target_invariant, 
                           operators=use_operators,
                           upperBound=False, 
                           time=my_time,
                           complexity_limit=my_complexity,
                           debug=debug,
                           verbose=verbose,
                           skips=my_skips,
                           notebook_path=notebook_path,
                           heuristic=heuristic,
                           params=params)
        inv_conjectures += conjs     
    print("\nnumber of conjectures", len(inv_conjectures))  
    
    for c in inv_conjectures:
        inv_file.write("%s\n" % c.__name__)
        inv_file.flush()

    return inv_conjectures

def property_conjecturing(Example, properties, inv_conjectures, 
                          categorical_names, target_property_names,
                          train_examples, my_complexity, my_time, my_skips, 
                          prop_file, verbose=False, debug=False, 
                          notebook_path="./"):

    all_properties = ["TARGET"] + properties + inv_conjectures #"TARGET" is just a placeholder
    prop_conjs = []
    conditions = {}
    if "TARGET" in categorical_names:
        for value in target_property_names:
            print(value)
            all_properties[0] = Example.__dict__[value]
            these_prop_conjs = propertyBasedConjecture(objects=train_examples, 
                                               properties = all_properties,
                                               mainProperty=0,
                                               complexity_limit=my_complexity,
                                               time=my_time,
                                               verbose=verbose,
                                               debug=debug,
                                               skips=my_skips,
                                               notebook_path=notebook_path)
            conditions[value] = []
            for c in these_prop_conjs: 
                conditions[value].append(get_premise(c, myprint=False))
            prop_conjs += these_prop_conjs
        if len(target_property_names) == 1:
            print(value + " Necessary")
            all_properties[0] = Example.__dict__[value]
            these_prop_conjs = propertyBasedConjecture(objects=train_examples,  
                                               properties = all_properties,
                                               mainProperty=0,
                                               sufficient=False,
                                               complexity_limit=my_complexity,
                                               time=my_time,
                                               verbose=verbose,
                                               debug=debug,
                                               skips=my_skips,
                                               notebook_path=notebook_path)
            conditions["necessary"] = []
            for c in these_prop_conjs:
                conditions["necessary"].append(get_conclusion(c, myprint=False))
            prop_conjs += these_prop_conjs  
    
    for c in prop_conjs:
        prop_file.write("%s\n" % c.__name__)
        prop_file.flush()

    return (prop_conjs, conditions)

def apply_property_conjectures(my_data, my_df, X_train, X_test, 
                               property_names, invariant_names, 
                               categorical_names, 
                               target_property_names, conditions,
                               train_examples, test_examples):

    # Applies the property conjectures to the training and testing 
    # data frames and creates new columns with values.

    X_train_df = my_df.loc[X_train,property_names+invariant_names]  # drop target and one level for each binary variable
    X_test_df = my_df.loc[X_test,property_names+invariant_names]
    y_train_df = my_data.loc[X_train,"TARGET"] # get original target, even if it is multiple levels
    y_test_df = my_data.loc[X_test, "TARGET"]
    if "TARGET" in categorical_names:
        index = 0
        for value in target_property_names:
            for condition in conditions[value]:
                index += 1
                X_train_df['conj_' + str(index)] = [condition(example) for example in train_examples]
                X_test_df['conj_' + str(index)] = [condition(example) for example in test_examples]
        if len(target_property_names) == 1:
            for condition in conditions["necessary"]:
                index += 1
                X_train_df['conj_' + str(index)] = [condition(example) for example in train_examples]
                X_test_df['conj_' + str(index)] = [condition(example) for example in test_examples]
            
    for value in target_property_names:
        this_value = value.replace("TARGET_", "")
    return (X_train_df, X_test_df, y_train_df, y_test_df)

def evaluate_property_conjectures(categorical_names, 
                                  target_property_names, Example,
                                  conditions, test_examples, 
                                  y_test_df):
    support = []
    lift = []
    precision = []
    recall = []
    f1 = []
    mcc = []
    classes = []
    if "TARGET" in categorical_names:
        for value in target_property_names:
            this_value = value.replace("TARGET_", "")
            my_function = getattr(Example, value)
            for i, condition in enumerate(conditions[value]):
                classes.append(value)
                num_true = 0
                num_in_class = 0
                num_hit = 0
                for example in test_examples:
                    if condition(example) == True:
                        num_true += 1  # TP + FP
                        if my_function(example) == True:
                            num_hit += 1 # TP
                    if my_function(example) == True:
                        num_in_class += 1 # TP + FN
                support.append(num_true)
                FP = num_true - num_hit
                FN = num_in_class - num_hit
                TP = num_hit
                TN = len(test_examples)-FP-FN-TP
                if (TP+FP>0) and (TP+FN>0) and (TN+FP>0) and (TN+FN>0):
                    mcc.append((TP*TN - FP*FN)/math.sqrt((TP+FP)*(TP+FN)*(TN+FP)*(TN+FN)))
                else:
                    mcc.append(0.0)
                if num_hit > 0: 
                    precision.append(num_hit/num_true)
                    lift.append((num_hit/num_true)/(num_in_class/len(test_examples)))
                    recall.append(num_hit/num_in_class)
                    my_precision = num_hit/num_true
                    my_recall = num_hit/num_in_class
                    f1.append((2*my_precision*my_recall)/(my_precision + my_recall))
                else:
                    precision.append(0.0)
                    lift.append(0.0)
                    recall.append(0.0)
                    f1.append(0.0)
        if len(target_property_names) == 1:
            for i, condition in enumerate(conditions["necessary"]):
                classes.append("necessary")
                num_false = 0
                num_in_class = 0
                num_hit = 0
                for example in test_examples:
                    if condition(example) == False:
                        num_false += 1 # TN + FN
                        if my_function(example) == False:
                            num_hit += 1 # TN
                    if my_function(example) == False:
                        num_in_class += 1  # TN + FP
                support.append(num_false)
                TN = num_hit
                FN = num_false - num_hit
                FP = num_in_class - num_hit
                TP = len(test_examples)-TN-FN-FP
                if (TP+FP>0) and (TP+FN>0) and (TN+FP>0) and (TN+FN>0):
                    mcc.append((TP*TN - FP*FN)/math.sqrt((TP+FP)*(TP+FN)*(TN+FP)*(TN+FN)))
                else:
                    mcc.append(0.0)
                if num_hit > 0: 
                    precision.append(num_hit/num_false)
                    lift.append((num_hit/num_false)/(num_in_class/len(test_examples)))
                    recall.append(num_hit/num_in_class)
                    my_precision = num_hit/num_false
                    my_recall = num_hit/num_in_class
                    f1.append((2*my_precision*my_recall)/(my_precision + my_recall))
                else:
                    precision.append(0.0)
                    lift.append(0.0)
                    recall.append(0.0)
                    f1.append(0.0)
                
    results_df = pd.DataFrame({
        'class': classes,
        'support':support, 
        'precision':precision, 
        'recall': recall, 
        'lift':lift, 
        'f1': f1,
        'mcc': mcc})
    return results_df

def evaluate_invariant_conjectures(Example, inv_conjectures, 
                                   test_examples):
    errors = []
    expressions = []
    for c in inv_conjectures:
        expressions.append(c.expression)
        try:
            error = np.mean([abs(example.TARGET() - c.evaluate(example, returnBoundValue=True)) for example in test_examples])
            errors.append(error)
        except:
            errors.append(pd.NA)
    results_df = pd.DataFrame({
        'expression': expressions,
        'MAE': errors})
    return results_df

# Creates invariant functions.
# pass the index (row name) and the data frame
# requires that the init function for the example class looks like:
# def __init__(self, name, my_df):
    #        self.name = name
    #        self.my_df = my_df
def build_inv(i):
    def inv(self):
        return self.my_df.loc[self.name][i]
    inv.__name__ = i
    return inv


#this function creates property functions
def build_prop(i):
    def prop(self):
        if float(self.my_df.loc[self.name][i]) == 1.0:
            return True
        return False
    prop.__name__ = i
    return prop



def convert_name(name):
    for i in range(26):
        name = name.replace('({})'.format(chr(ord('a') + i)), '')
    name = name.replace(' ', '_')
    textform_first = {
        '^2': '_squared',
        '^3': '_cubed',
        '1/': 'inverse_of_',
        '<=': '_leq_',
        '>=': '_geq_'
    }
    textform = {
        '<': '_lt_',
        '>': '_gt_',
        '+': '_plus_',
        '-': '_minus_',
        '*': '_times_',
        '/': '_divided_by_',
        '^': '_to_the_power_',
        '(': 'open_bracket_',
        ')': '_close_bracket',
        ',': '_or_', # added by Paul
        '\'': '', # added by Paul
        '=': '_equal_' # added by Paul
               }
    for op in textform_first:
        name = name.replace(op, textform_first[op])
    for op in textform:
        name = name.replace(op, textform[op])
    return name

def convert_name_back(name):
    for i in range(26):
        name = name.replace('({})'.format(chr(ord('a') + i)), '')
    # name = name.replace('_', ' ')
    textform_first = {
        '_squared': '^2',
        '_cubed': '^3',
        'inverse_of_': '1/',
         '_leq_': '<=',
         '_geq_': '>='
    }
    textform = {
        '_lt_': '<',
        '_gt_': '>',
        '_plus_': '+',
        '_minus_': '-',
        '_times_': '*',
        '_divided_by_': '/',
        '_to_the_power_': '^',
        'open_bracket_': '(',
        '_close_bracket': ')',
        '_or_': ',', # added by Paul
        '_equal_': '=' # added by Paul
               }
    for op in textform_first:
        name = name.replace(op, textform_first[op])
    for op in textform:
        name = name.replace(op, textform[op])
    return name

def convert_conjecture_names(conjectures):
    for conj in conjectures:
        conj.__name__ = convert_name(conj.__name__)

def convert_names_back(conjectures): #note the plural name(s)
    for conj in conjectures:
        conj.__name__ = convert_name_back(conj.__name__)

#class Conjecture(SageObject): #Based on GraphExpression from IndependenceNumberProject
class Conjecture(): #Based on GraphExpression from IndependenceNumberProject

    def __init__(self, stack, expression, pickling, sym_list, my_lambda, my_lambda_rhs):
        # not using stack or pickling.
        # expression has the expression in text
        # sym_list is the number of invariants
        """Constructs a new Conjecture from the given stack of functions."""
        self.stack = stack
        self.expression = expression
        self.pickling = pickling
        #self.__name__ = ''.join(c for c in repr(self.expression) if c != ' ')
        self.__name__ = expression
        self.sym_list = sym_list
        self.my_lambda = my_lambda
        self.my_lambda_rhs = my_lambda_rhs
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
        try:
            expr_values = tuple(getattr(g, i)() for i in self.sym_list)
            with warnings.catch_warnings(record=True) as w:
                warnings.simplefilter("always")
                if returnBoundValue:
                    my_value = self.my_lambda_rhs(*expr_values)
                    if w:
                        return float("NaN")
                    return my_value
                my_value = self.my_lambda(*expr_values)
                if w:
                    return float("NaN")
                return my_value
        except:
            return float("NaN")
        return float("NaN")

        ## a slow way of doing it, using sympy
        ## list of invariants in the conjecture
        #sym_vars = symbols((" ").join(self.sym_list))
        ## make the conjecture an expression
        #sym_expr = sympify(self.expression)
        # get the example values to substitute
        #expr_values = [(i, getattr(g, i)()) for i in self.sym_list]
        #expr_values = {i: getattr(g, i)() for i in self.sym_list}
        ## sub the values
        #try:
        #    sol_expr = sym_expr.subs(expr_values)
        #    if returnBoundValue: # only get the RHS of the bound
        #        my_rhs = sym_expr.rhs
        #        # numerically evaluate the RHS with the values
        #        return my_rhs.subs(expr_values).evalf()
        #    # return whether it is satisfied (True) or not
        #    return sol_expr
        #except:
        #    return "undefined"
    def simplify_conjecture(self):
        try:
            my_lhs = sympify(self.expression).lhs
            simp_expr = simplify(self.expression)
            simp_rel = str(reduce_inequalities(simp_expr, my_lhs))
            and_index = simp_rel.find("&")
            simp_rel = simp_rel[(and_index+1):]
            simp_rel = simp_rel.strip()
            simp_rel = simp_rel.strip("(")
            simp_rel = simp_rel.strip(")")
            return simp_rel
        except:
            return self.__name__
        return self.__name__

def wrapUnboundMethod(op, invariantsDict):
    return lambda obj: getattr(obj, invariantsDict[op].__name__)()

def wrapBoundMethod(op, invariantsDict):
    return lambda obj: invariantsDict[op](obj)

def _makeConjecture(inputList, variable, invariantsDict):
    import operator

    pre_specials = ['-()', '1/', '10**']
    post_specials = ['-1', '+1', '*2', '/2', '**2']
    two_specials = ["max", "min"]
   

    # only the keys of the dictionaries are used now
    unaryOperators = ['sqrt', 'ln', 'exp', 'ceil', 'floor',
                      'abs', 'sin','cos', 'tan', 'asin',
                      'acos', 'atan', 'sinh', 'cosh',
                      'tanh', 'asinh', 'acosh', 'atanh', 'log10']
    binaryOperators = ['+', '*', '-', '/', '^']
    comparators = ['<', '<=', '>', '>=']
    expressionStack = []
    operatorStack = []

    sym_list = []
    for op in inputList:
        if op != "^":
            op = op.replace("^", "**")
        #op = op.replace("-()", "-")
        if op in invariantsDict:
            expressionStack.append(op)
            sym_list.append(op)
            operatorStack.append((op, 0))
        elif op in pre_specials:
            if op == '-()':
                op = "-"
            expressionStack.append("(" + op + "(" + expressionStack.pop() + "))")
            operatorStack.append((op, 1))
        elif op in post_specials:
            expressionStack.append("((" + expressionStack.pop() + ")" + op + ")")
            operatorStack.append((op, 1))
        elif op in two_specials:
            right = expressionStack.pop()
            left = expressionStack.pop()
            expressionStack.append(op+"("+left + "," + right + ")")
            operatorStack.append((op, 2))
        elif op in unaryOperators:
            new_exp = expressionStack.pop()
            if op == 'log10':
                new_exp = 'log(' + new_exp + ', 10)' 
            elif op == 'ceil':
                new_exp = 'ceiling(' + new_exp + ')'
            elif op == 'abs':
                new_exp = 'Abs(' + new_exp + ')'
            else:
                new_exp = op + '('+new_exp+')'
            expressionStack.append(new_exp)
            operatorStack.append((op, 1))
        elif op in binaryOperators:
            right = expressionStack.pop()
            left = expressionStack.pop()
            expressionStack.append("("+ left + op + right + ")")
            operatorStack.append((op, 2))
        elif op in comparators:
            right = expressionStack.pop()
            left = expressionStack.pop()
            expressionStack.append(left + op + right)
            operatorStack.append((op, 2))
        else:
            raise ValueError("Error while reading output from expressions. Unknown element: {}".format(op))

    sym_vars = symbols((" ").join(sym_list))
    my_expression = expressionStack.pop()
    try: 
        sym_expr = sympify(my_expression)
        my_lambda = lambdify(sym_vars, sym_expr)
        my_rhs = sym_expr.rhs
        my_lambda_rhs = lambdify(sym_vars, my_rhs)
    except: 
        return None

    return Conjecture(operatorStack, my_expression, (inputList, variable, invariantsDict), sym_list, my_lambda, my_lambda_rhs)

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
    return [ '-1', '+1', '*2', '/2', '^2', '-()', '1/', 'sqrt', 'ln', 'log10',
       'exp', '10^', 'ceil', 'floor', 'abs', 'sin', 'cos', 'tan', 'asin',
       'acos', 'atan', 'sinh', 'cosh', 'tanh', 'asinh', 'acosh', 'atanh',
       '+', '*', 'max', 'min', '-', '/', '^']

def conjecture(objects, invariants, mainInvariant, variableName='x', time=5,
               debug=False, verbose=False, upperBound=True, operators=None,
               theory=None, precomputed=None, skips=0.0, complexity_limit=11, 
               notebook_path='./', heuristic='dalmatian', params=None):
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
    - ``skips`` - 
    - ``complexity_limit`` - maximum complexity of expressions explored.  
      2xbinary + unary operators.
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
    VALID_HEURISTICS = {
        "dalmatian": "--dalmatian",
        "sam": "--sam",
        "rl": "--rl"
    }
    
    try:
        heuristic_flag = VALID_HEURISTICS[heuristic.lower()]
    except KeyError:
        raise ValueError(f"Unknown heuristic: {heuristic}")
        
    param_flags = ""

    if params:
        for key, value in params.items():
            if value is None:
                continue
    
            # Convert Python-style names to CLI-style
            cli_key = key.replace("_", "-")
    
            param_flags += f" --{cli_key} {value}"

    # call the conjecturing program
    command = (
            notebook_path + 'expressions -c{}{} {} {} --time {} '
            '--invariant-names --output stack {} '
            '--allowed-skips {} --maximum-complexity '
            '--complexity-limit {}{}' 
    )
    command = command.format(
        'v' if verbose and debug else '',
        't' if theory is not None else '',
        heuristic_flag,
        '--all-operators ' if operators is None else '',
        time,
        '--leq' if upperBound else '--geq',
        skips,
        complexity_limit,
        param_flags
    )

    if verbose:
        print('Using the following command')
        print(command)

    import subprocess
    sp = subprocess.Popen(command, shell=True,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, close_fds=True,
                          encoding='utf-8')
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
            print("Started writing theory to expressions")
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
            print("Finished writing theory to expressions")

    if verbose:
        print("Started computing and writing invariant values to expressions")

    def format_value(invariant,o):
        try:
            return format(float(get_value(invariantsDict[invariant], o)))
        except:
            return 'NaN'

    values = [format_value(invariant, o) for o in objects for invariant in names]
 
    stdin.write('\n'.join(values)+'\n')
    stdin.flush()

    if verbose:
        print("Finished computing and writing invariant values to expressions")

    if debug:
        for l in sp.stderr:
            print('> ' + l.rstrip())

    # process the output
    out = sp.stdout

    variable = variableName

    conjectures = []
    inputList = []

    for l in out:
        op = l.strip()
        if op:
            inputList.append(op)
        else:
            this_conjecture = _makeConjecture(inputList, variable, invariantsDict)
            if this_conjecture is not None:
                conjectures.append(this_conjecture)
            inputList = []

    if verbose:
        print("Finished conjecturing")

    return conjectures

class PropertyBasedConjecture():

    def __init__(self, expression, propertyCalculators, pickling):
        """Constructs a new Conjecture from the given stack of functions."""
        self.expression = expression
        self.propertyCalculators = propertyCalculators
        self.pickling = pickling
        self.inputList = pickling[0]
        self.propertiesDict = pickling[1]
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
        binaryOperators = {'&', '|', '^', '->'}

        expressionStack = []
        for op in self.inputList:
            if op in self.propertiesDict:
                prop = ''.join([l for l in op if l.strip()])
                expressionStack.append("true" if self.propertyCalculators[prop](g) else "false")
            elif op == '<-':
                right = expressionStack.pop()
                left = expressionStack.pop()
                expressionStack.append('({})>>({})'.format(right, left))
            elif op == '->':
                right = expressionStack.pop()
                left = expressionStack.pop()
                expressionStack.append('({})>>({})'.format(left, right))
            elif op == '~':
                expressionStack.append('~({})'.format(expressionStack.pop()))
            elif op == '^':
                right = expressionStack.pop()
                left = expressionStack.pop()
                expressionStack.append('Xor({},{})'.format(left, right))
            elif op in binaryOperators:
                right = expressionStack.pop()
                left = expressionStack.pop()
                expressionStack.append('({}){}({})'.format(left, op, right))
            else:
                raise ValueError("Error while reading output from expressions. Unknown element: {}".format(op))

        my_expression = expressionStack.pop()
        sym_expr = sympify(my_expression, locals={"Xor": Xor})
        my_value = sym_expr.simplify()
        return my_value

class PropertyBasedExpression():

    def __init__(self, expression, propertyCalculators, pickling):
        """Constructs a new property based expression."""
        self.expression = expression
        self.propertyCalculators = propertyCalculators
        self.inputList = pickling[0]
        self.propertiesDict = pickling[1]
        self.__name__ = repr(self.expression)
        super(PropertyBasedExpression, self).__init__()

    def __eq__(self, other):
        return self.expression == other.expression

    def _repr_(self):
        return repr(self.expression)

    def _latex_(self):
        return latex(self.expression)

    def __call__(self, g):
        return self.evaluate(g)

    def evaluate(self, g):
        binaryOperators = {'&', '|', '^', '->'}

        expressionStack = []
        for op in self.inputList:
            if op in self.propertiesDict:
                prop = ''.join([l for l in op if l.strip()])
                expressionStack.append("true" if self.propertyCalculators[prop](g) else "false")
            elif op == '<-':
                right = expressionStack.pop()
                left = expressionStack.pop()
                expressionStack.append('({})>>({})'.format(right, left))
            elif op == '->':
                right = expressionStack.pop()
                left = expressionStack.pop()
                expressionStack.append('({})>>({})'.format(left, right))
            elif op == '~':
                expressionStack.append('~({})'.format(expressionStack.pop()))
            elif op == '^':
                right = expressionStack.pop()
                left = expressionStack.pop()
                expressionStack.append('Xor({},{})'.format(left, right))
            elif op in binaryOperators:
                right = expressionStack.pop()
                left = expressionStack.pop()
                expressionStack.append('({}){}({})'.format(left, op, right))

            else:
                raise ValueError("Error while reading output from expressions. Unknown element: {}".format(op))

        my_expression = expressionStack.pop()
        sym_expr = sympify(my_expression, locals={"Xor": Xor})
        my_value = sym_expr.simplify()
        return my_value

def get_premise(conjecture, myprint=True):
    assert "->" in conjecture.expression, 'Not an implication'

    inputList = list(conjecture.inputList)
    inputList = inputList[1:-1]
    conjecture.expression = conjecture.expression.replace("->", ">>")
    n_pattern = r"^\((TARGET.*?)\)>>"
    n_match = re.search(n_pattern, conjecture.expression)
    if n_match:
        my_premise = n_match.group(1)
        my_calc = {n_match.group(1): conjecture.propertyCalculators[n_match.group(1)]}
    else:
        s_pattern = r">>\((TARGET.*?)\)$"
        s_match = re.search(s_pattern, conjecture.expression)
        my_premise = conjecture.expression[:s_match.start()]
        my_calc = {k: v for k, v in conjecture.propertyCalculators.items() if k != s_match.group(1)}
    if myprint:
        print(my_premise)

    return PropertyBasedExpression(my_premise, my_calc, (inputList, conjecture.propertiesDict))


def get_conclusion(conjecture, myprint=True):
    assert "->" in conjecture.expression, 'Not an implication'

    inputList = list(conjecture.inputList)
    inputList = inputList[1:-1]
    conjecture.expression = conjecture.expression.replace("->", ">>")
    n_pattern = r"^\((TARGET.*?)\)>>"
    n_match = re.search(n_pattern, conjecture.expression)
    if n_match:
        my_conclusion = conjecture.expression[n_match.end():]
        my_calc = {k: v for k, v in conjecture.propertyCalculators.items() if k != n_match.group(1)}
    else:
        s_pattern = r">>\((TARGET.*?)\)$"
        s_match = re.search(s_pattern, conjecture.expression)
        my_conclusion = s_match.group(1)
        my_calc = {s_match.group(1): conjecture.propertyCalculators[s_match.group(1)]}
    if myprint:
        print(my_conclusion)

    return PropertyBasedExpression(my_conclusion, my_calc, (inputList, conjecture.propertiesDict))

def conjecturing_recover_formula(prefix_tree):
    #import sage.logic.logicparser as logicparser
    formula = ''
    if not isinstance(prefix_tree, list):
        raise TypeError("the input must be a parse tree as a list")

    formula = conjecturing_apply_func(prefix_tree, logicparser.recover_formula_internal)
    if prefix_tree[0] == '~' or len(prefix_tree) == 1:
        return formula
    return formula[1:-1]

def conjecturing_apply_func(tree, func):
    # used when full syntax parse tree is passed as argument
    if len(tree) == 1:
        return func(tree)
    # used when full syntax parse tree is passed as argument
    elif len(tree) == 2:
        rval = conjecturing_apply_func(tree[1], func)
        return func([tree[0], rval])
    elif isinstance(tree[1], list) and isinstance(tree[2], list):
        lval = conjecturing_apply_func(tree[1], func)
        rval = conjecturing_apply_func(tree[2], func)
    elif isinstance(tree[1], list):
        lval = conjecturing_apply_func(tree[1], func)
        rval = tree[2]
    elif isinstance(tree[2], list):
        lval = tree[1]
        rval = conjecturing_apply_func(tree[2], func)
    else:
        return func(tree)
    return func([tree[0], lval, rval])

def _makePropertyBasedConjecture(inputList, propertiesDict):
    import operator

    binaryOperators = {'&', '|', '^', '->'}

    expressionStack = []
    propertyCalculators = {}

    for op in inputList:
        if op in propertiesDict:
            import types
            if type(propertiesDict[op]) in (types.BuiltinMethodType, types.MethodType):
                f = wrapUnboundMethod(op, propertiesDict)
            else:
                f = wrapBoundMethod(op, propertiesDict)
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

    my_expression = expressionStack.pop()

    return PropertyBasedConjecture(my_expression, propertyCalculators, (inputList, propertiesDict))

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
                            theory=None, precomputed=None, skips=0.0, 
                            complexity_limit=11,notebook_path='./'):
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
    -  ``time`` - if given, this integer specifies the number of seconds before
       the conjecturing program times out and returns the best conjectures it
       has at that point. The default value is 5.
    -  ``debug`` - if given, this boolean value specifies whether the output of
       the program ``expressions`` to ``stderr`` is printed. The default value
       is ``False``.
    -  ``verbose`` - if given, this boolean value specifies whether the program
       ``expressions`` is ran in verbose mode. Note that this has nu purpose if
       ``debug`` is not also set to ``True``. The default value is ``False``.
    -  ``sufficient`` - if given, this boolean value specifies whether sufficient
       or necessary conditions for the main property should be generated. If
       ``True``, then sufficient conditions are generated. If ``False``, then
       necessary conditions are generated. The default value is ``True``
    -  ``operators`` - if given, specifies a set of operators that can be used.
       If this is ``None``, then all known operators are used. Otherwise only
       the specified operators are used. It is advised to use the method
       ``allPropertyBasedOperators()`` to get a set containing all operators and
       then removing the operators which are not needed. The default value is
       ``None``.
    -  ``theory`` - if given, specifies a list of known bounds. If this is
       ``None``, then no known bounds are used. Otherwise each conjecture will
       have to be more significant than the conditions in this list. The default
       value is ``None``.

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
    command = notebook_path + 'expressions -pc{}{} --dalmatian {} --time {} --invariant-names --output stack {} --allowed-skips {} --maximum-complexity --complexity-limit {}'
    command = command.format('v' if verbose and debug else '', 't' if theory is not None else '',
                             '--all-operators ' if operators is None else '',
                             time, '--sufficient' if sufficient else '--necessary',
                             skips,
                             complexity_limit)

    if verbose:
        print('Using the following command')
        print(command)

    import subprocess
    sp = subprocess.Popen(command, shell=True,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, close_fds=True,
                          encoding='utf-8')
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
            with warnings.catch_warnings(record=True) as w:
                warnings.simplefilter("always")
                my_value = prop(o)
                if w:
                    return float("NaN")
                return my_value 
        else:
            return precomputed_value

    if theory is not None:
        if verbose:
            print("Started writing theory to expressions")
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
            print("Finished writing theory to expressions")

    if verbose:
        print("Started computing and writing property values to expressions")

    def format_value(property,o):
        try:
            return '1' if bool(get_value(propertiesDict[property], o)) else '0'
        except:
            return '-1'

    values = [format_value(property, o) for o in objects for property in names]
    stdin.write('\n'.join(values)+'\n')
    stdin.flush()

    if verbose:
        print("Finished computing and writing property values to expressions")

    if debug:
        for l in sp.stderr:
            print('> ' + l.rstrip())

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
        print("Finished conjecturing")

    return conjectures

# ------------------------------------------------------------------
# Optimization-based selection of Dalmatian expressions
# ------------------------------------------------------------------

def invariants_used(conj):
    import re
    return set(re.findall(r"[A-Za-z_]\w*\(x\)", str(conj)))


def jaccard(A, B):
    A = set(A)
    B = set(B)
    if len(A | B) == 0:
        return 0.0
    return float(len(A & B)) / float(len(A | B))


def conjecture_complexity(conj):
    """
    Complexity = number of unary operators + 2 * number of binary operators.
    The final comparator <= or >= is stored as binary, so it is subtracted.
    """
    unary = 0
    binary = 0

    for op, opType in conj.stack:
        if opType == 1:
            unary += 1
        elif opType == 2:
            binary += 1

    binary = max(0, binary - 1)

    return unary + 2 * binary


def optimize_dalmatian_set(conjs, test_examples, invariants, target_invariant,
                           k=5, alpha=1.0, beta=1.0,
                           lam=0.1, rho=0.1,
                           upper_bound=True,
                           verbose=True):

    target_function = invariants[target_invariant]

    print("Running Dalmatian IP selection...")
    print("Number of Dalmatian candidates:", len(conjs))
    print("Number of holdout/test examples:", len(test_examples))

    n = len(conjs)

    if n == 0:
        raise ValueError("No Dalmatian conjectures were provided.")

    if int(k) > n:
        raise ValueError("k cannot exceed the number of candidate conjectures.")

    V, T, C = [], [], []

    for c in conjs:
        violations = []
        tightness = []

        for ex in test_examples:
            true_val = float(target_function(ex))

            try:
                pred = float(c(ex, returnBoundValue=True))
            except Exception:
                pred = float("nan")

            if not math.isfinite(pred):
                violations.append(1e6)
                tightness.append(1e6)
                continue

            if upper_bound:
                violation = max(0.0, true_val - pred)
            else:
                violation = max(0.0, pred - true_val)

            violations.append(violation)
            tightness.append(abs(pred - true_val))

        V.append(sum(violations) / float(len(violations)))
        T.append(sum(tightness) / float(len(tightness)))
        C.append(conjecture_complexity(c))

    cost = {
        i: float(alpha) * V[i] + float(beta) * T[i] + float(lam) * C[i]
        for i in range(n)
    }

    R = {}
    for i, j in combinations(range(n), 2):
        R[(i, j)] = jaccard(invariants_used(conjs[i]),
                             invariants_used(conjs[j]))

    model = pulp.LpProblem("Dalmatian_Optimal_Set_Selection", pulp.LpMinimize)

    x = {
        i: pulp.LpVariable("x_{}".format(i), cat="Binary")
        for i in range(n)
    }

    y = {
        (i, j): pulp.LpVariable("y_{}_{}".format(i, j), cat="Binary")
        for i, j in combinations(range(n), 2)
    }

    model += (
        pulp.lpSum(cost[i] * x[i] for i in range(n))
        +
        float(rho) * pulp.lpSum(R[(i, j)] * y[(i, j)] for i, j in y)
    )

    model += pulp.lpSum(x[i] for i in range(n)) == int(k)

    for i, j in y:
        model += y[(i, j)] <= x[i]
        model += y[(i, j)] <= x[j]
        model += y[(i, j)] >= x[i] + x[j] - 1


def invariants_used(conj):
    import re
    return set(re.findall(r"[A-Za-z_]\w*\(x\)", str(conj)))


def jaccard(A, B):
    A = set(A)
    B = set(B)
    if len(A | B) == 0:
        return 0.0
    return float(len(A & B)) / float(len(A | B))


def conjecture_complexity(conj):
    """
    Complexity = number of unary operators + 2 * number of binary operators.
    The final comparator <= or >= is stored as binary, so it is subtracted.
    """
    unary = 0
    binary = 0

    for op, opType in conj.stack:
        if opType == 1:
            unary += 1
        elif opType == 2:
            binary += 1

    binary = max(0, binary - 1)

    return unary + 2 * binary


def optimize_dalmatian_set(conjs, test_examples, invariants, target_invariant,
                           k=5, alpha=1.0, beta=1.0,
                           lam=0.1, rho=0.1,
                           upper_bound=True,
                           verbose=True):

    target_function = invariants[target_invariant]

    print("Running Dalmatian IP selection...")
    print("Number of Dalmatian candidates:", len(conjs))
    print("Number of holdout/test examples:", len(test_examples))

    n = len(conjs)

    if n == 0:
        raise ValueError("No Dalmatian conjectures were provided.")

    if int(k) > n:
        raise ValueError("k cannot exceed the number of candidate conjectures.")

    V, T, C = [], [], []

    for c in conjs:
        violations = []
        tightness = []

        for ex in test_examples:
            true_val = float(target_function(ex))

            try:
                pred = float(c(ex, returnBoundValue=True))
            except Exception:
                pred = float("nan")

            if not math.isfinite(pred):
                violations.append(1e6)
                tightness.append(1e6)
                continue

            if upper_bound:
                violation = max(0.0, true_val - pred)
            else:
                violation = max(0.0, pred - true_val)

            violations.append(violation)
            tightness.append(abs(pred - true_val))

        V.append(sum(violations) / float(len(violations)))
        T.append(sum(tightness) / float(len(tightness)))
        C.append(conjecture_complexity(c))

    cost = {
        i: float(alpha) * V[i] + float(beta) * T[i] + float(lam) * C[i]
        for i in range(n)
    }

    R = {}
    for i, j in combinations(range(n), 2):
        R[(i, j)] = jaccard(invariants_used(conjs[i]),
                             invariants_used(conjs[j]))

    model = pulp.LpProblem("Dalmatian_Optimal_Set_Selection", pulp.LpMinimize)

    x = {
        i: pulp.LpVariable("x_{}".format(i), cat="Binary")
        for i in range(n)
    }

    y = {
        (i, j): pulp.LpVariable("y_{}_{}".format(i, j), cat="Binary")
        for i, j in combinations(range(n), 2)
    }

    model += (
        pulp.lpSum(cost[i] * x[i] for i in range(n))
        +
        float(rho) * pulp.lpSum(R[(i, j)] * y[(i, j)] for i, j in y)
    )

    model += pulp.lpSum(x[i] for i in range(n)) == int(k)

    for i, j in y:
        model += y[(i, j)] <= x[i]
        model += y[(i, j)] <= x[j]
        model += y[(i, j)] >= x[i] + x[j] - 1

    model.solve(pulp.PULP_CBC_CMD(msg=False))

    selected_idx = [
        i for i in range(n)
        if pulp.value(x[i]) is not None and pulp.value(x[i]) > 0.5
    ]


    if verbose:

        print("\nSelected indices:", selected_idx)
        print("Objective:", pulp.value(model.objective))
    
        print("\nSelected expressions:")
    
        for i in selected_idx:
    
            print("\nIndex:", i)
            print(conjs[i])
    
            print("Holdout violation:", V[i])
            print("Holdout tightness:", T[i])
            print("Complexity:", C[i])
            print("Individual cost:", cost[i])
    
        print("\nPairwise Jaccard similarities:")
    
        for i, j in combinations(selected_idx, 2):
            print(
                "({}, {}) -> {}".format(
                    i,
                    j,
                    R[(i, j)]
                )
        )
    return {
        "selected_idx": selected_idx,
        "selected_conjectures": [conjs[i] for i in selected_idx],
        "objective": pulp.value(model.objective),
        "V": V,
        "T": T,
        "C": C,
        "cost": cost,
        "redundancy": R
    }
