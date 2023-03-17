# In[94]:

from sage.all_cmdline import *

import pandas as pd
import numpy as np
import sys
load("/home/jpbrooks/craig/learning/2023_02_ijds/aif_noise/conjecturing.py")


def run_conjecturing(my_timelimit=5, num_samples=10, data_fname="/home/jpbrooks/craigdata/learning/2021_04_aif/Feynman_with_units/I.10.7", invariant_names=["m0", "v", "c", "f"], use_pi=False, out_fname="I.10.7", operators=['+','-'], noise = 0):

    print(out_fname)
    print(operators)
    print(noise)
    my_data = pd.read_csv(data_fname+".bz2",
                         sep="\\s+",
                         header=None)

    #my_data.loc[:,len(my_data.columns)-1] = my_data.loc[:,len(my_data.columns)-1] + rg.normal(0, noise, len(my_data.index))
    # noise only to training data

    y_rms = ((my_data.iloc[range(num_samples), len(my_data.columns)-1]**2).mean())**(0.5) # get rms of target only using training data

    my_data.iloc[range(num_samples),len(my_data.columns)-1] = my_data.iloc[range(num_samples),len(my_data.columns)-1] + np.random.normal(0, y_rms*noise, num_samples)
    my_data.rename(columns={i:invariant_names[i] for i in range(len(invariant_names))}, inplace=True)
    #my_data

    
    class Example():
        def __init__(self, row):
            self.name = row.name
            
    def build_inv(i):
        def inv(self):
            return my_data.loc[self.name,i]
        inv.__name__ = i
        return inv
        
    for i in invariant_names:
        inv = build_inv(i)
        setattr(Example, inv.__name__, inv)
    
    train_examples = (
        my_data
        .iloc[range(Integer(num_samples)),]
        .apply(func=Example, axis='columns')
    )
    
    train_examples_list = train_examples.tolist()
    
    test_df = my_data.iloc[num_samples:(num_samples+100),]
    test_df = test_df.set_index(pd.Index(range(100)))
    test_examples = (
        my_data
        .iloc[num_samples:(num_samples+100),]
        .apply(func=Example, axis='columns')
    )
    test_examples_list = test_examples.tolist()
    
    sigma_y = test_df['f'].std()
    print(sigma_y)
    
    invariants = []
    for i in invariant_names:
        invariants.append(Example.__dict__[i])
    target_invariant = Example.__dict__[invariant_names[len(invariant_names)-1]]
    
    if use_pi == True:
        _sage_const_pi = pi
        
        def my_pi(dist):
            R = RealField(20)
            return R(_sage_const_pi)
        invariants.append(my_pi)
        
    #_sage_const_p0 = RealNumber('.00000001')
    #def my_const(example):
    #    return _sage_const_p0
    #invariants.append(my_const)
    
    np.random.seed(12345)
    set_random_seed(12345)
    #use_operators = {'+', '*', '-', '/', '+1', '-1', 'sqrt', 'exp', 
    #                 'ln', '1/', 'cos', 'abs', 'asin', 'atan', 'sin',
    #                '^2'}
    use_operators = operators
    
    out_file = open(out_fname, "a")
    
    inv_of_interest = invariants.index(target_invariant)
    conjs = conjecture(train_examples,
                      invariants,
                      inv_of_interest,
                      operators=use_operators,
                      upperBound=True,
                      debug=False,
                      time=my_timelimit,
                      verbose=False)
    convert_conjecture_names(conjs)
    error_df = pd.DataFrame()
    min_error = np.inf
    for i,c in enumerate(conjs):
        try:
            error = mean([abs(example.f() - c.evaluate(example, returnBoundValue=True)) for example in train_examples_list])
            out_file.write("%s,%s,%d,%d,%d,%f,%f\n" % (out_fname, c, my_timelimit, len(train_examples), len(operators), noise, error))
            if error < min_error:
                min_conj = c
                min_error = error
            #error_df['c'+str(i)] = [c.evaluate(example, returnBoundValue=True) for example in test_examples_list]
        except:
            print(c)
            #out_file.write("%s,%s,%d,%d,%d,%f\n" % (out_fname, c, my_timelimit, len(my_examples), len(operators), noise))
    
    #if len(conjs) > 1:
    #    error_df['min'] = error_df.apply(np.nanmin, axis=1)
    #elif len(conjs)==1:
    #    error_df['min'] = error_df['c0']
    #error_df['abs'] = abs(test_df['f'] - error_df['min'])

    try:
        if len(conjs) >= 1:
            #print(mean([abs(example.f() - min_conj.evaluate(example, returnBoundValue=True)) for example in train_examples_list]))
            #print(min_error)
            error_df['abs']  = [abs(example.f() - min_conj.evaluate(example, returnBoundValue=True)) for example in test_examples_list]
            nrmse = sqrt(mean(error_df['abs']**2))/sigma_y
            out_file.write("%f\n" % (nrmse))
    except:
        out_file.write("Error evaluating best conjecture on test data or no conjectures.\n")
    
    conjs = conjecture(train_examples,
                      invariants,
                      inv_of_interest,
                      operators=use_operators,
                      upperBound=False,
                      debug=False,
                      time=my_timelimit,
                      verbose=False)
    convert_conjecture_names(conjs)
    error_df = pd.DataFrame()
    min_error = np.inf
    for i, c in enumerate(conjs):
        try:
            error = mean([abs(example.f() - c.evaluate(example, returnBoundValue=True)) for example in train_examples_list])
            out_file.write("%s,%s,%d,%d,%d,%f,%f\n" % (out_fname, c, my_timelimit, len(train_examples), len(operators), noise, error))
            if error < min_error:
                min_conj = c
                min_error = error
        except:
            print(c)
            #out_file.write("%s,%s,%d,%d,%d,%f\n" % (out_fname, c, my_timelimit, len(my_examples), len(operators), noise))
    #if len(conjs) > 1:
    #    error_df['max'] = error_df.apply(np.nanmax, axis=1)
    #elif len(conjs) == 1:
    #    error_df['max'] = error_df['c0']
    #error_df['abs'] = abs(error_df['max'] - test_df['f'])
    out_file.flush()
    
    try:
        if len(conjs) >= 1:
            error_df['abs']  = [abs(example.f() - min_conj.evaluate(example, returnBoundValue=True)) for example in test_examples_list]
            nrmse = sqrt(mean(error_df['abs']**2))/sigma_y
            out_file.write("%f\n" % (nrmse))
    except:
        out_file.write("Error evaluating best conjecture on test data or no conjectures.\n")

    out_file.flush()
    out_file.close()
    
instances = ["I.6.2a", "I.6.2", "I.6.2b", "I.8.14", "I.9.18", "I.10.7", "I.11.19", "I.12.1", "I.12.2", "I.12.4"]
# name the equation f for each one
invariant_dict = {"I.6.2a": ["theta", "f"],
"I.6.2": ["sigma", "theta", "f"],
"I.6.2b": ["sigma", "theta", "theta1", "f"],
"I.8.14": ["x1", "x2", "y1", "y2", "f"],
"I.9.18": ["m1", "m2", "G", "x1", "x2", "y1", "y2", "z1", "z2", "f"],
"I.10.7": ["m0", "v", "c", "f"],
"I.11.19": ["x1", "x2", "x3", "y1", "y2", "y3", "f"],
"I.12.1": ["mu", "Nn", "f"],
"I.12.2": ["q1", "q2", "epsilon", "r", "f"],
"I.12.4": ["q1", "epsilon", "r", "f"]}
pi_dict = {"I.6.2a": True,
"I.6.2": True,
"I.6.2b": True,
"I.8.14": False,
"I.9.18": False,
"I.10.7": False,
"I.11.19": False,
"I.12.1": False,
"I.12.2": True,
"I.12.4": True}
aif_time = {"I.6.2a": 16,
"I.6.2": 2992,
"I.6.2b": 4792,
"I.8.14": 544,
"I.9.18": 5975,
"I.10.7": 14,
"I.11.19": 184,
"I.12.1": 12,
"I.12.2": 17,
"I.12.4": 12}
aif_points = {"I.6.2a": 10,
"I.6.2": 100,
"I.6.2b": 1000,
"I.8.14": 100,
"I.9.18": 1000,
"I.10.7": 10,
"I.11.19": 100,
"I.12.1": 10,
"I.12.2": 10,
"I.12.4": 10}
aif_noise = {"I.6.2a": 0.01,
"I.6.2":  0.0001,
"I.6.2b": 0.0001,
"I.8.14": 0.0001,
"I.9.18": 0.00001,
"I.10.7": 0.0001,
"I.11.19": 0.001,
"I.12.1": 0.001,
"I.12.2": 0.01,
"I.12.4": 0.01}
loc = "/home/jpbrooks/craigdata/learning/2021_04_aif"
outloc = "/home/jpbrooks/craig/learning/2023_02_ijds/aif_noise/"

operator_lists = [ 
['+', '-', '*', '/', '+1', '-1', '^2', 'sqrt'],
['+', '-', '*', '/', '+1', '-1', 'sin', 'ln', '1/', 'cos', 'exp', 'sqrt', '^2'],
['+', '-', '*', '/', '+1', '-1', 'sqrt', 'exp', 'ln', '1/', 'cos', 'abs', 'asin', 'atan', 'sin', '^2']]

#for instance in instances:
#    for operator_list in operator_lists:
#       run_conjecturing(my_timelimit=5, num_samples=10, data_fname=loc +"/Feynman_with_units/" + instance, invariant_names=invariant_dict[instance], use_pi=pi_dict[instance], out_fname=outloc+instance, operators=operator_list, noise=0.0)
#       run_conjecturing(my_timelimit=100, num_samples=10, data_fname=loc +"/Feynman_with_units/" + instance, invariant_names=invariant_dict[instance], use_pi=pi_dict[instance], out_fname=outloc+instance, operators=operator_list, noise=0.0)
#       run_conjecturing(my_timelimit=1000, num_samples=10, data_fname=loc +"/Feynman_with_units/" + instance, invariant_names=invariant_dict[instance], use_pi=pi_dict[instance], out_fname=outloc+instance, operators=operator_list, noise=0.0)
#    
# AI Feynman set up
for instance in instances:
    for operator_list in operator_lists:
        run_conjecturing(my_timelimit=aif_time[instance], num_samples=10, data_fname=loc +"/Feynman_with_units/" + instance, invariant_names=invariant_dict[instance], use_pi=pi_dict[instance], out_fname=outloc+instance, operators=operator_list, noise=aif_noise[instance])

