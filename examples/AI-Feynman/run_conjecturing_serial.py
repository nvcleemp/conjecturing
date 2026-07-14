# In[94]:

from sage.all_cmdline import *

import pandas as pd
import numpy as np
load("conjecturing.py")


def run_conjecturing(my_timelimit=5, num_samples=10, data_fname="/home/jpbrooks/craig/learning/2021_04_aif/Feynman_with_units/I.10.7", invariant_names=["m0", "v", "c", "m"], use_pi=False, out_fname="I.10.7", operators=['+','-'], noise = 0):

    print(out_fname)
    print(operators)
    print(noise)
    my_data = pd.read_csv(data_fname,
                         sep="\\s+",
                         header=None)

    #my_data.loc[:,len(my_data.columns)-1] = my_data.loc[:,len(my_data.columns)-1] + rg.normal(0, noise, len(my_data.index))
    my_data.loc[:,len(my_data.columns)-1] = my_data.loc[:,len(my_data.columns)-1] + np.random.normal(0, noise, len(my_data.index))
    
    my_data.rename(columns={i:invariant_names[i] for i in range(len(invariant_names))}, inplace=True)
    my_data
    
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
    
    my_examples = (
        my_data
        .iloc[range(Integer(num_samples)),]
        .apply(func=Example, axis='columns')
    )
    
    my_examples_list = my_examples.tolist()
    
    test_examples = (
        my_data
        .iloc[num_samples:(num_samples+100),]
        .apply(func=Example, axis='columns')
    )
    test_examples_list = test_examples.tolist()
    
    
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
        
    _sage_const_p0 = RealNumber('.00000001')
    def my_const(example):
        return _sage_const_p0
    invariants.append(my_const)
    
    set_random_seed(12345)
    #use_operators = {'+', '*', '-', '/', '+1', '-1', 'sqrt', 'exp', 
    #                 'ln', '1/', 'cos', 'abs', 'asin', 'atan', 'sin',
    #                '^2'}
    use_operators = operators
    
    out_file = open(out_fname, "a")
    
    inv_of_interest = invariants.index(target_invariant)
    conjs = conjecture(my_examples,
                      invariants,
                      inv_of_interest,
                      operators=use_operators,
                      upperBound=True,
                      debug=True,
                      time=my_timelimit,
                      verbose=True)
    convert_conjecture_names(conjs)
    for c in conjs:
        try:
            error = sum([abs(example.m() - c.evaluate(example, returnBoundValue=True)) for example in test_examples_list])/len(test_examples_list)
            out_file.write("%s,%s,%d,%d,%d,%f,%f\n" % (out_fname, c, my_timelimit, len(my_examples), len(operators), noise, error))
        except:
            print(c)
            out_file.write("%s,%s,%d,%d,%d,%f\n" % (out_fname, c, my_timelimit, len(my_examples), len(operators), noise))
    
    conjs = conjecture(my_examples,
                      invariants,
                      inv_of_interest,
                      operators=use_operators,
                      upperBound=False,
                      debug=True,
                      time=my_timelimit,
                      verbose=True)
    convert_conjecture_names(conjs)
    for c in conjs:
        try:
            error = sum([abs(example.m() - c.evaluate(example, returnBoundValue=True)) for example in test_examples_list])/len(test_examples_list)
            out_file.write("%s,%s,%d,%d,%d,%f,%f\n" % (out_fname, c, my_timelimit, len(my_examples), len(operators), noise, error))
        except:
            print(c)
            out_file.write("%s,%s,%d,%d,%d,%f\n" % (out_fname, c, my_timelimit, len(my_examples), len(operators), noise))
    out_file.flush()
    out_file.close()
    
instances = ["I.6.2a", "I.6.2", "I.6.2b", "I.8.14", "I.9.18", "I.10.7", "I.11.19", "I.12.1", "I.12.2", "I.12.4"]
invariant_dict = {"I.6.2a": ["theta", "f"],
"I.6.2": ["sigma", "theta", "f"],
"I.6.2b": ["sigma", "theta", "theta1", "f"],
"I.8.14": ["x1", "x2", "y1", "y2", "d"],
"I.9.18": ["m1", "m2", "G", "x1", "x2", "y1", "y2", "z1", "z2", "F"],
"I.10.7": ["m0", "v", "c", "m"],
"I.11.19": ["x1", "x2", "x3", "y1", "y2", "y3", "dot"],
"I.12.1": ["mu", "Nn", "F"],
"I.12.2": ["q1", "q2", "epsilon", "r", "F"],
"I.12.4": ["q1", "epsilon", "r", "F"]}
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
loc = "/home/jpbrooks/craig/learning/2021_04_aif"

operator_lists = [ 
['+', '-', '*', '/', '+1', '-1', '^2', 'sqrt'],
['+', '-', '*', '/', '+1', '-1', 'sin', 'ln', '1/', 'cos', 'exp', 'sqrt', '^2'],
['+', '-', '*', '/', '+1', '-1', 'sqrt', 'exp', 'ln', '1/', 'cos', 'abs', 'asin', 'atan', 'sin', '^2']]


np.random.seed(12345)

for instance in instances:
    for operator_list in operator_lists:
        for noise in [0,0.1]:
            run_conjecturing(my_timelimit=5, num_samples=10, data_fname=loc +"/Feynman_with_units/" + instance, invariant_names=invariant_dict[instance], use_pi=pi_dict[instance], out_fname=loc+instance, operators=operator_list, noise=noise)
            run_conjecturing(my_timelimit=aif_time[instance], num_samples=aif_points[instance], data_fname=loc +"/Feynman_with_units/" + instance, invariant_names=invariant_dict[instance], use_pi=pi_dict[instance], out_fname=loc+instance, operators=operator_list)
            run_conjecturing(my_timelimit=100, num_samples=10, data_fname=loc +"/Feynman_with_units/" + instance, invariant_names=invariant_dict[instance], use_pi=pi_dict[instance], out_fname=loc+instance, operators=operator_list, noise=noise)
            run_conjecturing(my_timelimit=1000, num_samples=10, data_fname=loc +"/Feynman_with_units/" + instance, invariant_names=invariant_dict[instance], use_pi=pi_dict[instance], out_fname=loc+instance, operators=operator_list, noise=noise)
    
for instance in instances:
    for operator_list in operator_lists:
        run_conjecturing(my_timelimit=5, num_samples=10, data_fname=loc +"/Feynman_with_units/" + instance, invariant_names=invariant_dict[instance], use_pi=pi_dict[instance], out_fname=loc+instance, operators=operator_list, noise=aif_noise[instance])
        run_conjecturing(my_timelimit=aif_time[instance], num_samples=aif_points[instance], data_fname=loc +"/Feynman_with_units/" + instance, invariant_names=invariant_dict[instance], use_pi=pi_dict[instance], out_fname=loc+instance, operators=operator_list, noise=aif_noise[instance])
        run_conjecturing(my_timelimit=100, num_samples=10, data_fname=loc +"/Feynman_with_units/" + instance, invariant_names=invariant_dict[instance], use_pi=pi_dict[instance], out_fname=loc+instance, operators=operator_list, noise=aif_noise[instance])


for instance in instances:
    for operator_list in operator_lists:
        for noise in [0,0.1]:
            print(instance)
            print(operator_list)
            print(noise)
            run_conjecturing(my_timelimit=10000, num_samples=10, data_fname=loc +"/Feynman_with_units/" + instance, invariant_names=invariant_dict[instance], use_pi=pi_dict[instance], out_fname=loc+"/"+instance, operators=operator_list, noise=noise)
            run_conjecturing(my_timelimit=100000, num_samples=10, data_fname=loc +"/Feynman_with_units/" + instance, invariant_names=invariant_dict[instance], use_pi=pi_dict[instance], out_fname=loc+"/"+instance, operators=operator_list, noise=noise)
    

