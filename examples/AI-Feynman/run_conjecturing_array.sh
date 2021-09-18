#!/bin/bash
# shell for qsub to use
#$ -S /bin/bash
# name on qstat
#$ -N aif
# limit to 17G; limit to 10 hours hard CPU; not using
# -l h_vmem=17G,h_stack=256M,h_cpu=10:00:00
# require 16GB mem to start, limit to 17G; limit to 10 hours hard CPU; not using
# -l mem_free=16G,h_vmem=40G,h_stack=256M
#$ -t 10-10:1
# tell SGE to run at most 4 jobs at once
#$ -tc 4

DATA_LOC=/home/jpbrooks/craigdata/learning/2021_04_aif

LOC=/home/jpbrooks/craig/learning/2021_04_aif

SEEDFILE=$LOC/aif_array.in

ID=$SGE_TASK_ID
SEED=$(sed -n -e "$ID p" $SEEDFILE)

#sage $LOC/run_conjecturing.py
TIME_LIMIT=10000
NUM_SAMPLES=10

echo "from sage.all_cmdline import *" > $LOC/$ID.py
echo "load(\"$LOC/run_conjecturing.py\")" >> $LOC/$ID.py
echo "for operator_list in operator_lists:" >> $LOC/$ID.py
echo "    for noise in [0,0.1]:" >> $LOC/$ID.py
echo "        run_conjecturing(my_timelimit=$TIME_LIMIT, num_samples=$NUM_SAMPLES, data_fname=\"$DATA_LOC\" +\"/Feynman_with_units/\" + \"$SEED.bz2\", invariant_names=invariant_dict[\"$SEED\"], use_pi=pi_dict[\"$SEED\"], out_fname=\"$LOC\"+\"/\"+\"$SEED\", operators=operator_list, noise=noise)" >> $LOC/$ID.py
/home/jpbrooks/anaconda3/envs/sage/bin/sage $LOC/$ID.py

