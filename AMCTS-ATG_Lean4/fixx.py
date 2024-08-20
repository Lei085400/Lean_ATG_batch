import json
import heapq
import transformers
import subprocess
import time
import timeit
from datetime import datetime
from tqdm import tqdm, trange
from pathlib import Path
from Lean4Gym import *
# from lean_dojo import *
import traceback
from generate import IMPORTS
import torch


def fix(file, tac_list, theorem_all):
    # file = "demo.lean"
    
    FF0 = open(file,'w')
    FF0.write(IMPORTS + theorem_all + ' lean_repl sorry' + '\n')
    FF0.close()
    
    lean_workdir = ".." 
    lean_file =  "AMCTS-ATG_Lean4_Llama3/" + file  

    lean = Lean4Gym(lean_workdir, lean_file)
    try:
        state = lean.getInitState()
    except:
        return False,""
        
    for tac in tac_list:
        
        state = lean.run_tactic(state, [tac])
        
        if state.error is not None:
            return False, []
            
    if state.isFinish(): #不用输入参数
        return True, []

    
    state = lean.run_tactic(state, ["assumption'"])
    
    if state.isFinish():
        return True, ["assumption'"]

    return False, []
