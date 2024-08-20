
import os

import torch
import pickle
import subprocess

import timeit
import select
import json
from Lean4Gym import Lean4Gym

from torch.nn.parallel import DataParallel  

from model import policy_model
from model import value_model
from trainer import Trainer
from mcts import Node
from mcts import MCTS
from transformers import AutoTokenizer, AutoModelForCausalLM, AutoModelForSeq2SeqLM
from generate import extract_theorem_expression
from generate import extract_premises
from generate import IMPORTS




device = torch.device('cuda:0') if torch.cuda.is_available() else torch.device('cpu') 


args = {
    
    'batch_size': 4,
    'numIters': 10,                                # Total number of training iterations
    'num_simulations': 100,                         # Total number of MCTS simulations to run when deciding on a move to play
    'numEps': 20,                                  # Number of full games (episodes) to run during each iteration
    'numItersForTrainExamplesHistory': 20,
    'epochs': 10,                                    # Number of epochs of training per iteration
    'checkpoint_path': 'latest.pth',                 # location to save latest set of weights
    'TACRIC_NUMBER': 16,
    'feature_size':100,
    'max_count': 10000,
    'time_out' : 300
}


state_list = []
lean_list = []

feature_size = args['feature_size']  


device_ids = list(range(torch.cuda.device_count()))  
policyModel = policy_model(feature_size*2, device).to(device)
valueModel = value_model(feature_size, device).to(device)


checkpoint_policy = torch.load("policy_model", map_location='cuda:0')
policyModel.load_state_dict(checkpoint_policy['state_dict'])

checkpoint_value = torch.load("value_model", map_location='cuda:0')
valueModel.load_state_dict(checkpoint_value['state_dict'])

def list_files(directory):
    filelist = []
    for file in os.listdir(directory):
        if os.path.isfile(os.path.join(directory, file)):
            print(file)
            filelist.append(file)
    return filelist

count = 0
new_theorems = []


root_folder = "CommGroup_basic_example"  # an example of ATG
lean_dir = root_folder
lean_workdir = ".." 
outfile = "example.lean"


file_list = list_files(lean_dir)


F = open(outfile,'a')
F.write(IMPORTS)
F.close() 

for i, file in enumerate(file_list):
    lean_file = "AMCTS-ATG_Lean4_Llama3/" + root_folder + "/" + file  

    lean = Lean4Gym(lean_workdir, lean_file)
    try:
        state = lean.getInitState()
    except:
        
        continue
    
    node = Node(state)
    
    root_name = os.path.splitext(file)[0]
    leanfile = root_folder + "/" + file
   
    assumptions = extract_premises(leanfile)
    theorem = extract_theorem_expression(leanfile,assumptions)

    print("SEARCH")
    print(file)
    
    mcts = MCTS(node, policyModel, valueModel, args, device)
    outputs = mcts.runmcts(lean, root_name, assumptions, theorem, outfile)
    new_theorems.extend(outputs)
        