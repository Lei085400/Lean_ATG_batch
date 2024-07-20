
import os

import torch
import pickle
import subprocess

import timeit
import select
import json
from Lean4Gym import Lean4Gym, ProofState
# print(torch.__version__)
from torch.nn.parallel import DataParallel  
# torch.cuda.set_device(2)

# import lean_dojo
# from lean_dojo import *
from model import policy_model
from model import value_model
from trainer import Trainer
from mcts import Node
from mcts import MCTS
from transformers import AutoTokenizer, AutoModelForCausalLM, AutoModelForSeq2SeqLM
from generate import assumption_theorem

# import ssl
# ssl._create_default_https_context = ssl._create_unverified_context


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
    'max_count': 200,
    'time_out' : 120
}


state_list = []
lean_list = []

feature_size = args['feature_size']  # 特征向量的size


device_ids = list(range(torch.cuda.device_count()))  
policyModel = policy_model(feature_size*2, device).to(device)
valueModel = value_model(feature_size, device).to(device)
print("hello,开始了！！")


checkpoint_policy = torch.load("/home2/wanglei/Project/ATG/policy_model")
policyModel.load_state_dict(checkpoint_policy['state_dict'])

checkpoint_value = torch.load("/home2/wanglei/Project/ATG/value_model")
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

# file_list = []
# with open('example_generate.txt', 'r') as file: 
#     lines = file.readlines() 
#     for line in lines:
#         line = ''.join(line).strip('\n')
#         file_list.append(line)
#         print(line)

# #待证明策略：
lean_dir = "/home2/wanglei/Project/testfolder/root"
# lean_dir = "/home2/wanglei/Project/testfolder"
file_list = list_files(lean_dir)
# print(len(file_list))

lean_workdir = "/home2/wanglei/Project" # Lean工程的根目录

for i, file in enumerate(file_list):
    print("============================================")
    lean_file = "testfolder/root/" + file  # 待证明定理的Lean文件
   
    print("证明定理为:{}".format(file))
    lean = Lean4Gym(lean_workdir, lean_file)
    try:
        state = lean.getInitState()
        # print(state.tacticState)
    except:
        print("状态异常")
        continue
    
    node = Node(state)
    root_name = os.path.splitext(file)[0]
    assumptions, theorem = assumption_theorem(state.tacticState)
    print("根节点名称、前提和结论")
    print(root_name)
    print(assumptions)
    print(theorem)
    print("=============")

    print("开始搜索策略")
    mcts = MCTS(node, policyModel, valueModel, args, device)
    outputs = mcts.runmcts(lean, root_name, assumptions, theorem)
    new_theorems.extend(outputs)
        
    print("第{}个定理".format(str(i)))
    print("找到{}条新定理".format(str(len(new_theorems))))
    
print("新定理总数：{}".format(str(len(new_theorems))))

F = open(r'new_theorems.txt','w')
for theorem in new_theorems:
    F.write(theorem +'\n')
F.close() 