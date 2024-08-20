import os
import re
import sys
import math
import random
import numpy as np
# from lean_dojo import *
import ssl
ssl._create_default_https_context = ssl._create_unverified_context
import torch
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim
from collections import deque
from transformers import AutoTokenizer, AutoModelForCausalLM, AutoModelForSeq2SeqLM
import json
import heapq
import transformers
import subprocess
import time
from pathlib import Path
# from lean_dojo import *
import traceback
import copy
import vllm
from datetime import datetime
from tqdm import tqdm, trange
from pathlib import Path
from Lean4Gym import *
import traceback
from generate import process_rw_list
from fixx import fix
MAX_ROUND_NUMBER = 10
os.environ["CUDA_VISIBLE_DEVICES"] = "0" 

model_name_or_path = "../model/llama3_lora_sft"

model = vllm.LLM(
    model=model_name_or_path,
    tensor_parallel_size=1,
    trust_remote_code=True,
    gpu_memory_utilization=0.8,
    dtype='float16'
)
tokenizer = transformers.GPTNeoXTokenizerFast.from_pretrained(model_name_or_path)


def _prompt_proofstep(ts):
    content = f"[GOAL]{ts}[PROOFSTEP]"
    prompt = f"<|begin_of_text|><|start_header_id|>user<|end_header_id|>\n\n{content}<|eot_id|><|start_header_id|>assistant<|end_header_id|>"
    if(len(prompt)>2048):
      prompt = prompt[:2048]
    return prompt

def _unique_sorted(texts, scores):
    texts_ = []
    scores_ = []
    for t, s in sorted(zip(texts, scores), key=lambda x: -x[1]):
        if t not in texts_:
            texts_.append(t)
            scores_.append(s)
    return texts_, scores_


def generate_vllm(prompt, model, tokenizer, temperatures, num_samples, stop, max_tokens=1024):
    texts, scores = [], []
    for temperature in temperatures:
        params = vllm.SamplingParams(
            n=num_samples,
            temperature=temperature,
            use_beam_search=temperature==0.0,
            max_tokens=max_tokens,
            stop=stop,
            logprobs=0,
            top_k=-1
        )
        outputs = model.generate([prompt], params, use_tqdm=False)



        if len(outputs) == 0:
            return [], []
        for output in outputs[0].outputs:
            text = output.text.replace(tokenizer.eos_token, '') 
            score = output.cumulative_logprob/max(len(output.token_ids), 1)
            texts.append(text)
            scores.append(score)

    texts, scores = _unique_sorted(texts, scores)
    return texts, scores

def encode_state(state, feature_size):
    if(state is None):
        state = "None"
    encode_state = [ord(char) for char in state]
    if(len(encode_state)<=feature_size):
        encode_state += [0]*(feature_size-len(encode_state))  #list
    else:
        encode_state = encode_state[:feature_size]

    return encode_state
 
def encode_tactic(tactic,feature_size):
    encode_tactic = [ord(char) for char in tactic]
    if(len(encode_tactic)<=feature_size):
        encode_tactic += [0]*(feature_size-len(encode_tactic))
    else:
        encode_tactic = encode_tactic[:feature_size]
    return encode_tactic


def plan1(node, path, root_name, assumptions, theorem_all): 
  processed_list = process_rw_list(path)
  new = 'rw[' + root_name + ']'
  processed_list.append(new)
  if assumptions != "":
    flag, step_list = fix("test.lean", processed_list, theorem_all)
    
    if flag == False:
      return False, processed_list
    
    processed_list.extend(step_list)
  return True, processed_list
  

def tactic_generator(state, num):

  state = state.getTacticState()
  tactic_candidates, scores = generate_vllm(_prompt_proofstep(state), model, tokenizer, 
                              temperatures=[0], num_samples=num, stop=tokenizer.eos_token)
      
  return tactic_candidates


def all_rw(node):
  # path = copy.copy(node.path)
  path = [elem.lstrip('\n') for elem in copy.copy(node.path)]
  return all(elem.startswith("rw") for elem in path if not elem.startswith("have"))

def have_tac(node):
  path = copy.copy(node.path)
  return sum(elem.startswith("have") for elem in path)


def generate_theorem(node, root_name, assumptions, theorem, count):
  lam_num = 3
  path = []

  state = node.state.tacticState
  match = re.search(r'⊢(.*)', state, re.DOTALL)
  if match:
      state_now = match.group(1).strip()
  
  path = copy.copy(node.path)
  
  err_list = ["contrapose","congr","swap","replace","ring","clear","assumption","case","apply","intro","refine","revert"] 
  
  for element in path:
    for err in err_list:
        if err in element:
            node.stepflag = False
            return ""
  
  if(all_rw(node) and have_tac(node)< lam_num):
    
    theorem_all = "theorem "+ root_name + str(count) + assumptions +":" + state_now + " := by" 
    flag, step = plan1(node, path, root_name, assumptions, theorem_all)
    
    if(step == ""):
      node.stepflag = False
      return step
    if flag == False and step!="":
      node.stepflag = False
      return step
  else:
    node.stepflag = False
    return ""
  
  for item in step:
    theorem_all += '\n' + item

  return theorem_all


def new_theorem(node, outputs):
  state = node.state.tacticState
  if(state == "no goals"):
    return False
  
  if 'have' in node.tac:
    return False
  if 'cases' in node.tac:
    return False
  if 'cases' in state:
    return False
  if 'case' in state:
    return False
  if '?' in state:
    return False
  if 'refine\'' in node.tac:
    return False
  
  for i in outputs:
    if i == state:
      return False
       
  return True



class Node(object):

  def __init__(self,state):
    self.parent = None
    self.children = []
    self.prob = 0
    self.puct = 0
    self.visit_times = 0
    self.quality_value = 0.0
    self.flag = True 
    self.new = False 
    self.tac = None  
    self.state = state
    self.path = None 
    self.tactic_candidates = None    
    self.assersion = None
    self.depth = 0 
    self.similarity = 0
    self.llmflag = True 
    self.path = []
    self.stepflag = True 

  def set_state(self, state):
    self.state = state

  def get_state(self):  
    return self.state

  def set_parent(self, parent):  
    self.parent = parent

  def get_children(self):  
    return self.children

  def get_visit_times(self):  
    return self.visit_times

  def visit_times_add_one(self):  
    self.visit_times += 1

  def get_quality_value(self): 
    return self.quality_value

  def quality_value_add_n(self, n):  
    self.quality_value += n

  def is_all_expand(self,TACRIC_NUMBER): 
    return len(self.children) == TACRIC_NUMBER
  
  def add_child(self, sub_node):
    sub_node.set_parent(self)
    self.children.append(sub_node)
  
  def select_action(self):

    visit_counts = np.array([child.visit_times for child in self.children])
    actions = [action for action in self.children.tac]
    action = actions[np.argmafx(visit_counts)]
    return action

  def is_terminal(self):  
    if(self.state.error is not None):
      self.flag == False 
      return True
    else:
      self.flag == True
      return False

  def compute_reward(self):   
    if (self.flag == False):
      return -1
    elif (self.flag == True):
      if(self.new == True):
        return 1
      else:
        return 0
  
  def proof(self,state,tac,lean):
    try:
      result = lean.run_tactic(state, [tac])
    except:
      return state
    return result

  def get_next_state_with_random_choice(self, lean, index, num):  
    
    if(self.tactic_candidates is None):
      self.tactic_candidates = tactic_generator(self.state, num)
    tactic_candidates = self.tactic_candidates
    
    try:
      random_choice = tactic_candidates[index]
    except:
      self.state.error = "llm error"
      return self
    next_state = self.proof(self.state, random_choice, lean)
    if(next_state.error is not None):
      correct_flag = False
    else:
      correct_flag = True
    next_node = Node(next_state)
    next_node.tac = random_choice
    next_node.flag = correct_flag
    return next_node

  
  
  def __repr__(self):
    return "Node: {}, Q/N: {}/{}, state: {}".format(
        hash(self), self.quality_value, self.visit_times, self.state)


class MCTS:

    def __init__(self, node, policy_model, value_model, args, device):
        self.node = node
        self.policy_model = policy_model
        self.value_model = value_model
        self.args = args
        self.device = device
        self.root = node

    def tree_policy(self, node, lean, is_exploration, outputs):
      
      # Check if the current node is the leaf node
      while node.is_terminal() == False:
        
        if node.is_all_expand(self.args['TACRIC_NUMBER']):

          best_node = self.best_child(node, is_exploration,outputs)
          
          if(best_node is None):
            node.flag = False
            if(node.parent is not None):
              node = node.parent
            else:
              node.llmflag = False
              return node
          else:
            node = best_node
            
        else:
          # Return the new sub node
          sub_node = self.expand(node,lean, outputs)
          return sub_node

      # Return the leaf node
      return node


    def expand(self, node, lean, outputs):
      
      new_node = node.get_next_state_with_random_choice(lean, len(node.children),self.args["TACRIC_NUMBER"]) 
      new_node.depth = node.depth + 1

      encodestate = encode_state(node.state.getTacticState(), self.args['feature_size'])
      encodetactic = encode_tactic(new_node.tac, self.args['feature_size'])
      input_policy = encodestate + encodetactic
      input_policy = torch.FloatTensor(np.array(input_policy).astype(np.float64)).to(self.device)
      new_node.prob = float(self.policy_model(input_policy))  

      node.add_child(new_node)
      new_node.path = copy.copy(new_node.parent.path)
      new_node.path.append(new_node.tac)
      if(new_node.flag == False):
        new_node.new = False
      else:
        if(new_theorem(new_node, outputs)):
          new_node.new = True
        else:
          new_node.new = False
      return new_node


    def best_child(self, node, is_exploration,outputs):
    

      # TODO: Use the min float value
      best_score = -sys.maxsize
      best_sub_node = None
      lambda_0 = 0.1 
      alpha = 0.05   
      step = self.root.visit_times
      lambda_p = lambda_0 * (1 + alpha * step)

      for sub_node in node.get_children():
        if(sub_node.flag == False or sub_node.llmflag == False):
          continue
          
        # Ignore exploration for inference
        if is_exploration:
          C = (1 / math.sqrt(2.0)) / (1 + 0.01 * step) * math.exp(-0.1 * (len(outputs) / self.root.visit_times))
        else:
          C = 0.01

        tac_count = node.path.count(sub_node.tac)
        penalty = tac_count / node.visit_times

        
        left = sub_node.get_quality_value() / sub_node.get_visit_times()
        right = math.sqrt(node.get_visit_times()) / (sub_node.get_visit_times()+1)
        Puct_score = left + C * sub_node.prob * right - lambda_p * penalty

        sub_node.puct = Puct_score

        if Puct_score > best_score:
          best_sub_node = sub_node
          best_score = Puct_score
     
      return best_sub_node


    def backup(self, node, reward):
      
      while node != None:
        # Update the visit times
        node.visit_times_add_one()

        # Update the quality value
        node.quality_value_add_n(reward)

        # Change the node to the parent node
        node = node.parent


    def run(self, lean, outputs):
      node =  self.node
      computation_budget = 1000
      time_out = self.args['time_out']
      start = time.time()

      for i in range(computation_budget):
        current_time = time.time()
        if current_time - start > time_out:
          return node, outputs

        expand_node = self.tree_policy(node, lean, True, outputs)
        
        if(expand_node.llmflag == False):
          return node, outputs
        
        if(not expand_node.flag):
          reward = -1
        elif(expand_node.new == True):
          reward = 1
        else:
          reward = 0

        self.backup(expand_node, reward)
        
        if(expand_node.state.isFinish()):
          return node, outputs
        
        if(expand_node.new): 
          new_theorems = expand_node.state.tacticState
          outputs.append(new_theorems)

      return node, outputs


    def runmcts(self, lean, root_name, assumptions, theorem, outfile):
      count = 0
      node =  self.node
      computation_budget = 1000000
      start = time.time()
      outputs = []
      time_out = self.args['time_out']
      
      state_counts = {}
     
      for i in trange(computation_budget):
        self.args['TACRIC_NUMBER'] = 32
        if(computation_budget>150):
          self.args['TACRIC_NUMBER'] = 24
        current_time = time.time()
        if current_time - start > time_out:
          return outputs
        if current_time - start > 60 and count < 1:
          return outputs
        if current_time - start > 120 and count < 2:
          return outputs
      
        expand_node = self.tree_policy(node, lean, True, outputs)
        
        if(expand_node.llmflag == False):
          return outputs
        
        if(not expand_node.flag):
          reward = -1
        elif(expand_node.new):
          encodestate = encode_state(expand_node.state.getTacticState(), self.args['feature_size'])
          input_value = torch.FloatTensor(np.array(encodestate).astype(np.float64)).to(self.device)
          reward = float(self.value_model(input_value))
        else:
          encodestate = encode_state(expand_node.state.getTacticState(), self.args['feature_size'])
          input_value = torch.FloatTensor(np.array(encodestate).astype(np.float64)).to(self.device)
          reward = float(self.value_model(input_value))
          try:
            encodestate = encode_state(expand_node.state.getTacticState(), self.args['feature_size'])
            input_value = torch.FloatTensor(np.array(encodestate).astype(np.float64)).to(self.device)
            reward = float(self.value_model(input_value))
            state_counts[expand_node.state.tacticState] += 1
            repeat = state_counts[expand_node.state.tacticState]
            if(repeat>5):
              lamm = 0.1
            elif(repeat>2):
              lamm = 0.05
            else:
              lamm = 0.01
            reward -= lamm * repeat
          except:
            reward -= 0.5
        
        if(expand_node.state.isFinish()):
          break

        self.backup(expand_node, reward)

        if(expand_node.new):
          expand_node.state.print()
          # print(expand_node.path)
          new_steps = generate_theorem(expand_node, root_name, assumptions, theorem, i)      
          # print(expand_node.stepflag)
          if expand_node.stepflag:
            F = open(outfile,'a')
            F.write('\n\n' + new_steps + '\n')
            F.close() 
            
            new_theorems = expand_node.state.tacticState
            outputs.append(new_theorems)
            
            count += 1
        
          if(count>=self.args['max_count']):
            break

      return outputs

  