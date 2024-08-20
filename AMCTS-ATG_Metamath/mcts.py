import sys
import math
import random
import metamath_llm_api
import numpy as np
import ssl
ssl._create_default_https_context = ssl._create_unverified_context
import torch
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim
import mmverify
from transformers import AutoTokenizer, AutoModelForCausalLM, AutoModelForSeq2SeqLM
import json
from datetime import datetime
from tqdm import tqdm, trange
from pathlib import Path
import copy
MAX_ROUND_NUMBER = 10
MIN_TECTIC_NUMBER = 16

model_path = "/models/llama3_lora_sft_set_all_0721"  
llm,tokenizer = metamath_llm_api.llm_init(model_path)  

def encode_state(state, feature_size):
    state = str([str(sublist) for sublist in state])
    encode_state = [ord(char) for char in state]
    if(len(encode_state)<=feature_size):
        encode_state += [0]*(feature_size-len(encode_state))  
    else:
        encode_state = encode_state[:feature_size]
    return encode_state
 
def encode_tactic(tactic,feature_size):
    tactic = str([str(sublist) for sublist in tactic])
    encode_tactic = [ord(char) for char in tactic]
    if(len(encode_tactic)<=feature_size):
        encode_tactic += [0]*(feature_size-len(encode_tactic))
    else:
        encode_tactic = encode_tactic[:feature_size]
    return encode_tactic


def cosine_similarity(vector1, vector2):
    dot_product = np.dot(vector1, vector2)
    norm_vector1 = np.linalg.norm(vector1)
    norm_vector2 = np.linalg.norm(vector2)   
    if norm_vector1 != 0 and norm_vector2 != 0:
        cosine_sim = dot_product / (norm_vector1 * norm_vector2)
    else:
        cosine_sim = 0  
    return cosine_sim


def tactic_generator(node,mm):
  theorem_name = ''
  stack = node.state
  path = node.path
  references = []
  stop_list = ["\n", ",", "]", " ", "/", "[", "(", ")","=","&","*",";","$"] 
  ref_list = ['wph', 'wps', 'wch', 'wth', 'wta', 'wcel', 'cA', 'cB', 'cfv', 'cX', 'cF', 'cc0', 'wet', 'wze', 'co', 'wbr', 'cC', 'cN', 'wsi', 'c1', 'wrh', 'cr', 'wmu', 'wla', 'wka', 'vx', 'vy', 'vz', 'wn', 'wi', 'ax-mp', 'ax-1', 'cc', 'wb', 'wa', 'df-an', 'wo', 'df-or', 'wif', 'w3o', 'w3a', 'df-3an', 'a1i', 'wnan', 'df-nan', 'wxo', 'wal', 'cv', 'wceq', 'syl', 'cR', 'cG', 'cK', 'cS', 'cvv', 'cP', 'adantr', 'cW', 'cD', 'cV', 'cM', 'cY', 'wss', 'wral', 'cU', 'cT', 'c2', 'cmul', 'cle', 'c0', 'cI', 'caddc', 'vk', 'cH', 'cn', 'clt', 'cJ', 'wrex', 'ex', 'cZ', 'cz', 'syl3anc', 'cmin', 'adantl', 'wne', 'cE', 'cn0', 'vn', 'eqeltrd', 'cQ', 'c.le']
  strategies, scores = metamath_llm_api.generate_vllm(theorem_name,path,stack,references,llm,tokenizer,[0],
                                                      num_samples=16,stop=stop_list,max_tokens=64)
  strategies = [s.strip() for s in strategies] 
  print('[tactic_generator] stack:',stack)
  print('[tactic_generator] strategies:',strategies) 
  tactics = []
  for i,tac in enumerate(strategies): 
    if tac in mm.labels:
      tactics.append(tac)
  if len(tactics) < MIN_TECTIC_NUMBER:
      needed = MIN_TECTIC_NUMBER - len(tactics)
      available_elements = [item for item in ref_list if item not in tactics]
      random.shuffle(available_elements)
      additional_elements = available_elements[:needed]
      tactics.extend(additional_elements)
  return tactics
  


def generate_theorem(node,name):
  references = []
  conclusion = " ".join(node.assersion[3])
  proof_steps = " ".join(node.path)
  for i in node.path:
    if i not in references:
      references.append(i)  
  references = " ".join(references)
  new_theorem = {"theorem": name, "conclusion": conclusion, "proof_steps": proof_steps, "references": references}
  return new_theorem
 
def new_theorem(node, mm, outputs):
  if(node.parent is None or node.flag == False or node.tac == '' or node.state == []):
    return False
  new_conclusion = node.state[-1]
  new_assersion = mm.fs.make_assertion(new_conclusion)
  node.assersion = new_assersion
  conclusion = " ".join(node.assersion[3])
  node.conclusion = conclusion
  new_flag = True
  if conclusion in outputs:
    new_flag = False
  return new_flag
  
  
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
    self.path = [] 
    self.tactic_candidates = None  
    self.tac_num = 0  
    self.assersion = None
    self.depth = 0 
    self.similarity = 0
    self.ref = []
    self.conclusion = ""

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

  def is_all_expand(self): 
    return len(self.children) == self.tac_num

  def add_child(self, sub_node):
    sub_node.set_parent(self)
    self.children.append(sub_node)
  
  def select_action(self):
    visit_counts = np.array([child.visit_times for child in self.children])
    actions = [action for action in self.children.tac]
    action = actions[np.argmafx(visit_counts)]
    return action

  def is_terminal(self):  
    return self.flag == False
  def compute_reward(self):   
    if (self.flag == False):
      return -1
    elif (self.flag == True):
      if(self.new == True):
        return 1
      else:
        return 0
    
  def proof(self, tac, mm, f_hyps, e_hyps):
    state = copy.copy(self.state)
    correct_flag, state, references = mm.verify_and_calculate_proof_step_normal(f_hyps,e_hyps,tac,state, 1)   
    return correct_flag, state, references, mm
  
  def get_next_state_with_random_choice(self, index, mm, f_hyps, e_hyps):  
    if(self.tac_num == 0):
      self.tactic_candidates = tactic_generator(self,mm)   
      self.tac_num = len(self.tactic_candidates)
    random_choice = self.tactic_candidates[index]
    correct_flag, next_state, references, mm = self.proof( random_choice, mm, f_hyps, e_hyps)
    next_node = Node(next_state)
    next_node.tac = random_choice
    next_node.flag = correct_flag
    if(next_node.tac == '' or next_node.state == []):
      next_node.flag = False
    next_node.ref = references
    return next_node,mm
  
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

    def tree_policy(self, node, is_exploration, mm, f_hyps, e_hyps, outputs):
      while node.is_terminal() == False:
        
        if node.is_all_expand() and node.tac_num != 0:
          best_node = self.best_child(node, is_exploration, outputs)
          node = best_node
        else:
          sub_node = self.expand(node, mm, f_hyps, e_hyps,outputs)
          return sub_node
      return node


    def expand(self,node, mm, f_hyps, e_hyps, outputs):

      new_node,mm = node.get_next_state_with_random_choice(len(node.children), mm, f_hyps, e_hyps)   
      new_node.depth = node.depth + 1
      encodestate = encode_state(node.state, self.args['feature_size'])
      encodetactic = encode_tactic(new_node.tac, self.args['feature_size'])
      input_policy = encodestate + encodetactic
      input_policy = torch.FloatTensor(np.array(input_policy).astype(np.float64))
      new_node.prob = float(self.policy_model(input_policy))  
      node.add_child(new_node)
      if(new_node.flag == False):
        new_node.new = False
      else:
        if(new_theorem(new_node,mm,outputs)):
          new_node.new = True
        else:
          new_node.new = False
      return new_node


    def best_child(self, node, is_exploration, outputs):
      best_score = -sys.maxsize
      best_sub_node = None
      lambda_0 = 0.1 
      alpha = 0.01    
      step = self.root.visit_times
      lambda_p = lambda_0 * (1 + alpha * node.depth)
      penalty = 0

      for sub_node in node.get_children():
        if is_exploration:
          C = (1 / math.sqrt(2.0)) / (1 + 0.01 * step) * math.exp(-0.1 * (len(outputs) / self.root.visit_times))
        else:
          C = 0.01
        
        tac_count = node.path.count(sub_node.tac)
        if(node.parent is not None):
          penalty = tac_count / len(node.path) - lambda_p * penalty
        else:
          penalty = 0

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
        node.visit_times_add_one()

        node.quality_value_add_n(reward)

        node = node.parent


    def run(self, mm, f_hyps, e_hyps, name, outputs):
      node =  self.node
      computation_budget = 6000
      
      for i in range(computation_budget):
        
        expand_node = self.tree_policy(node, True, mm, f_hyps, e_hyps, outputs)
        
        if(not expand_node.flag):
          reward = -1
        elif(expand_node.new):
          print('new theorem!')
          reward = 1
          outputs.append(expand_node.conclusion)
        else:
          encodestate = encode_state(expand_node.state, self.args['feature_size'])
          input_value = torch.FloatTensor(np.array(encodestate).astype(np.float64))
          reward = float(self.value_model(input_value))

        self.backup(expand_node, reward)

      return node, outputs


    def runmcts(self, mm, f_hyps, e_hyps):
      count = 0
      node =  self.node
      computation_budget = 50000
      state_counts = {}
      outputs = []
      outconclusion = []
      for i in range(computation_budget):
        # print("mcts{}，node.state：{}".format(i,node.state))
        expand_node = self.tree_policy(node, True, mm, f_hyps, e_hyps, outconclusion)   
        if(not expand_node.flag): 
          reward = -1
        elif(expand_node.new): 
          encodestate = encode_state(expand_node.state, self.args['feature_size'])
          input_value = torch.FloatTensor(np.array(encodestate).astype(np.float64))
          reward = float(self.value_model(input_value))
        else: 
          encodestate = encode_state(expand_node.state, self.args['feature_size'])
          input_value = torch.FloatTensor(np.array(encodestate).astype(np.float64))
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

        self.backup(expand_node, reward)

        if(expand_node.new): 
          name = "new" + str(i)
          path = []  
          unused_list = expand_node.state[:-1]
          new_node = copy.copy(expand_node)
          while new_node.parent is not None:
              if(new_node.state == unused_list):
                break
              path.append(new_node.tac)     
              new_node = new_node.parent
          path.reverse()
          expand_node.path = path  
          if(len(path) < 3): 
            continue
          
          new_theorem = generate_theorem(expand_node,name)

          outputs.append(new_theorem)
          outconclusion.append(expand_node.conclusion)
          with open('output.json', 'a') as file:
            json.dump(new_theorem, file)
            file.write('\n')                      
          count += 1 
          if(count>=self.args['max_count']):
            break
      return node,outputs
