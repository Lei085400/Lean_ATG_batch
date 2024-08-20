import os
import numpy as np
from random import shuffle
import copy
import torch
import torch.optim as optim
import pickle
from mcts import MCTS
from mcts import Node
from transformers import AutoTokenizer, AutoModelForSeq2SeqLM, AutoModelForCausalLM
import json
from tqdm import trange


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


class Trainer:

    def __init__(self, policy_model, value_model, args, device):
        self.policy_model = policy_model
        self.value_model = value_model
        self.args = args
        self.mcts = None
        self.device = device
       

    def exceute_episode(self, root): 

        policy_examples = []
        value_examples = []
        node = root
        state = node.state

        while True:  
            max_times = 0
            max_i = 0
            finish = 0
            action_probs = [0 for _ in range(self.args['TACRIC_NUMBER'])]
            for index, children_node in enumerate(node.children):
                action_probs[index] = children_node.visit_times  
                
                if(action_probs[index] > max_times):
                    max_times = action_probs[index]
                    max_i = index

            if(np.sum(action_probs)!=0):
                action_probs = action_probs / np.sum(action_probs)  

            if(children_node.flag == False):
                action_probs[index] = 0
            if(children_node.new == True):
                action_probs[index] = 1
                max_i = index
                max_times = 1

            encodestate = encode_state(state.getTacticState(), self.args['feature_size'])
            
            for index, children_node in enumerate(node.children): 
                encodetactic = encode_tactic(children_node.tac, self.args['feature_size'])
                input_policy = encodestate + encodetactic
                policy_examples.append((input_policy, action_probs[index]))
                
                children_state = children_node.state
                children_encodestate = encode_state(children_state.getTacticState(), self.args['feature_size'])

                reward = children_node.quality_value 

                value_examples.append((children_encodestate, reward)) 
            
            try: 
                node = node.children[max_i]
                state = node.state

            except:
                finish = 1
                
            if (finish == 1 or node.depth >= 10): 
                policy = []
                value = []
                for hist_input, hist_action_probs in policy_examples:
                    policy.append((hist_input, hist_action_probs))

                for hist_state, hist_reward in value_examples:
                    value.append((hist_state, hist_reward))

                return policy, value


    def learn(self, state_list, lean_list,file_list): 
        policy_train_example = []
        value_train_example = []
        for index, state in enumerate(state_list):
            F = open(r'train_theorem.txt','a')
            F.write(file_list[index] +'\n')
            F.close() 
            for i in range(1, self.args['numIters'] + 1): 
                print("{}/{}".format(i, self.args['numIters']))
                outputs = []
                count = 0
                node = Node(state)
            
                for i in trange(self.args['numEps']): 
                    self.mcts = MCTS(node, self.policy_model, self.value_model, self.args, self.device)
                    
                    node,output = self.mcts.run(lean_list[index], outputs)
                    outputs = output
                    count += 1
                    print(count)

                    if(count % 5 == 0):
                        policy_train_examples, value_train_examples = self.exceute_episode(node)
                        policy_train_example.extend(policy_train_examples)
                        value_train_example.extend(value_train_examples)
        
        shuffle(policy_train_example)
        shuffle(value_train_example)

        with open('policy_train_example.pickle', 'wb') as f:
            pickle.dump(policy_train_example, f)
        with open('value_train_example.pickle', 'wb') as f:
            pickle.dump(value_train_example, f)
            
        self.train()
        return
            
    def train(self):
        with open('policy_train_example.pickle', 'rb') as f:
            policy_train_example = pickle.load(f)
        with open('value_train_example.pickle', 'rb') as f:
            value_train_example = pickle.load(f)
        self.policy_train(policy_train_example) 
        self.value_train(value_train_example)

        self.save_checkpoint_policy(folder=".", filename="policy_model")  
        self.save_checkpoint_value(folder=".", filename="value_model") 
        return

    def policy_train(self, policy_examples):

        optimizer = optim.Adam(self.policy_model.parameters(), lr=5e-4)
        pi_losses = []

        for i in trange(self.args['epochs']):
            self.policy_model.train()

            batch_idx = 0

            while batch_idx < int(len(policy_examples) / self.args['batch_size']):
               
                sample_ids = np.random.randint(len(policy_examples), size=self.args['batch_size'])
                input, target = list(zip(*[policy_examples[i] for i in sample_ids]))
                input = torch.FloatTensor(np.array(input).astype(np.float64)).to(self.device)
                target = torch.FloatTensor(np.array(target).astype(np.float64)).to(self.device)

                # predict
                input = input.contiguous()
                target_pis = target.contiguous()
                
                
                out_pi = self.policy_model(input)
                l_pi = self.loss_pi(target_pis, out_pi)

                pi_losses.append(float(l_pi))

                optimizer.zero_grad()
                l_pi.backward()
                optimizer.step()

                batch_idx += 1



    def value_train(self, examples):

        optimizer = optim.Adam(self.value_model.parameters(), lr=5e-4)
        v_losses = []

        for i in trange(self.args['epochs']):
            self.value_model.train()

            batch_idx = 0

            while batch_idx < int(len(examples) / self.args['batch_size']):
            
                sample_ids = np.random.randint(len(examples), size=self.args['batch_size'])
                input, target = list(zip(*[examples[i] for i in sample_ids]))

                input = torch.FloatTensor(np.array(input).astype(np.float64)).to(self.device)
                target = torch.FloatTensor(np.array(target).astype(np.float64)).to(self.device)

                # predict
                boards = input.contiguous()
                target_vs = target.contiguous()
               
                # compute output
                out_v = self.value_model(boards)
                l_v = self.loss_pi(target_vs, out_v)

                v_losses.append(float(l_v))

                optimizer.zero_grad()
                l_v.backward()
                optimizer.step()

                batch_idx += 1
            
    
    def loss_pi(self,targets, outputs):
        loss = torch.sum((targets - outputs) ** 2) / targets.size()[0]
        return loss

    def loss_v(self, targets, outputs):
        loss = torch.sum((targets-outputs.view(-1))**2)/targets.size()[0]
        return loss

    def save_checkpoint_policy(self, folder, filename):
        if not os.path.exists(folder):
            os.mkdir(folder)

        filepath = os.path.join(folder, filename)
        torch.save({
            'state_dict': self.policy_model.state_dict(),
        }, filepath)
        
        
    def save_checkpoint_value(self, folder, filename):
        if not os.path.exists(folder):
            os.mkdir(folder)

        filepath = os.path.join(folder, filename)
        torch.save({
            'state_dict': self.value_model.state_dict(),
        }, filepath)

