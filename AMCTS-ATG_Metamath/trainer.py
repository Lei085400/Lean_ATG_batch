import os
import numpy as np
from random import shuffle
import torch
import torch.optim as optim
import pickle
from train_mcts  import Node
import json
from tqdm import trange
from train_mcts import node_run_tactic_mcts_train


# feature_size = 100

def encode_state(state, feature_size):
    state = str(state)
    if(state is None):
        state = "None"
    encode_state = [ord(char) for char in state]
    if(len(encode_state)<=feature_size):
        encode_state += [0]*(feature_size-len(encode_state))  #list
    else:
        encode_state = encode_state[:feature_size]
    # print("encode")
    # print(encode_state)
    # print(feature_size)
    return encode_state

def encode_tactic(tactic,feature_size):
    # tactic = str([str(sublist) for sublist in tactic])
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
        # self.mcts = MCTS(node, self.policy_model, self.value_model, self.args)


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

            encodestate = encode_state(state, self.args['feature_size'])
            
            for index, children_node in enumerate(node.children):  
                encodetactic = encode_tactic(children_node.tac, self.args['feature_size'])
                input_policy = encodestate + encodetactic
                policy_examples.append((input_policy, action_probs[index]))
                
                children_state = children_node.state
                children_encodestate = encode_state(children_state, self.args['feature_size'])
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


    def learn(self, mm, theorem_name,goal,references,llm, tokenizer, stop_list): 
        policy_train_example = []
        value_train_example = []
        
        for index in range(10):
           
            for i in range(1, self.args['numIters'] + 1): 
                print("{}/{}".format(i, self.args['numIters']))

                count = 0
                # node_ = copy.copy(node)
                node = Node([],[])
            
                for i in trange(self.args['numEps']): 
                    node = node_run_tactic_mcts_train( mm,node, theorem_name,goal,references,llm, tokenizer, stop_list,self.policy_model,self.value_model)
                    
                    count += 1

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
        # print("xunlian")
        with open('policy_train_example.pickle', 'rb') as f:
            policy_train_example = pickle.load(f)
        with open('value_train_example.pickle', 'rb') as f:
            value_train_example = pickle.load(f)
        
        self.policy_train(policy_train_example)  
        self.value_train(value_train_example)
        # filename = self.args['checkpoint_path']
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
                input = torch.FloatTensor(np.array(input).astype(np.float64))
                target = torch.FloatTensor(np.array(target).astype(np.float64))
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

            # print(pi_losses)
            # print("Policy Loss", np.mean(pi_losses))
            
            # print("Examples:")
            # print(outpi[0].detach())
            # print(targetpis[0])


    def value_train(self, examples):
        optimizer = optim.Adam(self.value_model.parameters(), lr=5e-4)
        v_losses = []

        for i in trange(self.args['epochs']):
            self.value_model.train()

            batch_idx = 0

            while batch_idx < int(len(examples) / self.args['batch_size']):
                
                sample_ids = np.random.randint(len(examples), size=self.args['batch_size'])
                # print(len(examples))
                # input, target = list(zip(*[(example[0], example[1]) for example in examples]))
                input, target = list(zip(*[examples[i] for i in sample_ids]))
                # print(input,target)
                
                input = torch.FloatTensor(np.array(input).astype(np.float64))
                target = torch.FloatTensor(np.array(target).astype(np.float64))

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
            
            # print(v_losses)
            # print("Value Loss", np.mean(v_losses))
            # print("Examples:")
            # print(out_pi[0].detach())
            # print(target_pis[0])

    # def loss_pi(self, targets, outputs):
    #     loss = -(targets * torch.log(outputs)).sum(dim=1)
    #     return loss.mean()
    
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

