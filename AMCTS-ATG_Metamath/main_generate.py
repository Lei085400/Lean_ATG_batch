"""DO NOT rename this file!"""
import os
import json
import pickle
import random
from string import Template
import os
import torch
import mmverify
import json
from model import policy_model
from model import value_model
from mcts import Node
from mcts import MCTS
# from verify import anatomy
from tqdm import tqdm
from verify import anatomy

os.environ['CUDA_VISIBLE_DEVICES'] = '0' 

class MyTemplate(Template):
    delimiter = "%"

class Submission:
    """A submission template. """

    def __init__(self, output_file: str):
        """You need to specify the following arguments."""

        self.output_file = output_file

        self.task = "Automated_Theorem_Generation"
        self.phase = "development"          # [development, final]

        self.base_url = "http://120.77.8.29:12345/v1/"  # The base url of the model server
        # If you are using OpenAI API or have set API key for
        # your own model, please fill in your API key
        self.api_key = "EMPTY"
        self.model = "./Mistral-7B-Instruct-v0.2"       # Your own model path, or GPTs
        self.prompt = MyTemplate("""
            You are a math expert and familar with Metamath formal language. 
            Now please derive new theorems from the following axioms, symbols and proven theorems. 
                                      
            Axioms: 
              {"theorem": "wn", "type": "$a", "conclusion": "wff -. ph", "d_vars": "", "f_hypos": ["wff ph"], "e_hypos": [], "proof_steps": "", "references": ""}
              {"theorem": "wi", "type": "$a", "conclusion": "wff ( ph -> ps )", "d_vars": "", "f_hypos": ["wff ph", "wff ps"], "e_hypos": [], "proof_steps": "", "references": ""}
              {"theorem": "ax-mp", "type": "$a", "conclusion": "|- ps", "d_vars": "", "f_hypos": ["wff ph", "wff ps"], "e_hypos": ["|- ph", "|- ( ph -> ps )"], "proof_steps": "", "references": ""}
              {"theorem": "ax-1", "type": "$a", "conclusion": "|- ( ph -> ( ps -> ph ) )", "d_vars": "", "f_hypos": ["wff ph", "wff ps"], "e_hypos": [], "proof_steps": "", "references": ""}
              {"theorem": "ax-2", "type": "$a", "conclusion": "|- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )", "d_vars": "", "f_hypos": ["wff ph", "wff ps", "wff ch"], "e_hypos": [], "proof_steps": "", "references": ""}
              {"theorem": "ax-3", "type": "$a", "conclusion": "|- ( ( -. ph -> -. ps ) -> ( ps -> ph ) )", "d_vars": "", "f_hypos": ["wff ph", "wff ps"], "e_hypos": [], "proof_steps": "", "references": ""}
                                      
            Symbols:
              {"theorem": "wph", "type": "$f", "conclusion": "wff ph", "d_vars": "", "f_hypos": [], "e_hypos": [], "proof_steps": "", "references": ""}
              {"theorem": "wps", "type": "$f", "conclusion": "wff ps", "d_vars": "", "f_hypos": [], "e_hypos": [], "proof_steps": "", "references": ""}
              {"theorem": "wch", "type": "$f", "conclusion": "wff ch", "d_vars": "", "f_hypos": [], "e_hypos": [], "proof_steps": "", "references": ""}
            
            Proven theorems:
              %proven_theorems
            
            Your output should follow the format as symbols and axioms.
            
            Example:
            {"theorem": "mp2", "type": "$p", "conclusion": "|- ch", "d_vars": "", "f_hypos": ["wff ph", "wff ps", "wff ch"], "e_hypos": ["|- ph", "|- ps", "|- ( ph -> ( ps -> ch ) )"], "proof_steps": "wps wch mp2.2 wph wps wch wi mp2.1 mp2.3 ax-mp ax-mp", "references": ["mp2.1", "mp2.2", "mp2.3", "wi", "ax-mp"]}
                                      
            Note: each proof step refers to the name of the theorem or axiom used in the proof， ``NAME.INDEX`` refers to the INDEX-th hypothesis of theorem NAME. The proof should be able to be verified by Metamath.
                                      
            Your response:
        """)

        # # custom generation parameters
        # self.max_tokens = 256
        # self.temperature = 0.9
        # self.top_p = 0.7
        # self.frequency_penalty = 0.0

    def generate(self, prompt):
        """We DO NOT recommend modifying this function, as 
        it will be used to test if the model is accessable"""

        return 1

    def post_process(self, model_output: str):
        """You can post-process the model output here, such as extract the theorem and verify the proof.
        For more information about proof in Metamath, please refer to:
        https://github.com/david-a-wheeler/mmverify.py"""

        end_of_theorem_index = model_output.index("}") + 1
        theorem= json.loads(model_output[:end_of_theorem_index])
        keys = ["theorem", "type", "conclusion", "d_vars", "f_hypos", "e_hypos", "proof_steps", "references"]
        if type(theorem) != dict:
            raise ValueError(f"Output should be a dictionary, got {type(theorem)}.")
        for key in keys:
            if key not in theorem:
                raise ValueError(f"Key {key} not found in the theorem.")

        return theorem

    def run(self):
        """Run your model on the given input data, and store the 
        predictions into the output file."""

        device = torch.device('cuda:0') 
        # device = torch.device('cpu') 

        args = {
            'batch_size': 10,
            'numIters': 1,                                # Total number of training iterations
            'num_simulations': 100,                         # Total number of MCTS simulations to run when deciding on a move to play
            'numEps': 50,                                  # Number of full games (episodes) to run during each iteration
            'numItersForTrainExamplesHistory': 20,
            'epochs': 15,                                    # Number of epochs of training per iteration
            'checkpoint_path': 'latest.pth',                 # location to save latest set of weights
            'TACRIC_NUMBER': 5,
            'feature_size':100,
            'max_count': 50000,                                #Control the number of generation theorems
            
            # 'MAX_ROUND_NUMBER' : 10
        }

        policyModel = policy_model(args['feature_size']*2, device)
        valueModel = value_model(args['feature_size'], device)
    
        checkpoint_policy = torch.load("policy_model")
        policyModel.load_state_dict(checkpoint_policy['state_dict'])

        checkpoint_value = torch.load("value_model")
        valueModel.load_state_dict(checkpoint_value['state_dict'])

        # print("hello！")

        verbosity = 30

        filename = "declare-set.mm"
        
        mm = mmverify.MM(None,None)

        mm.calculate_and_read_metamath(filename,def_verbosity=5,def_only_calculate=True)  
        
        f_hyps = []
        e_hyps = []
        step_int = 0
        state = []
        step = ''
        correct_flag,state,references = mm.verify_and_calculate_proof_step_normal(f_hyps,e_hyps,step,state,step_int) 
      
        node = Node(state)
        node.flag = correct_flag

        mcts = MCTS(node, policyModel, valueModel, args, device)
        node,outputs = mcts.runmcts(mm, f_hyps, e_hyps)

sub = Submission("output.json")
sub.run()
