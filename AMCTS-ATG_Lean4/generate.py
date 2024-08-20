import re


def extract_premises(lean_file_path):
    with open(lean_file_path, 'r', encoding='utf-8') as file:
        content = file.read()
    
    pattern = r'theorem\s+\w[\w\']*\s*((?:\s*(?:\([^)]*\)|\[[^\]]*\]|\{[^}]*\}))*)\s*:'

    match = re.search(pattern, content)
    if match:
        premises = match.group(1).strip()
        return premises
    else:
        return ""


def convert_to_lean_theorem(theorem_str, index):

    lines = theorem_str.split('\n')

    proof_index = None
    for i, line in enumerate(lines):
        if '⊢' in line:
            proof_index = i
            break
    
    if proof_index is None:
        raise ValueError("Invalid theorem string: missing '⊢' symbol")

    assumptions = lines[:proof_index]
    assumptions = [condition.replace('✝', '') for condition in assumptions]
    theorem = lines[proof_index].split('⊢')[1].strip()
    
    print(assumptions)
    print(theorem)
    

    assumptions_str = '\n'.join(f"({assumption})" for assumption in assumptions)
    

    theorem_name = f"theorem new{index}"
    lean_theorem = f"{theorem_name}\n{assumptions_str}:\n{theorem}:= by\nsorry\n"
    
    return lean_theorem



def extract_theorem_expression(file_path, premise_str):

    with open(file_path, 'r', encoding='utf-8') as file:
        lean_code = file.read()


    theorem_pattern = re.compile(r'theorem\s+[^\s\(\[\{]+.*', re.DOTALL)
    match = theorem_pattern.search(lean_code)
    if match:
        theorem = match.group(0)
        

        theorem_without_premise = theorem.replace(premise_str, '')


        expression_pattern = re.compile(r':\s*(.*?)(?=\s*:=)')
        expression_match = expression_pattern.search(theorem_without_premise)
        if expression_match:
            expression = expression_match.group(1).strip()
            return expression

    return ""




def assumption_theorem(theorem_str): 

    lines = theorem_str.split('\n')
    proof_index = None
    for i, line in enumerate(lines):
        if '⊢' in line:
            proof_index = i
            break
    
    if proof_index is None:
        raise ValueError("Invalid theorem string: missing '⊢' symbol")

    assumptions = lines[:proof_index]
    theorem = lines[proof_index].split('⊢')[1].strip()

    
    return assumptions, theorem


def reverse_rw_strategy(strategy):
   
    if strategy.startswith("←"):
        return strategy[1:] 
    else:
        return "←" + strategy  

def process_rw_element(element):
    start_idx = element.find("[")
    end_idx = element.find("]")
    
    if start_idx == -1 or end_idx == -1:
        raise ValueError("Invalid rw element format")
    
    strategies = element[start_idx+1:end_idx].split(", ")
    reversed_strategies = [reverse_rw_strategy(strategy) for strategy in strategies]
    reversed_strategies.reverse()  
    
    processed_element = element[:start_idx+1] + ", ".join(reversed_strategies) + element[end_idx:]
    return processed_element

def process_rw_list(lst):
    lst = [elem.lstrip('\n') for elem in lst]
    if not all(elem.startswith("rw") for elem in lst if not elem.startswith("have")):
        raise ValueError("Not all elements start with 'rw'")
    
    processed_list = [process_rw_element(elem) for elem in lst]
    processed_list.reverse()  
    
    return processed_list


IMPORTS = """import Importall

open Nat Real Rat BigOperators Function Finset Bool

variable [CommGroup G] {{a b c d : G }}

"""
