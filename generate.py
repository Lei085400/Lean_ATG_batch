import re


def extract_premises(lean_file_path):
    with open(lean_file_path, 'r', encoding='utf-8') as file:
        content = file.read()
    
    # 定义正则表达式来匹配theorem到第一个冒号之间的所有连续括号内容
    pattern = r'theorem\s+\w[\w\']*\s*((?:\s*(?:\([^)]*\)|\[[^\]]*\]|\{[^}]*\}))*)\s*:'

    match = re.search(pattern, content)
    if match:
        premises = match.group(1).strip()
        return premises
    else:
        return ""



# def extract_premises_test(content):
    
#     # 定义正则表达式来匹配theorem到第一个冒号之间的所有连续括号内容
#     pattern = r'theorem\s+\w[\w\']*\s*((?:\s*(?:\([^)]*\)|\[[^\]]*\]|\{[^}]*\}))*)\s*:'

#     match = re.search(pattern, content)
#     if match:
#         premises = match.group(1).strip()
#         return premises
#     else:
#         return ""

# content = "theorem div_eq_of_eq_mul'0 {a b c : G} (h : a = b * c) : a / b = c := by lean_repl sorry"
# print("前提为:")
# print(extract_premises_test(content))


def convert_to_lean_theorem(theorem_str, index):
    # 将字符串按行分割
    lines = theorem_str.split('\n')
    path = ['rw[Nat.pow_mul]', 'rw [Finset.sum_range_add]']
    path = ['rw[←Nat.pow_mul]', 'rw [Finset.sum_range_add]']
    
    # 找到⊢符号的位置
    proof_index = None
    for i, line in enumerate(lines):
        if '⊢' in line:
            proof_index = i
            break
    
    if proof_index is None:
        raise ValueError("Invalid theorem string: missing '⊢' symbol")

    # 提取前提条件和定理
    assumptions = lines[:proof_index]
    assumptions = [condition.replace('✝', '') for condition in assumptions]
    theorem = lines[proof_index].split('⊢')[1].strip()
    
    print(assumptions)
    print(theorem)
    
    # 生成每个前提条件的Lean格式
    assumptions_str = '\n'.join(f"({assumption})" for assumption in assumptions)
    
    # 生成Lean定理格式
    theorem_name = f"theorem new{index}"
    lean_theorem = f"{theorem_name}\n{assumptions_str}:\n{theorem}:= by\nsorry\n"
    
    return lean_theorem



def extract_theorem_expression(file_path, premise_str):
    # 读取文件内容
    with open(file_path, 'r', encoding='utf-8') as file:
        lean_code = file.read()

    # 使用正则表达式找到定理部分
    theorem_pattern = re.compile(r'theorem\s+[^\s\(\[\{]+.*', re.DOTALL)
    match = theorem_pattern.search(lean_code)
    if match:
        theorem = match.group(0)
        
        # 去掉提供的前提字符串
        theorem_without_premise = theorem.replace(premise_str, '')

        # 提取第一个冒号到 ":=" 之间的内容
        expression_pattern = re.compile(r':\s*(.*?)(?=\s*:=)')
        expression_match = expression_pattern.search(theorem_without_premise)
        if expression_match:
            expression = expression_match.group(1).strip()
            return expression

    return ""




def assumption_theorem(theorem_str): #给定定理状态，划分前提和定理
    # 将字符串按行分割
    lines = theorem_str.split('\n')
    
    # 找到⊢符号的位置
    proof_index = None
    for i, line in enumerate(lines):
        if '⊢' in line:
            proof_index = i
            break
    
    if proof_index is None:
        raise ValueError("Invalid theorem string: missing '⊢' symbol")

    # 提取前提条件和定理
    assumptions = lines[:proof_index]
    # assumptions = [condition.replace('✝', '') for condition in assumptions]
    theorem = lines[proof_index].split('⊢')[1].strip()
    
    # print(assumptions)
    # print(theorem)
    
    return assumptions, theorem


def reverse_rw_strategy(strategy):
    # 逆转单个策略
    if strategy.startswith("←"):
        return strategy[1:]  # 去掉箭头
    else:
        return "←" + strategy  # 添加箭头

def process_rw_element(element):
    # 找到"rw["和"]"之间的部分
    start_idx = element.find("[")
    end_idx = element.find("]")
    
    if start_idx == -1 or end_idx == -1:
        raise ValueError("Invalid rw element format")
    
    # 提取并处理策略部分
    strategies = element[start_idx+1:end_idx].split(", ")
    reversed_strategies = [reverse_rw_strategy(strategy) for strategy in strategies]
    reversed_strategies.reverse()  # 逆序处理策略
    
    # 重新组装rw元素
    processed_element = element[:start_idx+1] + ", ".join(reversed_strategies) + element[end_idx:]
    return processed_element

def process_rw_list(lst):
    # 检查所有元素是否都以"rw"开头
    if not all(elem.startswith("rw") for elem in lst):
        raise ValueError("Not all elements start with 'rw'")
    
    # 处理每个rw元素并逆序列表
    processed_list = [process_rw_element(elem) for elem in lst]
    processed_list.reverse()  # 逆序处理整个列表
    
    return processed_list


IMPORTS = """import AdaLean.sum_neg_cancel
import AdaLean.sum_eq_two
import AdaLean.two_mod_two_pow
import AdaLean.two_pow_eq_two_pow_sub_add
import AdaLean.mul_two_div_mul
import AdaLean.ico_choose_eq_two_pow
import AdaLean.inv_2m_add
import AdaLean.congr_Ico_succ
import AdaLean.range_sub_choose_add_sum
import AdaLean.choose_mul_pow_eq_mul
import AdaLean.sum_choose_eq_Ico
import AdaLean.Ico_odd_div_choose
import AdaLean.Ico_choose_add_eq_mul_pred
import AdaLean.two_mul_sum
import AdaLean.sum_add_eq_add
import AdaLean.sum_mul_congr
import AdaLean.sum_neg_comm
import AdaLean.Ico_succ_mul_choose_eq
import AdaLean.add_two_subY
import AdaLean.pow_neg_succ_succ
import AdaLean.sub_two_add_one
import AdaLean.Ico_choose
import AdaLean.mul_mul_div_succ_mul_choose
import AdaLean.neg_pow_div_choose
import AdaLean.range_choose_eq_ico_choose
import AdaLean.add_neg_div
import AdaLean.choose_add_div_distrib
import AdaLean.two_pow_div_two
import AdaLean.two_m_div_add
import AdaLean.lt_eq_le_sub
import AdaLean.sum_add_eq_two_pow
import AdaLean.sum_choose_sub_eq_add
import AdaLean.choose_mul_add_pow
import AdaLean.pow_eq_sub_one_mul
import AdaLean.Ico_simpn
import AdaLean.two_even_congr
import AdaLean.add_two_sub
import AdaLean.mul_sum_choose
import AdaLean.sum_neg_pow_mul_mul
import AdaLean.choose_mul_eq_mul_sub
import AdaLean.sum_neg_pow_mul_eq_sum_distrib
import AdaLean.mul_two_pow_add_eq_mul_pow
import AdaLean.two_mul_succ_sub
import AdaLean.sum_choose_symm
import AdaLean.sum_neg_pow_mul_add
import AdaLean.ico_mul_choose_sub
import AdaLean.choose_mul_eq_mul_sub'
import AdaLean.mul_mul_div_succ_mul_choose_eq_succ
import AdaLean.two_pow_eq_range_add_ico
import AdaLean.sub_add_eq_add
import AdaLean.choose_eq_choose_add
import AdaLean.sum_mul_choose_eq_mul_two_pow_sub
import AdaLean.two_mul_div_add
import AdaLean.sum_choose_sub_eq_add_sub
import AdaLean.add_div_two
import AdaLean.choose_sub_sub
import AdaLean.bot_sum_mul_congr
import AdaLean.range_eq_ico_mul_choose
import AdaLean.sum_two_pow_mul_choose
import AdaLean.sum_sub_sum_add
import AdaLean.h_pow_zero_mul_add
import AdaLean.sum_neg_pow_mul_mul_choose
import AdaLean.sum_neg_pow_mul_distrib
import AdaLean.add_div_two_eq_distrib
import AdaLean.sum_neg_pow_div_congr
import AdaLean.sum_assoc
import AdaLean.sum_neg_assoc
import AdaLean.pow_zero_mul_add_sum
import AdaLean.mul_same
import AdaLean.range_mul_add
import AdaLean.choose_eq_choose_add_nk
import AdaLean.Ico_mul_add
import AdaLean.ico_succ
import AdaLean.sum_mul_add_distrib
import AdaLean.Ico_div
import AdaLean.mul_choose_two_pow
import AdaLean.range_sub_choose
import AdaLean.mul_choose_eq_mul_choose
import AdaLean.range_sub_add_cancel
import AdaLean.ico_two_pow
import AdaLean.icc_eq_ico
import AdaLean.sum_add_div_two
import AdaLean.choose_eq_choose_sub_add
import AdaLean.Ico_choose_range_choose
import AdaLean.sum_mul_choose_eq_mul_two_pow
import AdaLean.mul_add_mul_eq_mul
import AdaLean.Transit_item
import AdaLean.choose_eq_choose_sub_add_nk
import AdaLean.choose_mul_eq_choose_mul
import AdaLean.neg_pow_mul_mul_mul
import AdaLean.choose_sub_eq_choose_sub_add
import AdaLean.two_mul_add_sub
import AdaLean.mul_choose_sub
import AdaLean.choose_le_sum
import AdaLean.neg_pow_choose
import AdaLean.neg_pow_cancel
import AdaLean.odd_choose_sum
import AdaLean.sum_choose_eq
import AdaLean.neg_pow_mul_choose_mul_eq_mul_sub
import Lean4Repl
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.LocallyFinite
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.Algebra.Associated
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.GroupPower.Identities
import Mathlib.Algebra.Order.Floor
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Parity
import Mathlib.Data.List.Intervals
import Mathlib.Data.List.Palindrome
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Digits
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Prime
import Mathlib.Data.PNat.Basic
import Mathlib.Data.PNat.Prime
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Finite
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.ZMod.Basic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.LocallyFinite
import Mathlib.Order.WellFounded
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.NNReal
import Aesop
set_option trace.aesop true
set_option trace.aesop.proof true
set_option maxHeartbeats 999999999999999999999999
open Nat Real Rat BigOperators Function Finset

"""

# # 示例字符串
# theorem_str = """G : Type u_1
# inst✝ : DivInvMonoid G
# a b c : G
# ⊢ b * a⁻¹ = c * a⁻¹ ↔ b = c
# ['rw [div_eq_mul_inv, div_eq_mul_inv]']
# """

# # 转换为Lean定理
# lean_theorem = convert_to_lean_theorem(theorem_str, 1)

# # 写入文件
# with open('new_theorem.lean', 'w') as f:
#     f.write(import_statements + '\n' + lean_theorem)

# print("Lean theorem written to 'new_theorem.lean'")