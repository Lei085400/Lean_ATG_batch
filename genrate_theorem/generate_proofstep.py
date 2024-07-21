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

# 示例列表
example_list = ['rw [mul_comm, div_eq_mul_inv]', 'rw [mul_comm, eq_comm]']

# 处理列表并输出结果
processed_list = process_rw_list(example_list)
print(processed_list)