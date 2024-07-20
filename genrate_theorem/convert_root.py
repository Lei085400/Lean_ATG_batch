import re


def extract_theorem_info(file_path):
    # 读取文件内容
    with open(file_path, 'r', encoding='utf-8') as file:
        file_content = file.read()

    # 打印文件内容进行调试
    print("File Content:\n", file_content)

    # 改进正则表达式，捕捉更多细节
    theorem_pattern = r'theorem\s+(\w+)\s+([^\:]+)\s*\:'

    # 提取定理名称和前提部分
    theorem_match = re.search(theorem_pattern, file_content, re.DOTALL)
    
    if not theorem_match:
        print("No theorem match found.")
        return None, None, None

    theorem_name = theorem_match.group(1)
    premises_content = theorem_match.group(2).strip()

    # 打印提取的定理名称和前提内容进行调试
    print("Theorem Name:", theorem_name)
    print("Premises Content:", premises_content)

    # 匹配单个前提，匹配()、[]、{}内的内容
    premises_pattern = r'(\([^\)]*\)|\{[^\}]*\}|\[[^\]]*\])'
    premises_matches = re.findall(premises_pattern, premises_content)

    # 打印匹配的前提进行调试
    print("Premises Matches:", premises_matches)

    # 整理前提部分
    premises = []
    variables = []

    for premise in premises_matches:
        premises.append(premise.strip())

        # 提取变量名称，变量名称在冒号之前，用空格分开
        var_pattern = r'(\w+)\s*:'
        variables += re.findall(var_pattern, premise)

    return theorem_name, premises, variables

# 示例文件路径
file_path = '/home2/wanglei/Project/testfolder/root/div_mul_div_cancel.lean'

# 提取定理信息
theorem_name, premises, variables = extract_theorem_info(file_path)

print(f"Theorem name: {theorem_name}")
print(f"Premises: {premises}")
print(f"Variables: {variables}")
