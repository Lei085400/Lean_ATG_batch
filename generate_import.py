import os

def generate_import_statements(folder_path, output_file):
    # 创建一个空列表，用于存储import语句
    import_statements = []

    # 遍历文件夹中的所有文件
    for filename in os.listdir(folder_path):
        # 仅处理扩展名为.lean的文件
        if filename.endswith('.lean'):
            # 去掉文件名的.lean后缀
            module_name = os.path.splitext(filename)[0]
            # 生成import语句
            import_statement = f"import AdaLean.{module_name}"
            # 将import语句添加到列表中
            import_statements.append(import_statement)

    # 将所有import语句写入指定的输出文件
    with open(output_file, 'w') as f:
        for statement in import_statements:
            f.write(statement + '\n')

# 指定文件夹路径和输出文件名
folder_path = '../AdaLean'  # 替换为实际文件夹路径
output_file = 'imports.txt'

# 生成import语句并写入文件
generate_import_statements(folder_path, output_file)
