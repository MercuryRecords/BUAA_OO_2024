import os
import statistics
import subprocess
from tqdm import tqdm
from data_generator import generate, special_hack_delay_rebuild


def run(jar_file_name, stdin_path):
    name = jar_file_name.split(".")[0]
    # stdout_path = f"stdout_{name}.txt"

    powershell_command = "Measure-Command { Get-Content " + stdin_path + " | java -jar " + jar_file_name + " }"

    # 使用subprocess.run来执行PowerShell命令
    result = subprocess.run(["powershell", "-Command", powershell_command],
                            capture_output=True, text=True, shell=True)

    # 获取命令执行的输出
    output = result.stdout

    # 打印输出
    # print(jar_file_name, end=": ")
    # print(output.split(":")[-1].strip())
    return output.split(":")[-1].strip()


def get_jar_files(directory):
    jar_files = [f for f in os.listdir(directory) if f.endswith('.jar')]
    return jar_files


def benchmark(jar_files, i):
    jar_dict = dict()

    # stdin_path = f"stdin_sp.txt"
    stdin_path = f"stdin_51.txt"
    # with open(stdin_path, "w") as f:
    #     tmp_stdin = generate()
    #     for entry in tmp_stdin:
    #         f.write(entry)

    for jar_file in jar_files:
        costs = []  # 存储每次运行的成本
        times = 3
        for _ in range(times):
            cost = float(run(jar_file, stdin_path))
            costs.append(cost)  # 将每次运行的成本添加到列表中
        jar_dict[jar_file] = statistics.median(costs)  # 使用中位数而不是平均值

    sorted_avg_jar_dict = sorted(jar_dict.items(), key=lambda item: item[1])

    print("")
    for jar_file, cost in sorted_avg_jar_dict:
        print(f"{jar_file:<40} {cost:>10.2f}")

    return jar_dict


if __name__ == "__main__":
    directory = os.getcwd()  # 获取当前工作目录
    jar_files = get_jar_files(directory)
    total_jar_dict = {jar_file: [] for jar_file in jar_files}  # 初始化累积字典

    for i in tqdm(range(1)):
        current_jar_dict = benchmark(jar_files, i)
        for jar_file, avg_cost in current_jar_dict.items():
            total_jar_dict[jar_file].append(avg_cost)  # 将当前的平均成本追加到列表中

    # 计算每个jar的平均成本并创建新的字典
    # avg_jar_dict = {jar_file: sum(costs) / len(costs) for jar_file, costs in total_jar_dict.items()}
    avg_jar_dict = {jar_file: max(costs) for jar_file, costs in total_jar_dict.items()}

    sorted_avg_jar_dict = sorted(avg_jar_dict.items(), key=lambda item: item[1])

    str1 = "jar files"
    str2 = "avg cost"

    print(f"{str1:<40} {str2:>10}")
    # 打印最终的平均成本字典
    for jar_file, avg_cost in sorted_avg_jar_dict:
        print(f"{jar_file:<40} {avg_cost:>10.2f}")
