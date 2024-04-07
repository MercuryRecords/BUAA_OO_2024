import re

import numpy as np
import pandas as pd
from matplotlib import pyplot as plt
import seaborn as sns


# 计算期望等待时间的函数
def ET(start_floor, dest_floor):
    # 定值参数
    F_min = 1
    F_max = 11
    T_open = 0.2
    T_close = 0.2
    T_move = 0.4

    # 计算移动时间期望
    move_expectation = 0
    for i in range(F_min, F_max + 1):
        move_expectation += abs(start_floor - i) * T_move
    move_expectation *= 1 / (F_max - F_min + 1)
    # 计算期望等待时间
    ET = T_open + T_close + abs(start_floor - dest_floor) * T_move + move_expectation
    return ET


def cal_performance(stdin, stdout):
    requests = {}
    W_ARRIVE = 0.4
    W_OPEN = 0.1
    W_CLOSE = 0.1

    N_ARRIVE = 0
    N_OPEN = 0
    N_CLOSE = 0
    pattern = re.compile(r"\[(\d+\.\d+)](\d+)-FROM-(\d+)-TO-(\d+)")

    with open(stdin, 'r') as file:
        for line in file:
            match = pattern.match(line)
            if match:
                time_stamp, request_id, start_floor, dest_floor = match.groups()
                start_floor = int(start_floor)
                dest_floor = int(dest_floor)

                expectation = ET(start_floor, dest_floor)
                request_id = int(request_id)
                time_stamp = float(time_stamp)
                requests[request_id] = [time_stamp + expectation, 0]

    pattern = re.compile(r"\[(\d+\.\d+)]OUT-(\d+)")
    with open(stdout, 'r') as file:
        for line in file:
            if 'ARRIVE' in line:
                N_ARRIVE += 1
            elif 'OPEN' in line:
                N_OPEN += 1
            elif 'CLOSE' in line:
                N_CLOSE += 1
            elif 'OUT' in line:  # TODO 先假设第一次下电梯就是到站
                match = pattern.match(re.sub(r"\s+", "", line))
                time_stamp = float(match.group(1))
                passenger = int(match.group(2))
                requests[passenger][1] = time_stamp - requests[passenger][0]
        MT = max([val for val in requests.values()])

    with open(stdout, 'rb') as file:
        pattern = re.compile(r"\[(\d+\.\d+)]")
        file.seek(-2, 2)
        while file.read(1) != b'\n':
            file.seek(-2, 1)
        last_line = file.readline().decode('utf-8')
        match = pattern.match(re.sub(r"\s+", "", last_line))
        last_time = float(match.group(1))

    W = W_ARRIVE * N_ARRIVE + W_OPEN * N_OPEN + W_CLOSE * N_CLOSE

    return last_time, MT, W


def r_function(x, base_min, base_max):
    if x <= base_min:
        return 1
    elif base_min < x <= base_max:
        return 1 - 10 ** (1 - (base_max - base_min) / (x - base_min))
    else:
        return 0


def cal_base(x_values):
    p = 0.25
    x_avg = sum(x_values) / len(x_values)
    x_min = min(x_values)
    x_max = max(x_values)

    base_min = p * x_avg + (1 - p) * x_min
    base_max = p * x_avg + (1 - p) * x_max
    return base_min, base_max


def cal(performances):
    tmp_list = list()
    result_dict = {}
    all_T_runs = [T_run for T_run, _, _ in performances.values()]
    all_MTs = [MT[1] for _, MT, _ in performances.values()]
    all_Ws = [W for _, _, W in performances.values()]

    base_min_T_run, base_max_T_run = cal_base(all_T_runs)
    base_min_MT, base_max_MT = cal_base(all_MTs)
    base_min_W, base_max_W = cal_base(all_Ws)

    # print(
    #     " {:>20}   {:>10}   {:>10}   {:>10}".format("jar_file_name", "T_run", "MT", "W"), end="")
    # print("   {:>10}   {:>10}   {:>10}   {:>10}".format("r_T_run", "r_MT", "r_W", "score"))
    for system in performances.keys():
        r_T_run = r_function(performances[system][0], base_min_T_run, base_max_T_run)
        r_MT = r_function(performances[system][1][1], base_min_MT, base_max_MT)
        r_W = r_function(performances[system][2], base_min_W, base_max_W)
        score = 0.3 * r_T_run + 0.3 * r_MT + 0.4 * r_W
        tmp_str = (" {:>20}   {:>10.2f}   {:>10.2f}   {:>10.2f}".format(system, performances[system][0],
                                                                        performances[system][1][1],
                                                                        performances[system][2]) +
                   "   {:>10.2f}   {:>10.2f}   {:>10.2f}   {:>10.2f}".format(r_T_run, r_MT, r_W, score))
        tmp_list.append((score, tmp_str))
        result_dict[system] = (r_T_run, r_MT, r_W, score)

    sorted_tmp_list = sorted(tmp_list, key=lambda x: x[0], reverse=True)

    # for score, tmp_str in sorted_tmp_list:
    #     print(tmp_str)

    return result_dict


# 主函数
def main():
    # cal_performance('stdin.txt', 'stdout.txt')
    # 设置base_min和base_max的值
    base_min = 0.2
    base_max = 0.5

    # 创建一个包含x值的数组，从base_min到base_max，包括这两个值
    x_values = np.linspace(base_min, base_max, 1000)

    # 计算每个x值对应的函数值
    y_values = [r_function(x, base_min, base_max) for x in x_values]

    # 绘制图像
    plt.plot(x_values, y_values, label='r_function')

    # 添加标题和标签
    plt.title('r_function(x, base_min, base_max)')
    plt.xlabel('x')
    plt.ylabel('r_function(x)')
    plt.legend()

    # 显示图像
    plt.show()

    table = [[ET(i, j) for j in range(1, 12)] for i in range(1, 12)]

    # 使用这个字典创建一个 DataFrame 对象
    df = pd.DataFrame(table)

    sns.heatmap(df, annot=True, cmap='coolwarm', fmt='.2f', square=True, cbar_kws={"shrink": .5})

    # 设置标题
    plt.title('ET')
    plt.xlabel('end')
    plt.ylabel('start')

    # 显示图形
    plt.show()

    base_min = 1
    base_max = 11

    # 创建一个包含x值的数组，从base_min到base_max，包括这两个值
    x_values = np.linspace(base_min, base_max, 1000)

    # 计算每个x值对应的函数值
    y_values = [ET(x, 2) for x in x_values]

    # 绘制图像
    plt.plot(x_values, y_values, label='r_function')

    # 添加标题和标签
    plt.title('ET at end 2')
    plt.xlabel('start_floor')
    plt.ylabel('ET(x)')
    plt.legend()

    # 显示图像
    plt.show()


if __name__ == "__main__":
    main()
