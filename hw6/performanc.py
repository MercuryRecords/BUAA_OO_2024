import re
import numpy as np
import pandas as pd
from matplotlib import pyplot as plt
import seaborn as sns

class Elevator:
    def __init__(self):
        self.passengersInside = dict()
        self.floor = 1
        self.doorOpen = False
        self.received = set()
        self.resetting = False
        self.capacity = 6
        self.speed = 0.399
        self.toReset = False
        self.moves = 0
        self.arriveTime = 0
        self.openTime = 0
        self.acceptTime = 0
        self.toSetCapacity = 0
        self.toSetSpeed = 0
        self.resetTime = 0

    pass


class ElevatorSystem:
    def __init__(self):
        self.ELEVATOR_CNT = 6
        self.passengers = dict()
        self.passengers_id = set()
        self.elevators = [0 if i == 0 else Elevator() for i in range(self.ELEVATOR_CNT + 1)]

    def expected_time_cal(self,start_floor,end_floor):
        ans = 0
        minFloor = 1
        maxFloor = 11
        for i in range(minFloor,maxFloor):
            ans += (abs(start_floor - i) * 0.4)
        ans /= (maxFloor - minFloor + 1)
        ans += 0.4 + abs(start_floor - end_floor) * 0.4
        return ans
    
    def parse_person(self, tmp_input,sendTime):
        pattern = r'(\d+)-FROM-(\d+)-TO-(\d+)'

        # 使用re.search()方法查找匹配项
        match = re.search(pattern, tmp_input)

        # 如果匹配成功，提取三个整数
        if match:
            start_floor = int(match.group(2))
            end_floor = int(match.group(3))
            self.passengers[int(match.group(1))] = [start_floor,end_floor,self.expected_time_cal(start_floor,end_floor),sendTime,0]
            # start / end / expected time / send time / out time
            self.passengers_id.add(int(match.group(1)))
        else:
            print("Failed to match person request!")

    def check_arrive(self, tmp_output, tmp_time):
        parts = tmp_output.split('-')
        if len(parts) == 3:
            floor, elevator_id = int(parts[1]), int(parts[2])
            if self.elevators[elevator_id].resetting:
                print(f"Elevator{elevator_id}: moved when resetting.")
                return False
            if len(self.elevators[elevator_id].received) == 0:
                print(f"Elevator{elevator_id}: moved when no receives.")
                return False
            if self.elevators[elevator_id].toReset and self.elevators[elevator_id].moves >= 2:
                print(f"Elevator{elevator_id}: moved too much after reset accept.")
                return False
            if abs(floor - self.elevators[elevator_id].floor) != 1 or floor < 1 or floor > 11:
                print(f"Elevator{elevator_id}: Illegal move to {floor}.")
                return False
            if self.elevators[elevator_id].doorOpen:
                print(f"Elevator{elevator_id}: Door not closed.")
                return False
            if tmp_time - self.elevators[elevator_id].arriveTime < self.elevators[elevator_id].speed:
                print(f"Elevator{elevator_id}: Moved too Fast (faster than {self.elevators[elevator_id].speed}).")
                return False
            self.elevators[elevator_id].arriveTime = tmp_time
            self.elevators[elevator_id].floor = floor
            if self.elevators[elevator_id].toReset:
                self.elevators[elevator_id].moves += 1
            return True
        else:
            return False

    def check_open(self, tmp_output, tmp_time):
        # 解析输出字符串以获取电梯ID和楼层
        parts = tmp_output.split('-')
        if len(parts) == 3:
            floor, elevator_id = int(parts[1]), int(parts[2])
            # 检查电梯是否正在重置
            if self.elevators[elevator_id].resetting:
                print(f"Elevator{elevator_id}: opened when resetting.")
                return False
            # 检查电梯是否已经在指定楼层
            if self.elevators[elevator_id].floor != floor:
                print(f"Elevator{elevator_id}: Opened at incorrect floor {floor}.")
                return False
            # 检查电梯门是否已经打开
            if self.elevators[elevator_id].doorOpen:
                print(f"Elevator{elevator_id}: Door opened twice at floor {floor}.")
                return False
            # 更新电梯的开门时间
            self.elevators[elevator_id].doorOpen = True
            self.elevators[elevator_id].openTime = tmp_time
            return True
        else:
            return False

    def check_close(self, tmp_output, tmp_time):
        # 解析输出字符串以获取电梯ID
        parts = tmp_output.split('-')
        if len(parts) == 3:
            floor, elevator_id = int(parts[1]), int(parts[2])
            # 检查电梯是否正在重置
            if self.elevators[elevator_id].resetting:
                print(f"Elevator{elevator_id}: closed when resetting.")
                return False
            # 检查电梯门是否已经打开
            if not self.elevators[elevator_id].doorOpen:
                print(f"Elevator{elevator_id}: Door closed twice without being open.")
                return False
            # 检查电梯是否已经在指定楼层
            if self.elevators[elevator_id].floor != floor:
                print(f"Elevator{elevator_id}: Opened at incorrect floor {floor}.")
                return False
            # 检查电梯门关闭的时间间隔是否合理
            if tmp_time - self.elevators[elevator_id].openTime < 0.399:
                print(f"Elevator{elevator_id}: Door close too fast.")
                return False
            # 更新电梯的关门状态
            self.elevators[elevator_id].doorOpen = False
            return True
        else:
            return False

    def check_in(self, tmp_output):
        # 解析输出字符串以获取乘客ID、电梯ID和楼层
        parts = tmp_output.split('-')
        if len(parts) == 4:
            person_id, floor, elevator_id = int(parts[1]), int(parts[2]), int(parts[3])
            # 检查电梯是否正在重置
            if self.elevators[elevator_id].resetting:
                print(f"Elevator{elevator_id}: person in when resetting.")
                return False
            if person_id not in self.passengers:
                print(f"Elevator{elevator_id}: no such person {person_id} in request.")
                return False
            # 检查电梯是否有足够的空间容纳新的乘客
            if len(self.elevators[elevator_id].passengersInside) >= self.elevators[elevator_id].capacity:
                print(f"Elevator{elevator_id}: Full at {floor}.")
                return False
            # 检查电梯是否在指定楼层
            if self.elevators[elevator_id].floor != floor:
                print(f"Elevator{elevator_id}: Not arrive at {floor}.")
                return False
            # 检查电梯门是否打开
            if not self.elevators[elevator_id].doorOpen:
                print(f"Elevator{elevator_id}: Door not open at {floor}.")
                return False
            if self.passengers.get(person_id)[0] != floor:
                print(
                    f"Elevator{elevator_id}: person {person_id} at {self.passengers.get(person_id)[0]} instead of {floor}.")
                return False
            # 将乘客添加到电梯中
            self.elevators[elevator_id].passengersInside[person_id] = self.passengers.pop(person_id)
            return True
        else:
            return False

    def check_out(self, tmp_output,out_time):
        # 解析输出字符串以获取乘客ID和电梯ID
        parts = tmp_output.split('-')
        if len(parts) == 4:
            person_id, floor, elevator_id = int(parts[1]), int(parts[2]), int(parts[3])
            # 检查电梯是否正在重置
            if self.elevators[elevator_id].resetting:
                print(f"Elevator{elevator_id}: person out when resetting.")
                return False
            # 检查乘客是否在电梯内
            if person_id not in self.elevators[elevator_id].passengersInside:
                print(f"Elevator{elevator_id}: Person {person_id} not in elevator.")
                return False
            # 检查电梯门是否打开
            if not self.elevators[elevator_id].doorOpen:
                print(f"Elevator{elevator_id}: Door not open for person {person_id} to get out.")
                return False
            # 检查电梯是否在指定楼层
            if self.elevators[elevator_id].floor != floor:
                print(f"Elevator{elevator_id}: Not arrive at {floor}.")
                return False

            try:
                self.elevators[elevator_id].received.remove(person_id)
            except KeyError:
                print(f"Elevator{elevator_id}: Person {person_id} No received.")
                return False

            self.passengers_id.add(person_id)
            tmp_person = self.elevators[elevator_id].passengersInside.pop(person_id)
            tmp_person[0] = floor
            tmp_person[4] = out_time
            self.passengers[person_id] = tmp_person

            return True
        else:
            return False

    def check_receive(self, tmp_output):
        # 解析输出字符串以获取乘客ID和电梯ID
        parts = tmp_output.split('-')
        if len(parts) == 3:
            person_id, elevator_id = int(parts[1]), int(parts[2])
            # 检查电梯是否正在重置
            if self.elevators[elevator_id].resetting:
                print(f"Elevator{elevator_id}: cannot receive person {person_id} when resetting.")
                return False
            # 将乘客添加到电梯的接收列表中
            try:
                self.passengers_id.remove(person_id)
            except KeyError:
                print(f"Elevator{elevator_id}: Person {person_id} already received.")
                return False
            self.elevators[elevator_id].received.add(person_id)
            return True
        else:
            return False

    def reset_config(self, tmp_output, tmp_time):
        # 解析输出字符串以获取电梯ID
        parts = tmp_output.split('-')
        if len(parts) == 4:
            elevator_id, capacity, speed = int(parts[1]), int(parts[2]), float(parts[3])
            # 开始重置电梯配置
            self.elevators[elevator_id].toReset = True
            self.elevators[elevator_id].acceptTime = tmp_time
            self.elevators[elevator_id].moves = 0
            self.elevators[elevator_id].toSetCapacity = capacity
            self.elevators[elevator_id].toSetSpeed = speed
            return True
        else:
            return False

    def check_reset_begin(self, tmp_output, tmp_time):
        # 解析输出字符串以获取电梯ID
        parts = tmp_output.split('-')
        if len(parts) == 2:
            elevator_id = int(parts[1])
            # 检查电梯是否已经接受了重置请求
            if not self.elevators[elevator_id].toReset:
                print(f"Elevator{elevator_id}: No reset request when begin reset.")
                return False
            # 检查电梯是否为空
            if len(self.elevators[elevator_id].passengersInside) != 0:
                print(f"Elevator{elevator_id}: Elevator not empty when begin reset.")
                return False
            # 检查电梯门是否已经关闭
            if self.elevators[elevator_id].doorOpen:
                print(f"Elevator{elevator_id}: Elevator not closed when begin reset.")
                return False
            # 标记电梯开始重置
            self.elevators[elevator_id].resetting = True
            self.elevators[elevator_id].resetTime = tmp_time
            for id in self.elevators[elevator_id].received:
                self.passengers_id.add(id)
            self.elevators[elevator_id].received = set()
            return True
        else:
            return False

    def check_reset_end(self, tmp_output, tmp_time):
        # 解析输出字符串以获取电梯ID
        parts = tmp_output.split('-')
        if len(parts) == 2:
            elevator_id = int(parts[1])
            # 检查电梯是否正在重置
            if not self.elevators[elevator_id].resetting or not self.elevators[elevator_id].toReset:
                print(f"Elevator{elevator_id}: No resetting state when end reset.")
                return False
            # 检查自接受重置请求以来是否过了合理的时间
            if tmp_time - self.elevators[elevator_id].acceptTime > 5.01:
                print(f"Elevator{elevator_id}: Response too slow.")
                return False
            # 检查自开始重置以来是否过了过短的时间
            if tmp_time - self.elevators[elevator_id].resetTime < 1.19:
                print(f"Elevator{elevator_id}: Reset too fast.")
                return False
            # 完成电梯的重置
            self.elevators[elevator_id].toReset = False
            self.elevators[elevator_id].resetting = False
            self.elevators[elevator_id].speed = self.elevators[elevator_id].toSetSpeed - 0.01
            self.elevators[elevator_id].capacity = self.elevators[elevator_id].toSetCapacity
            return True
        else:
            return False

    def check_all_arrived(self):
        MT = 0
        MP = 0
        for id, passenger in self.passengers.items():
            if passenger[0] != passenger[1]:
                print(f"Person {id} not arrived.")
                return False
            else:
                missed_time = passenger[4] - passenger[3] - passenger[2]
                if(missed_time > MT):
                    MT = missed_time
                    MP = id
        print(MT,"  ", id)
        return True


def parse_time_stamp(tmp_str: str):
    to_parse = tmp_str.split(']')[0]
    return float(to_parse[1:])


def check_output_string(line: str, system: ElevatorSystem):
    tmp_time = parse_time_stamp(line)
    tmp_output = line.split(']')[1]
    if tmp_output.startswith("ARRIVE"):
        return system.check_arrive(tmp_output, tmp_time)
    if tmp_output.startswith("OPEN"):
        return system.check_open(tmp_output, tmp_time)
    if tmp_output.startswith("CLOSE"):
        return system.check_close(tmp_output, tmp_time)
    if tmp_output.startswith("IN"):
        return system.check_in(tmp_output)
    if tmp_output.startswith("OUT"):
        return system.check_out(tmp_output, tmp_time)
    if tmp_output.startswith("RECEIVE"):
        return system.check_receive(tmp_output)
    if tmp_output.startswith("RESET_ACCEPT"):
        return system.reset_config(tmp_output, tmp_time)
    if tmp_output.startswith("RESET_BEGIN"):
        return system.check_reset_begin(tmp_output, tmp_time)
    if tmp_output.startswith("RESET_END"):
        return system.check_reset_end(tmp_output, tmp_time)
    return False


def check(input_path="stdin.txt", output_path="stdout.txt"):
    mySystem = ElevatorSystem()
    with open(input_path, "r") as fin:
        for line in fin.readlines():
            tmp_input = line.split(']')[1]
            sendTime = parse_time_stamp(line)
            if not tmp_input.startswith("RESET"):
                mySystem.parse_person(tmp_input,sendTime)

    with open(output_path, "r") as fout:
        for line in fout.readlines():
            if not check_output_string(line, mySystem):
                print(line, end="")
                return False
        if not mySystem.check_all_arrived():
            return False

    # print("Everything's fine.")
    return True

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
                requests[request_id] = time_stamp + expectation

    pattern = re.compile(r"\[(\d+\.\d+)]OUT-(\d+)")
    with open(stdout, 'r') as file:
        for line in file:
            if 'ARRIVE' in line:
                N_ARRIVE += 1
            elif 'OPEN' in line:
                N_OPEN += 1
            elif 'CLOSE' in line:
                N_CLOSE += 1
            elif 'OUT' in line: 
                match = pattern.match(re.sub(r"\s+", "", line))
                time_stamp = float(match.group(1))
                passenger = int(match.group(2))
                requests[passenger] = time_stamp - requests[passenger]
        MT = max(requests.values())

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
    all_T_runs = [T_run for T_run, _, _ in performances.values()]
    all_MTs = [MT for _, MT, _ in performances.values()]
    all_Ws = [W for _, _, W in performances.values()]

    base_min_T_run, base_max_T_run = cal_base(all_T_runs)
    base_min_MT, base_max_MT = cal_base(all_MTs)
    base_min_W, base_max_W = cal_base(all_Ws)

    print(
        " {:>20}   {:>10}   {:>10}   {:>10}".format("jar_file_name", "T_run", "MT", "W"), end="")
    print("   {:>10}   {:>10}   {:>10}   {:>10}".format("r_T_run", "r_MT", "r_W", "score"))
    for system in performances.keys():
        r_T_run = r_function(performances[system][0], base_min_T_run, base_max_T_run)
        r_MT = r_function(performances[system][1], base_min_MT, base_max_MT)
        r_W = r_function(performances[system][2], base_min_W, base_max_W)
        score = 0.3 * r_T_run + 0.3 * r_MT + 0.4 * r_W
        tmp_str = (" {:>20}   {:>10.2f}   {:>10.2f}   {:>10.2f}".format(system, performances[system][0],
                                                                      performances[system][1],
                                                                      performances[system][2]) +
                   "   {:>10.2f}   {:>10.2f}   {:>10.2f}   {:>10.2f}".format(r_T_run, r_MT, r_W, score))
        tmp_list.append((score, tmp_str))

    sorted_tmp_list = sorted(tmp_list, key=lambda x: x[0], reverse=True)

    for score, tmp_str in sorted_tmp_list:
        print(tmp_str)


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

