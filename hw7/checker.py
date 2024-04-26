import re

DEBUG_FLAG = '#'


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
        
        self.transfer = 0
        self.doubleType = '0' # 0代表非双轿厢，A代表下轿箱 B代表上轿箱
        self.occupied = False

    pass


class ElevatorSystem:
    def __init__(self):
        self.ELEVATOR_CNT = 6
        self.passengers = dict()
        self.passengers_id = set()
        self.elevators = [0 if i == 0 else Elevator() for i in range(self.ELEVATOR_CNT + 11)]

    def parse_person(self, tmp_input):
        pattern = r'(\d+)-FROM-(\d+)-TO-(\d+)'

        # 使用re.search()方法查找匹配项
        match = re.search(pattern, tmp_input)

        # 如果匹配成功，提取三个整数
        if match:
            self.passengers[int(match.group(1))] = [int(match.group(2)), int(match.group(3))]
            self.passengers_id.add(int(match.group(1)))
        else:
            print("Failed to match person request!")

    def check_double(self, tmp_output):
        parts = tmp_output.split('-')
        elevator_id = int(parts[-2])
        if self.elevators[elevator_id].doubleType == '0' :
            return False
        return True
    
    def check_one_move(self, elevator_id, floor) :
        if self.elevators[elevator_id].doubleType == '0' :
            return False
        dx = 1
        if self.elevators[elevator_id].doubleType == 'A' :
            dx = -1
        if (self.elevators[elevator_id].transfer + dx == floor) :
            return True
        return False
    
    def check_arrive(self, tmp_output, tmp_time):
        parts = tmp_output.split('-')
        floor = 0
        elevator_id = 0
        if len(parts) == 3:
            floor, elevator_id = int(parts[1]), int(parts[2])
        else:
            return False

        brother = elevator_id
        if self.elevators[elevator_id].doubleType == 'A' :
            brother = elevator_id + 10

        if self.elevators[brother].occupied and floor == self.elevators[elevator_id].transfer :
            print(f"Elevator{elevator_id}: brother in here.")
            return False
        if self.elevators[elevator_id].resetting:
            print(f"Elevator{elevator_id}: moved when resetting.")
            return False
        if len(self.elevators[elevator_id].received) == 0 and not self.check_one_move(elevator_id, floor):
            print(f"Elevator{elevator_id}: moved when no receives.")
            return False
        if self.elevators[elevator_id].toReset and self.elevators[elevator_id].moves >= 2:
            print(f"Elevator{elevator_id}: moved too much after reset accept.: " + str(self.elevators[elevator_id].moves))
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
        
        if self.elevators[elevator_id].floor == self.elevators[elevator_id].transfer :
            self.elevators[elevator_id].occupied = False
        if floor == self.elevators[elevator_id].transfer :
            self.elevators[elevator_id].occupied = True

        self.elevators[elevator_id].arriveTime = tmp_time
        self.elevators[elevator_id].floor = floor
        if self.elevators[elevator_id].toReset:
            self.elevators[elevator_id].moves += 1
        return True

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

    def check_out(self, tmp_output):
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
        elif len(parts) == 5:
            elevator_id, transfer, capacity, speed = int(parts[1]), int(parts[2]), int(parts[3]), float(parts[4])
            # 开始重置电梯配置
            self.elevators[elevator_id].toReset = True
            self.elevators[elevator_id].acceptTime = tmp_time
            self.elevators[elevator_id].moves = 0
            self.elevators[elevator_id].toSetCapacity = capacity
            self.elevators[elevator_id].toSetSpeed = speed
            self.elevators[elevator_id].transfer = transfer
            self.elevators[elevator_id].doubleType = 'A'

            self.elevators[elevator_id + 10].toReset = True
            self.elevators[elevator_id + 10].acceptTime = tmp_time
            self.elevators[elevator_id + 10].moves = 0
            self.elevators[elevator_id + 10].toSetCapacity = capacity
            self.elevators[elevator_id + 10].toSetSpeed = speed
            self.elevators[elevator_id + 10].transfer = transfer
            self.elevators[elevator_id + 10].doubleType = 'B'
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
            if (self.elevators[elevator_id].doubleType == 'A') :
                self.elevators[elevator_id].floor = self.elevators[elevator_id].transfer - 1
                self.elevators[elevator_id + 10].floor = self.elevators[elevator_id + 10].transfer + 1

                self.elevators[elevator_id + 10].toReset = False
                self.elevators[elevator_id + 10].resetting = False
                self.elevators[elevator_id + 10].speed = self.elevators[elevator_id + 10].toSetSpeed - 0.01
                self.elevators[elevator_id + 10].capacity = self.elevators[elevator_id + 10].toSetCapacity
            return True
        else:
            return False

    def check_all_arrived(self):
        for id, passenger in self.passengers.items():
            if passenger[0] != passenger[1]:
                print(f"Person {id} not arrived.")
                return False
        return True


def parse_time_stamp(tmp_str: str):
    to_parse = tmp_str.split(']')[0]
    try:
        ret = float(to_parse[1:])
        return ret
    except ValueError:
        return None


def check_output_string(line: str, system: ElevatorSystem, debug: bool):
    if line.startswith(DEBUG_FLAG) and debug:
        return True
    tmp_time = parse_time_stamp(line)
    if tmp_time is None:
        return False
    tmp_output = line.split(']')[1].strip()
    if tmp_output.split('-')[-1] == "A" or tmp_output.split('-')[-1] == "B" :
        flag = system.check_double(tmp_output)
        if flag == False:
            return False
        elif tmp_output.split('-')[-1] == "B":
            tmp_output = tmp_output[:-3] + "1" + tmp_output[-3]
        else :
            tmp_output = tmp_output[:-2]

    if tmp_output.startswith("ARRIVE"):
        return system.check_arrive(tmp_output, tmp_time)
    if tmp_output.startswith("OPEN"):
        return system.check_open(tmp_output, tmp_time)
    if tmp_output.startswith("CLOSE"):
        return system.check_close(tmp_output, tmp_time)
    if tmp_output.startswith("IN"):
        return system.check_in(tmp_output)
    if tmp_output.startswith("OUT"):
        return system.check_out(tmp_output)
    if tmp_output.startswith("RECEIVE"):
        return system.check_receive(tmp_output)
    if tmp_output.startswith("RESET_ACCEPT"):
        return system.reset_config(tmp_output, tmp_time)
    if tmp_output.startswith("RESET_BEGIN"):
        return system.check_reset_begin(tmp_output, tmp_time)
    if tmp_output.startswith("RESET_END"):
        return system.check_reset_end(tmp_output, tmp_time)
    return True


def check(input_path="stdin.txt", output_path="stdout.txt", debug=False):
    mySystem = ElevatorSystem()
    with open(input_path, "r") as fin:
        for line in fin.readlines():
            tmp_input = line.split(']')[1]
            if not tmp_input.startswith("RESET"):
                mySystem.parse_person(tmp_input)

    with open(output_path, "r") as fout:
        for line in fout.readlines():
            line = line.strip()
            if not check_output_string(line, mySystem, debug):
                print(line, end=" ")
                return False
                # continue
        if not mySystem.check_all_arrived():
            return False

    # print("Everything's fine.")
    return True


def main():
    print(check(input_path="stdin.txt", output_path="stdout.txt", debug=False))


if __name__ == "__main__":
    main()
