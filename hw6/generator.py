from random import randint, random

MAX_FLOOR = 11
MIN_FLOOR = 1
MAX_ELEVATOR = randint(2, 6)
MIN_ELEVATOR = 1
INTENSIVE = True if randint(0, 1) == 0 else False
COMPRESSED = True if randint(0, 1) == 0 else False
MAX_TIME = 50 if not COMPRESSED else 10


def chooseFloor(_min, _max):
    start, end = randint(_min, _max), randint(_min, _max)
    while start == end:
        start, end = randint(_min, _max), randint(_min, _max)
    return start, end


def chooseTime(base: float = 0.0):
    if base != 0.0:
        return max(base + 5, MAX_TIME * random() + 1)
    else:
        if INTENSIVE:
            return min(MAX_TIME * random() + 1, 50.0)
        else:
            return MAX_TIME


def chooseElevator():
    return randint(MIN_ELEVATOR, MAX_ELEVATOR)


def chooseCapacity():
    tmp = [3, 4, 5, 6, 7, 8]
    return tmp[randint(0, len(tmp) - 1)]


def chooseSpeed():
    tmp = ["0.2", "0.3", "0.4", "0.5", "0.6"]
    return tmp[randint(0, len(tmp) - 1)]


def genData(length=70, mutualTest=False):
    length = min(length, 30 * (MAX_ELEVATOR - MIN_ELEVATOR + 1))
    ans = []
    SPECIAL_START, SPECIAL_END = 11, 2
    reset_cnt = 0
    last_reset = dict()
    for i in range(1, MAX_ELEVATOR + 1):
        last_reset[i] = 0.0
    alreadyReset = dict()
    for i in range(1, MAX_ELEVATOR + 1):
        alreadyReset[i] = False
    # ans is a list of time, id, start, end, by

    for i in range(length):
        if reset_cnt < 20 and randint(1, 10) < 4:  # 37分出reset
            id = chooseElevator()
            if (mutualTest and alreadyReset[id]) or last_reset[id] >= MAX_TIME - 5:
                time = chooseTime()
                if randint(0, 1) == 0:
                    start, end = chooseFloor(MIN_FLOOR, MAX_FLOOR)
                else:
                    start, end = SPECIAL_START, SPECIAL_END
                    if randint(0, 1) == 0:
                        SPECIAL_START, SPECIAL_END = SPECIAL_END, SPECIAL_START
                ans.append((time, f"[{time:.1f}]{i + 1}-FROM-{start}-TO-{end}\n"))
                continue

            if mutualTest:
                alreadyReset[id] = True
            time = chooseTime(last_reset[id])
            last_reset[id] = time
            capacity = chooseCapacity()
            speed = chooseSpeed()
            reset_cnt += 1
            ans.append((time, f"[{time:.1f}]RESET-Elevator-{id}-{capacity}-{speed}\n"))
        else:
            time = chooseTime()
            if randint(0, 1) == 0:
                start, end = chooseFloor(MIN_FLOOR, MAX_FLOOR)
            else:
                start, end = SPECIAL_START, SPECIAL_END
                if randint(0, 1) == 0:
                    SPECIAL_START, SPECIAL_END = SPECIAL_END, SPECIAL_START
            ans.append((time, f"[{time:.1f}]{i + 1}-FROM-{start}-TO-{end}\n"))
    ans.sort(key=lambda x: x[0])
    return [item[1] for item in ans]


if __name__ == "__main__":
    print(genData(70))
