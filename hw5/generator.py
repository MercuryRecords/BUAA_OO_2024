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


def chooseTime():
    if INTENSIVE:
        return MAX_TIME * random() + 1
    else:
        return MAX_TIME


def chooseBy():
    return randint(MIN_ELEVATOR, MAX_ELEVATOR)


def genData(length=70):
    length = min(length, 30 * (MAX_ELEVATOR - MIN_ELEVATOR + 1))
    ans = []
    requests_by_elevator = [0 for _ in range(MAX_ELEVATOR + 1)]
    SPECIAL_START, SPECIAL_END = 11, 2
    # ans is a list of time, id, start, end, by

    for i in range(length):
        time = chooseTime()
        if randint(0, 1) == 0:
            start, end = chooseFloor(MIN_FLOOR, MAX_FLOOR)
        else:
            start, end = SPECIAL_START, SPECIAL_END
            if randint(0, 1) == 0:
                SPECIAL_START, SPECIAL_END = SPECIAL_END, SPECIAL_START
        by = chooseBy()
        while requests_by_elevator[by] >= 30:
            by = chooseBy()
        requests_by_elevator[by] += 1
        requests_by_elevator[0] += 1
        ans.append((time, f"[{time:.1f}]{i+1}-FROM-{start}-TO-{end}-BY-{by}\n"))
    ans.sort(key=lambda x: x[0])

    # for i in range(length):
    #     print(ans[i][1], end="")

    return [item[1] for item in ans]


if __name__ == "__main__":
    ans = genData(70)
