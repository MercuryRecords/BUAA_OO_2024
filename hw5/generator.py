from random import randint, random

MAX_TIME = 20
MAX_FLOOR = 11
MIN_FLOOR = 1
MAX_ID = 0
MAX_ELEVATOR = 6
MIN_ELEVATOR = 1

def chooseFloor(min,max):
    start, end = randint(min, max), randint(min, max)
    while start == end:
            start, end = randint(min, max), randint(min, max)
    return start,end

def chooseTime():
    return MAX_TIME * random()

def chooseBy():
    return randint(MIN_ELEVATOR, MAX_ELEVATOR)

def genData(length):
    ans = []
    # ans is a list of time,id,start,end,by

    for i in range(length):
        time = chooseTime()
        start,end = chooseFloor(MIN_ELEVATOR,MAX_FLOOR)
        by = chooseBy()
        ans.append((time,f"[{time:.1f}]{i}-FROM-{start}-TO-{end}-BY-{by}\n"))
    ans.sort(key=lambda x: x[0])
    return [item[1] for item in ans]


if __name__ == "__main__":
    ans = genData(20)
    for i in range(20):
        print(ans[i],end="")