from random import choice, randint, random, sample

MAX_VALUE = 200
MAX_M_VALUE = 200
MAX_AGE = 200
instrs = ['ap', 'mr', 'mr', 'mr', 'mr', 'mr', 'qv',
          'qci', 'qbs', 'qbs', 'qbs', 'qts', 'qts', 'qts']


# unsupport ln and lnl


def generate(sp=False, instr_num=3000 - 1, people_num=300):  # 互测强度
    if sp:
        return sp_data(instr_num, people_num)
    elif random() < 0.7:
        return normal_data(instr_num, people_num)
    else:
        return crazy_data(instr_num, people_num)


def person_instr(instr_name, id):
    instr = instr_name
    instr += ' '
    instr += str(id)
    instr += ' '
    instr += 'MS-' + str(id)
    instr += ' '
    instr += str(randint(0, MAX_AGE))
    instr += '\n'
    return instr


def relation_instr(instr_name, id1, id2, value):
    instr = instr_name
    instr += ' '
    instr += str(id1)
    instr += ' '
    instr += str(id2)
    instr += ' '
    instr += str(value)
    instr += '\n'
    return instr


def check_instr(instr_name, id1, id2):
    instr = instr_name
    instr += ' '
    instr += str(id1)
    instr += ' '
    instr += str(id2)
    instr += ' '
    instr += '\n'
    return instr


def overall_instr(instr_name):
    instr = instr_name
    instr += '\n'
    return instr


def ln_data(people_num):
    sample_num = min(people_num, 100)
    sample_list = sample(range(1, people_num + 1), sample_num)
    instrlist = []
    # 添加 load_network 指令和对应的 n+2 行数据
    instrlist.append(f"ln {sample_num}\n")
    instrlist.append(' '.join([str(i) for i in sample_list]) + '\n')
    instrlist.append(' '.join(["MS-" + str(i) for i in sample_list]) + '\n')
    instrlist.append(' '.join([str(randint(0, MAX_AGE)) for _ in sample_list]) + '\n')
    # 接下来是 n-1 行关系数据
    for i in range(1, sample_num):
        values = [1 if random() < 0.99 else 0 for _ in range(i)]
        instrlist.append(' '.join([str(v) for v in values]) + '\n')
    return instrlist


def normal_data(instr_num, people_num):
    instrlist = list()
    for i in range(randint(int(people_num * 0.7), people_num)):
        instrlist.append(person_instr('ap', i))
    for i in range(instr_num - people_num):
        instr = choice(instrs)
        if instr == 'ap':
            instrlist.append(person_instr('ap', i))
        elif instr == 'ar':
            instrlist.append(
                relation_instr('ar', randint(1, people_num), randint(1, people_num), randint(1, MAX_VALUE)))
        elif instr == 'mr':
            instrlist.append(relation_instr('mr', randint(1, people_num), randint(1, people_num),
                                            randint(-MAX_M_VALUE, MAX_M_VALUE)))
        elif instr == 'qv':
            instrlist.append(check_instr('qv', randint(1, people_num), randint(1, people_num)))
        elif instr == 'qci':
            instrlist.append(check_instr('qci', randint(1, people_num), randint(1, people_num)))
        elif instr == 'qbs':
            instrlist.append(overall_instr('qbs'))
        elif instr == 'qts':
            instrlist.append(overall_instr('qts'))
    return instrlist


def crazy_data(instr_num, people_num):
    instrlist = list()
    people_num = people_num
    for i in range(instr_num):
        instr = choice(instrs)
        if instr == 'ap':
            instrlist.append(person_instr('ap', i))
        elif instr == 'ar':
            instrlist.append(
                relation_instr('ar', randint(1, people_num), randint(1, people_num), randint(1, MAX_VALUE)))
        elif instr == 'mr':
            instrlist.append(relation_instr('mr', randint(1, people_num), randint(1, people_num),
                                            randint(-MAX_M_VALUE, MAX_M_VALUE)))
        elif instr == 'qv':
            instrlist.append(check_instr('qv', randint(1, people_num), randint(1, people_num)))
        elif instr == 'qci':
            instrlist.append(check_instr('qci', randint(1, people_num), randint(1, people_num)))
        elif instr == 'qbs':
            instrlist.append(overall_instr('qbs'))
        elif instr == 'qts':
            instrlist.append(overall_instr('qts'))
    return instrlist


def sp_data(instr_num, people_num):
    instrlist = ln_data(people_num)
    people_num = people_num
    for i in range(instr_num):
        instr = choice(instrs)
        if instr == 'ap':
            instrlist.append(person_instr('ap', randint(1, people_num)))
        elif instr == 'ar':
            instrlist.append(
                relation_instr('ar', randint(1, people_num), randint(1, people_num), randint(1, MAX_VALUE)))
        elif instr == 'mr':
            instrlist.append(relation_instr('mr', randint(1, people_num), randint(1, people_num),
                                            randint(1, MAX_M_VALUE) if random() < 0.3 else -200))
        elif instr == 'qv':
            instrlist.append(check_instr('qv', randint(1, people_num), randint(1, people_num)))
        elif instr == 'qci':
            instrlist.append(check_instr('qci', randint(1, people_num), randint(1, people_num)))
        elif instr == 'qbs':
            instrlist.append(overall_instr('qbs'))
        elif instr == 'qts':
            instrlist.append(overall_instr('qts'))
    return instrlist


if __name__ == '__main__':
    # print(generate(300, 100))
    instrs = generate(sp=True)
    for entry in instrs:
        print(entry, end="")
