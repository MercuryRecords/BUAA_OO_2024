from random import choice, randint, random

MAX_VALUE = 200
MAX_M_VALUE = 200
MAX_AGE = 200
instrs = ['ap', 'ar', 'mr', 'qv', 'qci', 'qbs', 'qts', 'at', 'att',
          'dt', 'dft', 'qtvs', 'qtav', 'qba', 'qcs', 'qsp', 'qsp', 'qsp']
# unsupport ln and lnl


# unsupport ln and lnl


def generate(instr_num=2900, people_num=100, tag_num=500):
    k = random()
    if k < 0.2:
        return fuck_u_data(instr_num, people_num)
    elif k < 0.4:
        return normal_data(instr_num, people_num, tag_num)
    elif k < 0.6:
        return extend_data(instr_num, people_num, tag_num)
    elif k < 0.8:
        return all_random(instr_num, people_num, tag_num)
    elif k < 0.9:
        return special_qtvs()
    else:
        return special_hack_delay_rebuild()
    # return crazy_data(100, 20, 10)


def ln_generator(n=100, sparse=True if random() < 0.5 else False):
    instr = f"load_network {n}\n"
    for i in range(1, n+1):
        instr += str(i)
        instr += ' '
    instr += '\n'
    for i in range(1, n+1):
        instr += 'MA-'+str(i)
        instr += ' '
    instr += '\n'
    for i in range(1, n+1):
        instr += str(randint(0, MAX_AGE))
        instr += ' '
    instr += '\n'
    for i in range(1, n):
        for j in range(1, i + 1):
            if sparse:
                instr += str(randint(0, int(MAX_VALUE * 0.3))
                             if random() < 0.1 else 0)
            else:
                instr += str(1)
            instr += ' '
        instr += '\n'
    return instr


def locate_tag(person_id, people_num, tag_num):
    return person_id * int(tag_num / people_num) + randint(0, int(tag_num / people_num - 1))


def locate_tag_overlapped(person_id, people_num, tag_num):
    return person_id * int(tag_num / people_num/2) + randint(0, int(tag_num / people_num - 1))


def person_instr(instr_name, id):
    instr = instr_name
    instr += ' '
    instr += str(id)
    instr += ' '
    instr += 'MS-'+str(id)
    instr += ' '
    instr += str(randint(0, MAX_AGE))
    instr += '\n'
    return instr


def sigle_arg_instr(instr_name, id):
    instr = instr_name
    instr += ' '
    instr += str(id)
    instr += ' '
    instr += '\n'
    return instr


def triplet_arg_instr(instr_name, id1, id2, value):
    instr = instr_name
    instr += ' '
    instr += str(id1)
    instr += ' '
    instr += str(id2)
    instr += ' '
    instr += str(value)
    instr += '\n'
    return instr


def twin_arg_instr(instr_name, id1, id2):
    instr = instr_name
    instr += ' '
    instr += str(id1)
    instr += ' '
    instr += str(id2)
    instr += ' '
    instr += '\n'
    return instr


def zero_arg_instr(instr_name):
    instr = instr_name
    instr += '\n'
    return instr


def normal_data(instr_num, people_num, tag_num):
    instrlist = []
    for i in range(1, randint(int(people_num * 0.7), people_num)):
        instrlist.append(person_instr('ap', i))
    for i in range(1, randint(int(tag_num * 0.7), tag_num)):
        instrlist.append(twin_arg_instr(
            'at', int((i + (tag_num / people_num) - 1) / (tag_num / people_num)), i))
    for i in range(instr_num-people_num-tag_num):
        instr = choice(instrs)
        if instr == 'ap':
            instrlist.append(person_instr(instr, randint(1, people_num)))
        elif instr == 'ar':
            instrlist.append(triplet_arg_instr(instr, randint(
                1, people_num), randint(1, people_num), randint(1, MAX_VALUE)))
        elif instr == 'mr':
            instrlist.append(triplet_arg_instr(instr, randint(1, people_num), randint(1, people_num),
                                               randint(-MAX_M_VALUE, int(MAX_M_VALUE * 0.3))))
        elif instr == 'qv' or instr == 'qci' or instr == 'qsp':
            instrlist.append(twin_arg_instr(instr, randint(
                1, people_num), randint(1, people_num)))
        elif instr == 'qbs' or instr == 'qts' or instr == 'qcs':
            instrlist.append(zero_arg_instr(instr))
        elif instr == 'at' or instr == 'dt':
            person_id = randint(1, people_num)
            instrlist.append(twin_arg_instr(instr, person_id,
                             locate_tag(person_id, people_num, tag_num)))
        elif instr == 'att' or instr == 'dft':
            person_id = randint(1, people_num)
            instrlist.append(triplet_arg_instr(instr, randint(
                1, people_num), person_id, locate_tag(person_id, people_num, tag_num)))
        elif instr == 'qtvs' or instr == 'qtav':
            person_id = randint(1, people_num)
            instrlist.append(twin_arg_instr(instr, person_id,
                             locate_tag(person_id, people_num, tag_num)))
        elif instr == 'qba':
            instrlist.append(sigle_arg_instr(instr, randint(1, people_num)))
    return instrlist


def extend_data(instr_num, people_num, tag_num):
    instrlist = []
    for i in range(1, randint(int(people_num * 0.7), people_num)):
        instrlist.append(person_instr('ap', i))
    for i in range(5, randint(int(tag_num * 0.7), tag_num)):
        instrlist.append(twin_arg_instr(
            'at', int((i / (tag_num / people_num)) - 1), i))
        instrlist.append(twin_arg_instr(
            'at', int((i / (tag_num / people_num))), i))
    for i in range(instr_num-people_num-tag_num):
        instr = choice(instrs)
        if instr == 'ap':
            instrlist.append(person_instr(instr, randint(1, people_num)))
        elif instr == 'ar':
            instrlist.append(triplet_arg_instr(instr, randint(
                1, people_num), randint(1, people_num), randint(1, MAX_VALUE)))
        elif instr == 'mr':
            instrlist.append(triplet_arg_instr(instr, randint(1, people_num), randint(
                1, people_num), randint(-MAX_M_VALUE, MAX_M_VALUE * 0.3)))
        elif instr == 'qv' or instr == 'qci' or instr == 'qsp':
            instrlist.append(twin_arg_instr(instr, randint(
                1, people_num), randint(1, people_num)))
        elif instr == 'qbs' or instr == 'qts' or instr == 'qcs':
            instrlist.append(zero_arg_instr(instr))
        elif instr == 'at' or instr == 'dt':
            person_id = randint(1, people_num)
            instrlist.append(twin_arg_instr(
                instr, person_id, locate_tag_overlapped(person_id, people_num, tag_num)))
        elif instr == 'att' or instr == 'dft':
            person_id = randint(1, people_num)
            instrlist.append(triplet_arg_instr(instr, randint(
                1, people_num), person_id, locate_tag_overlapped(person_id, people_num, tag_num)))
        elif instr == 'qtvs' or instr == 'qtav':
            person_id = randint(1, people_num)
            instrlist.append(twin_arg_instr(
                instr, person_id, locate_tag_overlapped(person_id, people_num, tag_num)))
        elif instr == 'qba':
            instrlist.append(sigle_arg_instr(instr, randint(1, people_num)))
    return instrlist


def all_random(instr_num, people_num, tag_num):
    instrlist = []
    people_num = people_num
    for i in range(instr_num):
        instr = choice(instrs)
        if instr == 'ap':
            instrlist.append(person_instr(instr, randint(1, people_num)))
        elif instr == 'ar':
            instrlist.append(triplet_arg_instr(instr, randint(
                1, people_num), randint(1, people_num), randint(1, MAX_VALUE)))
        elif instr == 'mr':
            instrlist.append(triplet_arg_instr(instr, randint(1, people_num), randint(
                1, people_num), randint(-MAX_M_VALUE, MAX_M_VALUE * 0.3)))
        elif instr == 'qv' or instr == 'qci' or instr == 'qsp':
            instrlist.append(twin_arg_instr(instr, randint(
                1, people_num), randint(1, people_num)))
        elif instr == 'qbs' or instr == 'qts' or instr == 'qcs':
            instrlist.append(zero_arg_instr(instr))
        elif instr == 'at' or instr == 'dt':
            instrlist.append(twin_arg_instr(
                instr, randint(1, people_num), randint(1, tag_num)))
        elif instr == 'att' or instr == 'dft':
            instrlist.append(triplet_arg_instr(instr, randint(
                1, people_num), randint(1, people_num), randint(1, tag_num)))
        elif instr == 'qtvs' or instr == 'qtav':
            instrlist.append(twin_arg_instr(
                instr, randint(1, people_num), randint(1, tag_num)))
        elif instr == 'qba':
            instrlist.append(sigle_arg_instr(instr, randint(1, people_num)))
        return instrlist


def fuck_u_data(instr_num=3000, n=80, tag_num=120):
    special_instr = ['mr', 'mr', 'mr', 'mr', 'qbs', 'qts', 'att', 'dft',
                     'qtvs', 'qtvs', 'qtav', 'qtav', 'qcs', 'qcs', 'qsp', 'qsp', 'qsp']
    instrlist = []
    instrlist.append(ln_generator(n))
    for i in range(1, randint(int(tag_num * 0.7), tag_num)):
        instrlist.append(twin_arg_instr(
            'at', int((i + (tag_num / n) - 1) / (tag_num / n)), i))
    for i in range(instr_num-1 - tag_num):
        instr = choice(special_instr)
        if instr == 'ap':
            instrlist.append(person_instr(instr, randint(1, n)))
        elif instr == 'ar':
            instrlist.append(triplet_arg_instr(instr, randint(
                1, n), randint(1, n), randint(1, MAX_VALUE)))
        elif instr == 'mr':
            instrlist.append(triplet_arg_instr(instr, randint(1, n), randint(
                1, n), randint(-MAX_M_VALUE, MAX_M_VALUE * 0.3)))
        elif instr == 'qv' or instr == 'qci' or instr == 'qsp':
            instrlist.append(twin_arg_instr(
                instr, randint(1, n), randint(1, n)))
        elif instr == 'qbs' or instr == 'qts' or instr == 'qcs':
            instrlist.append(zero_arg_instr(instr))
        elif instr == 'at' or instr == 'dt':
            person_id = randint(1, n)
            instrlist.append(twin_arg_instr(instr, person_id,
                             locate_tag(person_id, n, tag_num)))
        elif instr == 'att' or instr == 'dft':
            person_id = randint(1, n)
            instrlist.append(triplet_arg_instr(instr, randint(
                1, n), person_id, locate_tag(person_id, n, tag_num)))
        elif instr == 'qtvs' or instr == 'qtav':
            person_id = randint(1, n)
            instrlist.append(twin_arg_instr(instr, person_id,
                             locate_tag(person_id, n, tag_num)))
        elif instr == 'qba':
            instrlist.append(sigle_arg_instr(instr, randint(1, n)))
    return instrlist


def special_qtvs_I(instr_num=10000, n=2000):
    instrlist = []
    instrlist.append(ln_generator(100))
    for i in range(101, n + 1):
        instrlist.append(person_instr('ap', i))
    for i in range(101, n + 1):
        instrlist.append(triplet_arg_instr('ar', 1, i, randint(1, MAX_VALUE)))
    instrlist.append(twin_arg_instr('at', 1, 1))
    for i in range(1, n + 1):
        instrlist.append(triplet_arg_instr('att', i, 1, 1))
    for i in range(1, instr_num - 2 - (n - 100)*2 - n):
        instrlist.append(twin_arg_instr('qtvs', 1, 1))
    instrlist.append(twin_arg_instr('qtav', 1, 1))
    return instrlist


def special_qtvs_II():
    instrlist = []
    n = 800
    instr_num = 3000
    instrlist.append(ln_generator(100))
    for i in range(101, n + 1):
        instrlist.append(person_instr('ap', i))
    for i in range(101, n + 1):
        instrlist.append(triplet_arg_instr('ar', 1, i, randint(1, MAX_VALUE)))
    instrlist.append(twin_arg_instr('at', 1, 1))
    for i in range(1, n + 1):
        instrlist.append(triplet_arg_instr('att', i, 1, 1))
    for i in range(1, n + 1):
        instrlist.append(triplet_arg_instr('mr', i, 1, -199))
    instrlist.append(twin_arg_instr('qtvs', 1, 1))
    return instrlist


def special_hack_delay_rebuild():
    instrlist = []
    i = 1
    instr_num = 3000
    instrlist.append(ln_generator(100))
    while i < instr_num:
        instrlist.append(triplet_arg_instr('mr', 11, 57, -200))
        i += 1
        instrlist.append(zero_arg_instr('qbs'))
        i += 1
        instrlist.append(triplet_arg_instr('ar', 11, 57, 1))
        i += 1
        instrlist.append(zero_arg_instr('qbs'))
        i += 1
    return instrlist


if __name__ == '__main__':
    # for entry in extend_data(100,10,20):
    #         print(entry,end='')
    for entry in special_qtvs_I():
        print(entry, end='')
