from random import choice, randint, random

MAX_VALUE = 200
MAX_M_VALUE = 200
MAX_AGE = 200
instrs = ['ap', 'ar', 'mr', 'qv', 'qci', 'qbs', 'qts', 'at', 'att', 'dft', 'qtvs', 'qtav', 'qba', 'qcs', 'qsp','qsp','qsp']
#unsupport ln and lnl


def generate(instr_num =3000, people_num = 200, tag_num = 200):
    if random() < 0.2:     
        return fuck_u_data(instr_num, 100) 
    if random() < 0.7:     
        return normal_data(instr_num, people_num, tag_num)
    elif random() < 0.9:
        return crazy_data(instr_num, people_num, tag_num)
    else:
        return crazy_data(2000, 20, 30)
    # return crazy_data(100, 20, 10)

def ln_generator(n):
    instr = f"load_network {n}\n"
    for i in range(1,n+1):
        instr += str(i)
        instr += ' '
    instr += '\n'
    for i in range(1,n+1):
        instr += 'MA-'+str(i)
        instr += ' '
    instr += '\n'
    for i in range(1,n+1):
        instr += str(randint(0, MAX_AGE))
        instr += ' '
    instr += '\n'
    for i in range(1,n):
        for j in range(1,i + 1):
            instr += str(randint(0, MAX_VALUE * 0.3))
            instr += ' '
        instr += '\n'
    return instr

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

def triplet_arg_instr(instr_name,id1,id2,value):
    instr = instr_name
    instr += ' '
    instr += str(id1)
    instr += ' '
    instr += str(id2)
    instr += ' '
    instr += str(value)
    instr += '\n'
    return instr

def twin_arg_instr(instr_name, id1,id2):
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
    for i in range(randint(int(people_num * 0.7),people_num)):
        instrlist.append(person_instr('ap',i))
    for i in range(randint(int(tag_num * 0.7),tag_num)):
        instrlist.append(twin_arg_instr('at',randint(1,people_num),i))
    for i in range(instr_num-people_num-tag_num):
        instr = choice(instrs)
        if   instr == 'ap':
            instrlist.append(person_instr(instr,randint(1,people_num)))
        elif instr == 'ar':
            instrlist.append(triplet_arg_instr(instr,randint(1,people_num),randint(1,people_num),randint(1,MAX_VALUE)))
        elif instr == 'mr':
            instrlist.append(triplet_arg_instr(instr,randint(1,people_num),randint(1,people_num),randint(-MAX_M_VALUE,MAX_M_VALUE * 0.3)))
        elif instr == 'qv' or instr == 'qci' or instr == 'qsp':
            instrlist.append(twin_arg_instr(instr,randint(1,people_num),randint(1,people_num)))
        elif instr == 'qbs' or instr == 'qts' or instr == 'qcs':
            instrlist.append(zero_arg_instr(instr))
        elif instr == 'at' or instr == 'dt':
            instrlist.append(twin_arg_instr(instr,randint(1,people_num),randint(1,tag_num)))
        elif instr == 'att' or instr == 'dft':
            instrlist.append(triplet_arg_instr(instr,randint(1,people_num),randint(1,people_num),randint(1,tag_num)))
        elif instr == 'qtvs' or instr == 'qtav':
            instrlist.append(twin_arg_instr(instr,randint(1,people_num),randint(1,tag_num)))
        elif instr == 'qba':
            instrlist.append(sigle_arg_instr(instr,randint(1,people_num)))
    return instrlist


def crazy_data(instr_num, people_num, tag_num):
    instrlist = []
    people_num = people_num
    for i in range(instr_num):
        instr = choice(instrs)
        if   instr == 'ap':
            instrlist.append(person_instr(instr,randint(1,people_num)))
        elif instr == 'ar':
            instrlist.append(triplet_arg_instr(instr,randint(1,people_num),randint(1,people_num),randint(1,MAX_VALUE)))
        elif instr == 'mr':
            instrlist.append(triplet_arg_instr(instr,randint(1,people_num),randint(1,people_num),randint(-MAX_M_VALUE,MAX_M_VALUE * 0.3)))
        elif instr == 'qv' or instr == 'qci' or instr == 'qsp':
            instrlist.append(twin_arg_instr(instr,randint(1,people_num),randint(1,people_num)))
        elif instr == 'qbs' or instr == 'qts' or instr == 'qcs':
            instrlist.append(zero_arg_instr(instr))
        elif instr == 'at' or instr == 'dt':
            instrlist.append(twin_arg_instr(instr,randint(1,people_num),randint(1,tag_num)))
        elif instr == 'att' or instr == 'dft':
            instrlist.append(triplet_arg_instr(instr,randint(1,people_num),randint(1,people_num),randint(1,tag_num)))
        elif instr == 'qtvs' or instr == 'qtav':
            instrlist.append(twin_arg_instr(instr,randint(1,people_num),randint(1,tag_num)))
        elif instr == 'qba':
            instrlist.append(sigle_arg_instr(instr,randint(1,people_num)))
        return instrlist

def fuck_u_data(instr_num = 3000, n = 80, tag_num = 120):
    special_instr = ['mr', 'qbs', 'qts', 'att', 'dft', 'qtvs','qtvs', 'qtav','qtav', 'qcs','qcs', 'qsp', 'qsp', 'qsp']
    instrlist = []
    instrlist.append(ln_generator(n))
    for i in range(randint(int(tag_num * 0.7),tag_num)):
        instrlist.append(twin_arg_instr('at',randint(1,n),i))
    for i in range(instr_num-1 - tag_num):
        instr = choice(special_instr)
        if   instr == 'ap':
            instrlist.append(person_instr(instr,randint(1,n)))
        elif instr == 'ar':
            instrlist.append(triplet_arg_instr(instr,randint(1,n),randint(1,n),randint(1,MAX_VALUE)))
        elif instr == 'mr':
            instrlist.append(triplet_arg_instr(instr,randint(1,n),randint(1,n),randint(-MAX_M_VALUE,MAX_M_VALUE * 0.3)))
        elif instr == 'qv' or instr == 'qci' or instr == 'qsp':
            instrlist.append(twin_arg_instr(instr,randint(1,n),randint(1,n)))
        elif instr == 'qbs' or instr == 'qts' or instr == 'qcs':
            instrlist.append(zero_arg_instr(instr))
        elif instr == 'at' or instr == 'dt':
            instrlist.append(twin_arg_instr(instr,randint(1,n),randint(1,tag_num)))
        elif instr == 'att' or instr == 'dft':
            instrlist.append(triplet_arg_instr(instr,randint(1,n),randint(1,n),randint(1,tag_num)))
        elif instr == 'qtvs' or instr == 'qtav':
            instrlist.append(twin_arg_instr(instr,randint(1,n),randint(1,tag_num)))
        elif instr == 'qba':
            instrlist.append(sigle_arg_instr(instr,randint(1,n)))
    return instrlist

if __name__ == '__main__':
    for entry in fuck_u_data(100,10,10):
            print(entry,end='')