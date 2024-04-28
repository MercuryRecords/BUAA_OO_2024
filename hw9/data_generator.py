from random import choice, randint, random

MAX_VALUE = 200
MAX_M_VALUE = 200
MAX_AGE = 200
instrs = ['ap', 'mr','mr','mr','mr','mr','qbs','qts','qts','qts','qts']
#unsupport ln and lnl


def generate(instr_num =3000, people_num = 200):
    if random() < 0.3:     
        return fuck_u_data(instr_num, 100) 
    if random() < 0.7:     
        return normal_data(instr_num, people_num)
    elif random() < 0.9:
        return crazy_data(instr_num, people_num)
    else:
        return crazy_data(2000, 20)

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

def relation_instr(instr_name,id1,id2,value):
    instr = instr_name
    instr += ' '
    instr += str(id1)
    instr += ' '
    instr += str(id2)
    instr += ' '
    instr += str(value)
    instr += '\n'
    return instr

def check_instr(instr_name, id1,id2):
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

def normal_data(instr_num, people_num):
    instrlist = []
    for i in range(randint(int(people_num * 0.7),people_num)):
        instrlist.append(person_instr('ap',i))
    for i in range(instr_num-people_num):
        instr = choice(instrs)
        if   instr == 'ap':
            instrlist.append(person_instr('ap',i))
        elif instr == 'ar':
            instrlist.append(relation_instr('ar',randint(1,people_num),randint(1,people_num),randint(1,MAX_VALUE)))
        elif instr == 'mr':
            instrlist.append(relation_instr('mr',randint(1,people_num),randint(1,people_num),randint(-MAX_M_VALUE,MAX_M_VALUE * 0.3)))
        elif instr == 'qv':
            instrlist.append(check_instr('qv',randint(1,people_num),randint(1,people_num)))
        elif instr == 'qci':
            instrlist.append(check_instr('qci',randint(1,people_num),randint(1,people_num)))
        elif instr == 'qbs':
            instrlist.append(overall_instr('qbs'))
        elif instr == 'qts':
            instrlist.append(overall_instr('qts'))    
    return instrlist


def crazy_data(instr_num, people_num):
    instrlist = []
    people_num = people_num
    for i in range(instr_num):
        instr = choice(instrs)
        if   instr == 'ap':
            instrlist.append(person_instr('ap',i))
        elif instr == 'ar':
            instrlist.append(relation_instr('ar',randint(1,people_num),randint(1,people_num),randint(1,MAX_VALUE)))
        elif instr == 'mr':
            instrlist.append(relation_instr('mr',randint(1,people_num),randint(1,people_num),randint(-MAX_M_VALUE,MAX_M_VALUE * 0.3)))
        elif instr == 'qv':
            instrlist.append(check_instr('qv',randint(1,people_num),randint(1,people_num)))
        elif instr == 'qci':
            instrlist.append(check_instr('qci',randint(1,people_num),randint(1,people_num)))
        elif instr == 'qbs':
            instrlist.append(overall_instr('qbs'))
        elif instr == 'qts':
            instrlist.append(overall_instr('qts'))   
    return instrlist

def fuck_u_data(instr_num =3000, n = 100):
    instrlist = []
    instrlist.append(ln_generator(n))
    for i in range(instr_num-1):
        instr = choice(instrs)
        if   instr == 'ap':
            continue
        elif instr == 'ar':
            instrlist.append(relation_instr('ar',randint(1,n),randint(1,n),randint(1,MAX_VALUE)))
        elif instr == 'mr':
            instrlist.append(relation_instr('mr',randint(1,n),randint(1,n),randint(-MAX_M_VALUE,MAX_M_VALUE * 0.3)))
        elif instr == 'qv':
            instrlist.append(check_instr('qv',randint(1,n),randint(1,n)))
        elif instr == 'qci':
            instrlist.append(check_instr('qci',randint(1,n),randint(1,n)))
        elif instr == 'qbs':
            instrlist.append(overall_instr('qbs'))
        elif instr == 'qts':
            instrlist.append(overall_instr('qts'))    
    return instrlist

if __name__ == '__main__':
    for entry in fuck_u_data(100,100):
            print(entry,end='')