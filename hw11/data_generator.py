from random import choice, randint, random

MAX_VALUE = 200
MAX_M_VALUE = 200
MAX_AGE = 200
MAX_LIMIT = 20
instrs = ['ap', 'ar', 'mr', 'qv', 'qci', 'qbs', 'qts', 'at', 'att', 'dt','dft', 'qtvs', 'qtav', 'qba', 'qcs', 'qsp','am' ,'am' ,'am' , 'cn','sm', 'qsv', 'qrm', 'arem', 'anm', 'sei', 'qp', 'dce', 'qm','am' ,'am' ,'am' , 'cn','sm', 'qsv', 'qrm', 'arem', 'anm', 'sei', 'qp', 'dce', 'qm']
messages = set()
relations = {}
#unsupport ln and lnl
#hw11 possiblity up


def generate(instr_num =10000, people_num = 50, tag_num = 500, message_num = 200,emoji_num = 200):
    k = random()
    if k < 0.1:
        return special_qtvs_I() # test 1111
    # elif k < 0.2:     
    #     return fuck_u_data(instr_num, 100) 
    elif k < 0.6:     
        return normal_data(instr_num, people_num, tag_num, message_num, emoji_num) # one tag one person
    elif k < 0.9:
        return extend_data(instr_num, people_num, tag_num, message_num, emoji_num) # one tag many person
    else:
        return all_random(instr_num, people_num, tag_num, message_num, emoji_num)  # test exception
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
def locate_tag(person_id, people_num, tag_num):
    return (person_id - 1) * int(tag_num / people_num )  + randint(0,int(tag_num / people_num - 1))

def locate_tag_overlapped(person_id, people_num, tag_num):
    return (person_id - 1) * int(tag_num / people_num/2 )  + randint(0, int(tag_num /people_num - 1))

def store_relation(id1, id2):
    relations[min(id1,id2)] = max(id1,id2)
    
def read_relation(people_num):
    if relations:
        random_key = choice(list(relations.keys()))
        random_value = relations[random_key]
        return random_key, random_value
    else:
        return randint(1, people_num), randint(1, people_num)
    

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

def message_instr(instr_name, message_id, social_content, type, person_id1, dst, message_type = 0):
    instr = instr_name + ' '
    instr += str(message_id) + ' '
    if (message_type == 1):
        instr += str('noticeMessage') + str(social_content) + ' '
    else: 
        instr += str(social_content) + ' '
    instr += str(type) + ' '
    instr += str(person_id1) + ' '
    instr += str(dst) + ' '
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

def generate_message(id, people_num, tag_num, emoji_num):
    message_type = randint(0,3)
    dst_type = randint(0,1)
    sender_id, reciever_id = read_relation(people_num)
    if message_type == 0:
        if dst_type == 0:
            return message_instr('am',id,randint(-1000,1000), dst_type,
                                 sender_id, reciever_id)
        else:
            return message_instr('am',id,randint(-1000,1000), dst_type,
                                 sender_id, locate_tag(sender_id,people_num,tag_num))
    elif message_type == 1:
        if dst_type == 0:
            return message_instr('aem',id,randint(1,emoji_num), dst_type,
                                 sender_id, reciever_id)
        else:
            return message_instr('aem',id,randint(1,emoji_num), dst_type,
                                 sender_id, locate_tag(sender_id,people_num,tag_num))
    elif message_type == 2:
        if dst_type == 0:
            return message_instr('arem',id,randint(0, 1000), dst_type,
                                 sender_id, reciever_id)
        else:
            return message_instr('arem',id,randint(0, 1000), dst_type,
                                 sender_id, locate_tag(sender_id,people_num,tag_num))
    elif message_type == 3:
        if dst_type == 0:
            return message_instr('anm',id,randint(0, 100000), dst_type,
                                 sender_id, reciever_id, message_type=1)
        else:
            return message_instr('anm',id,randint(0, 100000), dst_type,
                                 sender_id, locate_tag(sender_id,people_num,tag_num), message_type=1)
            

def normal_data(instr_num, people_num, tag_num, message_num, emoji_num):
    instrlist = []
    for i in range(1,randint(int(people_num * 0.9),people_num)):
        instrlist.append(person_instr('ap',i))
    for i in range(1,randint(int(tag_num * 0.9),tag_num)):
        instrlist.append(twin_arg_instr('at',int((i + (tag_num / people_num) - 1) / (tag_num / people_num)),i))
    for i in range(1,randint(people_num,people_num * people_num / 5)):
        id1 = randint(1,people_num)
        id2 = randint(1,people_num)
        instrlist.append(triplet_arg_instr('ar',id1 ,id2 ,randint(1,MAX_VALUE)))
        store_relation(id1, id2)
    for i in range(1, emoji_num):
        instrlist.append(sigle_arg_instr('sei', i))
    for i in range(1, randint(int(message_num * 0.9),message_num)):
        instrlist.append(generate_message(i,people_num,tag_num, emoji_num))
        messages.add(i)
    for i in range(instr_num-people_num-tag_num-emoji_num-message_num):
        instr = choice(instrs)
        if   instr == 'ap':
            instrlist.append(person_instr(instr,randint(1,people_num)))
        elif instr == 'ar':
            id1 = randint(1,people_num)
            id2 = randint(1,people_num)
            instrlist.append(triplet_arg_instr('ar',id1 ,id2 ,randint(1,MAX_VALUE)))
            store_relation(id1, id2)
        elif instr == 'mr':
            instrlist.append(triplet_arg_instr(instr,randint(1,people_num),randint(1,people_num),randint(-MAX_M_VALUE,MAX_M_VALUE * 0.3)))
        elif instr == 'qv' or instr == 'qci' or instr == 'qsp':
            instrlist.append(twin_arg_instr(instr,randint(1,people_num),randint(1,people_num)))
        elif instr == 'qbs' or instr == 'qts' or instr == 'qcs':
            instrlist.append(zero_arg_instr(instr))
        elif instr == 'at' or instr == 'dt':
            person_id = randint(1,people_num)
            instrlist.append(twin_arg_instr(instr,person_id,locate_tag(person_id,people_num,tag_num)))
        elif instr == 'att' or instr == 'dft':
            person_id = randint(1,people_num)
            instrlist.append(triplet_arg_instr(instr,randint(1,people_num),person_id,locate_tag(person_id,people_num,tag_num)))
        elif instr == 'qtvs' or instr == 'qtav':
            person_id = randint(1,people_num)
            instrlist.append(twin_arg_instr(instr,person_id,locate_tag(person_id,people_num,tag_num)))
        elif instr == 'qba':
            instrlist.append(sigle_arg_instr(instr,randint(1,people_num)))
        elif instr == 'am' or instr == 'arem' or instr == 'anm' or instr == 'aem':
            message_id = randint(1, message_num)
            generate_message(message_id, people_num,tag_num, emoji_num)
            messages.add(message_id)
        elif instr == 'sm':
            if messages:
                instrlist.append(sigle_arg_instr(instr, messages.pop()))
            else:
                instrlist.append(sigle_arg_instr(instr, randint(1, message_num)))
        elif instr == 'qsv' or instr == 'qrm' or instr == 'cn' or instr == 'qm':
            instrlist.append(sigle_arg_instr(instr, randint(1, people_num)))
        elif instr == 'sei' or instr == 'qp':
            instrlist.append(sigle_arg_instr(instr, randint(1,emoji_num)))
        elif instr == 'dce':
            instrlist.append(sigle_arg_instr(instr, randint(0, MAX_LIMIT)))
    return instrlist




def extend_data(instr_num, people_num, tag_num, message_num, emoji_num):
    instrlist = []
    for i in range(1,randint(int(people_num * 0.9),people_num)):
        instrlist.append(person_instr('ap',i))
    for i in range(5,randint(int(tag_num * 0.9),tag_num)):
        instrlist.append(twin_arg_instr('at',int((i / (tag_num / people_num)) ),i))
        instrlist.append(twin_arg_instr('at',int((i / (tag_num / people_num)) + 1), i))
    for i in range(1,randint(people_num,people_num * people_num / 5)):
        id1 = randint(1,people_num)
        id2 = randint(1,people_num)
        instrlist.append(triplet_arg_instr('ar',id1 ,id2 ,randint(1,MAX_VALUE)))
        store_relation(id1, id2)
    for i in range(1, randint(int(emoji_num * 0.9),emoji_num)):
        instrlist.append(sigle_arg_instr('sei', i))
    for i in range(1, randint(int(message_num * 0.9),message_num)):
        instrlist.append(generate_message(i,people_num,tag_num, emoji_num))
        messages.add(i)
    for i in range(instr_num-people_num-tag_num * 2-emoji_num-message_num):
        instr = choice(instrs)
        if   instr == 'ap':
            instrlist.append(person_instr(instr,randint(1,people_num)))
        elif instr == 'ar':
            id1 = randint(1,people_num)
            id2 = randint(1,people_num)
            instrlist.append(triplet_arg_instr('ar',id1 ,id2 ,randint(1,MAX_VALUE)))
            store_relation(id1, id2)
        elif instr == 'mr':
            instrlist.append(triplet_arg_instr(instr,randint(1,people_num),randint(1,people_num),randint(-MAX_M_VALUE,MAX_M_VALUE * 0.3)))
        elif instr == 'qv' or instr == 'qci' or instr == 'qsp':
            instrlist.append(twin_arg_instr(instr,randint(1,people_num),randint(1,people_num)))
        elif instr == 'qbs' or instr == 'qts' or instr == 'qcs':
            instrlist.append(zero_arg_instr(instr))
        elif instr == 'at' or instr == 'dt':
            person_id = randint(1,people_num)
            instrlist.append(twin_arg_instr(instr,person_id,locate_tag(person_id,people_num,tag_num)))
        elif instr == 'att' or instr == 'dft':
            person_id = randint(1,people_num)
            instrlist.append(triplet_arg_instr(instr,randint(1,people_num),person_id,locate_tag(person_id,people_num,tag_num)))
        elif instr == 'qtvs' or instr == 'qtav':
            person_id = randint(1,people_num)
            instrlist.append(twin_arg_instr(instr,person_id,locate_tag(person_id,people_num,tag_num)))
        elif instr == 'qba':
            instrlist.append(sigle_arg_instr(instr,randint(1,people_num)))
        elif instr == 'am' or instr == 'arem' or instr == 'anm' or instr == 'aem':
            message_id = randint(1, message_num)
            generate_message(message_id, people_num,tag_num, emoji_num)
            messages.add(message_id)
        elif instr == 'sm':
            if messages:
                instrlist.append(sigle_arg_instr(instr, messages.pop()))
            else:
                instrlist.append(sigle_arg_instr(instr, randint(1, message_num)))
        elif instr == 'qsv' or instr == 'qrm' or instr == 'cn' or instr == 'qm':
            instrlist.append(sigle_arg_instr(instr, randint(1, people_num)))
        elif instr == 'sei' or instr == 'qp':
            instrlist.append(sigle_arg_instr(instr, randint(1,emoji_num)))
        elif instr == 'dce':
            instrlist.append(sigle_arg_instr(instr, randint(0, MAX_LIMIT)))
    return instrlist

def all_random(instr_num, people_num, tag_num, emoji_num, message_num):
    instrlist = []
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
            person_id = randint(1,people_num)
            instrlist.append(twin_arg_instr(instr,person_id,locate_tag(person_id,people_num,tag_num)))
        elif instr == 'att' or instr == 'dft':
            person_id = randint(1,people_num)
            instrlist.append(triplet_arg_instr(instr,randint(1,people_num),person_id,locate_tag(person_id,people_num,tag_num)))
        elif instr == 'qtvs' or instr == 'qtav':
            person_id = randint(1,people_num)
            instrlist.append(twin_arg_instr(instr,person_id,locate_tag(person_id,people_num,tag_num)))
        elif instr == 'qba':
            instrlist.append(sigle_arg_instr(instr,randint(1,people_num)))
        elif instr == 'am' or instr == 'arem' or instr == 'anm' or instr == 'aem':
            generate_message(randint(1, message_num), people_num,tag_num, emoji_num)
        elif instr == 'sm':
            instrlist.append(sigle_arg_instr(instr, randint(1, message_num)))
        elif instr == 'qsv' or instr == 'qrm' or instr == 'cn' or instr == 'qm':
            instrlist.append(sigle_arg_instr(instr, randint(1, people_num)))
        elif instr == 'sei' or instr == 'qp':
            instrlist.append(sigle_arg_instr(instr, randint(1, emoji_num)))
        elif instr == 'dce':
            instrlist.append(sigle_arg_instr(instr, randint(0, MAX_LIMIT)))
    return instrlist


## seems no need in hw 11
def fuck_u_data(instr_num = 3000, n = 80, tag_num = 120):
    special_instr = ['mr', 'mr','mr','mr','qbs', 'qts', 'att', 'dft', 'qtvs','qtvs', 'qtav','qtav', 'qcs','qcs', 'qsp', 'qsp', 'qsp']
    instrlist = []
    instrlist.append(ln_generator(n))
    for i in range(1,randint(int(tag_num * 0.7),tag_num)):
        instrlist.append(twin_arg_instr('at',int((i + (tag_num / n) - 1) / (tag_num / n)),i))
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
            person_id = randint(1,n)
            instrlist.append(twin_arg_instr(instr,person_id,locate_tag(person_id,n,tag_num)))
        elif instr == 'att' or instr == 'dft':
            person_id = randint(1,n)
            instrlist.append(triplet_arg_instr(instr,randint(1,n),person_id,locate_tag(person_id,n,tag_num)))
        elif instr == 'qtvs' or instr == 'qtav':
            person_id = randint(1,n)
            instrlist.append(twin_arg_instr(instr,person_id,locate_tag(person_id,n,tag_num)))
        elif instr == 'qba':
            instrlist.append(sigle_arg_instr(instr,randint(1,n)))
    return instrlist

def special_qtvs_I(instr_num = 10000, n = 2000):
    instrlist = []
    instrlist.append(ln_generator(100))
    for i in range(101, n + 1):
        instrlist.append(person_instr('ap',i))
    for i in range(101, n + 1):
        instrlist.append(triplet_arg_instr('ar',1,i,randint(1,MAX_VALUE)))
    instrlist.append(twin_arg_instr('at',1,1))
    for i in range(1,n + 1):
        instrlist.append(triplet_arg_instr('att',i,1,1))
    for i in range(1,instr_num - 2 - (n - 100)*2 - n):
        instrlist.append(twin_arg_instr('qtvs',1,1))
    instrlist.append(twin_arg_instr('qtav',1,1))
    return instrlist

# seems no need
def special_qtvs_II():
    instrlist = []
    n = 800
    instr_num = 3000
    instrlist.append(ln_generator(100))
    for i in range(101, n + 1):
        instrlist.append(person_instr('ap',i))
    for i in range(101, n + 1):
        instrlist.append(triplet_arg_instr('ar',1,i,randint(1,MAX_VALUE)))
    instrlist.append(twin_arg_instr('at',1,1))
    for i in range(1,n + 1):
        instrlist.append(triplet_arg_instr('att',i,1,1))
    for i in range(1,n + 1):
        instrlist.append(triplet_arg_instr('mr',i,1, -199))
    instrlist.append(twin_arg_instr('qtvs',1,1))
    return instrlist

if __name__ == '__main__':
    # for entry in extend_data(100,10,20):
    #         print(entry,end='')
    for entry in normal_data(100,10,20,50,50):
        print(entry,end='')