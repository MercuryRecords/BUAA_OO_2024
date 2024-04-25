import re
DEBUG_FLAG = '#'


def check(file1 = 'stdout_1.txt', file2 = 'stdout_2.txt'):
    with open(file1, 'r') as f1, open(file2, 'r') as f2:
        for line1, line2 in zip(f1, f2):
            # 忽略以 # 开头的行
            if line1.startswith(DEBUG_FLAG) or line2.startswith('#'):
                continue
            # 去除行尾的换行符并比较
            if line1.rstrip() != line2.rstrip():
                print(file1 + '     ' + file2)
                print(line1 + ' not equals ' + line2)
                return False

        if sum(1 for line in f1 if not line.startswith(DEBUG_FLAG)) != sum(1 for line in f2 if not line.startswith('#')):
            return False
    return True

if __name__ == '__main__':
    print(check())