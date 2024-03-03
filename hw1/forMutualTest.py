import re
import subprocess
import time

import sympy
from tqdm import tqdm

from gendata import genData


def execute_java(stdin, fname):
    cmd = ['java', '-jar', fname]
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    stdout, stderr = proc.communicate(stdin.encode())
    return stdout.decode().strip()


def main():
    cnt = 0
    while cnt < 100:
        hack_list = list()
        poly, ans, cost = genData()
        real_poly = poly.replace("**", "^").replace(" ", "").replace("\t", "")
        for_copy = poly.replace("**", "^")
        while cost > 10000 or len(real_poly) > 50:
            poly, ans, cost = genData()
            real_poly = poly.replace("**", "^").replace(" ", "").replace("\t", "")
            for_copy = poly.replace("**", "^")

        forSympy = re.sub(r'\b0+(\d+)\b', r'\1', poly)
        f = sympy.parse_expr(forSympy)
        for i in range(1, 9):
            start = time.perf_counter()  # 记录开始时间
            strr = execute_java(for_copy, 'code{}.jar'.format(i))
            end = time.perf_counter()  # 记录结束时间
            elapsed = end - start  # 计算经过的时间（单位为秒）
            if elapsed > 10:
                hack_list.append(i)
                continue
            try:
                g = sympy.parse_expr(strr.replace("^", "**"))
                if sympy.simplify(f).equals(g):
                    pass
                else:
                    hack_list.append(i)
                    continue
            except Exception as e:
                print(str(i) + ": ")
                print(e)
                hack_list.append(i)
                continue
        if len(hack_list) > 0:
            with open('hacking.txt', 'a+') as f:
                f.write(for_copy)
                cnt += 1
                print(cnt)


if __name__ == '__main__':
    main()
