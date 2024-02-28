import sympy  # 如果报错显示没有这个包，就需要导入
from xeger import Xeger
import random
import subprocess
from subprocess import STDOUT, PIPE
from gendata import genData


def execute_java(stdin):
    cmd = ['java', '-jar', 'oohomework_2024_21371285_hw_1.jar']
    proc = subprocess.Popen(cmd, stdin=PIPE, stdout=PIPE, stderr=STDOUT)
    stdout, stderr = proc.communicate(stdin.encode())
    return stdout.decode().strip()


def main():
    x = sympy.Symbol('x')
    X = Xeger(limit=10)
    cnt = 1
    while True:
        cnt = cnt + 1
        if cnt % 1000 == 0:
            print(cnt)
        poly, ans = genData()
        # print(poly)
        f = sympy.parse_expr(poly)
        strr = execute_java(poly.replace("**", "^"))
        # print(strr)
        try:
            g = sympy.parse_expr(strr.replace("^", "**"))
            if sympy.simplify(f).equals(g):
                print("AC : " + str(cnt))
            else:
                print("!!WA!! with " + "poly : " + poly + " YOURS: " + strr)
                return
        except Exception as e:
            #  print(e)
            pass


if __name__ == '__main__':
    main()
