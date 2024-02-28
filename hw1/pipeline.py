import sympy
import subprocess
from tqdm import tqdm
from gendata import genData
from subprocess import STDOUT, PIPE


def execute_java(stdin):
    cmd = ['java', '-jar', 'oohomework_2024_21371285_hw_1.jar']
    proc = subprocess.Popen(cmd, stdin=PIPE, stdout=PIPE, stderr=STDOUT)
    stdout, stderr = proc.communicate(stdin.encode())
    return stdout.decode().strip()


def main(times=1000):
    for cnt in tqdm(range(times)):
        poly, ans = genData()
        # print(poly)
        f = sympy.parse_expr(poly.replace(' ', '').replace('\t', ''))
        strr = execute_java(poly.replace("**", "^"))
        # print(strr)
        try:
            g = sympy.parse_expr(strr.replace("^", "**"))
            if sympy.simplify(f).equals(g):
                # print("AC : " + str(cnt))
                pass
            else:
                print("!!WA!! with " + "poly : " + poly)
                print("yours: " + strr)
                print("sympy: ", end="")
                print(f)
                # return
        except Exception as e:
            print(e)
            print("!!WA!! with " + "poly : " + poly)
            print("yours: " + strr)
            print("sympy: ", end="")
            print(f)
            return
            pass


if __name__ == '__main__':
    main()
