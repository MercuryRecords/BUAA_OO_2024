import re
import sympy
import subprocess
from tqdm import tqdm
from gendata import genData
from subprocess import STDOUT, PIPE


def execute_java(stdin):
    cmd = ['java', '-jar', 'oohomework_2024_22371213_hw_1.jar']
    proc = subprocess.Popen(cmd, stdin=PIPE, stdout=PIPE, stderr=STDOUT)
    stdout, stderr = proc.communicate(stdin.encode())
    return stdout.decode().strip()


def main(times=1000):
    exprDict = dict()
    for cnt in tqdm(range(times)):
        poly, ans = genData()
        # print(poly)
        forSympy = re.sub(r'\b0+(\d+)\b', r'\1', poly)
        f = sympy.parse_expr(forSympy)
        strr = execute_java(poly.replace("**", "^"))
        # print(strr)
        try:
            g = sympy.parse_expr(strr.replace("^", "**"))
            if sympy.simplify(f).equals(g):
                # print("AC : " + str(cnt))
                ans = ans.replace("**", "^").replace(" ", "")
                exprDict[poly] = (len(strr) / len(ans), ans)
                # print("x: {:.6f}".format(len(strr) / len(ans)))
                pass
            else:
                print("!!WA!! with " + "poly : " + poly.replace("**", "^"))
                print("yours: " + strr)
                print("sympy: ", end="")
                print(f)
                # return
        except Exception as e:
            print(e)
            print("!!WA!! with " + "poly : " + poly.replace("**", "^"))
            print("yours: " + strr)
            print("sympy: ", end="")
            print(f)
            return
            pass
    sorted_exprDict = sorted(exprDict.items(), key=lambda x: x[1][0], reverse=True)
    for i in range(10):
        print(sorted_exprDict[i][0].replace("**", "^"))
        print(sorted_exprDict[i][1][1])
        print(sorted_exprDict[i][1][0])


if __name__ == '__main__':
    main()
