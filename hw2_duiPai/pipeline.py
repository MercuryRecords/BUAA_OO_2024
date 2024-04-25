import json
import os
import re
import sympy
import subprocess
from tqdm import tqdm
from gendata import genData
from subprocess import STDOUT, PIPE


def execute_java(stdin, fname):
    # cmd = ['java', '-version']
    # proc = subprocess.Popen(cmd, stdin=PIPE, stdout=PIPE, stderr=STDOUT)
    # stdout, stderr = proc.communicate()
    # stdout, stderr = proc.communicate(stdin.encode())
    cmd = ['java', '-jar', fname]
    proc = subprocess.Popen(cmd, stdin=PIPE, stdout=PIPE, stderr=STDOUT)
    stdout, stderr = proc.communicate(stdin.encode())
    return stdout.decode().strip()


def main(fname, times=100):
    exprDict = dict()
    for _ in tqdm(range(times)):
        poly, ans, cost = genData()
        # print(poly)
        strr = execute_java(poly.replace("**", "^"), fname)
        # print(strr)
        # while cost > 10000:
        #     poly, ans, cost = genData()
        ans = ans.replace("**", "^").replace(" ", "")
        # print(poly)
        forSympy = re.sub(r'\b0+(\d+)\b', r'\1', poly)
        # f = sympy.parse_expr(forSympy)

        # print(strr)
        try:
            g = sympy.parse_expr(strr.replace("^", "**"))
            if sympy.simplify(ans).equals(g):
                # print("AC : " + str(cnt))
                exprDict[poly] = (len(strr) / len(ans), ans)
                # print("x: {:.6f}".format(len(strr) / len(ans)))
                pass
            else:
                print("!!WA!! with " + "poly : " + poly.replace("**", "^"))
                print("yours: " + strr)
                print("sympy: ", end="")
                print(ans)
                return
        except Exception as e:
            print(e)
            print("!!WA!! with " + "poly : " + poly.replace("**", "^"))
            print("yours: " + strr)
            print("sympy: ", end="")
            print(ans)
            return
            pass
        os.system('cls')
    sorted_exprDict = sorted(exprDict.items(), key=lambda x: x[1][0], reverse=True)
    print("worst score (x): " + str(sorted_exprDict[0][1][0]))
    print("best score (x): " + str(sorted_exprDict[-1][1][0]))
    output = list()
    for i in range(10):
        tmpdict = dict()
        tmpdict['generated_expression'] = sorted_exprDict[i][0].replace("**", "^")
        tmpdict['sympy_simplified'] = sorted_exprDict[i][1][1]
        tmpdict['score'] = sorted_exprDict[i][1][0]
        output.append(tmpdict)

        # print(sorted_exprDict[i][0].replace("**", "^"))
        # print(sorted_exprDict[i][1][1])
        # print(sorted_exprDict[i][1][0])
    with open('output.json', 'w') as f:
        json.dump(output, f)


if __name__ == '__main__':
    main('oohomework_2024_21371285_hw_2.jar', 100)
