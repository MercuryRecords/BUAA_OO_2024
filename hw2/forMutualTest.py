import multiprocessing
import os
import re
import subprocess

import sympy
from tqdm import tqdm

from DataGenerator import DataGenerator

x_values = [0, 1, 2]
x = sympy.symbols('x')


def compare(stdin, jar_names=None):
    expr_dict = dict()
    expr_list = list()

    def exec_jar(jar_name):
        cmd = ['java', '-jar', jar_name]
        proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        stdout, stderr = proc.communicate(stdin.encode())
        yourAns = stdout.decode().strip()
        yourExpr = yourAns.replace("^", "**")
        yourAns = re.sub(r'\b0+(\d+)\b', r'\1', yourExpr)
        exprAns = sympy.expand_multinomial(yourAns)
        results = [exprAns.subs(x, x_val) for x_val in x_values]
        # return exprAns
        return results

    for fname in jar_names:
        expr_list.append(exec_jar(fname))

    for i in range(len(expr_list) - 1):
        if expr_list[i] != expr_list[i + 1]:
            return False
    return True


def compare_with_timeout(jar_names=None):
    output = ""
    DataGenerato = DataGenerator()
    num = DataGenerato.generateFunction()
    output += str(num) + '\n'
    output += DataGenerato.getCustomDef()

    expr_len = 210
    while expr_len > 200:
        expr, cost = DataGenerato.getExpr(False)
        expr_len = len(expr.replace("**", "^").replace(" ", "").replace("\t", ""))

    input = (output + expr).replace("**", "^")

    timeout = 10 * len(jar_names)

    with multiprocessing.Pool(processes=1) as pool:
        async_result = pool.apply_async(compare, (input, jar_names,))
        try:
            result = (async_result.get(timeout), input, cost)
            pass
        except multiprocessing.TimeoutError:
            # print('OverTime..')
            result = (None,) * 3
        except subprocess.CalledProcessError as e:
            print(e.stderr)
            result = (None,) * 3
        except Exception:
            result = (None,) * 3
        finally:
            pool.close()  # 关闭进程池
            return result


def main(times=100):
    files_and_dirs = os.listdir('.')
    jar_names = [f for f in files_and_dirs if f.endswith('.jar')]
    for i in tqdm(range(times), position=0):
        isSame, stdin, cost = compare_with_timeout(jar_names)
        if isSame is not None and isSame == False:
            print(cost)
            print(stdin)
            break


if __name__ == '__main__':
    main(1000)
