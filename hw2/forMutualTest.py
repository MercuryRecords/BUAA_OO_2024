import datetime
import multiprocessing
import os
import re
import subprocess
import sympy
from tqdm import tqdm
from DataGenerator import DataGenerator

x_values = [0, 1, 2]
x = sympy.symbols('x')
GLOBAL_POINTER = 5

EXPRESSION_LENGTH = 50
EXPRESSION_COST = 5000
FUNCTION_LENGTH = 30
FUNCTION_COST = 2000


def compare(stdin, jar_names, checker):
    expr_dict = dict()
    expr_list = list()

    def exec_jar(jar_name):
        cmd = ['java', '-jar', jar_name]
        proc = subprocess.Popen(
            cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        stdout, stderr = proc.communicate(stdin.encode())
        yourAns = stdout.decode().strip()
        proc.terminate()
        proc.wait()
        proc.kill()

        # for format
        cmd = ['java', '-jar', checker]
        proc = subprocess.Popen(
            cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        output = '0\n' + yourAns
        stdout, stderr = proc.communicate(output.encode())
        yourAns = stdout.decode().strip()
        proc.terminate()
        proc.wait()
        proc.kill()

        if yourAns.startswith("Exception"):
            return [-1 for _ in x_values]

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


def compare_with_timeout(checker, jar_names=None):
    _input = ""
    while _input == "":
        try:
            output = ""
            DataGenerato = DataGenerator()
            num = DataGenerato.generateFunction(FUNCTION_LENGTH, FUNCTION_COST)
            output += str(num) + '\n'
            output += DataGenerato.getCustomDef()

            expr_len = EXPRESSION_LENGTH + 10
            cost = EXPRESSION_COST + 10
            while expr_len > EXPRESSION_LENGTH or cost > EXPRESSION_COST:
                global GLOBAL_POINTER
                expr, cost = DataGenerato.genData(
                    GLOBAL_POINTER, isFunction=False)
                GLOBAL_POINTER = GLOBAL_POINTER + 1
                expr_len = len(expr.replace(
                    "**", "^").replace(" ", "").replace("\t", ""))

            _input = (output + expr).replace("**", "^")
        except Exception as e:
            print(e)
            pass

    timeout = 10 * len(jar_names)

    with multiprocessing.Pool(processes=4) as pool:
        async_result = pool.apply_async(compare, (_input, jar_names, checker,))
        try:
            result = (async_result.get(timeout), _input, cost)
            pass
        except multiprocessing.TimeoutError:
            # print('OverTime..')
            result = (None,) * 3
        except subprocess.CalledProcessError as e:
            print(e.stderr)
            result = (None,) * 3
        except Exception as e:
            print(e)
            result = (None,) * 3
        finally:
            pool.close()  # 关闭进程池
            return result


def main(format_checker, times=100):
    files_and_dirs = os.listdir('.')
    jar_names = [f for f in files_and_dirs if f.endswith(
        '.jar') and f != format_checker]
    print(len(jar_names))
    for i in tqdm(range(times), position=0):
        isSame, stdin, cost = compare_with_timeout(format_checker, jar_names)
        if isSame is not None and isSame == False:
            time_str = datetime.datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
            filename = f"{cost}_at_{time_str}.txt"
            with open(filename, 'w') as f:
                f.write(stdin)
            # print(cost)
            # print(stdin)
            break


if __name__ == '__main__':
    main('checker.jar', 1000)
