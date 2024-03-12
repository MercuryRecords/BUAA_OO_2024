import itertools
import multiprocessing
import os
import random
import re
import signal
import subprocess
import sympy
from subprocess import STDOUT, PIPE
from tqdm import tqdm


def replaceFunction(stdin):
    cmd = ['java', '-jar', "replace.jar"]
    proc = subprocess.Popen(cmd, stdin=PIPE, stdout=PIPE, stderr=STDOUT)
    stdout, stderr = proc.communicate(stdin.encode())
    return stdout.decode().strip()


class DataGenerator:
    def __init__(self):
        self.actual_para_limit = 500
        self.func_list_hed = dict()
        self.func_list_par = dict()
        self.func_list_exp = dict()
        self.intPool = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
                        10, 11, 12, 13, 14, 15, 16,
                        2147483647, 5223333333,
                        5423333333,
                        1145141919810,
                        23333333234212332333,
                        23333333233335467543,
                        23495723459823752039
                        ]  # 常量池
        self.hasWhiteSpace = True  # 是否加入空白字符
        self.hasLeadZeros = True  # 数字是否有前导零，如果传入sympy的表达式中数字有前导零，sympy将无法识别
        self.maxTerm = 3  # 表达式中的最大项数
        self.maxFactor = 2  # 项中最大因子个数
        self.specialData = ["exp((-x))", "x-x", "-1",
                            "1", "exp((-2*x))"]  # 可以放一些特殊数据\
        self.dataCost = [3, 1, 2, 2, 3]
        self.globalPointer = len(self.specialData)
        self.funcNames = ['f', 'g', 'h']
        self.used = dict()
        self.funcName = 'f'
        self.funcVars = []
        self.isFunction = False

    def rd(self, a, b):
        return random.randint(a, b)

    def getWhiteSpace(self):
        if not self.hasWhiteSpace:
            return ""
        blankTerm = ""
        cnt = self.rd(0, 2)
        for i in range(cnt):
            type = self.rd(0, 1)
            if type == 0:
                blankTerm = blankTerm + " "
            else:
                blankTerm = blankTerm + "\t"
        return blankTerm

    def getSymbol(self):
        if self.rd(0, 1) == 1:
            return "+"
        else:
            return "-"

    def getNum(self, posOnly):
        result = ""
        integer = self.intPool[self.rd(0, len(self.intPool) - 1)]
        cost = len(str(integer))
        iszero = self.rd(0, 2)
        for i in range(iszero):
            result = result + "0"
        if not self.hasLeadZeros:
            result = ""
        result = result + str(integer)
        if self.rd(0, 1) == 1:
            if posOnly:
                result = "+" + result
            else:
                result = self.getSymbol() + result
                # print("num:"+result)
            cost += 1
        return result, cost

    def getExponent(self):
        result = "**"
        result = result + self.getWhiteSpace()
        case = self.rd(0, 8)
        cost = len(str(case))
        if self.rd(0, 1) == 1:
            result = result + "+"
            cost += 1
        result = result + str(case)
        # print("exponent: " + result)
        return result, cost

    def getPower(self):
        if self.isFunction:
            var = self.funcVars
            addNum = len(var)
            case = self.rd(0, addNum - 1)
            result = var[case]
            if self.rd(0, 1) == 1:
                toAdd, _ = self.getExponent()
                result = result + self.getWhiteSpace() + toAdd
        else:
            result = "x"
            if self.rd(0, 1) == 1:
                toAdd, _ = self.getExponent()
                result = result + self.getWhiteSpace() + toAdd
        # print("Power:"+result)
        return result, 1

    def getExpoFunc(self):
        result = "exp"
        result += self.getWhiteSpace()
        result += "("
        result += self.getWhiteSpace()
        toAdd, factorCost = self.getFactor(True)
        factorCost += 1
        result += toAdd
        result += self.getWhiteSpace()
        result += ")"
        if self.rd(0, 1) == 1:
            toAdd, expCost = self.getExponent()
            result = result + self.getWhiteSpace() + toAdd
            factorCost += 2 ** expCost
        return result, factorCost

    def getFuncFactor(self):
        cost = 1
        name = random.choice(list(self.func_list_par.keys()))
        result = name + self.getWhiteSpace() + '('
        for index, var in enumerate(self.func_list_par[name]):
            result += self.getWhiteSpace()
            toAdd, factorCost = self.getFactor(True, True)
            cost *= factorCost * 2
            result += toAdd
            if index < len(self.func_list_par[name]) - 1:
                result += ","
            else:
                result += ")"
        return result, factorCost

    def getFactor(self, genExpr, asActual=False):
        factor = self.rd(0, 9)
        if factor <= 1:
            toAdd, factorCost = self.getNum(False)
        elif factor <= 3:
            toAdd, factorCost = self.getPower()
        elif factor <= 5 and genExpr:
            toAdd, factorCost = self.getExpr(True)
        elif factor <= 7:
            toAdd, factorCost = self.getExpoFunc()
        elif factor <= 13 and (self.isFunction == False) and (len(self.func_list_par) > 0):
            toAdd, factorCost = self.getFuncFactor()
        else:
            toAdd = "0"
            factorCost = 1
        while asActual and factorCost > self.actual_para_limit:
            factor = self.rd(0, 13)
            if factor <= 3:
                toAdd, factorCost = self.getNum(False)
            elif factor <= 7:
                toAdd, factorCost = self.getPower()
            elif factor <= 11 and genExpr:
                toAdd, factorCost = self.getExpr(True)
            elif factor <= 12:
                toAdd, factorCost = self.getExpoFunc()
            elif factor <= 13 and (self.isFunction == False) and (len(self.func_list_par) > 0):
                toAdd, factorCost = self.getFuncFactor()
            else:
                toAdd = "0"
                factorCost = 1
        return toAdd, factorCost

    def getTerm(self, genExpr):
        factorNum = self.rd(1, self.maxFactor)
        result = ""
        cost = 1
        if self.rd(0, 1) == 1:
            result = self.getSymbol() + self.getWhiteSpace()
        for i in range(factorNum):
            toAdd, factorCost = self.getFactor(genExpr)
            result += toAdd
            cost *= factorCost
            if i < factorNum - 1:
                result = result + self.getWhiteSpace() + "*" + self.getWhiteSpace()
                # print("term:"+result)
        return result, cost

    def getExpr(self, isFactor):
        termNum = self.rd(1, self.maxTerm)
        result = self.getWhiteSpace()
        cost = 0
        genExpr = True
        if isFactor:
            genExpr = False
        for i in range(termNum):
            toAdd, termCost = self.getTerm(genExpr)
            result = result + self.getSymbol() + self.getWhiteSpace() + \
                toAdd + self.getWhiteSpace()
            cost += termCost
        if isFactor:
            result = "(" + result + ")"
            if self.rd(0, 1) == 1:
                toAdd, expCost = self.getExponent()
                result = result + self.getWhiteSpace() + toAdd
                cost = max(cost, 2) ** max(expCost, 1)
                # print("Expr:"+result)
        return result, cost

    def getFuncDefHead(self):
        false_keys = [key for key, value in self.used.items() if not value]
        if false_keys:
            fgh = random.choice(false_keys)
        self.funcName = fgh
        result = fgh
        result += self.getWhiteSpace() + '('
        case = self.rd(0, 5)
        permutation = ['x', 'y', 'z']
        all_permutation = list(itertools.permutations(permutation))
        to_pick = all_permutation[case]
        result += self.getWhiteSpace() + to_pick[0] + self.getWhiteSpace()
        addNum = self.rd(0, 2)
        for i in range(0, addNum):
            result += ',' + self.getWhiteSpace() + \
                      to_pick[i + 1] + self.getWhiteSpace()
        result += ')'
        temp = list(to_pick)[:addNum + 1]
        self.func_list_par[fgh] = temp
        self.func_list_hed[fgh] = result
        return result

    def genData(self, GLOBALPOINTER=0, isFunction=False, expr=None, cost=-1):
        if expr is None:
            if GLOBALPOINTER < len(self.specialData):
                expr = self.specialData[GLOBALPOINTER]
                cost = self.dataCost[GLOBALPOINTER]
                # self.globalPointer = self.globalPointer + 1
            else:
                expr, cost = self.getExpr(isFunction)
        # x = sympy.Symbol('x')

        # # def exp(x):
        # #     return sympy.sympify("E**(x)", locals={'x': x})

        # toEval = re.sub(r'\b0+(\d+)\b', r'\1', expr)
        # expr_sym = sympy.sympify(toEval)
        # # expr_sym = sympy.simplify(toEval, locals={'exp': exp})
        # simplified = sympy.expand(expr_sym)
        # return str(expr), str(simplified).replace("**", "^").replace(" ", ""), cost
        return expr, cost

    def getFuncExpBody(self, name, var):
        self.funcName = name
        self.funcVars = var
        self.isFunction = True
        expr, cost = self.getExpr(False)
        self.isFunction = False
        self.func_list_exp[name] = expr
        return str(expr), cost  # 返回函数的表达式部分和cost

    def generateFunction(self, length=150, cost_limit=2000):
        self.isFunction = True
        funcNum = self.rd(0, 3)
        self.used = {func_name: False for func_name in self.funcNames}
        for i in range(0, funcNum):
            func_len = length + 10
            cost = cost_limit + 10
            while func_len > length or cost > cost_limit:  # HERE to set func_len_limit
                false_keys = [key for key,
                              value in self.used.items() if not value]
                if false_keys:
                    fgh = random.choice(false_keys)
                else:
                    return
                self.funcName = fgh
                result = fgh
                result += self.getWhiteSpace() + '('
                case = self.rd(0, 5)
                permutation = ['x', 'y', 'z']
                all_permutation = list(itertools.permutations(permutation))
                to_pick = all_permutation[case]
                result += self.getWhiteSpace() + \
                    to_pick[0] + self.getWhiteSpace()
                addNum = self.rd(0, 2)
                for j in range(0, addNum):
                    result += ',' + self.getWhiteSpace() + \
                              to_pick[j + 1] + self.getWhiteSpace()
                result += ')'
                temp = list(to_pick)[:addNum + 1]
                # self.getFuncExpBody(name, var)
                self.funcName = fgh
                self.funcVars = temp
                expr, cost = self.getExpr(False)
                func_len = len((result + '=' + expr).replace("**",
                               "^").replace(" ", "").replace("\t", ""))
            # self.getFuncDefHead(used)
            self.func_list_par[fgh] = temp
            self.func_list_hed[fgh] = result
            self.func_list_exp[fgh] = expr
            self.used[self.funcName] = True
            self.globalPointer = 0
        # for name, var in self.func_list_par.items():
        #     # print(name, var)
        #     self.getFuncExpBody(name, var)

        self.isFunction = False

        return funcNum  # 返回生成了多少函数

    def getCustomDef(self):
        ret = ""
        for _func_name in self.func_list_par.keys():
            ret += self.func_list_hed[_func_name]
            ret += self.getWhiteSpace() + '=' + self.getWhiteSpace()
            ret += self.func_list_exp[_func_name] + '\n'
        return ret

    def parseCustom(self):
        func_dict = dict()
        for name, params in self.func_list_par.items():
            symbols = {param: sympy.symbols(param) for param in params}
            expr_str = self.func_list_exp[name]
            expr_str = expr_str.replace(" ", "").replace("\t", "")
            expr_str = re.sub(r'\b0+(\d+)\b', r'\1', expr_str)
            expr = sympy.parse_expr(
                expr_str, local_dict=symbols, global_dict=None)
            func = sympy.lambdify(tuple(symbols.values()), expr)
            func_dict[name] = func
        return func_dict


def compare(jar_name_1, jar_name_2):
    x_values = [0, 1, 2]
    x = sympy.symbols('x')
    output = ""
    DataGenerato = DataGenerator()
    num = DataGenerato.generateFunction()
    output += str(num) + '\n'
    output += DataGenerato.getCustomDef()

    expr_len = 210
    while expr_len > 200:
        expr, cost = DataGenerato.getExpr(False)
        expr_len = len(expr.replace(
            "**", "^").replace(" ", "").replace("\t", ""))

    # newExpr = replaceFunction((output + expr).replace("**", "^"))
    # newExpr = newExpr.replace("^", "**")
    # newExpr = re.sub(r'\b0+(\d+)\b', r'\1', newExpr)
    #  = sympy.expand_multinomial(newExpr)
    # results = [exprAns.subs(x, x_val) for x_val in x_values]

    cmd = ['java', '-jar', jar_name_1]
    stdin = (output + expr).replace("**", "^")
    proc = subprocess.Popen(cmd, stdin=PIPE, stdout=PIPE, stderr=STDOUT)
    stdout, stderr = proc.communicate(stdin.encode())
    yourAns = stdout.decode().strip()
    proc.terminate()
    proc.wait()
    proc.kill()
    yourExpr = yourAns.replace("^", "**")
    yourAns = re.sub(r'\b0+(\d+)\b', r'\1', yourExpr)
    exprAns = sympy.expand_multinomial(yourAns)
    results = [exprAns.subs(x, x_val) for x_val in x_values]

    cmd = ['java', '-jar', jar_name_2]
    stdin = (output + expr).replace("**", "^")
    proc = subprocess.Popen(cmd, stdin=PIPE, stdout=PIPE, stderr=STDOUT)
    stdout, stderr = proc.communicate(stdin.encode())
    yourAns = stdout.decode().strip()
    yourExpr = yourAns.replace("^", "**")
    proc.terminate()
    proc.wait()
    proc.kill()
    yourAns = re.sub(r'\b0+(\d+)\b', r'\1', yourExpr)
    yourAnsSym = sympy.expand_multinomial(yourAns)
    yourResults = [yourAnsSym.subs(x, x_val) for x_val in x_values]

    return stdin, cost, yourResults == results, yourResults, results, 1


def compare_with_timeout(jar_name1, jar_name_2, timeout=10):
    with multiprocessing.Pool(processes=1) as pool:
        async_result = pool.apply_async(compare, (jar_name1, jar_name_2,))
        try:
            result = async_result.get(timeout)
            pass
        except multiprocessing.TimeoutError:
            print('OverTime..')
            result = (None,) * 6
        except Exception:
            print('ReStart..')
            result = (None,) * 6
        finally:
            pool.close()  # 关闭进程池
        return result


def main(jar_name_1, jar_name_2, times=100):
    for i in tqdm(range(times), position=0):
        stdin, cost, isSame, firsts, seconds, restart = compare_with_timeout(
            jar_name_1, jar_name_2)
        if restart is None:
            continue
        if not isSame:
            print(firsts)
            print(seconds)
            print(cost)
            print(stdin)
            break


if __name__ == '__main__':
    main("name.jar", "checker.jar", 1000)
