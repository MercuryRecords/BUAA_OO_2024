import itertools
import random
import re

import sympy


class DataGenerator:
    def __init__(self):
        self.func_list_hed = dict()
        self.func_list_def = dict()
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
        self.maxFactor = 3  # 项中最大因子个数
        self.specialData = ["1", "x-x", "-1"]  # 可以放一些特殊数据
        self.dataCost = [1, 2, 2]
        self.globalPointer = len(self.specialData)
        self.funcNames = ['f', 'g', 'h']
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
        result += toAdd
        result += self.getWhiteSpace()
        result += ")"
        result += self.getWhiteSpace()
        toAdd, expCost = self.getExponent()
        result += toAdd
        return result, 2 ** expCost + factorCost

    def getFactor(self, genExpr):
        factor = self.rd(0, 3)
        if factor == 0:
            toAdd, factorCost = self.getNum(False)
        elif factor == 1:
            toAdd, factorCost = self.getPower()
        elif factor == 2 and genExpr:
            toAdd, factorCost = self.getExpr(True)
        elif factor == 3:
            toAdd, factorCost = self.getExpoFunc()
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

    def getFuncDefHead(self, used):
        false_keys = [key for key, value in used.items() if not value]
        if false_keys:
            fgh = random.choice(false_keys)
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
        self.func_list_def[fgh] = temp
        self.func_list_hed[fgh] = result
        return result

    def genData(self, expr=None, cost=-1):
        if expr is None:
            if self.globalPointer < len(self.specialData):
                expr = self.specialData[self.globalPointer]
                cost = self.dataCost[self.globalPointer]
                globalPointer = self.globalPointer + 1
            else:
                expr, cost = self.getExpr(False)
        x = sympy.Symbol('x')

        # def exp(x):
        #     return sympy.sympify("E**(x)", locals={'x': x})

        toEval = re.sub(r'\b0+(\d+)\b', r'\1', expr)
        expr_sym = sympy.sympify(toEval)
        # expr_sym = sympy.simplify(toEval, locals={'exp': exp})
        simplified = sympy.expand(expr_sym)
        return str(expr), str(simplified).replace("**", "^").replace(" ", ""), cost

    def getFuncExpBody(self, name, var):
        self.funcName = name
        self.funcVars = var
        self.isFunction = True
        expr, cost = self.getExpr(False)
        self.isFunction = False
        self.func_list_exp[name] = expr
        return str(expr), cost  # 返回函数的表达式部分和cost

    def generateFunction(self):
        funcNum = self.rd(0, 4)
        for i in range(0, funcNum):
            used = {func_name: False for func_name in self.funcNames}
            self.getFuncDefHead(used)
            used[self.funcName] = True
        for name, var in self.func_list_def.items():
            # print(name, var)
            self.getFuncExpBody(name, var)

        return funcNum  # 返回生成了多少函数

    def getCustomDef(self):
        ret = ""
        for _func_name in self.func_list_def.keys():
            ret += self.func_list_hed[_func_name]
            ret += self.getWhiteSpace() + '=' + self.getWhiteSpace()
            ret += self.func_list_exp[_func_name] + '\n'
        return ret

    def parseCustom(self):
        func_dict = {}
        for name, params in self.func_list_def.items():
            symbols = {param: sympy.symbols(param) for param in params}
            expr_str = self.func_list_exp[name]
            expr_str = expr_str.replace(" ", "").replace("\t", "")
            expr_str = re.sub(r'\b0+(\d+)\b', r'\1', expr_str)
            expr = sympy.parse_expr(expr_str, local_dict=symbols, global_dict=None)
            func = sympy.lambdify(tuple(symbols.values()), expr)
            func_dict[name] = func
        return func_dict


if __name__ == '__main__':
    output = ""
    DataGenerato = DataGenerator()
    num = DataGenerato.generateFunction()
    output += str(num) + '\n'
    output += DataGenerato.getCustomDef()
    print(output)
    print(DataGenerato.parseCustom())

    # print(DataGenerato.func_list_def)
    # print(DataGenerato.func_list_exp)
    # for funcName in DataGenerato.func_list_def.keys():
    #     print(funcName, end=" ")
    #     print(DataGenerato.func_list_def[funcName], end=" ")
    #     print(DataGenerato.func_list_exp[funcName].replace("**", "^").replace(" ", "").replace("\t", ""))

# 在生成函数之后记得把global pointer还原为0
# text = "(-exp(x)^4*x*+010-exp(+13)^+1*exp((+0016*012))^8*exp((-0023495723459823752039*004*x++exp(exp(-23333333233335467543)^3)^3*+9*-005-exp(x^8)^+5))^3)*-11*x^7-007*(-+-01*0*exp(x^3)^4)^3*(-exp((+-23333333233335467543*15))^2*x)^+1"
# text = "-exp(+13)^+1*exp((+0016*012))^8*exp((-0023495723459823752039*004*x++exp(exp(-23333333233335467543)^3)^3*+9*-005-exp(x^8)^+5))^3"
# text = "exp(2)*exp(11)^2*exp((-9*4*x++exp(exp(-23333333233335467543)^3)^3*+9*-005-exp(x^8)^+5))^3"
# print(text)
# poly, ans, cost = genData(text)
# print(ans)
# pass