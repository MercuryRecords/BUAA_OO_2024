import itertools
import random
import re

import sympy


class DataGenerator:
    def __init__(self):
        self.func_list = dict()
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
        self.globalPointer = 0

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
            result = result + self.getSymbol() + self.getWhiteSpace() + toAdd + self.getWhiteSpace()
            cost += termCost
        if isFactor:
            result = "(" + result + ")"
            if self.rd(0, 1) == 1:
                toAdd, expCost = self.getExponent()
                result = result + self.getWhiteSpace() + toAdd
                cost = max(cost, 2) ** max(expCost, 1)
                # print("Expr:"+result)
        return result, cost

    def getFuncDefHand(self):
        case = self.rd(0, 2)
        name = "fgh"
        fgh = name[case]
        result = fgh
        result += self.getWhiteSpace() + '('
        case = self.rd(0, 5)
        permutation = ['x', 'y', 'z']
        all_permutation = list(itertools.permutations(permutation))
        to_pick = all_permutation[case]
        result += self.getWhiteSpace() + to_pick[0] + self.getWhiteSpace()
        addNum = self.rd(0, 2)
        for i in range(0, addNum):
            result += ',' + self.getWhiteSpace() + to_pick[i + 1] + self.getWhiteSpace()
        result += ')'
        self.func_list[fgh] = list(to_pick)[:addNum]
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
        # expr_sym = sympy.sympify(toEval, locals={'exp': exp})
        simplified = sympy.expand(expr_sym)
        return str(expr), str(simplified).replace("**", "^").replace(" ", ""), cost


if __name__ == '__main__':
    getFuncDef()
    text = "(-exp(x)^4*x*+010-exp(+13)^+1*exp((+0016*012))^8*exp((-0023495723459823752039*004*x++exp(exp(-23333333233335467543)^3)^3*+9*-005-exp(x^8)^+5))^3)*-11*x^7-007*(-+-01*0*exp(x^3)^4)^3*(-exp((+-23333333233335467543*15))^2*x)^+1"
    text = "-exp(+13)^+1*exp((+0016*012))^8*exp((-0023495723459823752039*004*x++exp(exp(-23333333233335467543)^3)^3*+9*-005-exp(x^8)^+5))^3"
    text = "exp(2)*exp(11)^2*exp((-9*4*x++exp(exp(-23333333233335467543)^3)^3*+9*-005-exp(x^8)^+5))^3"
    print(text)
    poly, ans, cost = genData(text)
    print(ans)
    pass
