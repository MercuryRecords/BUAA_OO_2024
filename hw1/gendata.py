import random
import re

import sympy

intPool = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
           10, 11, 12, 13, 14, 15, 16,
           2147483647, 5223333333,
           5423333333,
           1145141919810,
           23333333234212332333,
           23333333233335467543,
           23495723459823752039
           ]                        # 常量池
hasWhiteSpace = True                # 是否加入空白字符
hasLeadZeros = True                 # 数字是否有前导零，如果传入sympy的表达式中数字有前导零，sympy将无法识别
maxTerm = 6                         # 表达式中的最大项数
maxFactor = 4                       # 项中最大因子个数
specialData = ["1", "x-x", "-1"]    # 可以放一些特殊数据
globalPointer = 0


def rd(a, b):
    return random.randint(a, b)


def getWhiteSpace():
    if not hasWhiteSpace:
        return ""
    blankTerm = ""
    cnt = rd(0, 2)
    for i in range(cnt):
        type = rd(0, 1)
        if type == 0:
            blankTerm = blankTerm + " "
        else:
            blankTerm = blankTerm + "\t"
    return blankTerm


def getSymbol():
    if rd(0, 1) == 1:
        return "+"
    else:
        return "-"


def getNum(posOnly):
    result = ""
    integer = intPool[rd(0, len(intPool) - 1)]
    iszero = rd(0, 2)
    for i in range(iszero):
        result = result + "0"
    if not hasLeadZeros:
        result = ""
    result = result + str(integer)
    if rd(0, 1) == 1:
        if posOnly:
            result = "+" + result
        else:
            result = getSymbol() + result
            # print("num:"+result)
    return result


def getExponent():
    result = "**"
    result = result + getWhiteSpace()
    case = rd(0, 8)
    if rd(0, 1) == 1:
        result = result + "+"
    result = result + str(case)
    # print("exponent: " + result)
    return result


def getPower():
    result = "x"
    if rd(0, 1) == 1:
        result = result + getWhiteSpace() + getExponent()
    # print("Power:"+result)
    return result


def getTerm(genExpr):
    factorNum = rd(1, maxFactor)
    result = ""
    if rd(0, 1) == 1:
        result = getSymbol() + getWhiteSpace()
    for i in range(factorNum):
        factor = rd(0, 2)
        if factor == 0:
            result = result + getNum(False)
        elif factor == 1:
            result = result + getPower()
        elif factor == 2 and genExpr:
            result = result + getExpr(True)
        else:
            result = result + "0"
        if i < factorNum - 1:
            result = result + getWhiteSpace() + "*" + getWhiteSpace()
            # print("term:"+result)
    return result


def getExpr(isFactor):
    termNum = rd(1, maxTerm)
    result = getWhiteSpace()
    genExpr = True
    if isFactor:
        genExpr = False
    for i in range(termNum):
        result = result + getSymbol() + getWhiteSpace() + getTerm(genExpr) + getWhiteSpace()
    if isFactor:
        result = "(" + result + ")"
        if rd(0, 1) == 1:
            result = result + getWhiteSpace() + getExponent()
            # print("Expr:"+result)
    return result


def genData():
    global globalPointer
    if globalPointer < len(specialData):
        expr = specialData[globalPointer]
        globalPointer = globalPointer + 1
    else:
        expr = getExpr(False)
    x = sympy.Symbol('x')
    toEval = re.sub(r'\b0+(\d+)\b', r'\1', expr)
    simplifed = sympy.expand(eval(toEval))
    return str(expr), str(simplifed)


if __name__ == '__main__':
    x = sympy.Symbol('x')
    fx = "+x**+0*x**0++3++x**+1*+1"
    y = sympy.expand(eval(fx))
    print(y)
