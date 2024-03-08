from DataGenerator import DataGenerator


class CustomFuncGenerator(DataGenerator):
    # 此类用于生成自定义函数定义的函数表达式
    def __init__(self):
        super().__init__()

    def getPower(self):  # todo 重写此方法以随机使用所有形参
        # result = "x"
        # if self.rd(0, 1) == 1:
        #     toAdd, _ = self.getExponent()
        #     result = result + self.getWhiteSpace() + toAdd
        # print("Power:"+result)
        var = self.func_list_def[self.funcName]
        addNum = len(var)
        case = self.rd(0, var - 1)
        result = var[case]
        if self.rd(0, 1) == 1:
            toAdd, _ = self.getExponent()
            result = result + self.getWhiteSpace() + toAdd
        return result, 1


if __name__ == '__main__':
    DataGenerato = CustomFuncGenerator()
    DataGenerato.getFuncDefHand()
    expr = DataGenerato.getFuncExpHand()
    print(DataGenerato.func_list_def)
    print(DataGenerato.func_list_exp)
