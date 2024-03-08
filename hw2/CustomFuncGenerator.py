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
        cost = 1
        return "powerFunction", cost

    def getXYZPower(self, fgh):
        var = self.func_list[fgh]
