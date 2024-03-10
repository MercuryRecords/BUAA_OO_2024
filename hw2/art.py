import os
import subprocess


def compare(stdin, jar_names):
    expr_list = list()

    def exec_jar(jar_name):
        cmd = ['java', '-jar', jar_name]
        proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        stdout, stderr = proc.communicate(stdin.encode())
        yourAns = stdout.decode().strip()
        proc.terminate()
        proc.wait()
        proc.kill()
        print(jar_name + " : " + str(yourAns))
        return yourAns

    for fname in jar_names:
        expr_list.append(exec_jar(fname))

    for i in range(len(expr_list) - 1):
        if expr_list[i] != expr_list[i + 1]:
            return False
    return True


if __name__ == '__main__':
    files_and_dirs = os.listdir('.')
    jar_names = [f for f in files_and_dirs if f.endswith('.jar')]
    print(len(jar_names))
    with open('in.txt', 'r', encoding='utf-8') as file:
        text = file.read()
    compare(text, jar_names)
