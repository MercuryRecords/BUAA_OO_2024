import os
from random import randint
import subprocess
import multiprocessing
import shutil
from tqdm import tqdm
from data_generator import generate
from checker import check
import sys

########## configs you need to modify BEGIN ##########

JAR_NAME = 'oohomework_2024_21371285_hw_10.jar'
STD_NAME = 'oohomework_2024_22371213_hw_10.jar'
PROCESS_COUNT = 4  # int(os.cpu_count())
ITERATIONS = 10000
DEBUG = True

########## configs you need to modify END ##########

CACHE_PATH = f"cache-{randint(0, 100)}"


def run_iteration(iteration):
    cache_folder = os.path.join(CACHE_PATH, f"iteration_{iteration}")
    os.makedirs(cache_folder, exist_ok=True)

    stdin_path = os.path.join(cache_folder, f"stdin.txt")
    stdin = ''
    with open(stdin_path, "w") as f:
        tmp_stdin = generate()
        for entry in tmp_stdin:
            f.write(entry)
            stdin += entry

    # run your program
    stdout_path_U = os.path.join(cache_folder, f"stdout_1.txt")
    stdout_path_STD = os.path.join(cache_folder, f"stdout_2.txt")
    with open(stdin_path, 'r') as stdin_file:
        # 打开 stdout 文件以写入输出数据
        with open(stdout_path_U, 'w') as stdout_file_U:
            # 执行 Java 程序，并将 stdin 文件作为输入
            java_proc = subprocess.Popen(["java", "-jar", JAR_NAME], stdin=stdin_file,
                                         stdout=stdout_file_U, stderr=subprocess.STDOUT)

    with open(stdin_path, 'r') as stdin_file:
        with open(stdout_path_STD, 'w') as stdout_file_STD:
            std_proc = subprocess.Popen(["java", "-jar", STD_NAME], stdin=stdin_file,
                                        stdout=stdout_file_STD, stderr=subprocess.STDOUT)

    try:
        return_code_U = java_proc.wait(timeout=5)
        return_code_STD = std_proc.wait(timeout=5)
        if return_code_U is None or return_code_U != 0 or return_code_STD is None or return_code_STD != 0:
            java_proc.kill()
            java_proc.wait()
            std_proc.kill()
            std_proc.wait()
            return f"{CACHE_PATH}-{iteration}: Error-{return_code_U}-{return_code_STD}", cache_folder
    except subprocess.TimeoutExpired:
        java_proc.kill()
        java_proc.wait()
        std_proc.kill()
        std_proc.wait()
        return f"{iteration}: OverTime1", cache_folder

    # 检查子进程是否已经结束
    if java_proc.poll() is None:
        java_proc.kill()
        java_proc.wait()
        std_proc.kill()
        std_proc.wait()
        return f"{iteration}: OverTime2", cache_folder
    if java_proc.poll() != 0:
        java_proc.kill()
        java_proc.wait()
        std_proc.kill()
        std_proc.wait()
        return f"{iteration}: OverTime3", cache_folder
    if java_proc.stderr:
        java_proc.kill()
        java_proc.wait()
        std_proc.kill()
        std_proc.wait()
        return f"{iteration}: Error2", cache_folder

    # 运行 checker，传递 stdin.txt 和 stdout.txt 的路径作为命令行参数
    if not check(str(stdout_path_U), str(stdout_path_STD), str(stdin_path)):
        java_proc.kill()
        java_proc.wait()
        std_proc.kill()
        std_proc.wait()
        return f"{iteration} didn't pass checker", cache_folder
    else:
        java_proc.kill()
        java_proc.wait()
        std_proc.kill()
        std_proc.wait()
        return "Correct", cache_folder


def run(jar_name):
    print('processor name: ' + CACHE_PATH)
    pool = multiprocessing.Pool(processes=PROCESS_COUNT, maxtasksperchild=PROCESS_COUNT)

    iterations = range(1, ITERATIONS + 1)

    with tqdm(total=len(iterations), desc="Iterations") as pbar:
        for result in pool.imap_unordered(run_iteration, iterations):
            pbar.update()
            if result[0] != "Correct":
                print(result[0])
                with open("res.txt", "a+") as f:
                    f.write(result[0] + "\n")
            else:
                shutil.rmtree(result[1])
    pool.close()
    pool.join()
    if not os.listdir(CACHE_PATH):
        print(jar_name, " CORRECT, DEL CACHE", jar_name)
        os.rmdir(CACHE_PATH)


if __name__ == "__main__":
    # print(os.cpu_count())
    if len(sys.argv) == 2:
        if sys.argv[1] != STD_NAME:
            run(sys.argv[1])
    else:
        run(JAR_NAME)
