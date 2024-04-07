import itertools
import os
import platform
import subprocess
import multiprocessing
import shutil
import sys

from tqdm import tqdm

from checker import check
from generator import genData

########## configs you need to modify BEGIN ##########

JAR_NAME = '2.jar'
PROCESS_COUNT = 5
ITERATIONS = 100
DEBUG = False

########## configs you need to modify END ##########

CACHE_PATH = "cache"
if platform.system() == 'Windows':
    FEED_PROGRAM = 'datainput_student_win64.exe'
else:
    FEED_PROGRAM = './datainput_student_linux_x86_64'


def run_iteration(argvs):
    iteration, jar_name = argvs
    fname = jar_name.split(".")[0]
    cache_folder = os.path.join(CACHE_PATH, f"{fname}_iteration_{iteration}")
    os.makedirs(cache_folder, exist_ok=True)

    stdin_path = os.path.join(cache_folder, f"stdin.txt")
    with open(stdin_path, "w") as f:
        tmp_stdin = genData()
        for entry in tmp_stdin:
            f.write(entry)

    shutil.copy(FEED_PROGRAM, cache_folder)

    # run your program
    stdout_path = os.path.join(cache_folder, f"stdout.txt")
    with open(stdout_path, "w") as stdout_file:
        datainput_proc = subprocess.Popen([FEED_PROGRAM], cwd=cache_folder, stdout=subprocess.PIPE,
                                          stderr=subprocess.STDOUT)
        java_proc = subprocess.Popen(["java", "-jar", jar_name], stdin=datainput_proc.stdout,
                                     stdout=stdout_file, stderr=subprocess.STDOUT)

    try:
        return_code = java_proc.wait(timeout=220)
        if return_code is None or return_code != 0:
            java_proc.kill()
            java_proc.wait()
            datainput_proc.kill()
            datainput_proc.wait()
            return f"{jar_name}_at_{iteration}: Error-{return_code}", cache_folder
    except subprocess.TimeoutExpired:
        java_proc.kill()
        java_proc.wait()
        datainput_proc.kill()
        datainput_proc.wait()
        check(input_path=stdin_path, output_path=stdout_path)
        return f"{jar_name}_at_{iteration}: OverTime1", cache_folder

    # 检查子进程是否已经结束
    if java_proc.poll() is None:
        java_proc.kill()
        java_proc.wait()
        datainput_proc.kill()
        datainput_proc.wait()
        return f"{jar_name}_at_{iteration}: OverTime2", cache_folder
    if java_proc.poll() != 0:
        java_proc.kill()
        java_proc.wait()
        datainput_proc.kill()
        datainput_proc.wait()
        return f"{jar_name}_at_{iteration}: OverTime3", cache_folder
    if java_proc.stderr:
        java_proc.kill()
        java_proc.wait()
        datainput_proc.kill()
        datainput_proc.wait()
        return f"{jar_name}_at_{iteration}: Error2", cache_folder

    # 运行 checker，传递 stdin.txt 和 stdout.txt 的路径作为命令行参数
    if not check(input_path=stdin_path, output_path=stdout_path, debug=DEBUG):
        java_proc.kill()
        java_proc.wait()
        datainput_proc.kill()
        datainput_proc.wait()
        return f"{jar_name}_at_{iteration} didn't pass checker", cache_folder
    else:
        java_proc.kill()
        java_proc.wait()
        datainput_proc.kill()
        datainput_proc.wait()
        return "Correct", cache_folder


def run(jar_name):
    pool = multiprocessing.Pool(processes=PROCESS_COUNT, maxtasksperchild=PROCESS_COUNT)

    iterations = range(1, ITERATIONS + 1)
    fnames = [jar_name for _ in range(1, ITERATIONS + 1)]
    argvs = [(i, jar_name) for i in range(1, ITERATIONS + 1)]

    with tqdm(total=len(iterations), desc="Iterations") as pbar:
        for result in pool.imap_unordered(run_iteration, argvs):
            pbar.update()
            if result[0] != "Correct":
                print(result[0])
                with open("res.txt", "a+") as f:
                    f.write(result[0] + "\n")
            else:
                shutil.rmtree(result[1])
    pool.close()
    pool.join()


if __name__ == "__main__":
    # print(os.cpu_count())
    if len(sys.argv) == 2:
        run(sys.argv[1])
    else:
        run(JAR_NAME)
