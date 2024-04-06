import os
import platform
import subprocess
import multiprocessing
import shutil
from random import randint
from tqdm import tqdm
from generator import genData
from performance import cal_performance, cal
from checker import check

CACHE_PATH = "cache"
if platform.system() == 'Windows':
    FEED_PROGRAM = 'datainput_student_win64.exe'
    SHELL = True
else:
    FEED_PROGRAM = './datainput_student_linux_x86_64'
    SHELL = False


# 假设这是您要对每个.jar文件执行的函数
def process_jar_file(jar_file_path, cache_folder, stdin_path, performances):
    # 在这里添加处理.jar文件的代码
    # print(f"Processing {jar_file_path}")
    # run your program
    stdout_path = os.path.join(cache_folder, f"stdout_{jar_file_path}.txt")
    with open(stdout_path, "w") as stdout_file:
        datainput_proc = subprocess.Popen([FEED_PROGRAM], cwd=cache_folder, stdout=subprocess.PIPE,
                                          stderr=subprocess.STDOUT)
        java_proc = subprocess.Popen(["java", "-jar", jar_file_path], stdin=datainput_proc.stdout,
                                     stdout=stdout_file, stderr=subprocess.STDOUT, shell=SHELL)

    try:
        return_code = java_proc.wait(timeout=120)
        if return_code is None or return_code != 0:
            return f"Error-{return_code}"
    except subprocess.TimeoutExpired:
        return "OverTime1"

    # 检查子进程是否已经结束
    if java_proc.poll() is None:
        return "OverTime2"
    if java_proc.poll() != 0:
        return "OverTime3"
    if java_proc.stderr:
        return "Error2"

    # 运行 checker，传递 stdin.txt 和 stdout.txt 的路径作为命令行参数
    checker_output = check(stdin_path,stdout_path)
    if checker_output != True:
        return "Error3"
    else:
        a, b, c = cal_performance(stdin_path, stdout_path)
        # print(a, b, c)
        performances[jar_file_path] = (a, b, c)
        # print("Here")
        return "Correct"


# 获取当前目录下所有的.jar文件
def get_jar_files(directory):
    jar_files = [f for f in os.listdir(directory) if f.endswith('.jar')]
    return jar_files


# 创建并启动一个进程来处理每个.jar文件
def start_processes(jar_files):
    processor_id = randint(0, 100000)
    cache_folder = os.path.join(CACHE_PATH, f"{processor_id}_art")
    try:
        os.makedirs(cache_folder, exist_ok=True)
        to_be_deleted = True

        # genData
        stdin_path = os.path.join(cache_folder, f"stdin.txt")
        with open(stdin_path, "w") as f:
            tmp_stdin = genData()
            for entry in tmp_stdin:
                f.write(entry)

        # stdin_path = os.path.join(os.getcwd(), "stdin.txt")
        shutil.copy(FEED_PROGRAM, cache_folder)
        # shutil.copy(stdin_path, cache_folder)

        manager = multiprocessing.Manager()
        performances = manager.dict()

        with multiprocessing.Pool() as pool:
            # 使用列表推导式创建一个包含所有任务的列表
            tasks = [(jar_file, pool.apply_async(process_jar_file, (jar_file, cache_folder, stdin_path, performances, ))) for
                     jar_file in jar_files]

            # 遍历所有任务，并获取结果或处理超时
            for fname, task in tasks:
                # print(fname)
                try:
                    # 尝试获取结果，设置超时时间
                    result = task.get()
                    if result != "Correct":
                        to_be_deleted = False
                        with open(f"{result}_by_{fname}_at_{processor_id}_iteration_{processor_id}.txt", "w") as fout, open(
                                stdin_path, 'r') as fin:
                            fout.write(fin.read())
                except KeyboardInterrupt:
                    # shutil.rmtree(cache_folder)
                    pass

            if to_be_deleted:
                # print(performances)
                cal(performances)
            # shutil.rmtree(cache_folder)
        # else:
        #     break

        # shutil.rmtree(cache_folder)
        pass
    except KeyboardInterrupt:
        # shutil.rmtree(cache_folder)
        pass


# 主函数
def main():
    directory = os.getcwd()  # 获取当前工作目录
    jar_files = get_jar_files(directory)

    if not jar_files:
        print("No jar files found in the current directory.")
        return

    print(jar_files)
    start_processes(jar_files)


if __name__ == "__main__":
    main()
