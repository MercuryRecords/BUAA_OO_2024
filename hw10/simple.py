import os
import subprocess
import multiprocessing
import shutil
from random import randint

from tqdm import tqdm
from data_generator import generate
from checker import check

CACHE_PATH = "cache"


# 假设这是您要对每个.jar文件执行的函数
def process_jar_file(jar_file_path, cache_folder, stdin_path):
    stdout_path = os.path.join(cache_folder, f"stdout_{jar_file_path}.txt")
    with open(stdin_path, 'r') as stdin_file:
        with open(stdout_path, "w") as stdout_file:
            java_proc = subprocess.Popen(["java", "-jar", jar_file_path], stdin=stdin_file,
                                         stdout=stdout_file, stderr=subprocess.STDOUT)

    try:
        return_code = java_proc.wait(timeout=8)
        if return_code is None or return_code != 0:
            java_proc.kill()
            java_proc.wait()
            return f"{jar_file_path}: Error-{return_code}", cache_folder
    except subprocess.TimeoutExpired:
        java_proc.kill()
        java_proc.wait()
        return f"{jar_file_path}: OverTime1", cache_folder

    # 检查子进程是否已经结束
    if java_proc.poll() is None:
        java_proc.kill()
        java_proc.wait()
        return f"{jar_file_path}: OverTime2", cache_folder
    if java_proc.poll() != 0:
        java_proc.kill()
        java_proc.wait()
        return f"{jar_file_path}: OverTime3", cache_folder
    if java_proc.stderr:
        java_proc.kill()
        java_proc.wait()
        return f"{jar_file_path}: Error2", cache_folder

    return "successfully runned", cache_folder


# 获取当前目录下所有的.jar文件
def get_jar_files(directory):
    jar_files = [f for f in os.listdir(directory) if f.endswith('.jar')]
    return jar_files


# 创建并启动一个进程来处理每个.jar文件
def start_processes(jar_files):
    processor_id = randint(0, 100000)
    cache_folder = os.path.join(CACHE_PATH, f"{processor_id}")
    try:
        os.makedirs(cache_folder, exist_ok=True)
        to_be_deleted = True

        # genData
        stdin_path = "stdin_51.txt"

        stdouts = list()

        with multiprocessing.Pool() as pool:
            # 使用列表推导式创建一个包含所有任务的列表
            tasks = [(jar_file, pool.apply_async(process_jar_file, (jar_file, cache_folder, stdin_path))) for
                     jar_file in jar_files]

            # 遍历所有任务，并获取结果或处理超时
            for fname, task in tasks:
                # print(fname)
                try:
                    result = task.get()
                    if result[0] != "successfully runned":
                        to_be_deleted = False
                        print(f"{result[0]}_by_{fname}_at_{processor_id}")
                        with open(f"{result[0]}_by_{fname}_at_{processor_id}.txt", "w") as fout, open(stdin_path,
                                                                                                      'r') as fin:
                            fout.write(fin.read())
                except KeyboardInterrupt:
                    # shutil.rmtree(cache_folder)
                    pass
                stdout_path = os.path.join(cache_folder, f"stdout_{fname}.txt")
                stdouts.append(stdout_path)

            for i in range(len(stdouts) - 1):
                if not check(str(stdouts[i]), str(stdouts[i + 1]), stdin_path):
                    to_be_deleted = False
                    print(f"{striper(stdouts[i])}_diff_{striper(stdouts[i + 1])}_at_{processor_id}")
                    with open(f"{striper(stdouts[i])}_diff_{striper(stdouts[i + 1])}_at_{processor_id}.txt",
                              "w") as fout, open(stdin_path, 'r') as fin:
                        fout.write(fin.read())

        if to_be_deleted:
            shutil.rmtree(cache_folder)
        else:
            return None
        pass
    except KeyboardInterrupt:
        pass
    return None


def striper(_input):
    _input = str(_input)
    _input = _input.split(".")[0]
    _input = _input.split("\\")[2]
    return _input


# 主函数
def main():
    directory = os.getcwd()  # 获取当前工作目录
    jar_files = get_jar_files(directory)
    print(jar_files)
    start_processes(jar_files)


if __name__ == "__main__":
    main()
