import os
import subprocess
import multiprocessing
import shutil
from tqdm import tqdm

FEED_PROGRAM = 'datainput_student_linux_x86_64'
CACHE_PATH = "cache"
PROCESS_COUNT = 16
ITERATIONS = 100
C_NAME = 'checker'
PYTHON = 'python3'
JAR_NAME = ''


def run_iteration(iteration):
    cache_folder = os.path.join(CACHE_PATH, f"iteration_{iteration}")
    os.makedirs(cache_folder, exist_ok=True)

    # genData
    stdin_path = os.path.join(cache_folder, f"stdin.txt")
    subprocess.run([PYTHON, "generator.py"], stdout=open(stdin_path, "w"))
    shutil.copy(f"./{FEED_PROGRAM}", cache_folder)

    # run your program
    stdout_path = os.path.join(cache_folder, f"stdout.txt")
    with open(stdout_path, "w") as stdout_file:
        datainput_proc = subprocess.Popen([f"./{FEED_PROGRAM}"], cwd=cache_folder, stdout=subprocess.PIPE,
                                          stderr=subprocess.STDOUT)
        java_proc = subprocess.Popen(["java", "-jar", JAR_NAME], stdin=datainput_proc.stdout, stdout=stdout_file)

        java_proc.wait()

    # 运行 checker，传递 stdin.txt 和 stdout.txt 的路径作为命令行参数
    checker_output = subprocess.run([f"./{C_NAME}", stdin_path, stdout_path], capture_output=True,
                                    text=True).stdout.strip()
    # print(f"Iteration {iteration} completed.")
    if checker_output != "Correct.":
        print(f"Iteration {iteration} completed with checker output: {checker_output}")
    return f"Iteration {iteration} completed."


def run():
    pool = multiprocessing.Pool(processes=PROCESS_COUNT)

    iterations = range(1, ITERATIONS + 1)

    with tqdm(total=len(iterations), desc="Iterations") as pbar:
        for result in pool.imap_unordered(run_iteration, iterations):
            pbar.update()
    pool.close()
    pool.join()


if __name__ == "__main__":
    files_and_dirs = os.listdir('.')
    jar_names = [f for f in files_and_dirs if f.endswith('.jar')]

    print(jar_names)
    for name in jar_names:
        print(f"check {name} start")
        JAR_NAME = name
        run()
