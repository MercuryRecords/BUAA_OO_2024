import os
import subprocess
import multiprocessing
import shutil
CACHE_PATH = "cache"
PROCESS_COUNT = 16
ITERATIONS = 100
JAR_NAME = 'Nadleeh.jar'
def run_iteration(iteration):
    cache_folder = os.path.join(CACHE_PATH, f"iteration_{iteration}")
    os.makedirs(cache_folder, exist_ok=True)
    
    # genData
    stdin_path = os.path.join(cache_folder, f"stdin.txt")
    subprocess.run(["python3", "generator.py"], stdout=open(stdin_path, "w"))
    shutil.copy("./datainput_student_linux_x86_64", cache_folder)
    
    # run your program
    stdout_path = os.path.join(cache_folder, f"stdout.txt")
    with open(stdout_path, "w") as stdout_file:
        datainput_proc = subprocess.Popen(["./datainput_student_linux_x86_64"],cwd=cache_folder, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        java_proc = subprocess.Popen(["java", "-jar", JAR_NAME], stdin=datainput_proc.stdout, stdout=stdout_file)
        
        
        java_proc.wait()

    # 运行 checker，传递 stdin.txt 和 stdout.txt 的路径作为命令行参数
    subprocess.run(["./checker", stdin_path, stdout_path])

    print(f"Iteration {iteration} completed.")

if __name__ == "__main__":
    pool = multiprocessing.Pool(processes=PROCESS_COUNT)
    
    iterations = range(1, ITERATIONS+1)
    pool.map(run_iteration, iterations)
    
    pool.close()
    pool.join()