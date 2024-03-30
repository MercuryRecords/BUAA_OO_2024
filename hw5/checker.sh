#!/bin/bash

# 循环100次
for ((i=1; i<=100; i++))
do
    # 运行 generator.py 并将输出写入 stdin.txt
    python3 generator.py > stdin.txt
    
    # 运行 datainput_student_linux_x86_64，并将其输出作为标准输入提供给 code.jar
    ./datainput_student_linux_x86_64 | java -jar Nadleeh.jar > stdout.txt
    
    # 运行 checker
    ./checker
    
    echo "Iteration $i completed."
done
