#!/bin/bash

# 检查是否提供了必要的参数
if [ "$#" -ne 1 ]; then
    echo "Usage: $0 <jar_file>"
    exit 1
fi

# 检查jar文件是否存在
if [ ! -f "$1" ]; then
    echo "Error: Jar file '$1' not found."
    exit 1
fi

# 运行java命令并重定向输入
time java -jar "$1" < 'stdin.txt'