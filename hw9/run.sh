#!/bin/bash

# 遍历当前目录下的所有.jar文件
for file in *.jar; do
    # 检查文件是否存在
    if [ -e "$file" ]; then
        # 提取文件名（不含扩展名）
        filename=$(basename -- "$file" .jar)
        # 执行命令
        echo "$filename.jar"
        python3 masProgress.py "$filename.jar"
    else
        echo "文件 $file 不存在"
    fi
done