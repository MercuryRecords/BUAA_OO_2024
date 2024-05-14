import os
import shutil
import zipfile
import tempfile
import subprocess

code_dir = os.path.join(os.getcwd(), "code")
dependence_dir = r'E:\ObjectOriented\oohomework_2024_21371285_hw_10\src\com'


def zip2jar(zip_path: str, dependence_dir: str = '') -> bool:
    if not zip_path.endswith('.zip') or (dependence_dir != '' and not os.path.isdir(dependence_dir)):
        return False
    with tempfile.TemporaryDirectory() as temp_dir:
        empty_flag = True
        with zipfile.ZipFile(zip_path, 'r') as zip_ref:
            for zip_info in zip_ref.infolist():
                if zip_info.filename.startswith('src/'):
                    zip_ref.extract(zip_info, temp_dir)
                    empty_flag = False
        if empty_flag:
            return False
        src_dir = os.path.join(temp_dir, 'src')
        main_name = ''
        for filename in os.listdir(src_dir):
            if filename == 'Main.java' or filename == 'MainClass.java' or filename == 'Mainclass.java':
                main_name = filename
            file_path = os.path.join(src_dir, filename)
            shutil.move(file_path, temp_dir)
        if main_name == '':
            return False
        temp_dependence_dir = os.path.join(temp_dir, os.path.basename(dependence_dir))
        if dependence_dir != '' and not os.path.exists(temp_dependence_dir):
            shutil.copytree(dependence_dir, temp_dependence_dir)
        if subprocess.run(['javac', main_name, '-encoding', 'UTF-8'], cwd=temp_dir).returncode != 0:
            return False
        MANIFEST_path = os.path.join(temp_dir, 'MANIFEST.MF')
        with open(MANIFEST_path, 'w', encoding='utf-8') as file:
            file.write('Manifest-Version: 1.0\nMain-Class: ' + main_name.removesuffix('.java') + '\n')
        new_path = zip_path.removesuffix('.zip') + '.jar'
        with zipfile.ZipFile(new_path, 'w', zipfile.ZIP_DEFLATED) as zip_ref:
            zip_ref.write(MANIFEST_path, 'META-INF\\MANIFEST.MF')
            for root, dirs, files in os.walk(temp_dir):
                for file in files:
                    if file.endswith('.class'):
                        file_path = os.path.join(root, file)
                        arcname = os.path.relpath(file_path, temp_dir)
                        zip_ref.write(file_path, arcname)
    return True


if __name__ == "__main__":
    for file_name in os.listdir(code_dir):
        if file_name.endswith('.zip'):
            print(file_name)
            file_path = os.path.join(code_dir, file_name)
            result = zip2jar(file_path, dependence_dir)
            print(file_name + ' : ' + '转换成功' if result else '转换失败')
