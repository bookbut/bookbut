import sys
import os
from cx_Freeze import setup, Executable

# 包含的额外文件列表
include_files = [
    # "class_config.json",  # 直接包含文件
    # 如果需要包含整个目录，可以这样写：
    # "source_dir/", "target_dir/"
]

# 包含的Python模块
includes = [
    "tkinter",
    "os",
    "json",
    "threading",
    "time",
    "datetime",
    "shutil",
    "subprocess",
    "platform",
    "hashlib",
    "difflib",
    "re",
    "logging",
    "collections",
    "pypinyin",
    "concurrent",
    "multiprocessing"
]

# 排除不需要的模块，可以减小打包体积
excludes = [
    "unittest",
    "email",
    "http",
    "xml",
    "pydoc"
]

# 构建可执行文件的选项
build_exe_options = {
    "includes": includes,
    "excludes": excludes,
    "include_files": include_files,
    "include_msvcr": True,  # 包含微软运行库
    "optimize": 2  # 优化级别
}

# 对于Windows GUI程序（使用tkinter），设置base为"Win32GUI"可以避免命令行窗口
base = "Win32GUI" if sys.platform == "win32" else None

# 定义主程序
executables = [
    Executable(
        script="main.py",  # 你的主Python文件
        base=base,
        target_name="作业检查系统V8.exe",  # 生成的可执行文件名称
        icon="PCR.ico"  # 可选：如果有图标文件的话
    )
]

setup(
    name="作业检查系统V8",
    version="1.0",
    description="作业检查系统",
    options={"build_exe": build_exe_options},
    executables=executables
)