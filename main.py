import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import os
import json
import threading
import time
from datetime import datetime, timedelta
import shutil
import subprocess
import platform
import hashlib
import difflib
import re
import logging
from collections import defaultdict
from pypinyin import pinyin, Style
from concurrent.futures import ThreadPoolExecutor, as_completed
import multiprocessing


class HomeworkCheckSystem:
    def __init__(self, root):
        self.root = root
        self.root.title("学生作业检查系统 - 多班级版 - 雷州市职业高级中学 林勇良")
        self.root.geometry("1350x750")

        # 性能优化参数 - 动态调整线程数
        self.max_workers = min(8, max(2, multiprocessing.cpu_count() * 2))  # 增加线程数
        self.min_file_size = 10
        self.max_file_size = 10 * 1024 * 1024

        # 窗口居中显示
        self.center_window(self.root, 1350, 750)

        # 初始化日志系统
        self.setup_logging()

        # 绑定右键关闭事件（只在窗口空白处）
        self.root.bind("<Button-3>", self.on_right_click)

        # 设置窗口图标和作者信息
        self.setup_window_info()

        # 设置样式
        self.style = ttk.Style()
        self.style.configure("TButton", padding=6, relief="flat", background="#4CAF50", foreground="black",
                             font=("Arial", 9))
        self.style.configure("TFrame", background="#f0f0f0")
        self.style.configure("TLabel", background="#f0f0f0", font=("Arial", 9))
        self.style.configure("Header.TLabel", background="#f0f0f0", font=("Arial", 10, "bold"))
        self.style.configure("Author.TLabel", background="#e3f2fd", font=("Arial", 8), foreground="#1565C0")

        # 初始化数据
        self.current_class = "默认班级"
        self.classes = {}
        self.file_extensions = [".py", ".txt", ".java", ".cpp", ".c", ".cs", ".js", ".html", ".css"]
        self.check_mode = "hybrid"  # 默认改为混合模式
        self.auto_refresh = False
        self.refresh_interval = 10
        self.similarity_threshold = 85

        # 核心数据结构
        self.student_files_data = {}
        self.all_similarity_results = {}
        self.file_content_cache = {}
        self.file_hash_cache = {}

        # 考勤相关变量
        self.attendance_folder = ""
        self.last_migration_dir = ""

        # 排序相关变量
        self.sort_column = "状态"
        self.sort_reverse = False

        # 窗口关闭标志
        self.closing = False

        # 界面锁定标志
        self.ui_locked = False

        # 控件变量
        self.dir_var = tk.StringVar()
        self.mode_var = tk.StringVar(value=self.check_mode)
        self.refresh_var = tk.BooleanVar(value=self.auto_refresh)
        self.interval_var = tk.StringVar(value=str(self.refresh_interval))
        self.class_var = tk.StringVar(value=self.current_class)
        self.similarity_var = tk.StringVar(value=str(self.similarity_threshold))

        # 线程控制
        self.refresh_thread = None
        self.stop_refresh = False
        self.is_checking = False

        # 加载配置并创建界面
        self.load_all_classes()
        self.create_widgets()
        self.start_auto_refresh()

    def center_window(self, window, width, height):
        """将窗口居中显示"""
        screen_width = window.winfo_screenwidth()
        screen_height = window.winfo_screenheight()

        x = (screen_width - width) // 2
        y = (screen_height - height) // 2

        window.geometry(f"{width}x{height}+{x}+{y}")

    def setup_logging(self):
        """设置日志系统"""
        self.logger = logging.getLogger('HomeworkCheckSystem')
        self.logger.setLevel(logging.DEBUG)

        log_file = 'log.txt'
        file_handler = logging.FileHandler(log_file, mode='w', encoding='utf-8')
        file_handler.setLevel(logging.DEBUG)

        console_handler = logging.StreamHandler()
        console_handler.setLevel(logging.INFO)

        formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
        file_handler.setFormatter(formatter)
        console_handler.setFormatter(formatter)

        self.logger.addHandler(file_handler)
        self.logger.addHandler(console_handler)

        self.logger.info("学生作业检查系统启动")
        self.logger.info(f"当前时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        self.logger.info(f"CPU核心数: {multiprocessing.cpu_count()}")
        self.logger.info(f"最大工作线程数: {self.max_workers}")

    def lock_ui(self):
        """锁定界面，防止重复操作"""
        self.ui_locked = True
        self.root.config(cursor="wait")
        self.root.update()

    def unlock_ui(self):
        """解锁界面"""
        self.ui_locked = False
        self.root.config(cursor="")
        self.root.update()

    def on_right_click(self, event):
        """处理右键点击事件 - 只在窗口空白处关闭"""
        try:
            # 只允许在窗口的空白区域（不是Treeview上）点击右键关闭
            widget = event.widget
            if widget == self.root or isinstance(widget, ttk.Frame):
                if platform.system() == "Windows" and event.num == 3:
                    self.on_closing()
        except Exception as e:
            self.logger.error(f"右键点击事件处理出错: {str(e)}")

    def setup_window_info(self):
        """设置窗口作者信息和时间戳"""
        self.status_frame = ttk.Frame(self.root)
        self.status_frame.pack(fill=tk.X, side=tk.BOTTOM)

        self.timestamp_label = ttk.Label(self.status_frame, text="最后检查: 从未检查", style="Author.TLabel")
        self.timestamp_label.pack(side=tk.LEFT, padx=5, pady=2)

        author_info = "学校：雷州市职业高级中学 | 作者：林勇良"
        self.author_label = ttk.Label(self.status_frame, text=author_info, style="Author.TLabel")
        self.author_label.pack(side=tk.RIGHT, padx=5, pady=2)

    def create_widgets(self):
        main_paned = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        main_paned.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        left_frame = ttk.Frame(main_paned, width=400)
        main_paned.add(left_frame, weight=1)

        right_frame = ttk.Frame(main_paned)
        main_paned.add(right_frame, weight=2)

        self.create_left_panel(left_frame)
        self.create_right_panel(right_frame)

        self.load_current_class_data()

    def create_left_panel(self, parent):
        # 班级管理部分
        class_frame = ttk.LabelFrame(parent, text="班级管理", padding="5")
        class_frame.pack(fill=tk.X, pady=3, padx=3)

        class_top_frame = ttk.Frame(class_frame)
        class_top_frame.pack(fill=tk.X, pady=2)

        ttk.Label(class_top_frame, text="当前班级:").pack(side=tk.LEFT)
        self.class_combo = ttk.Combobox(class_top_frame, textvariable=self.class_var,
                                        values=list(self.classes.keys()), width=15)
        self.class_combo.pack(side=tk.LEFT, padx=3)
        self.class_combo.bind('<<ComboboxSelected>>', self.on_class_changed)

        ttk.Button(class_top_frame, text="新建班级", command=self.create_new_class).pack(side=tk.LEFT, padx=3)
        ttk.Button(class_top_frame, text="删除班级", command=self.delete_class).pack(side=tk.LEFT, padx=3)

        class_bottom_frame = ttk.Frame(class_frame)
        class_bottom_frame.pack(fill=tk.X, pady=2)

        ttk.Button(class_bottom_frame, text="保存配置",
                   command=lambda: self.save_current_class(show_message=True)).pack(side=tk.LEFT, padx=3)
        ttk.Button(class_bottom_frame, text="导出配置", command=self.export_class_config).pack(side=tk.LEFT, padx=3)
        ttk.Button(class_bottom_frame, text="导入配置", command=self.import_class_config).pack(side=tk.LEFT, padx=3)

        # 学生名单部分
        student_frame = ttk.LabelFrame(parent, text="学生名单", padding="5")
        student_frame.pack(fill=tk.BOTH, expand=True, pady=3, padx=3)

        ttk.Label(student_frame, text="学生名单（每行一个名字，支持学号+姓名格式）:").pack(anchor=tk.W)

        self.student_text = tk.Text(student_frame, height=8, width=40)
        self.student_text.pack(fill=tk.BOTH, expand=True, pady=3)

        button_frame = ttk.Frame(student_frame)
        button_frame.pack(fill=tk.X, pady=2)

        ttk.Button(button_frame, text="保存名单", command=self.save_students).pack(side=tk.LEFT, padx=3)
        ttk.Button(button_frame, text="清空名单", command=self.clear_students).pack(side=tk.LEFT, padx=3)
        ttk.Button(button_frame, text="导入名单", command=self.import_students_from_file).pack(side=tk.LEFT, padx=3)

        # 设置部分
        settings_frame = ttk.LabelFrame(parent, text="系统设置", padding="5")
        settings_frame.pack(fill=tk.X, pady=3, padx=3)

        # 根目录选择
        dir_frame = ttk.Frame(settings_frame)
        dir_frame.pack(fill=tk.X, pady=2)

        ttk.Label(dir_frame, text="作业根目录:").pack(side=tk.LEFT)
        ttk.Entry(dir_frame, textvariable=self.dir_var, width=30).pack(side=tk.LEFT, padx=3)
        ttk.Button(dir_frame, text="浏览", command=self.browse_directory).pack(side=tk.LEFT, padx=3)

        # 检查模式选择 - 添加混合模式
        mode_frame = ttk.Frame(settings_frame)
        mode_frame.pack(fill=tk.X, pady=2)

        ttk.Label(mode_frame, text="检查模式:").pack(side=tk.LEFT)
        ttk.Radiobutton(mode_frame, text="混合模式", variable=self.mode_var,
                        value="hybrid", command=self.update_mode).pack(side=tk.LEFT, padx=5)
        ttk.Radiobutton(mode_frame, text="文件夹模式", variable=self.mode_var,
                        value="folder", command=self.update_mode).pack(side=tk.LEFT, padx=5)
        ttk.Radiobutton(mode_frame, text="文件模式", variable=self.mode_var,
                        value="file", command=self.update_mode).pack(side=tk.LEFT, padx=5)

        # 文件扩展名设置 - 修复按钮显示问题
        ext_frame = ttk.Frame(settings_frame)
        ext_frame.pack(fill=tk.X, pady=2)

        ttk.Label(ext_frame, text="文件扩展名:").pack(side=tk.LEFT)

        # 创建扩展名显示框架和添加按钮框架
        ext_buttons_frame = ttk.Frame(ext_frame)
        ext_buttons_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)

        self.ext_frame_inner = ttk.Frame(ext_buttons_frame)
        self.ext_frame_inner.pack(side=tk.LEFT, fill=tk.X, expand=True)

        # 在扩展名框架后面添加按钮
        button_container = ttk.Frame(ext_buttons_frame)
        button_container.pack(side=tk.LEFT, padx=(5, 0))

        # 添加扩展名按钮 - 修复：使用tk.Button确保字体显示
        self.add_ext_btn = tk.Button(button_container, text="添加", command=self.add_extension,
                                     font=("Arial", 9), width=6, height=1)
        self.add_ext_btn.pack(side=tk.LEFT)

        # 更新扩展名显示
        self.update_extensions()

        # 自动刷新设置
        refresh_frame = ttk.Frame(settings_frame)
        refresh_frame.pack(fill=tk.X, pady=2)

        ttk.Label(refresh_frame, text="自动刷新:").pack(side=tk.LEFT)
        ttk.Checkbutton(refresh_frame, text="启用", variable=self.refresh_var,
                        command=self.toggle_auto_refresh).pack(side=tk.LEFT, padx=5)

        ttk.Label(refresh_frame, text="间隔(秒):").pack(side=tk.LEFT, padx=(10, 2))
        self.interval_spinbox = tk.Spinbox(refresh_frame, from_=5, to=300, width=5, textvariable=self.interval_var,
                                           command=self.update_refresh_interval)
        self.interval_spinbox.pack(side=tk.LEFT, padx=3)

        # 抄袭检测设置
        plagiarism_frame = ttk.Frame(settings_frame)
        plagiarism_frame.pack(fill=tk.X, pady=2)

        ttk.Label(plagiarism_frame, text="抄袭检测:").pack(side=tk.LEFT)
        ttk.Checkbutton(plagiarism_frame, text="启用", variable=tk.BooleanVar(value=True),
                        state="disabled").pack(side=tk.LEFT, padx=5)

        ttk.Label(plagiarism_frame, text="相似度阈值(%):").pack(side=tk.LEFT, padx=(10, 2))
        self.similarity_spinbox = tk.Spinbox(plagiarism_frame, from_=1, to=100, width=5,
                                             textvariable=self.similarity_var,
                                             command=self.update_similarity_threshold)
        self.similarity_spinbox.pack(side=tk.LEFT, padx=3)

        self.similarity_spinbox.bind('<Return>', lambda e: self.update_similarity_threshold())
        self.similarity_spinbox.bind('<FocusOut>', lambda e: self.update_similarity_threshold())

        # 考勤功能部分
        attendance_frame = ttk.LabelFrame(parent, text="考勤功能", padding="5")
        attendance_frame.pack(fill=tk.X, pady=3, padx=3)

        attendance_dir_frame = ttk.Frame(attendance_frame)
        attendance_dir_frame.pack(fill=tk.X, pady=2)

        ttk.Label(attendance_dir_frame, text="考勤文件夹:").pack(side=tk.LEFT)
        self.attendance_dir_var = tk.StringVar()
        ttk.Entry(attendance_dir_frame, textvariable=self.attendance_dir_var, width=20).pack(side=tk.LEFT, padx=3)
        ttk.Button(attendance_dir_frame, text="浏览",
                   command=lambda: self.browse_attendance_directory()).pack(side=tk.LEFT, padx=3)

        ttk.Button(attendance_dir_frame, text="考勤统计", command=self.check_attendance).pack(side=tk.LEFT, padx=3)

        # 操作按钮区域
        action_frame = ttk.Frame(parent)
        action_frame.pack(fill=tk.X, pady=5, padx=3)

        self.stats_label = ttk.Label(action_frame, text="", font=("Arial", 9, "bold"))
        self.stats_label.pack(side=tk.LEFT, padx=3)

        ttk.Button(action_frame, text="立即检查", command=self.check_homework).pack(side=tk.RIGHT, padx=3)
        ttk.Button(action_frame, text="作业迁移", command=self.migrate_homework).pack(side=tk.RIGHT, padx=3)

    def create_right_panel(self, parent):
        """创建右侧结果显示面板"""
        result_frame = ttk.LabelFrame(parent, text="检查结果", padding="5")
        result_frame.pack(fill=tk.BOTH, expand=True, pady=3, padx=3)

        self.result_tree = ttk.Treeview(result_frame, height=23)

        self.result_tree["columns"] = ("学生", "文件名", "状态", "相似度", "详细信息", "最后更新时间", "文件路径")
        self.result_tree["show"] = "headings"

        columns_config = [
            ("学生", "学生", 65),
            ("文件名", "文件名", 105),
            ("状态", "状态", 65),
            ("相似度", "相似度", 65),
            ("详细信息", "详细信息", 210),
            ("最后更新时间", "最后更新时间", 105),
            ("文件路径", "文件路径", 0)
        ]

        for col, text, width in columns_config:
            self.result_tree.heading(col, text=text,
                                     command=lambda c=col: self.treeview_sort_column(c))
            self.result_tree.column(col, width=width,
                                    anchor=tk.W if col in ["学生", "文件名", "详细信息"] else tk.CENTER,
                                    stretch=(col == "详细信息"))

        self.result_tree.tag_configure('submitted', background='#e8f5e9')
        self.result_tree.tag_configure('not_submitted', background='#f5f5f5')
        self.result_tree.tag_configure('suspected_plagiarism', background='#ffebee')

        self.result_tree.bind("<Double-1>", self.on_item_double_click)
        self.result_tree.bind("<Button-3>", self.on_tree_right_click)

        scrollbar = ttk.Scrollbar(result_frame, orient=tk.VERTICAL, command=self.result_tree.yview)
        self.result_tree.configure(yscrollcommand=scrollbar.set)

        self.result_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

    def treeview_sort_column(self, col):
        """对树形视图的列进行排序 - 优化版：多级排序"""
        try:
            items = [(self.result_tree.set(item, col), item) for item in self.result_tree.get_children('')]

            # 状态顺序：未提交(1)、疑似抄袭(2)、已提交(3)
            status_order = {"未提交": 1, "疑似抄袭": 2, "已提交": 3}

            if col == "状态":
                # 按状态排序时，先按状态，再按相似度（降序）
                def get_sort_key(item):
                    student = self.result_tree.set(item[1], "学生")
                    file_name = self.result_tree.set(item[1], "文件名")
                    status = self.result_tree.set(item[1], "状态")
                    similarity_str = self.result_tree.set(item[1], "相似度")

                    # 获取相似度数值
                    try:
                        if similarity_str and similarity_str.strip() and similarity_str != "0%":
                            similarity_value = float(similarity_str.strip('%'))
                        else:
                            similarity_value = 0.0
                    except (ValueError, AttributeError):
                        similarity_value = 0.0

                    student_pinyin = self.get_chinese_pinyin(student)
                    file_name_pinyin = self.get_chinese_pinyin(file_name)

                    status_rank = status_order.get(status, 4)

                    # 先按状态，再按相似度（降序），最后按学生和文件名
                    return (status_rank, -similarity_value, student_pinyin, file_name_pinyin)

                items.sort(key=get_sort_key, reverse=self.sort_reverse)

            elif col == "相似度":
                # 按相似度排序时，先按相似度（降序），再按状态
                def get_sort_key(item):
                    student = self.result_tree.set(item[1], "学生")
                    file_name = self.result_tree.set(item[1], "文件名")
                    status = self.result_tree.set(item[1], "状态")
                    similarity_str = self.result_tree.set(item[1], "相似度")

                    try:
                        if similarity_str and similarity_str.strip() and similarity_str != "0%":
                            similarity_value = float(similarity_str.strip('%'))
                        else:
                            similarity_value = 0.0
                    except (ValueError, AttributeError):
                        similarity_value = 0.0

                    student_pinyin = self.get_chinese_pinyin(student)
                    file_name_pinyin = self.get_chinese_pinyin(file_name)

                    status_rank = status_order.get(status, 4)

                    # 先按相似度（降序），再按状态，最后按学生和文件名
                    return (-similarity_value, status_rank, student_pinyin, file_name_pinyin)

                items.sort(key=get_sort_key, reverse=not self.sort_reverse)

            elif col == "学生":
                # 按学生排序时，先按学生，再按状态，最后按相似度
                def get_sort_key(item):
                    student = item[0]
                    file_name = self.result_tree.set(item[1], "文件名")
                    status = self.result_tree.set(item[1], "状态")
                    similarity_str = self.result_tree.set(item[1], "相似度")

                    try:
                        if similarity_str and similarity_str.strip() and similarity_str != "0%":
                            similarity_value = float(similarity_str.strip('%'))
                        else:
                            similarity_value = 0.0
                    except (ValueError, AttributeError):
                        similarity_value = 0.0

                    student_pinyin = self.get_chinese_pinyin(student)
                    file_name_pinyin = self.get_chinese_pinyin(file_name)

                    status_rank = status_order.get(status, 4)

                    # 先按学生，再按状态，最后按相似度（降序）
                    return (student_pinyin, status_rank, -similarity_value, file_name_pinyin)

                items.sort(key=get_sort_key, reverse=self.sort_reverse)

            elif col == "文件名":
                # 按文件名排序时，先按文件名，再按状态，最后按相似度
                def get_sort_key(item):
                    file_name = item[0]
                    student = self.result_tree.set(item[1], "学生")
                    status = self.result_tree.set(item[1], "状态")
                    similarity_str = self.result_tree.set(item[1], "相似度")

                    try:
                        if similarity_str and similarity_str.strip() and similarity_str != "0%":
                            similarity_value = float(similarity_str.strip('%'))
                        else:
                            similarity_value = 0.0
                    except (ValueError, AttributeError):
                        similarity_value = 0.0

                    file_name_pinyin = self.get_chinese_pinyin(file_name)
                    student_pinyin = self.get_chinese_pinyin(student)

                    status_rank = status_order.get(status, 4)

                    # 先按文件名，再按状态，最后按相似度（降序）
                    return (file_name_pinyin, status_rank, -similarity_value, student_pinyin)

                items.sort(key=get_sort_key, reverse=self.sort_reverse)

            elif col == "最后更新时间":
                # 按最后更新时间排序时，先按时间，再按状态，最后按相似度
                def get_sort_key(item):
                    time_str = item[0]
                    student = self.result_tree.set(item[1], "学生")
                    file_name = self.result_tree.set(item[1], "文件名")
                    status = self.result_tree.set(item[1], "状态")
                    similarity_str = self.result_tree.set(item[1], "相似度")

                    try:
                        if similarity_str and similarity_str.strip() and similarity_str != "0%":
                            similarity_value = float(similarity_str.strip('%'))
                        else:
                            similarity_value = 0.0
                    except (ValueError, AttributeError):
                        similarity_value = 0.0

                    student_pinyin = self.get_chinese_pinyin(student)
                    file_name_pinyin = self.get_chinese_pinyin(file_name)

                    status_rank = status_order.get(status, 4)

                    try:
                        if time_str != "未知":
                            time_value = datetime.strptime(time_str, "%Y-%m-%d %H:%M:%S")
                            return (time_value, status_rank, -similarity_value, student_pinyin, file_name_pinyin)
                        else:
                            return (datetime.min, status_rank, -similarity_value, student_pinyin, file_name_pinyin)
                    except (ValueError, AttributeError):
                        return (datetime.min, status_rank, -similarity_value, student_pinyin, file_name_pinyin)

                items.sort(key=get_sort_key, reverse=not self.sort_reverse)

            else:
                # 其他列排序时，先按该列值，再按状态，最后按相似度
                def get_sort_key(item):
                    value = item[0]
                    student = self.result_tree.set(item[1], "学生")
                    file_name = self.result_tree.set(item[1], "文件名")
                    status = self.result_tree.set(item[1], "状态")
                    similarity_str = self.result_tree.set(item[1], "相似度")

                    try:
                        if similarity_str and similarity_str.strip() and similarity_str != "0%":
                            similarity_value = float(similarity_str.strip('%'))
                        else:
                            similarity_value = 0.0
                    except (ValueError, AttributeError):
                        similarity_value = 0.0

                    student_pinyin = self.get_chinese_pinyin(student)
                    file_name_pinyin = self.get_chinese_pinyin(file_name)

                    status_rank = status_order.get(status, 4)

                    return (value.lower(), status_rank, -similarity_value, student_pinyin, file_name_pinyin)

                items.sort(key=get_sort_key, reverse=self.sort_reverse)

            # 移动项目到新位置
            for index, (_, item) in enumerate(items):
                self.result_tree.move(item, '', index)

            # 更新列标题显示排序方向
            self.update_column_heading(col)
            self.sort_column = col
            self.sort_reverse = not self.sort_reverse

        except Exception as e:
            self.logger.error(f"树形视图排序出错: {str(e)}")

    def update_column_heading(self, col):
        """更新列标题显示排序方向"""
        # 清除所有列的箭头
        for column in self.result_tree["columns"]:
            current_text = self.result_tree.heading(column)["text"]
            if current_text.endswith(" ↑") or current_text.endswith(" ↓"):
                # 移除箭头，保留原始文本
                base_text = current_text[:-2]
                self.result_tree.heading(column, text=base_text)

        # 为当前排序列添加箭头
        current_text = self.result_tree.heading(col)["text"]
        arrow = " ↑" if not self.sort_reverse else " ↓"
        if not current_text.endswith(arrow):
            self.result_tree.heading(col, text=current_text + arrow)

    def get_chinese_pinyin(self, text):
        """获取中文字符串的拼音，用于排序"""
        try:
            if not text or text.strip() == "":
                return ""

            pinyin_list = pinyin(text, style=Style.FIRST_LETTER)
            return ''.join([item[0] for item in pinyin_list if item[0]]).lower()
        except Exception as e:
            self.logger.error(f"获取中文拼音出错: {str(e)}")
            return text.lower()

    def on_tree_right_click(self, event):
        """处理树形视图右键点击事件"""
        try:
            row_id = self.result_tree.identify_row(event.y)
            if row_id:
                self.result_tree.selection_set(row_id)

                menu = tk.Menu(self.root, tearoff=0)
                menu.add_command(label="查看完整详情", command=lambda: self.show_full_detailed_info(row_id))
                menu.add_command(label="打开文件位置", command=lambda: self.open_file_location(row_id))
                menu.add_separator()

                menu.add_command(label="按状态排序", command=lambda: self.treeview_sort_column("状态"))
                menu.add_command(label="按学生排序", command=lambda: self.treeview_sort_column("学生"))
                menu.add_command(label="按相似度排序", command=lambda: self.treeview_sort_column("相似度"))
                menu.add_command(label="按文件名排序", command=lambda: self.treeview_sort_column("文件名"))
                menu.add_command(label="按时间排序", command=lambda: self.treeview_sort_column("最后更新时间"))

                # 移除右键菜单中的"关闭窗口"选项，避免误操作
                menu.post(event.x_root, event.y_root)
        except Exception as e:
            self.logger.error(f"树形视图右键事件处理出错: {str(e)}")

    def show_full_detailed_info(self, item_id):
        """显示学生文件的完整详细作业信息"""
        try:
            values = self.result_tree.item(item_id, "values")
            if not values or len(values) < 7:
                messagebox.showwarning("警告", "未找到有效的文件信息")
                return

            student_name = values[0]
            file_name = values[1]
            file_path = values[6]

            detail_dialog = tk.Toplevel(self.root)
            detail_dialog.title(f"{student_name} - {file_name} - 作业详情")
            detail_dialog.geometry("800x600")

            # 居中显示并立即定位
            detail_dialog.withdraw()
            self.center_dialog(detail_dialog, 800, 600)
            detail_dialog.deiconify()

            detail_dialog.resizable(True, True)

            text_frame = ttk.Frame(detail_dialog)
            text_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

            text_widget = tk.Text(text_frame, wrap=tk.WORD, font=("Arial", 10))
            text_widget.pack(fill=tk.BOTH, expand=True, side=tk.LEFT)

            scrollbar = ttk.Scrollbar(text_widget, command=text_widget.yview)
            scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
            text_widget.config(yscrollcommand=scrollbar.set)

            details = f"学生: {student_name}\n"
            details += f"文件名: {file_name}\n"
            details += f"文件路径: {file_path}\n"
            details += f"状态: {values[2]}\n"
            details += f"相似度: {values[3]}\n"
            details += f"最后更新时间: {values[5]}\n\n"

            if file_path and os.path.exists(file_path):
                try:
                    file_size = os.path.getsize(file_path)
                    file_time = self.get_file_modification_time(file_path)
                    details += f"文件大小: {file_size} 字节\n"
                    details += f"文件修改时间: {file_time}\n\n"
                except Exception as e:
                    details += f"文件信息获取失败: {str(e)}\n\n"
            else:
                details += "文件路径不存在\n\n"

            if student_name in self.all_similarity_results:
                for file_key, sim_info in self.all_similarity_results.get(student_name, {}).items():
                    if file_key == file_name:
                        details += "相似度详情:\n"
                        details += f"  最高相似度: {sim_info.get('similarity', 0)}%\n"
                        if 'matches' in sim_info:
                            matches = sim_info['matches']
                            if matches:
                                details += "  相似文件:\n"
                                for match in matches:
                                    details += f"    {match}\n"

            if file_path and os.path.exists(file_path) and file_path.lower().endswith(
                    ('.py', '.txt', '.java', '.cpp', '.c', '.h', '.js', '.html', '.css')):
                try:
                    with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                        content = f.read()
                        details += f"\n文件内容预览（前1000字符）:\n{content[:1000]}"
                        if len(content) > 1000:
                            details += "...\n（内容截断，完整内容请查看文件）"
                except Exception as e:
                    details += f"\n无法读取文件内容: {str(e)}"

            text_widget.insert(tk.END, details)
            text_widget.config(state=tk.DISABLED)

            btn_frame = ttk.Frame(detail_dialog)
            btn_frame.pack(pady=10)
            ttk.Button(btn_frame, text="关闭", command=detail_dialog.destroy).pack()

            detail_dialog.transient(self.root)
            detail_dialog.grab_set()
        except Exception as e:
            self.logger.error(f"显示详细信息出错: {str(e)}")
            messagebox.showerror("错误", f"显示详细信息出错: {str(e)}")

    def open_file_location(self, item_id):
        """打开文件所在位置 - 修复版"""
        try:
            values = self.result_tree.item(item_id, "values")
            if not values or len(values) < 7:
                messagebox.showwarning("警告", "未找到有效的文件信息")
                return

            file_path = values[6]
            student_name = values[0]

            # 检查文件路径是否为空
            if not file_path or file_path == "":
                # 如果没有文件路径，尝试查找学生文件夹
                root_dir = self.dir_var.get()
                if root_dir and os.path.exists(root_dir):
                    student_folder = self.find_student_folder(root_dir, student_name)
                    if student_folder and os.path.exists(student_folder):
                        self.open_file_explorer(student_folder)
                        return
                    else:
                        messagebox.showinfo("提示", f"未找到学生 {student_name} 的文件夹")
                        return
                else:
                    messagebox.showwarning("警告", "请先设置作业根目录")
                    return

            # 尝试打开文件所在目录
            self.open_file_explorer(file_path)

        except Exception as e:
            self.logger.error(f"打开文件位置出错: {str(e)}")
            messagebox.showerror("错误", f"打开文件位置出错: {str(e)}")

    def on_item_double_click(self, event):
        """双击结果项时打开学生作业目录或文件 - 修复版"""
        try:
            selection = self.result_tree.selection()
            if not selection:
                return

            item = selection[0]
            values = self.result_tree.item(item, "values")
            if not values or len(values) < 7:
                messagebox.showwarning("警告", "未找到有效的文件信息")
                return

            student_name = values[0]
            file_path = values[6]

            # 检查文件路径是否为空
            if not file_path or file_path == "":
                # 如果没有文件路径，尝试查找学生文件夹
                root_dir = self.dir_var.get()
                if root_dir and os.path.exists(root_dir):
                    student_folder = self.find_student_folder(root_dir, student_name)
                    if student_folder and os.path.exists(student_folder):
                        self.open_file_explorer(student_folder)
                        return
                    else:
                        messagebox.showinfo("提示", f"未找到学生 {student_name} 的文件夹")
                        return
                else:
                    messagebox.showwarning("警告", "请先设置作业根目录")
                    return

            # 文件路径不为空，尝试打开
            self.open_file_explorer(file_path)

        except Exception as e:
            self.logger.error(f"双击结果项处理出错: {str(e)}")
            messagebox.showerror("错误", f"打开失败: {str(e)}")

    def open_file_explorer(self, path):
        """打开文件资源管理器并定位到指定路径"""
        try:
            if not path or path == "":
                messagebox.showwarning("警告", "路径为空")
                return

            normalized_path = os.path.normpath(path)

            # 检查路径是否存在
            if not os.path.exists(normalized_path):
                messagebox.showwarning("警告", f"路径不存在: {normalized_path}")
                return

            # 如果是文件，打开所在文件夹；如果是文件夹，直接打开
            if os.path.isfile(normalized_path):
                # 获取文件所在目录
                folder_path = os.path.dirname(normalized_path)
                if platform.system() == "Windows":
                    # Windows系统：使用explorer打开文件夹并选择文件
                    subprocess.run(f'explorer /select,"{normalized_path}"', shell=True)
                elif platform.system() == "Darwin":
                    # macOS系统：使用open命令
                    subprocess.call(["open", "-R", normalized_path])
                else:
                    # Linux系统：使用xdg-open
                    subprocess.call(["xdg-open", folder_path])
            else:
                # 如果是文件夹，直接打开
                if platform.system() == "Windows":
                    os.startfile(normalized_path)
                elif platform.system() == "Darwin":
                    subprocess.call(["open", normalized_path])
                else:
                    subprocess.call(["xdg-open", normalized_path])

        except Exception as e:
            self.logger.error(f"打开文件资源管理器出错: {str(e)}")
            messagebox.showerror("错误", f"无法打开目录: {str(e)}")

    def calculate_md5(self, file_path):
        """计算文件的MD5哈希值"""
        try:
            with open(file_path, 'rb') as f:
                file_hash = hashlib.md5()
                while chunk := f.read(8192):
                    file_hash.update(chunk)
            return file_hash.hexdigest()
        except Exception as e:
            self.logger.error(f"计算MD5时出错: {e}")
            return None

    def calculate_similarity_optimized(self, file1_path, file2_path):
        """优化的相似度计算算法 - 提高准确率，减少误判"""
        try:
            # 检查文件是否存在
            if not os.path.exists(file1_path) or not os.path.exists(file2_path):
                return 0.0

            # 检查文件大小
            size1 = os.path.getsize(file1_path)
            size2 = os.path.getsize(file2_path)

            # 文件大小过滤
            if size1 < self.min_file_size or size2 < self.min_file_size:
                return 0.0

            if size1 > self.max_file_size or size2 > self.max_file_size:
                return 0.0

            # 读取文件内容
            try:
                with open(file1_path, 'r', encoding='utf-8', errors='ignore') as f1:
                    content1 = f1.read()
                with open(file2_path, 'r', encoding='utf-8', errors='ignore') as f2:
                    content2 = f2.read()
            except Exception as e:
                self.logger.error(f"读取文件出错: {e}")
                return 0.0

            # 如果内容完全相同
            if content1 == content2:
                return 100.0

            # 方法1: 基本的序列匹配
            basic_similarity = difflib.SequenceMatcher(None, content1, content2).ratio() * 100

            # 如果基本相似度非常高，直接返回
            if basic_similarity > 95:
                return basic_similarity

            # 方法2: 预处理内容 - 移除常见模板代码
            def preprocess_content(content):
                # 移除空行
                lines = [line.strip() for line in content.split('\n') if line.strip()]

                # 对于代码文件，移除常见的导入语句和模板代码
                # 这些通常是老师提供的模板，不应该计入相似度
                common_patterns = [
                    r'^import\s+.*$',
                    r'^from\s+.*$',
                    r'^#.*$',  # Python注释
                    r'^//.*$',  # C/Java/JS注释
                    r'^/\*.*$',  # 多行注释开始
                    r'^\*.*$',  # 多行注释中间
                    r'^\*/.*$',  # 多行注释结束
                    r'^#include\s+.*$',
                    r'^using\s+.*$',
                    r'^package\s+.*$',
                    r'^public\s+class\s+.*$',
                    r'^class\s+.*$',
                    r'^def\s+.*$',
                    r'^function\s+.*$',
                ]

                filtered_lines = []
                for line in lines:
                    line_stripped = line.strip()
                    is_common = False
                    for pattern in common_patterns:
                        if re.match(pattern, line_stripped, re.IGNORECASE):
                            is_common = True
                            break

                    if not is_common:
                        filtered_lines.append(line_stripped)

                return '\n'.join(filtered_lines)

            preprocessed1 = preprocess_content(content1)
            preprocessed2 = preprocess_content(content2)

            # 如果预处理后内容太少，直接返回基本相似度
            if len(preprocessed1) < 10 or len(preprocessed2) < 10:
                return basic_similarity

            # 方法3: 预处理后的序列匹配
            preprocessed_similarity = difflib.SequenceMatcher(None, preprocessed1, preprocessed2).ratio() * 100

            # 方法4: 行级比较 - 过滤掉常见行
            lines1 = [line.strip() for line in content1.split('\n') if line.strip()]
            lines2 = [line.strip() for line in content2.split('\n') if line.strip()]

            # 过滤掉常见模板行
            common_template_lines = {
                'import', 'from', 'include', 'using', 'package',
                'public class', 'class', 'def', 'function',
                'void main', 'int main', 'main()'
            }

            filtered_lines1 = [line for line in lines1 if
                               not any(template in line.lower() for template in common_template_lines)]
            filtered_lines2 = [line for line in lines2 if
                               not any(template in line.lower() for template in common_template_lines)]

            line_similarity = 0
            if filtered_lines1 and filtered_lines2:
                # 找出相同的行
                common_lines = set(filtered_lines1) & set(filtered_lines2)
                if common_lines:
                    line_similarity = (len(common_lines) / max(len(filtered_lines1), len(filtered_lines2))) * 100

            # 方法5: 代码结构相似度（针对代码文件）
            structure_similarity = 0
            file1_ext = os.path.splitext(file1_path)[1].lower()
            file2_ext = os.path.splitext(file2_path)[1].lower()

            if file1_ext in ['.py', '.java', '.cpp', '.c', '.js'] and file2_ext == file1_ext:
                def extract_code_structure(content):
                    # 提取函数/方法定义
                    patterns = {
                        '.py': r'def\s+(\w+)\s*\(',
                        '.java': r'(public|private|protected)?\s*(static)?\s*\w+\s+(\w+)\s*\(',
                        '.cpp': r'\w+\s+(\w+)\s*\([^)]*\)\s*\{',
                        '.c': r'\w+\s+(\w+)\s*\([^)]*\)\s*\{',
                        '.js': r'function\s+(\w+)\s*\(|(\w+)\s*=\s*function\s*\('
                    }

                    ext_pattern = file1_ext
                    pattern = patterns.get(ext_pattern, r'\w+\s+(\w+)\s*\(')

                    matches = re.findall(pattern, content)
                    if matches:
                        # 清理匹配结果
                        if isinstance(matches[0], tuple):
                            # 对于多个捕获组的情况，取最后一个非空组
                            cleaned = []
                            for match in matches:
                                for item in match:
                                    if item:
                                        cleaned.append(item)
                                        break
                            return cleaned
                        else:
                            return list(matches)
                    return []

                struct1 = extract_code_structure(content1)
                struct2 = extract_code_structure(content2)

                if struct1 and struct2:
                    common_struct = set(struct1) & set(struct2)
                    if common_struct:
                        structure_similarity = (len(common_struct) / max(len(struct1), len(struct2))) * 100

            # 综合计算最终相似度
            # 调整权重：预处理相似度最重要，基本相似度其次，行相似度和结构相似度作为补充
            final_similarity = (
                    preprocessed_similarity * 0.4 +
                    basic_similarity * 0.3 +
                    line_similarity * 0.2 +
                    structure_similarity * 0.1
            )

            # 考虑文件大小差异
            if size1 > 0 and size2 > 0:
                size_ratio = min(size1, size2) / max(size1, size2)
                # 如果大小差异太大，降低相似度
                if size_ratio < 0.5:
                    final_similarity *= 0.7
                elif size_ratio < 0.7:
                    final_similarity *= 0.85

            # 确保在合理范围内
            result = round(max(0.0, min(100.0, final_similarity)), 2)

            self.logger.debug(f"相似度计算: {os.path.basename(file1_path)} vs {os.path.basename(file2_path)}")
            self.logger.debug(f"  基本相似度: {basic_similarity:.2f}%")
            self.logger.debug(f"  预处理相似度: {preprocessed_similarity:.2f}%")
            self.logger.debug(f"  行相似度: {line_similarity:.2f}%")
            self.logger.debug(f"  结构相似度: {structure_similarity:.2f}%")
            self.logger.debug(f"  最终相似度: {result:.2f}%")

            return result

        except Exception as e:
            self.logger.error(f"计算相似度时出错: {e}")
            return 0.0

    def get_file_modification_time(self, file_path):
        """获取文件的最后修改时间"""
        try:
            if os.path.exists(file_path):
                timestamp = os.path.getmtime(file_path)
                return datetime.fromtimestamp(timestamp).strftime("%Y-%m-%d %H:%M:%S")
        except Exception as e:
            self.logger.error(f"获取文件修改时间时出错: {e}")
        return "未知"

    def extract_student_name(self, text):
        """从字符串中提取学生姓名，支持多种格式"""
        try:
            students = self.classes[self.current_class]["students"]

            if not students:
                return None

            clean_text = text.strip()

            for student in students:
                if student in clean_text:
                    return student

            best_match = None
            best_score = 0

            for student in students:
                clean_student = re.sub(r'^\d+[\s\-_]*', '', student)

                patterns = [
                    rf'.*{re.escape(clean_student)}.*',
                    rf'.*\d+[\-\_\s]*{re.escape(clean_student)}.*',
                    rf'.*{re.escape(clean_student)}[\-\_\s]*\d+.*',
                ]

                for pattern in patterns:
                    if re.match(pattern, clean_text, re.IGNORECASE):
                        return student

                similarity = difflib.SequenceMatcher(None, clean_student, clean_text).ratio()

                if clean_student in clean_text or clean_text in clean_student:
                    similarity += 0.3

                common_chars = set(clean_student) & set(clean_text)
                if len(common_chars) > 0:
                    similarity += 0.1 * len(common_chars)

                if similarity > best_score:
                    best_score = similarity
                    best_match = student

            if best_score > 0.6:
                return best_match

            return None
        except Exception as e:
            self.logger.error(f"提取学生姓名出错: {str(e)}")
            return None

    def find_student_folder(self, root_dir, student):
        """在根目录中查找学生文件夹，支持模糊匹配"""
        try:
            if not os.path.exists(root_dir):
                return None

            best_match = None
            best_score = 0

            latest_folder = self.get_latest_folder(root_dir)
            search_folders = []

            if latest_folder:
                search_folders.append(latest_folder)

            search_folders.append(root_dir)

            for folder in search_folders:
                for item in os.listdir(folder):
                    item_path = os.path.join(folder, item)
                    if os.path.isdir(item_path):
                        extracted_name = self.extract_student_name(item)
                        if extracted_name == student:
                            return item_path

                        similarity = difflib.SequenceMatcher(None, student, item).ratio()
                        if similarity > best_score:
                            best_score = similarity
                            best_match = item_path

            if best_score > 0.7:
                return best_match

            return None
        except Exception as e:
            self.logger.error(f"查找学生文件夹出错: {str(e)}")
            return None

    def find_student_files_recursive(self, root_dir, student, max_depth=3):
        """递归查找学生文件，支持文件夹嵌套"""
        found_files = []

        def search_in_dir(current_dir, current_depth):
            if current_depth > max_depth:
                return

            try:
                for item in os.listdir(current_dir):
                    item_path = os.path.join(current_dir, item)

                    if os.path.isdir(item_path):
                        if not item.startswith('.') and item not in ['__pycache__', 'node_modules', 'venv', '.git',
                                                                     '.idea']:
                            search_in_dir(item_path, current_depth + 1)

                    elif os.path.isfile(item_path):
                        extracted_name = self.extract_student_name(item)
                        if extracted_name == student:
                            if any(item.lower().endswith(ext.lower()) for ext in self.file_extensions):
                                found_files.append((item, item_path))
            except (PermissionError, OSError) as e:
                self.logger.warning(f"无法访问目录 {current_dir}: {str(e)}")
            except Exception as e:
                self.logger.error(f"搜索目录时出错: {str(e)}")

        try:
            latest_folder = self.get_latest_folder(root_dir)
            if latest_folder:
                search_in_dir(latest_folder, 1)

            search_in_dir(root_dir, 1)
        except Exception as e:
            self.logger.error(f"递归查找学生文件出错: {str(e)}")

        return found_files

    def find_student_files_in_folder(self, folder_path, student, max_depth=2):
        """在文件夹内查找学生文件"""
        found_files = []

        def search_in_dir(current_dir, current_depth):
            if current_depth > max_depth:
                return

            try:
                for item in os.listdir(current_dir):
                    item_path = os.path.join(current_dir, item)

                    if os.path.isfile(item_path):
                        extracted_name = self.extract_student_name(item)
                        if extracted_name == student:
                            if any(item.lower().endswith(ext.lower()) for ext in self.file_extensions):
                                found_files.append((item, item_path))
            except (PermissionError, OSError) as e:
                self.logger.warning(f"无法访问目录 {current_dir}: {str(e)}")
            except Exception as e:
                self.logger.error(f"搜索目录时出错: {str(e)}")

        try:
            search_in_dir(folder_path, 1)
        except Exception as e:
            self.logger.error(f"在文件夹内查找学生文件出错: {str(e)}")

        return found_files

    def get_latest_folder(self, root_dir):
        """获取根目录下最新的文件夹"""
        try:
            if not os.path.exists(root_dir):
                return None

            folders = []
            for item in os.listdir(root_dir):
                item_path = os.path.join(root_dir, item)
                if os.path.isdir(item_path):
                    if not item.startswith('.') and item not in ['__pycache__', 'node_modules', 'venv']:
                        folders.append((item_path, os.path.getmtime(item_path)))

            if not folders:
                return None

            folders.sort(key=lambda x: x[1], reverse=True)
            return folders[0][0]
        except Exception as e:
            self.logger.error(f"获取最新文件夹出错: {str(e)}")
            return None

    def check_similarity_all_files_optimized(self, student_files_data):
        """对所有文件进行相似度检测 - 优化版本（增加线程数）"""
        try:
            self.logger.info(f"开始优化的相似度检测，使用 {self.max_workers} 个工作线程")

            # 清空缓存
            self.file_content_cache.clear()
            self.file_hash_cache.clear()

            # 重新组织数据结构
            all_files = []
            student_file_map = {}  # 学生 -> [文件信息列表]

            for student, files in student_files_data.items():
                self.logger.info(f"处理学生 {student} 的文件，共 {len(files)} 个文件")
                student_file_map[student] = []

                for file_info in files:
                    file_path = file_info['file_path']
                    file_name = file_info['file_name']

                    # 计算MD5
                    if file_path not in self.file_hash_cache:
                        md5_hash = self.calculate_md5(file_path)
                        if md5_hash:
                            self.file_hash_cache[file_path] = md5_hash
                        else:
                            continue

                    file_size = os.path.getsize(file_path)
                    file_ext = os.path.splitext(file_name)[1].lower()

                    file_data = {
                        'student': student,
                        'file_name': file_name,
                        'file_path': file_path,
                        'file_size': file_size,
                        'file_ext': file_ext,
                        'md5': self.file_hash_cache[file_path]
                    }

                    all_files.append(file_data)
                    student_file_map[student].append(file_data)

            self.logger.info(f"收集到 {len(all_files)} 个文件数据")

            # 如果文件数量很少，减少线程数
            dynamic_max_workers = min(self.max_workers, max(2, len(all_files) // 10))
            if dynamic_max_workers != self.max_workers:
                self.logger.info(f"文件较少，调整线程数为: {dynamic_max_workers}")

            # 存储所有相似度结果
            all_similarity_results = defaultdict(dict)

            # 初始化所有文件的相似度记录
            for file_data in all_files:
                student = file_data['student']
                file_name = file_data['file_name']

                all_similarity_results[student][file_name] = {
                    'similarity': 0.0,
                    'matches': [],
                    'file_path': file_data['file_path']
                }

            # 第一阶段：MD5相同检测 - 只检测不同学生的文件
            md5_groups = defaultdict(list)
            for file_data in all_files:
                if file_data['md5']:
                    md5_groups[file_data['md5']].append(file_data)

            for md5_hash, files in md5_groups.items():
                if len(files) > 1:
                    # 按学生分组，确保不比较同一学生的文件
                    student_files = defaultdict(list)
                    for file_data in files:
                        student_files[file_data['student']].append(file_data)

                    # 获取所有有该MD5文件的学生列表
                    students_with_same_md5 = list(student_files.keys())

                    if len(students_with_same_md5) > 1:
                        # 比较不同学生的文件
                        for i in range(len(students_with_same_md5)):
                            student1 = students_with_same_md5[i]
                            for file_data1 in student_files[student1]:
                                for j in range(i + 1, len(students_with_same_md5)):
                                    student2 = students_with_same_md5[j]
                                    for file_data2 in student_files[student2]:
                                        # 更新相似度信息
                                        file_name1 = file_data1['file_name']
                                        file_name2 = file_data2['file_name']

                                        all_similarity_results[student1][file_name1]['similarity'] = 100.0
                                        match_info = f"{student2}({file_name2}): 100.0% (MD5相同)"
                                        all_similarity_results[student1][file_name1]['matches'].append(match_info)

                                        all_similarity_results[student2][file_name2]['similarity'] = 100.0
                                        match_info = f"{student1}({file_name1}): 100.0% (MD5相同)"
                                        all_similarity_results[student2][file_name2]['matches'].append(match_info)

            # 第二阶段：相似度计算 - 只比较不同学生的文件
            similarity_count = 0

            # 按文件扩展名分组
            files_by_extension = defaultdict(list)
            for file_data in all_files:
                # 跳过已经有MD5相同匹配的文件
                student = file_data['student']
                file_name = file_data['file_name']
                if all_similarity_results[student][file_name]['similarity'] >= 100:
                    continue

                files_by_extension[file_data['file_ext']].append(file_data)

            # 动态调整线程池大小
            total_file_pairs = 0
            for ext, file_list in files_by_extension.items():
                if len(file_list) > 1:
                    # 计算可能的文件对数量
                    total_file_pairs += len(file_list) * (len(file_list) - 1) // 2

            # 根据文件对数量进一步调整线程数
            if total_file_pairs > 1000:
                dynamic_max_workers = min(self.max_workers * 2, 16)  # 对于大量文件，使用更多线程
                self.logger.info(f"文件对数量较多 ({total_file_pairs})，增加线程数为: {dynamic_max_workers}")
            elif total_file_pairs < 100:
                dynamic_max_workers = max(2, min(4, self.max_workers))  # 对于少量文件，减少线程数
                self.logger.info(f"文件对数量较少 ({total_file_pairs})，减少线程数为: {dynamic_max_workers}")

            with ThreadPoolExecutor(max_workers=dynamic_max_workers) as executor:
                futures = []

                # 为每个扩展名组生成文件对
                for ext, file_list in files_by_extension.items():
                    if len(file_list) <= 1:
                        continue

                    self.logger.info(f"开始比较扩展名 {ext} 的文件，共 {len(file_list)} 个文件")

                    # 按学生分组
                    files_by_student = defaultdict(list)
                    for file_data in file_list:
                        files_by_student[file_data['student']].append(file_data)

                    # 获取所有学生列表
                    students = list(files_by_student.keys())

                    # 生成不同学生之间的文件对
                    for i in range(len(students)):
                        student1 = students[i]
                        files1 = files_by_student[student1]

                        for j in range(i + 1, len(students)):
                            student2 = students[j]
                            files2 = files_by_student[student2]

                            # 生成学生1和学生2之间的所有文件对
                            for file_data1 in files1:
                                # 跳过已经有MD5相同匹配的文件
                                if all_similarity_results[student1][file_data1['file_name']]['similarity'] >= 100:
                                    continue

                                for file_data2 in files2:
                                    # 跳过已经有MD5相同匹配的文件
                                    if all_similarity_results[student2][file_data2['file_name']]['similarity'] >= 100:
                                        continue

                                    # 快速过滤：大小差异太大（超过5倍）
                                    size1 = file_data1['file_size']
                                    size2 = file_data2['file_size']
                                    if max(size1, size2) > min(size1, size2) * 5:
                                        continue

                                    # 提交相似度计算
                                    future = executor.submit(
                                        self.calculate_similarity_optimized,
                                        file_data1['file_path'],
                                        file_data2['file_path']
                                    )
                                    futures.append((future, student1, file_data1, student2, file_data2))

                # 处理计算结果
                self.logger.info(f"开始计算 {len(futures)} 个文件对的相似度")

                # 分批处理结果，避免内存占用过高
                batch_size = 100
                for batch_start in range(0, len(futures), batch_size):
                    batch_end = min(batch_start + batch_size, len(futures))
                    batch = futures[batch_start:batch_end]

                    self.logger.info(
                        f"处理批次 {batch_start // batch_size + 1}/{(len(futures) + batch_size - 1) // batch_size}")

                    for future, student1, file_data1, student2, file_data2 in batch:
                        try:
                            similarity = future.result(timeout=60)  # 增加超时时间

                            # 只记录相似度超过20%的结果
                            if similarity >= 20:
                                similarity_count += 1

                                file_name1 = file_data1['file_name']
                                file_name2 = file_data2['file_name']

                                # 更新最高相似度
                                if similarity > all_similarity_results[student1][file_name1]['similarity']:
                                    all_similarity_results[student1][file_name1]['similarity'] = similarity

                                if similarity > all_similarity_results[student2][file_name2]['similarity']:
                                    all_similarity_results[student2][file_name2]['similarity'] = similarity

                                # 添加匹配信息
                                match_info1 = f"{student2}({file_name2}): {similarity:.1f}%"
                                if match_info1 not in all_similarity_results[student1][file_name1]['matches']:
                                    all_similarity_results[student1][file_name1]['matches'].append(match_info1)

                                match_info2 = f"{student1}({file_name1}): {similarity:.1f}%"
                                if match_info2 not in all_similarity_results[student2][file_name2]['matches']:
                                    all_similarity_results[student2][file_name2]['matches'].append(match_info2)

                        except Exception as e:
                            self.logger.error(f"计算相似度时出错: {e}")
                            continue

            self.logger.info(f"相似度检测完成，发现 {similarity_count} 组相似文件，使用线程数: {dynamic_max_workers}")

            return all_similarity_results

        except Exception as e:
            self.logger.error(f"检查相似度出错: {str(e)}")
            return {}

    def update_similarity_threshold(self):
        """更新相似度阈值"""
        try:
            new_threshold = int(self.similarity_var.get())
            if 1 <= new_threshold <= 100:
                self.similarity_threshold = new_threshold
                if self.current_class in self.classes:
                    self.classes[self.current_class]["similarity_threshold"] = new_threshold
                self.logger.info(f"相似度阈值已更新为: {new_threshold}%")
            else:
                self.similarity_threshold = 85
                self.similarity_var.set("85")
                if self.current_class in self.classes:
                    self.classes[self.current_class]["similarity_threshold"] = 85
                messagebox.showwarning("警告", "相似度阈值必须在1-100之间，已恢复为默认值85%")
        except ValueError as e:
            self.logger.error(f"更新相似度阈值出错: {str(e)}")
            self.similarity_threshold = 85
            self.similarity_var.set("85")
            if self.current_class in self.classes:
                self.classes[self.current_class]["similarity_threshold"] = 85
            messagebox.showwarning("警告", "请输入有效的数字，已恢复为默认值85%")

    def load_all_classes(self):
        """加载所有班级配置"""
        try:
            if os.path.exists("class_configs.json"):
                with open("class_configs.json", "r", encoding="utf-8") as f:
                    self.classes = json.load(f)

                if "last_current_class" in self.classes and self.classes["last_current_class"] in self.classes:
                    self.current_class = self.classes["last_current_class"]
                    self.class_var.set(self.current_class)

                if "last_migration_dir" in self.classes:
                    self.last_migration_dir = self.classes["last_migration_dir"]
            else:
                self.classes = {}

            if "默认班级" not in self.classes:
                self.classes["默认班级"] = self.get_default_class_config()

        except Exception as e:
            self.logger.error(f"加载班级配置时出错: {str(e)}")
            self.classes = {"默认班级": self.get_default_class_config()}

    def get_default_class_config(self):
        """获取默认班级配置"""
        return {
            "students": [],
            "root_directory": "",
            "file_extensions": [".py", ".txt", ".java", ".cpp", ".c", ".cs", ".js", ".html", ".css"],
            "check_mode": "hybrid",  # 默认改为混合模式
            "auto_refresh": False,
            "refresh_interval": 10,
            "similarity_threshold": 85,
            "attendance_folder": "",
            "migration_directory": ""
        }

    def save_all_classes(self, show_message=False):
        """保存所有班级配置"""
        try:
            self.classes["last_current_class"] = self.current_class
            self.classes["last_migration_dir"] = self.last_migration_dir

            with open("class_configs.json", "w", encoding="utf-8") as f:
                json.dump(self.classes, f, ensure_ascii=False, indent=2)

            if show_message:
                messagebox.showinfo("成功", "班级配置已保存")

            self.logger.info("班级配置已保存")
        except Exception as e:
            self.logger.error(f"保存班级配置时出错: {str(e)}")
            if show_message:
                messagebox.showerror("错误", f"保存班级配置时出错: {str(e)}")

    def load_current_class_data(self):
        """加载当前班级数据到界面"""
        try:
            if self.current_class in self.classes:
                config = self.classes[self.current_class]

                self.student_text.delete(1.0, tk.END)
                if config["students"]:
                    self.student_text.insert(tk.END, "\n".join(config["students"]))

                self.dir_var.set(config.get("root_directory", ""))
                self.file_extensions = config.get("file_extensions",
                                                  [".py", ".txt", ".java", ".cpp", ".c", ".cs", ".js", ".html", ".css"])
                self.check_mode = config.get("check_mode", "hybrid")  # 默认改为混合模式
                self.auto_refresh = config.get("auto_refresh", False)
                self.refresh_interval = config.get("refresh_interval", 10)

                self.attendance_folder = config.get("attendance_folder", "")
                self.attendance_dir_var.set(self.attendance_folder)

                self.last_migration_dir = config.get("migration_directory", "")

                self.similarity_threshold = config.get("similarity_threshold", 85)
                self.similarity_var.set(str(self.similarity_threshold))

                self.update_extensions()
                self.mode_var.set(self.check_mode)
                self.refresh_var.set(self.auto_refresh)
                self.interval_var.set(str(self.refresh_interval))
        except Exception as e:
            self.logger.error(f"加载当前班级数据出错: {str(e)}")

    def save_current_class(self, show_message=False):
        """保存当前班级配置"""
        try:
            self.save_students()

            if self.current_class in self.classes:
                self.update_similarity_threshold()

                self.attendance_folder = self.attendance_dir_var.get()

                self.classes[self.current_class].update({
                    "root_directory": self.dir_var.get(),
                    "file_extensions": self.file_extensions,
                    "check_mode": self.check_mode,
                    "auto_refresh": self.auto_refresh,
                    "refresh_interval": self.refresh_interval,
                    "similarity_threshold": self.similarity_threshold,
                    "attendance_folder": self.attendance_folder,
                    "migration_directory": self.last_migration_dir
                })
                self.save_all_classes(show_message=show_message)

                if show_message:
                    messagebox.showinfo("成功", "班级配置已保存")
        except Exception as e:
            self.logger.error(f"保存当前班级配置出错: {str(e)}")
            if show_message:
                messagebox.showerror("错误", f"保存班级配置时出错: {str(e)}")

    def on_class_changed(self, event=None):
        """切换班级时的处理"""
        try:
            new_class = self.class_var.get()
            if new_class != self.current_class and new_class in self.classes:
                self.save_current_class(show_message=False)
                self.current_class = new_class
                self.load_current_class_data()
                self.clear_results()
        except Exception as e:
            self.logger.error(f"切换班级时出错: {str(e)}")

    def create_new_class(self):
        """创建新班级"""

        def save_new_class():
            try:
                class_name = name_entry.get().strip()
                if not class_name:
                    messagebox.showerror("错误", "班级名称不能为空")
                    return

                if class_name in self.classes:
                    messagebox.showerror("错误", "班级名称已存在")
                    return

                self.classes[class_name] = self.get_default_class_config()
                self.save_all_classes(show_message=False)

                self.class_combo['values'] = list(self.classes.keys())
                self.class_var.set(class_name)
                self.on_class_changed()

                new_class_dialog.destroy()
            except Exception as e:
                self.logger.error(f"创建新班级出错: {str(e)}")

        try:
            new_class_dialog = tk.Toplevel(self.root)
            new_class_dialog.title("新建班级")
            new_class_dialog.geometry("300x120")
            new_class_dialog.resizable(False, False)

            # 直接居中显示，不使用动画
            new_class_dialog.withdraw()
            self.center_dialog(new_class_dialog, 300, 120)
            new_class_dialog.deiconify()

            ttk.Label(new_class_dialog, text="请输入班级名称:").pack(pady=10)
            name_entry = ttk.Entry(new_class_dialog, width=20)
            name_entry.pack(pady=5)
            name_entry.focus()

            button_frame = ttk.Frame(new_class_dialog)
            button_frame.pack(pady=10)

            # 使用tk.Button并设置合适的宽度和高度
            tk.Button(button_frame, text="确定", command=save_new_class,
                      font=("Arial", 9), width=10, height=1).pack(side=tk.LEFT, padx=10)
            tk.Button(button_frame, text="取消", command=new_class_dialog.destroy,
                      font=("Arial", 9), width=10, height=1).pack(side=tk.LEFT, padx=10)

            new_class_dialog.transient(self.root)
            new_class_dialog.grab_set()
            self.root.wait_window(new_class_dialog)
        except Exception as e:
            self.logger.error(f"创建新班级对话框出错: {str(e)}")

    def delete_class(self):
        """删除当前班级"""
        try:
            if self.current_class == "默认班级":
                messagebox.showerror("错误", "不能删除默认班级")
                return

            if messagebox.askyesno("确认删除", f"确定要删除班级 '{self.current_class}' 吗？"):
                del self.classes[self.current_class]
                self.save_all_classes(show_message=False)

                self.current_class = "默认班级"
                self.class_var.set(self.current_class)
                self.class_combo['values'] = list(self.classes.keys())
                self.load_current_class_data()
        except Exception as e:
            self.logger.error(f"删除班级出错: {str(e)}")

    def export_class_config(self):
        """导出当前班级配置"""
        try:
            filename = filedialog.asksaveasfilename(
                title="导出班级配置",
                defaultextension=".json",
                filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
            )
            if filename:
                config = {
                    "class_name": self.current_class,
                    "config": self.classes[self.current_class]
                }
                with open(filename, "w", encoding="utf-8") as f:
                    json.dump(config, f, ensure_ascii=False, indent=2)
                messagebox.showinfo("成功", f"班级配置已导出到: {filename}")
                self.logger.info(f"班级配置已导出到: {filename}")
        except Exception as e:
            self.logger.error(f"导出配置时出错: {str(e)}")
            messagebox.showerror("错误", f"导出配置时出错: {str(e)}")

    def import_class_config(self):
        """导入班级配置"""
        try:
            filename = filedialog.askopenfilename(
                title="导入班级配置",
                filetypes=[("JSON files", "*.json"), ("All files", "*.*")]
            )
            if filename:
                with open(filename, "r", encoding="utf-8") as f:
                    config = json.load(f)

                class_name = config.get("class_name")
                class_config = config.get("config")

                if not class_name or not class_config:
                    messagebox.showerror("错误", "配置文件格式不正确")
                    return

                if class_name in self.classes:
                    if not messagebox.askyesno("确认覆盖", f"班级 '{class_name}' 已存在，是否覆盖？"):
                        return

                self.classes[class_name] = class_config
                self.save_all_classes(show_message=False)

                self.class_combo['values'] = list(self.classes.keys())
                messagebox.showinfo("成功", f"已导入班级配置: {class_name}")
                self.logger.info(f"已导入班级配置: {class_name}")

        except Exception as e:
            self.logger.error(f"导入配置时出错: {str(e)}")
            messagebox.showerror("错误", f"导入配置时出错: {str(e)}")

    def import_students_from_file(self):
        """从文件导入学生名单"""
        try:
            filename = filedialog.askopenfilename(
                title="选择学生名单文件",
                filetypes=[("Text files", "*.txt"), ("All files", "*.*")]
            )
            if filename:
                with open(filename, "r", encoding="utf-8") as f:
                    content = f.read().strip()

                students = [name.strip() for name in content.split("\n") if name.strip()]

                if students:
                    self.student_text.delete(1.0, tk.END)
                    self.student_text.insert(tk.END, "\n".join(students))
                    messagebox.showinfo("成功", f"已导入 {len(students)} 个学生")
                    self.logger.info(f"已导入 {len(students)} 个学生")
                else:
                    messagebox.showwarning("警告", "文件中没有找到有效的学生名单")
                    self.logger.warning("导入的学生名单文件中没有找到有效学生")

        except Exception as e:
            self.logger.error(f"导入学生名单时出错: {str(e)}")
            messagebox.showerror("错误", f"导入学生名单时出错: {str(e)}")

    def browse_attendance_directory(self):
        """浏览考勤文件夹"""
        try:
            initial_dir = self.attendance_dir_var.get()
            if not initial_dir or not os.path.exists(initial_dir):
                initial_dir = os.getcwd()

            directory = filedialog.askdirectory(initialdir=initial_dir)
            if directory:
                self.attendance_dir_var.set(directory)
                self.attendance_folder = directory
                if self.current_class in self.classes:
                    self.classes[self.current_class]["attendance_folder"] = directory
                    self.save_all_classes(show_message=False)
        except Exception as e:
            self.logger.error(f"浏览考勤文件夹出错: {str(e)}")

    def extract_names_from_text(self, text):
        """从文本中提取中文姓名"""
        try:
            chinese_names = re.findall(r'[\u4e00-\u9fa5]{2,4}', text)
            return chinese_names
        except Exception as e:
            self.logger.error(f"提取中文姓名出错: {str(e)}")
            return []

    def fuzzy_match_student(self, attendance_text, system_students):
        """模糊匹配学生姓名"""
        try:
            extracted_names = self.extract_names_from_text(attendance_text)

            if not extracted_names:
                return None

            best_match = None
            best_score = 0

            for extracted_name in extracted_names:
                for system_student in system_students:
                    clean_system_student = re.sub(r'^\d+[\s\-_]*', '', system_student)

                    score = difflib.SequenceMatcher(None, extracted_name, clean_system_student).ratio()

                    if extracted_name == clean_system_student:
                        return system_student

                    if clean_system_student in extracted_name or extracted_name in clean_system_student:
                        score += 0.3

                    system_numbers = re.findall(r'\d+', system_student)
                    extracted_numbers = re.findall(r'\d+', attendance_text)
                    if system_numbers and extracted_numbers and system_numbers[0] == extracted_numbers[0]:
                        score += 0.2

                    if score > best_score:
                        best_score = score
                        best_match = system_student

            if best_score > 0.6:
                return best_match

            return None
        except Exception as e:
            self.logger.error(f"模糊匹配学生姓名出错: {str(e)}")
            return None

    def check_attendance(self):
        """考勤统计功能 - 修复版：合并15分钟内的时间相近文件"""
        try:
            attendance_folder = self.attendance_dir_var.get()
            if not attendance_folder or not os.path.exists(attendance_folder):
                messagebox.showerror("错误", "请先选择有效的考勤文件夹")
                return

            # 获取所有txt文件及其修改时间
            txt_files = []
            for file in os.listdir(attendance_folder):
                if file.lower().endswith('.txt'):
                    file_path = os.path.join(attendance_folder, file)
                    if os.path.isfile(file_path):
                        try:
                            mtime = os.path.getmtime(file_path)
                            txt_files.append((file_path, mtime, datetime.fromtimestamp(mtime)))
                        except Exception as e:
                            self.logger.warning(f"获取文件 {file} 的修改时间失败: {str(e)}")
                            continue

            if not txt_files:
                messagebox.showerror("错误", "考勤文件夹中没有找到txt文件")
                return

            # 按修改时间从新到旧排序
            txt_files.sort(key=lambda x: x[1], reverse=True)

            # 获取最新文件的时间
            latest_time = txt_files[0][2]  # 最新文件的修改时间

            # 收集15分钟内的文件
            recent_files = []
            for file_path, mtime, file_time in txt_files:
                time_diff = latest_time - file_time
                if time_diff.total_seconds() <= 900:  # 15分钟 = 900秒
                    recent_files.append((file_path, file_time))

            # 读取所有最近文件的考勤内容
            all_attendance_lines = []
            file_info = []

            for file_path, file_time in recent_files:
                try:
                    with open(file_path, 'r', encoding='utf-8') as f:
                        file_lines = [line.strip() for line in f.readlines() if line.strip()]

                    if file_lines:
                        all_attendance_lines.extend(file_lines)
                        file_info.append(f"{os.path.basename(file_path)} ({file_time.strftime('%H:%M:%S')})")
                except Exception as e:
                    self.logger.error(f"读取考勤文件 {file_path} 出错: {str(e)}")

            if not all_attendance_lines:
                messagebox.showerror("错误", "考勤文件为空")
                return

            system_students = self.classes[self.current_class]["students"]

            if not system_students:
                messagebox.showerror("错误", "系统学生名单为空，请先录入学生名单")
                return

            attended = []
            matched_attendance = []
            not_attended = []

            for attendance_line in all_attendance_lines:
                matched_student = self.fuzzy_match_student(attendance_line, system_students)

                if matched_student and matched_student not in matched_attendance:
                    matched_attendance.append(matched_student)

            matched_attendance = list(set(matched_attendance))

            for system_student in system_students:
                if system_student in matched_attendance:
                    attended.append(system_student)
                else:
                    not_attended.append(system_student)

            # 显示考勤结果，包含使用的文件信息
            self.show_attendance_result(all_attendance_lines, attended, not_attended, file_info)

        except Exception as e:
            self.logger.error(f"考勤统计出错: {str(e)}")
            messagebox.showerror("错误", f"读取考勤文件时出错: {str(e)}")

    def show_attendance_result(self, attendance_lines, attended, not_attended, file_info):
        """显示考勤结果 - 优化版：缺勤名单一行多个，自动换行"""
        try:
            result_dialog = tk.Toplevel(self.root)
            result_dialog.title(f"{self.current_class}考勤统计结果")  # 修改标题包含班级名称
            result_dialog.geometry("700x500")
            result_dialog.resizable(True, True)

            # 直接居中显示，不使用动画
            result_dialog.withdraw()
            self.center_dialog(result_dialog, 700, 500)
            result_dialog.deiconify()

            # 创建主框架
            main_frame = ttk.Frame(result_dialog)
            main_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=20)

            # 标题和文件信息
            title_frame = ttk.Frame(main_frame)
            title_frame.pack(fill=tk.X, pady=10)

            ttk.Label(title_frame, text=f"{self.current_class}考勤统计结果",
                      font=("Arial", 14, "bold")).pack()  # 修改标题包含班级名称

            # 显示使用的文件信息
            if file_info:
                files_text = "使用的考勤文件: "
                files_text += "、".join(file_info)
                files_label = ttk.Label(title_frame, text=files_text, font=("Arial", 9), foreground="blue",
                                        wraplength=650)
                files_label.pack(pady=5)

            # 统计信息
            stats_frame = ttk.Frame(main_frame)
            stats_frame.pack(fill=tk.X, pady=10)

            system_total = len(self.classes[self.current_class]['students'])
            attendance_total = len(attendance_lines)
            attended_count = len(attended)
            not_attended_count = len(not_attended)

            stats_text = f"系统名单人数: {system_total}人  |  "
            stats_text += f"考勤名单行数: {attendance_total}行  |  "
            stats_text += f"已到人数: {attended_count}人  |  "
            stats_text += f"缺勤人数: {not_attended_count}人"
            if system_total > 0:
                stats_text += f"  |  出勤率: {attended_count / system_total * 100:.1f}%"
            ttk.Label(stats_frame, text=stats_text, font=("Arial", 11)).pack()

            # 创建记事本风格的文本区域
            text_frame = ttk.Frame(main_frame)
            text_frame.pack(fill=tk.BOTH, expand=True, pady=10)

            # 创建文本控件
            text_widget = tk.Text(text_frame, wrap=tk.WORD, font=("Arial", 10))
            text_widget.pack(fill=tk.BOTH, expand=True, side=tk.LEFT)

            # 添加滚动条
            scrollbar = ttk.Scrollbar(text_widget)
            scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
            text_widget.config(yscrollcommand=scrollbar.set)
            scrollbar.config(command=text_widget.yview)

            # 写入考勤结果
            text_widget.insert(tk.END, "=" * 80 + "\n")
            text_widget.insert(tk.END, f"{self.current_class}考勤统计结果\n")  # 修改标题包含班级名称
            text_widget.insert(tk.END, "=" * 80 + "\n\n")

            # 已到名单
            if attended:
                text_widget.insert(tk.END, f"【已到名单】({attended_count}人)\n")
                text_widget.insert(tk.END, "-" * 40 + "\n")

                # 一行显示多个学生，自动换行
                line = ""
                for i, student in enumerate(attended, 1):
                    student_entry = f"{i:2d}.{student}  "
                    if len(line) + len(student_entry) > 80:  # 大约80字符换行
                        text_widget.insert(tk.END, line + "\n")
                        line = student_entry
                    else:
                        line += student_entry

                if line:  # 写入最后一行
                    text_widget.insert(tk.END, line + "\n")

                text_widget.insert(tk.END, "\n")

            # 缺勤名单
            if not_attended:
                text_widget.insert(tk.END, f"【缺勤名单】({not_attended_count}人)\n")
                text_widget.insert(tk.END, "-" * 40 + "\n")

                # 一行显示多个学生，自动换行
                line = ""
                for i, student in enumerate(not_attended, 1):
                    student_entry = f"{i:2d}.{student}  "
                    if len(line) + len(student_entry) > 80:  # 大约80字符换行
                        text_widget.insert(tk.END, line + "\n")
                        line = student_entry
                    else:
                        line += student_entry

                if line:  # 写入最后一行
                    text_widget.insert(tk.END, line + "\n")

                text_widget.insert(tk.END, "\n")

            # 设置文本为只读
            text_widget.config(state=tk.DISABLED)

            # 按钮区域
            btn_frame = ttk.Frame(main_frame)
            btn_frame.pack(pady=10)

            ttk.Button(btn_frame, text="关闭", command=result_dialog.destroy).pack()

            result_dialog.transient(self.root)
            result_dialog.grab_set()
        except Exception as e:
            self.logger.error(f"显示考勤结果出错: {str(e)}")

    def migrate_homework(self):
        """作业迁移功能"""

        def perform_migration():
            try:
                target_dir = target_entry.get().strip()
                if not target_dir:
                    messagebox.showerror("错误", "请选择目标目录")
                    return

                if not os.path.exists(target_dir):
                    try:
                        os.makedirs(target_dir)
                    except Exception as e:
                        messagebox.showerror("错误", f"创建目标目录失败: {str(e)}")
                        return

                source_dir = self.dir_var.get()
                if not source_dir or not os.path.exists(source_dir):
                    messagebox.showerror("错误", "源目录不存在，请先设置正确的作业根目录")
                    return

                students = [name.strip() for name in self.student_text.get(1.0, tk.END).strip().split("\n") if
                            name.strip()]

                if not students:
                    messagebox.showerror("错误", "没有学生名单")
                    return

                self.last_migration_dir = target_dir
                if self.current_class in self.classes:
                    self.classes[self.current_class]["migration_directory"] = target_dir
                    self.save_all_classes(show_message=False)

                class_folder = os.path.join(target_dir, self.current_class)
                if not os.path.exists(class_folder):
                    os.makedirs(class_folder)

                timestamp = datetime.now().strftime("%Y年%m月%d日%H时")
                timestamp_folder = os.path.join(class_folder, timestamp)
                if not os.path.exists(timestamp_folder):
                    os.makedirs(timestamp_folder)

                migration_dialog.destroy()
                self._do_migration(source_dir, timestamp_folder, students)
            except Exception as e:
                self.logger.error(f"执行迁移出错: {str(e)}")

        try:
            migration_dialog = tk.Toplevel(self.root)
            migration_dialog.title("作业迁移")
            migration_dialog.geometry("550x250")
            migration_dialog.resizable(False, False)

            # 直接居中显示，不使用动画
            migration_dialog.withdraw()
            self.center_dialog(migration_dialog, 550, 250)
            migration_dialog.deiconify()

            ttk.Label(migration_dialog, text="作业迁移功能", font=("Arial", 12, "bold")).pack(pady=10)
            ttk.Label(migration_dialog, text="将当前班级的作业文件复制到指定目录").pack(pady=5)

            class_frame = ttk.Frame(migration_dialog)
            class_frame.pack(fill=tk.X, pady=5, padx=20)
            ttk.Label(class_frame, text=f"当前班级: {self.current_class}", font=("Arial", 10, "bold")).pack()

            dir_frame = ttk.Frame(migration_dialog)
            dir_frame.pack(fill=tk.X, pady=10, padx=20)

            ttk.Label(dir_frame, text="目标目录:").pack(side=tk.LEFT)
            target_var = tk.StringVar()

            if self.last_migration_dir and os.path.exists(self.last_migration_dir):
                target_var.set(self.last_migration_dir)

            target_entry = ttk.Entry(dir_frame, textvariable=target_var, width=40)
            target_entry.pack(side=tk.LEFT, padx=5)

            default_dir = self.last_migration_dir if self.last_migration_dir else self.dir_var.get()
            if not default_dir or not os.path.exists(default_dir):
                default_dir = os.getcwd()

            ttk.Button(dir_frame, text="浏览",
                       command=lambda: target_var.set(filedialog.askdirectory(initialdir=default_dir))).pack(
                side=tk.LEFT)

            info_frame = ttk.Frame(migration_dialog)
            info_frame.pack(fill=tk.X, pady=5, padx=20)

            info_text = f"迁移将创建文件夹: {self.current_class}/年-月-日-时"
            ttk.Label(info_frame, text=info_text, font=("Arial", 9), foreground="blue").pack()

            button_frame = ttk.Frame(migration_dialog)
            button_frame.pack(pady=20)

            ttk.Button(button_frame, text="开始迁移", command=perform_migration).pack(side=tk.LEFT, padx=10)
            ttk.Button(button_frame, text="取消", command=migration_dialog.destroy).pack(side=tk.LEFT, padx=10)

            migration_dialog.transient(self.root)
            migration_dialog.grab_set()
            self.root.wait_window(migration_dialog)
        except Exception as e:
            self.logger.error(f"创建迁移对话框出错: {str(e)}")

    def _do_migration(self, source_dir, target_dir, students):
        """执行作业迁移"""
        migrated_count = 0
        error_count = 0

        try:
            progress_dialog = tk.Toplevel(self.root)
            progress_dialog.title("作业迁移中...")
            progress_dialog.geometry("400x150")
            progress_dialog.resizable(False, False)

            # 直接居中显示，不使用动画
            progress_dialog.withdraw()
            self.center_dialog(progress_dialog, 400, 150)
            progress_dialog.deiconify()

            ttk.Label(progress_dialog, text="正在迁移作业，请稍候...", font=("Arial", 11)).pack(pady=20)

            progress_var = tk.DoubleVar()
            progress_bar = ttk.Progressbar(progress_dialog, variable=progress_var, maximum=len(students))
            progress_bar.pack(fill=tk.X, padx=20, pady=10)

            status_label = ttk.Label(progress_dialog, text="准备开始...")
            status_label.pack(pady=10)

            progress_dialog.update()

            for idx, student in enumerate(students):
                try:
                    status_label.config(text=f"正在迁移 {student} 的作业...")
                    progress_var.set(idx + 1)
                    progress_dialog.update()

                    if self.check_mode == "folder" or self.check_mode == "hybrid":
                        student_folder = self.find_student_folder(source_dir, student)
                        self.logger.info(f"查找学生 {student} 的文件夹: {student_folder}")

                        if student_folder and os.path.isdir(student_folder):
                            target_student_dir = os.path.join(target_dir, student)

                            if os.path.exists(target_student_dir):
                                shutil.rmtree(target_student_dir)

                            self.logger.info(f"复制文件夹: {student_folder} -> {target_student_dir}")
                            shutil.copytree(student_folder, target_student_dir)
                            migrated_count += 1
                            self.logger.info(f"学生 {student} 的作业迁移成功")
                        else:
                            self.logger.warning(f"未找到学生 {student} 的文件夹")

                    if self.check_mode == "file" or (self.check_mode == "hybrid" and not student_folder):
                        found_files = self.find_student_files_recursive(source_dir, student)
                        self.logger.info(f"查找学生 {student} 的文件: 找到 {len(found_files)} 个文件")

                        if found_files:
                            target_student_dir = os.path.join(target_dir, student)
                            if not os.path.exists(target_student_dir):
                                os.makedirs(target_student_dir)

                            for file_name, file_path in found_files:
                                clean_file_name = file_name
                                if student in file_name:
                                    clean_file_name = re.sub(r'.*' + re.escape(student) + r'[_\-\s]*', '', file_name)
                                    if not clean_file_name or clean_file_name == file_name:
                                        clean_file_name = file_name

                                target_file = os.path.join(target_student_dir, clean_file_name)
                                self.logger.info(f"复制文件: {file_path} -> {target_file}")
                                shutil.copy2(file_path, target_file)

                            if self.check_mode != "hybrid" or not student_folder:
                                migrated_count += 1
                                self.logger.info(f"学生 {student} 的作业迁移成功")
                        else:
                            self.logger.warning(f"未找到学生 {student} 的文件")

                except Exception as e:
                    error_count += 1
                    self.logger.error(f"迁移学生 {student} 的作业时出错: {str(e)}")

            progress_dialog.destroy()

            if os.path.exists(target_dir):
                migrated_folders = os.listdir(target_dir)
                self.logger.info(f"迁移完成，目标目录 {target_dir} 中的文件夹: {migrated_folders}")

            messagebox.showinfo("迁移完成",
                                f"作业迁移完成！\n\n"
                                f"目标文件夹: {target_dir}\n"
                                f"成功迁移: {migrated_count} 个学生\n"
                                f"失败: {error_count} 个")
            self.logger.info(f"作业迁移完成: 成功 {migrated_count} 个，失败 {error_count} 个")

        except Exception as e:
            self.logger.error(f"迁移过程中出错: {str(e)}")
            messagebox.showerror("迁移错误", f"迁移过程中出错: {str(e)}")

    def update_extensions(self):
        """更新扩展名显示 - 修复版：确保添加按钮不会被移除"""
        # 移除扩展名框架内的旧控件
        for widget in self.ext_frame_inner.winfo_children():
            widget.destroy()

        # 确保扩展名显示框架存在
        if not hasattr(self, 'ext_frame_inner'):
            return

        # 添加扩展名标签和删除按钮
        for i, ext in enumerate(self.file_extensions):
            ext_frame = ttk.Frame(self.ext_frame_inner)
            ext_frame.pack(side=tk.LEFT, padx=2)

            ttk.Label(ext_frame, text=ext).pack(side=tk.LEFT)
            # 删除按钮使用tk.Button确保字体显示
            tk.Button(ext_frame, text="×", width=2, font=("Arial", 8),
                      command=lambda e=ext: self.remove_extension(e)).pack(side=tk.LEFT, padx=2)

    def add_extension(self):
        """添加文件扩展名"""

        def save_ext():
            try:
                ext = ext_entry.get().strip()
                if ext and not ext.startswith("."):
                    ext = "." + ext
                if ext and ext not in self.file_extensions:
                    self.file_extensions.append(ext)
                    self.update_extensions()
                    ext_dialog.destroy()
            except Exception as e:
                self.logger.error(f"添加文件扩展名出错: {str(e)}")

        try:
            ext_dialog = tk.Toplevel(self.root)
            ext_dialog.title("添加文件扩展名")
            ext_dialog.geometry("300x130")  # 增加高度以容纳更大的按钮
            ext_dialog.resizable(False, False)

            # 直接居中显示，不使用动画
            ext_dialog.withdraw()
            self.center_dialog(ext_dialog, 300, 130)
            ext_dialog.deiconify()

            ttk.Label(ext_dialog, text="请输入文件扩展名:").pack(pady=15)  # 增加上边距
            ext_entry = ttk.Entry(ext_dialog, width=20)
            ext_entry.pack(pady=5)
            ext_entry.focus()

            button_frame = ttk.Frame(ext_dialog)
            button_frame.pack(pady=15)  # 增加按钮上下的间距

            # 修复：使用tk.Button并设置合适的宽度和高度（与其他按钮一致）
            tk.Button(button_frame, text="确定", command=save_ext,
                      font=("Arial", 10), width=10, height=2).pack(side=tk.LEFT, padx=10)  # 增加高度为2
            tk.Button(button_frame, text="取消", command=ext_dialog.destroy,
                      font=("Arial", 10), width=10, height=2).pack(side=tk.LEFT, padx=10)  # 增加高度为2

            ext_dialog.transient(self.root)
            ext_dialog.grab_set()
            self.root.wait_window(ext_dialog)
        except Exception as e:
            self.logger.error(f"创建扩展名对话框出错: {str(e)}")

    def remove_extension(self, ext):
        """移除文件扩展名"""
        try:
            self.file_extensions.remove(ext)
            self.update_extensions()
        except Exception as e:
            self.logger.error(f"移除文件扩展名出错: {str(e)}")

    def update_mode(self):
        """更新检查模式"""
        try:
            self.check_mode = self.mode_var.get()
        except Exception as e:
            self.logger.error(f"更新检查模式出错: {str(e)}")

    def toggle_auto_refresh(self):
        """切换自动刷新"""
        try:
            self.auto_refresh = self.refresh_var.get()
            if self.auto_refresh:
                self.start_auto_refresh()
            else:
                self.stop_auto_refresh()
        except Exception as e:
            self.logger.error(f"切换自动刷新出错: {str(e)}")

    def update_refresh_interval(self):
        """更新刷新间隔"""
        try:
            new_interval = int(self.interval_var.get())
            if 5 <= new_interval <= 300:
                self.refresh_interval = new_interval
            else:
                self.refresh_interval = 10
                self.interval_var.set("10")
        except ValueError as e:
            self.logger.error(f"更新刷新间隔出错: {str(e)}")
            self.refresh_interval = 10
            self.interval_var.set("10")

    def start_auto_refresh(self):
        """开始自动刷新"""
        try:
            if self.auto_refresh and not self.refresh_thread:
                self.stop_refresh = False
                self.refresh_thread = threading.Thread(target=self.auto_refresh_worker, daemon=True)
                self.refresh_thread.start()
        except Exception as e:
            self.logger.error(f"开始自动刷新出错: {str(e)}")

    def stop_auto_refresh(self):
        """停止自动刷新"""
        try:
            self.stop_refresh = True
            self.refresh_thread = None
        except Exception as e:
            self.logger.error(f"停止自动刷新出错: {str(e)}")

    def auto_refresh_worker(self):
        """自动刷新工作线程"""
        try:
            while self.auto_refresh and not self.stop_refresh:
                time.sleep(self.refresh_interval)
                if self.auto_refresh and not self.stop_refresh:
                    self.root.after(0, self.auto_check_homework)
        except Exception as e:
            self.logger.error(f"自动刷新工作线程出错: {str(e)}")

    def auto_check_homework(self):
        """自动检查作业"""
        try:
            if not self.dir_var.get() or not os.path.exists(self.dir_var.get()):
                return
            if not self.classes[self.current_class]["students"]:
                return

            self.update_similarity_threshold()

            threading.Thread(target=self._background_check, daemon=True).start()
        except Exception as e:
            self.logger.error(f"自动检查作业出错: {str(e)}")

    def _background_check(self):
        """后台检查"""
        try:
            if self.check_mode == "folder":
                self.check_folder_mode(background=True)
            elif self.check_mode == "file":
                self.check_file_mode(background=True)
            elif self.check_mode == "hybrid":
                self.check_hybrid_mode(background=True)
        except Exception as e:
            self.logger.error(f"后台检查出错: {str(e)}")

    def browse_directory(self):
        """浏览目录"""
        try:
            current_dir = self.dir_var.get()

            if not current_dir or not os.path.exists(current_dir):
                base_dir = os.getcwd()
                dirs = []
                for item in os.listdir(base_dir):
                    item_path = os.path.join(base_dir, item)
                    if os.path.isdir(item_path):
                        dirs.append((item_path, os.path.getmtime(item_path)))

                if dirs:
                    dirs.sort(key=lambda x: x[1], reverse=True)
                    current_dir = dirs[0][0]
                else:
                    current_dir = base_dir

            directory = filedialog.askdirectory(initialdir=current_dir)
            if directory:
                self.dir_var.set(directory)
        except Exception as e:
            self.logger.error(f"浏览目录出错: {str(e)}")

    def save_students(self):
        """保存学生名单"""
        try:
            text = self.student_text.get(1.0, tk.END).strip()
            students = [name.strip() for name in text.split("\n") if name.strip()]

            if self.current_class in self.classes:
                self.classes[self.current_class]["students"] = students
                self.save_all_classes(show_message=False)

            self.logger.info(f"已保存 {len(students)} 个学生名单")
        except Exception as e:
            self.logger.error(f"保存学生名单出错: {str(e)}")

    def clear_students(self):
        """清空学生名单"""
        try:
            self.student_text.delete(1.0, tk.END)
            if self.current_class in self.classes:
                self.classes[self.current_class]["students"] = []
            self.logger.info("已清空学生名单")
        except Exception as e:
            self.logger.error(f"清空学生名单出错: {str(e)}")

    def check_homework(self):
        """检查作业"""
        try:
            if self.ui_locked:
                messagebox.showwarning("警告", "正在检查中，请稍候...")
                return

            if self.is_checking:
                messagebox.showwarning("警告", "正在检查中，请稍候...")
                return

            if not self.dir_var.get() or not os.path.exists(self.dir_var.get()):
                messagebox.showerror("错误", "请先选择有效的作业根目录")
                return

            if not self.classes[self.current_class]["students"]:
                messagebox.showerror("错误", "请先输入学生名单")
                return

            self.update_similarity_threshold()

            self.lock_ui()
            self.is_checking = True

            self.clear_results()

            threading.Thread(target=self._perform_check, daemon=True).start()

        except Exception as e:
            self.logger.error(f"检查作业出错: {str(e)}")
            self.unlock_ui()
            self.is_checking = False

    def _perform_check(self):
        """执行检查"""
        try:
            submitted_count = 0

            try:
                if self.check_mode == "folder":
                    submitted_count = self.check_folder_mode()
                elif self.check_mode == "file":
                    submitted_count = self.check_file_mode()
                elif self.check_mode == "hybrid":
                    submitted_count = self.check_hybrid_mode()
            except Exception as e:
                self.logger.error(f"检查过程中出错: {str(e)}")
                messagebox.showerror("检查错误", f"检查过程中出错: {str(e)}")
            finally:
                self.root.after(0, lambda: self.update_stats(submitted_count))

                current_time = datetime.now().strftime("%Y-%m-d %H:%M:%S")
                self.timestamp_label.config(text=f"最后检查: {current_time}")

                self.root.after(0, self.unlock_ui)
                self.is_checking = False

        except Exception as e:
            self.logger.error(f"执行检查出错: {str(e)}")
            self.root.after(0, self.unlock_ui)
            self.is_checking = False

    def clear_results(self):
        """清空结果"""
        try:
            for item in self.result_tree.get_children():
                self.result_tree.delete(item)
            self.student_files_data.clear()
            self.all_similarity_results.clear()
            self.file_content_cache.clear()
            self.file_hash_cache.clear()
        except Exception as e:
            self.logger.error(f"清空结果出错: {str(e)}")

    def update_stats(self, submitted_count):
        """更新统计信息"""
        try:
            students = self.classes[self.current_class]["students"]
            total_count = len(students)
            not_submitted_count = total_count - submitted_count

            self.stats_label.config(
                text=f"总计: {total_count}人 | 已提交: {submitted_count}人 | 未提交: {not_submitted_count}人"
            )
        except Exception as e:
            self.logger.error(f"更新统计信息出错: {str(e)}")

    def find_files_in_folder_recursive(self, folder_path, max_depth=5):
        """递归查找文件夹内的所有文件"""
        found_files = []

        def search_in_dir(current_dir, current_depth):
            if current_depth > max_depth:
                return

            try:
                for item in os.listdir(current_dir):
                    item_path = os.path.join(current_dir, item)

                    if os.path.isdir(item_path):
                        if not item.startswith('.') and item not in ['__pycache__', 'node_modules', 'venv', '.git',
                                                                     '.idea']:
                            search_in_dir(item_path, current_depth + 1)

                    elif os.path.isfile(item_path):
                        if any(item.lower().endswith(ext.lower()) for ext in self.file_extensions):
                            found_files.append(item_path)
            except (PermissionError, OSError) as e:
                self.logger.warning(f"无法访问目录 {current_dir}: {str(e)}")
            except Exception as e:
                self.logger.error(f"搜索目录时出错: {str(e)}")

        try:
            search_in_dir(folder_path, 1)
        except Exception as e:
            self.logger.error(f"递归查找文件夹文件出错: {str(e)}")

        return found_files

    def check_folder_mode(self, background=False):
        """文件夹模式检查"""
        try:
            submitted_count = 0
            students = self.classes[self.current_class]["students"]
            root_dir = self.dir_var.get()

            # 清空数据
            self.student_files_data.clear()
            self.all_similarity_results.clear()

            for student in students:
                student_folder = self.find_student_folder(root_dir, student)

                if not student_folder or not os.path.isdir(student_folder):
                    self.add_result_item(
                        student=student,
                        file_name="未提交",
                        status="未提交",
                        similarity="0%",
                        details="未找到学生文件夹",
                        file_time="未知",
                        tag="not_submitted",
                        file_path=""
                    )
                    continue

                found_files = self.find_files_in_folder_recursive(student_folder)

                if found_files:
                    submitted_count += 1
                    self.student_files_data[student] = []

                    for file_path in found_files:
                        file_name = os.path.basename(file_path)
                        file_time = self.get_file_modification_time(file_path)

                        self.student_files_data[student].append({
                            'file_name': file_name,
                            'file_path': file_path,
                            'file_time': file_time
                        })

                        self.add_result_item(
                            student=student,
                            file_name=file_name,
                            status="已提交",
                            similarity="0%",
                            details=f"文件大小: {os.path.getsize(file_path)} 字节",
                            file_time=file_time,
                            tag="submitted",
                            file_path=file_path
                        )
                else:
                    self.add_result_item(
                        student=student,
                        file_name="无文件",
                        status="未提交",
                        similarity="0%",
                        details="文件夹中没有指定扩展名的文件",
                        file_time="未知",
                        tag="not_submitted",
                        file_path=""
                    )

            if self.student_files_data:
                self.logger.info(f"开始相似度检测，共有 {len(self.student_files_data)} 个学生提交了文件")
                self.all_similarity_results = self.check_similarity_all_files_optimized(self.student_files_data)

                # 更新相似度结果到界面
                self.update_all_similarity_results()

                # 默认按状态排序，再按相似度排序
                self.treeview_sort_column("状态")
            else:
                self.logger.info("没有学生提交文件，跳过相似度检测")
                # 如果没有提交文件，也按状态排序
                self.treeview_sort_column("状态")

            return submitted_count
        except Exception as e:
            self.logger.error(f"文件夹模式检查出错: {str(e)}")
            return 0

    def check_file_mode(self, background=False):
        """文件模式检查"""
        try:
            submitted_count = 0
            students = self.classes[self.current_class]["students"]
            root_dir = self.dir_var.get()

            # 清空数据
            self.student_files_data.clear()
            self.all_similarity_results.clear()

            for student in students:
                found_files_info = self.find_student_files_recursive(root_dir, student)

                if found_files_info:
                    submitted_count += 1
                    self.student_files_data[student] = []

                    for file_name, file_path in found_files_info:
                        file_time = self.get_file_modification_time(file_path)

                        self.student_files_data[student].append({
                            'file_name': file_name,
                            'file_path': file_path,
                            'file_time': file_time
                        })

                        self.add_result_item(
                            student=student,
                            file_name=file_name,
                            status="已提交",
                            similarity="0%",
                            details=f"文件大小: {os.path.getsize(file_path)} 字节",
                            file_time=file_time,
                            tag="submitted",
                            file_path=file_path
                        )
                else:
                    self.add_result_item(
                        student=student,
                        file_name="未提交",
                        status="未提交",
                        similarity="0%",
                        details="未找到学生文件",
                        file_time="未知",
                        tag="not_submitted",
                        file_path=""
                    )

            if self.student_files_data:
                self.logger.info(f"开始相似度检测，共有 {len(self.student_files_data)} 个学生提交了文件")
                self.all_similarity_results = self.check_similarity_all_files_optimized(self.student_files_data)

                # 更新相似度结果到界面
                self.update_all_similarity_results()

                # 默认按状态排序，再按相似度排序
                self.treeview_sort_column("状态")
            else:
                self.logger.info("没有学生提交文件，跳过相似度检测")
                # 如果没有提交文件，也按状态排序
                self.treeview_sort_column("状态")

            return submitted_count
        except Exception as e:
            self.logger.error(f"文件模式检查出错: {str(e)}")
            return 0

    def check_hybrid_mode(self, background=False):
        """混合模式检查 - 修复版：避免重复记录"""
        try:
            submitted_count = 0
            students = self.classes[self.current_class]["students"]
            root_dir = self.dir_var.get()

            # 清空数据
            self.student_files_data.clear()
            self.all_similarity_results.clear()

            for student in students:
                # 第一步：尝试查找学生文件夹
                student_folder = self.find_student_folder(root_dir, student)
                found_files = []
                file_paths_set = set()  # 用于去重

                # 如果有学生文件夹，优先查找文件夹内的文件
                if student_folder and os.path.isdir(student_folder):
                    folder_files = self.find_files_in_folder_recursive(student_folder)
                    for file_path in folder_files:
                        if file_path not in file_paths_set:  # 去重
                            found_files.append(file_path)
                            file_paths_set.add(file_path)

                # 如果没有在文件夹内找到文件，或者没有学生文件夹，则查找整个目录的文件
                if not found_files:
                    found_files_info = self.find_student_files_recursive(root_dir, student)
                    for file_name, file_path in found_files_info:
                        if file_path not in file_paths_set:  # 去重
                            found_files.append(file_path)
                            file_paths_set.add(file_path)
                else:
                    # 如果在文件夹内找到了文件，仍然需要检查整个目录是否有其他同名学生的文件
                    # 但为了避免重复，只添加不在已找到集合中的文件
                    found_files_info = self.find_student_files_recursive(root_dir, student)
                    for file_name, file_path in found_files_info:
                        if file_path not in file_paths_set:  # 去重
                            found_files.append(file_path)
                            file_paths_set.add(file_path)

                if found_files:
                    submitted_count += 1
                    self.student_files_data[student] = []

                    for file_path in found_files:
                        file_name = os.path.basename(file_path)
                        file_time = self.get_file_modification_time(file_path)

                        self.student_files_data[student].append({
                            'file_name': file_name,
                            'file_path': file_path,
                            'file_time': file_time
                        })

                        self.add_result_item(
                            student=student,
                            file_name=file_name,
                            status="已提交",
                            similarity="0%",
                            details=f"文件大小: {os.path.getsize(file_path)} 字节",
                            file_time=file_time,
                            tag="submitted",
                            file_path=file_path
                        )
                else:
                    self.add_result_item(
                        student=student,
                        file_name="未提交",
                        status="未提交",
                        similarity="0%",
                        details="未找到学生作业",
                        file_time="未知",
                        tag="not_submitted",
                        file_path=""
                    )

            if self.student_files_data:
                self.logger.info(f"开始相似度检测，共有 {len(self.student_files_data)} 个学生提交了文件")
                self.all_similarity_results = self.check_similarity_all_files_optimized(self.student_files_data)

                # 更新相似度结果到界面
                self.update_all_similarity_results()

                # 默认按状态排序，再按相似度排序
                self.treeview_sort_column("状态")
            else:
                self.logger.info("没有学生提交文件，跳过相似度检测")
                # 如果没有提交文件，也按状态排序
                self.treeview_sort_column("状态")

            return submitted_count
        except Exception as e:
            self.logger.error(f"混合模式检查出错: {str(e)}")
            return 0

    def add_result_item(self, student, file_name, status, similarity, details, file_time, tag, file_path):
        """添加结果项到Treeview"""
        try:
            self.result_tree.insert("", tk.END, values=(
                student,
                file_name,
                status,
                similarity,
                details,
                file_time,
                file_path
            ), tags=(tag,))
        except Exception as e:
            self.logger.error(f"添加结果项出错: {str(e)}")

    def update_all_similarity_results(self):
        """更新相似度结果到Treeview"""
        try:
            self.logger.info("开始更新相似度结果到界面")

            # 获取Treeview中的所有项目
            all_items = self.result_tree.get_children()
            if not all_items:
                self.logger.warning("Treeview中没有项目可更新")
                return

            # 记录更新统计
            updated_count = 0
            total_count = 0

            # 遍历所有Treeview项目
            for item_id in all_items:
                try:
                    values = self.result_tree.item(item_id, "values")
                    if not values or len(values) < 7:
                        continue

                    student = values[0]
                    file_name = values[1]
                    original_status = values[2]

                    total_count += 1

                    # 查找该文件的相似度信息
                    similarity_info = None
                    if student in self.all_similarity_results:
                        if file_name in self.all_similarity_results[student]:
                            similarity_info = self.all_similarity_results[student][file_name]

                    # 如果没有相似度信息，创建默认的
                    if similarity_info is None:
                        similarity_info = {
                            'similarity': 0.0,
                            'matches': []
                        }

                    similarity = similarity_info.get('similarity', 0.0)
                    matches = similarity_info.get('matches', [])

                    # 创建新的values列表
                    new_values = list(values)

                    # 更新相似度
                    new_values[3] = f"{similarity:.1f}%"

                    # 更新状态
                    if similarity >= self.similarity_threshold and matches:
                        new_values[2] = "疑似抄袭"
                        self.result_tree.item(item_id, tags=('suspected_plagiarism',))
                    elif original_status == "未提交":
                        new_values[2] = "未提交"
                        self.result_tree.item(item_id, tags=('not_submitted',))
                    else:
                        new_values[2] = "已提交"
                        self.result_tree.item(item_id, tags=('submitted',))

                    # 更新详细信息
                    if matches:
                        # 按相似度排序
                        try:
                            sorted_matches = sorted(
                                matches,
                                key=lambda x: float(re.search(r'(\d+\.?\d*)%', x).group(1)) if re.search(
                                    r'(\d+\.?\d*)%', x) else 0,
                                reverse=True
                            )

                            if len(sorted_matches) <= 3:
                                details_text = f"相似文件: {', '.join(sorted_matches)}"
                            else:
                                top_matches = sorted_matches[:3]
                                details_text = f"相似文件: {', '.join(top_matches)} 等{len(sorted_matches)}个"
                        except:
                            details_text = f"相似文件: {', '.join(matches[:3])}"

                        new_values[4] = details_text
                    else:
                        if similarity > 0:
                            new_values[4] = f"最高相似度: {similarity:.1f}%"
                        else:
                            new_values[4] = "无相似文件"

                    # 更新Treeview项目
                    self.result_tree.item(item_id, values=tuple(new_values))
                    updated_count += 1

                    # 每更新100个项目记录一次
                    if updated_count % 100 == 0:
                        self.logger.info(f"已更新 {updated_count}/{total_count} 个项目")

                except Exception as e:
                    self.logger.error(f"更新项目 {item_id} 时出错: {str(e)}")
                    continue

            self.logger.info(f"相似度结果更新完成: 总计 {total_count} 个项目，成功更新 {updated_count} 个")

            # 如果有未更新的项目，记录警告
            if updated_count < total_count:
                self.logger.warning(f"有 {total_count - updated_count} 个项目未能更新")

        except Exception as e:
            self.logger.error(f"更新相似度结果出错: {str(e)}")

    def center_dialog(self, dialog, width, height):
        """使对话框居中显示在父窗口上"""
        # 获取父窗口位置
        parent_x = self.root.winfo_x()
        parent_y = self.root.winfo_y()
        parent_width = self.root.winfo_width()
        parent_height = self.root.winfo_height()

        # 计算对话框位置
        x = parent_x + (parent_width - width) // 2
        y = parent_y + (parent_height - height) // 2

        # 确保对话框在屏幕内
        screen_width = self.root.winfo_screenwidth()
        screen_height = self.root.winfo_screenheight()

        x = max(0, min(x, screen_width - width))
        y = max(0, min(y, screen_height - height))

        # 直接设置位置，不使用动画
        dialog.geometry(f"{width}x{height}+{x}+{y}")

    def on_closing(self):
        """关闭程序时的处理"""
        if self.closing:
            return

        try:
            self.closing = True
            self.logger.info("系统正在关闭...")

            self.stop_auto_refresh()
            self.save_current_class(show_message=False)
            self.logger.info("系统关闭完成")
            self.root.destroy()
        except Exception as e:
            self.logger.error(f"关闭程序时出错: {str(e)}")
            self.root.destroy()


if __name__ == "__main__":
    try:
        root = tk.Tk()
        app = HomeworkCheckSystem(root)
        root.protocol("WM_DELETE_WINDOW", app.on_closing)
        root.mainloop()
    except Exception as e:
        import traceback

        error_msg = f"系统启动失败: {str(e)}\n{traceback.format_exc()}"
        print(error_msg)

        try:
            with open('log.txt', 'a', encoding='utf-8') as f:
                f.write(f"{datetime.now().strftime('%Y-%m-%d %H:%M:%S')} - 系统启动失败: {error_msg}\n")
        except:
            pass

        messagebox.showerror("系统错误", f"系统启动失败: {str(e)}")