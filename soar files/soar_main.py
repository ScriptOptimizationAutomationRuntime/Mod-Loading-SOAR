# =====================================================
# SOAR MAIN SYSTEM
# SOAR - Script Optimization and Automation Runtime
# Made by Philip Kluz
# Version 1.00.10 Early Beta 
# DO NOT EDIT CORE PARTS.
# =====================================================

from __future__ import annotations

import ast
import copy
import difflib
import traceback
import io
import json
import os
import platform
import random
import re
import queue
import shlex
import socket
import subprocess
import sys
import threading
import time
try:
    import psutil
except Exception:
    psutil = None
import webbrowser
from datetime import datetime
from pathlib import Path
from textwrap import dedent
from urllib.parse import quote_plus
import urllib.request
import ssl
try:
    import certifi
except Exception:
    certifi = None

pronoun = "sir" # you can change this to prefered pronoun.
_last_resource_alert = 0
RESOURCE_COOLDOWN = 10  #seconds
intro_start_time = 0 

IS_SPEAKING = False

intro_proc = None

try:
    import pyttsx3
except Exception:
    pyttsx3 = None

try:
    import speech_recognition as sr
except Exception:
    sr = None

try:
    import soar_autocode
except Exception:
    soar_autocode = None

try:
    import soar_avss
except Exception:
    soar_avss = None

try:
    import rsms  # type: ignore
except Exception:
    rsms = None

APP_NAME = "SOAR"
BASE_DIR = Path(__file__).resolve().parent
MAIN_SCRIPT = Path(__file__).resolve()
DATA_DIR = BASE_DIR / "soar_data"
PROJECTS_DIR = Path.home() / "SOAR" / "Projects"
SETTINGS_FILE = DATA_DIR / "settings.json"
NOTES_FILE = DATA_DIR / "notes.txt"
MEMORY_FILE = DATA_DIR / "memories.txt"
TODO_FILE = DATA_DIR / "todos.txt"
CHAT_LOG = DATA_DIR / "chat_log.txt"
MODS_DIR = BASE_DIR / "soar-mods"

GROQ_API_ENDPOINT = "https://api.groq.com/openai/v1/chat/completions"
GROQ_DEFAULT_MODEL = "openai/gpt-oss-20b"
GROQ_REQUEST_TIMEOUT = 25
GROQ_SYSTEM_PROMPT = (
    "You are SOAR, the Script Optimization and Automation Runtime. "
    "Answer naturally and concisely, be helpful and honest, and do not claim "
    "to have performed actions that SOAR did not actually perform. "
    "When the user asks for a local SOAR command, the command handler has already "
    "processed it; here you are handling ordinary conversation."
)
GROQ_FALLBACK_KEY = ""
_groq_last_error = ""
_groq_last_error_time = 0.0

BRAIN_MEMORY_FILE = DATA_DIR / "brain_memory.json"
BRAIN_KNOWLEDGE_FILE = DATA_DIR / "brain_knowledge.json"
BRAIN_LEARNING_FILE = DATA_DIR / "brain_learning.json"

BRAIN_DEFAULT_KNOWLEDGE = {
    "soar": {
        "name": "Script Optimization and Automation Runtime"
    },
    "python": {
        "type": "programming language"
    }
}

PROFILES_FILE = DATA_DIR / "profiles.json"
SCHEDULE_FILE = DATA_DIR / "scheduler.json"
ALIASES_FILE = DATA_DIR / "aliases.json"
WORKSPACES_FILE = DATA_DIR / "workspaces.json"
CLIPBOARD_HISTORY_FILE = DATA_DIR / "clipboard_history.json"
COMMAND_HISTORY_FILE = DATA_DIR / "command_history.txt"
EVENT_LOG_FILE = DATA_DIR / "events.log"

SOAR_SAFE_MODE = False
SOAR_ACTIVE_PROFILE = "default"
SOAR_MANUAL_DISABLED_MODULES = set()
SOAR_AUTO_LIGHTWEIGHT_ACTIVE = False
SOAR_AUTO_LIGHTWEIGHT_ENABLED = True
SOAR_AUTO_LIGHTWEIGHT_LOW_SINCE = None

MODULE_HEALTH = {
    "CORE": {"status": "healthy", "failures": 0, "last_error": "", "last_error_time": ""},
    "VOICE": {"status": "unknown", "failures": 0, "last_error": "", "last_error_time": ""},
    "AUTOCODE": {"status": "unknown", "failures": 0, "last_error": "", "last_error_time": ""},
    "AVSS": {"status": "unknown", "failures": 0, "last_error": "", "last_error_time": ""},
    "RSMS": {"status": "unknown", "failures": 0, "last_error": "", "last_error_time": ""},
    "CSRS": {"status": "unknown", "failures": 0, "last_error": "", "last_error_time": ""},
    "SCHEDULER": {"status": "unknown", "failures": 0, "last_error": "", "last_error_time": ""},
}

SCHEDULE_THREAD = None
SCHEDULE_STOP_EVENT = threading.Event()
EVENT_HANDLERS = {}
FEATURE_RUNTIME_READY = False
COMMAND_HISTORY_LIMIT = 500
CLIPBOARD_HISTORY_LIMIT = 20


for p in [DATA_DIR, PROJECTS_DIR, NOTES_FILE, MEMORY_FILE, TODO_FILE, CHAT_LOG, SETTINGS_FILE]:
    if p == DATA_DIR or p == PROJECTS_DIR:
        p.mkdir(parents=True, exist_ok=True)
    elif not p.exists():
        p.write_text("", encoding="utf-8")

STARTUP_TIME = datetime.now()

for brain_path, brain_default in (
    (BRAIN_MEMORY_FILE, {}),
    (BRAIN_KNOWLEDGE_FILE, BRAIN_DEFAULT_KNOWLEDGE),
    (BRAIN_LEARNING_FILE, {"aliases": {}, "responses": {}}),
):
    if not brain_path.exists():
        brain_path.write_text(
            json.dumps(brain_default, indent=2, ensure_ascii=False),
            encoding="utf-8"
        )

autocode_enabled = False
autocode_stop = threading.Event()

SOAR_RESOURCE_LIMITS = {
    "ram_bytes": None,
    "cpu_percent": None,
    "gpu_percent": None,
}

SOAR_RESOURCE_LIMITS_ACTIVE = False
RESOURCE_WATCHDOG_INTERVAL = 10.0

SOAR_LIGHTWEIGHT_MODE = False
SOAR_DISABLED_MODULES = set()
avss_stop_event = threading.Event()
resource_limit_lock = threading.Lock()

stop_event = threading.Event()
bot_lock = threading.Lock()

voice_pause = threading.Event()
voice_enabled = True
listener_stop = None
voice_state_lock = threading.Lock()

recognizer = None

tts_engine = None
tts_queue = queue.Queue()
tts_ready = threading.Event()
tts_thread = None

speech_cooldown_until = 0.0
speech_cooldown_lock = threading.Lock()

shutting_down = False

SETTINGS_LOCK = threading.Lock()
SETTINGS_CACHE = None

tts_voice_label = None
tts_voice_id = None

ssl_context = (
    ssl.create_default_context(cafile=certifi.where())
    if certifi is not None
    else ssl.create_default_context()
)

# ======================================================
# SPA (SOAR Project Agent) V 1.0
# SOAR Help Module #005
# Made by Philip Kluz 2026 Jul 19 Late
# "eS p eY e"
# ======================================================

class ProjectAgent:
    """
    SOAR Advanced Autonomous Project Builder Agent
    Features: Dynamic project routing, intelligent scaffolding, multi-file AST validation, 
    metadata tracking, and context-aware execution.
    """
    def __init__(self, prompt: str, project_name: str):
        self.prompt = prompt.strip()
        self.project_name = project_name.strip().replace(" ", "_")
        
        self.project_dir = PROJECTS_DIR / self.project_name
        
        self.logs = []
        self.project_type = self._determine_project_type()
        self.entry_point = "main.py" 
        self.features = []

    def log(self, message: str):
        full_msg = f"[{self.project_name.upper()}-BUILDER] {message}"
        self.logs.append(full_msg)
        print(full_msg)

    def _determine_project_type(self) -> str:
        """Analyzes the prompt to route to the correct architecture."""
        prompt_lower = self.prompt.lower()
        if any(word in prompt_lower for word in ["bot", "discord", "slack", "telegram"]):
            return "bot"
        elif any(word in prompt_lower for word in ["web", "website", "html", "flask", "django"]):
            return "web_app"
        elif any(word in prompt_lower for word in ["api", "endpoint", "rest", "backend"]):
            return "api"
        elif any(word in prompt_lower for word in ["data", "scrape", "csv", "json"]):
            return "data_tool"
        elif any(word in prompt_lower for word in ["game", "pygame", "arcade"]):
            return "game"
        elif any(word in prompt_lower for word in ["gui", "interface", "desktop", "tkinter"]):
            return "desktop_gui"
        elif any(word in prompt_lower for word in ["automation", "organize", "cleanup", "file"]):
            return "automation_script"
        else:
            return "cli" 

    def execute_pipeline(self):
        self.log(f"Initializing ADVANCED build pipeline.")
        self.log(f"Detected Project Architecture: {self.project_type.upper()}")
        
        self.make_folders()
        self.write_code()
        
        success = self.debug_and_test()
        
        if success:
            self.run_project()
        else:
            self.log("Pipeline stopped: Code checking failed validation step.")
            
        self.explain_everything()

    def make_folders(self):
        self.log("Scaffolding dynamic workspace directories...")
        
        directories = ["src", "tests", "docs", "config"]
        
        if self.project_type == "web_app":
            directories.extend(["src/templates", "src/static"])
        elif self.project_type == "data_tool":
            directories.extend(["data/input", "data/output"])

        for d in directories:
            (self.project_dir / d).mkdir(parents=True, exist_ok=True)
            
        self.log(f"Directory structure prepared at: {self.project_dir}")

    def write_code(self):
        self.log("Generating source assets, routing templates, and configuring dependencies...")
        
        manifest = {
            "name": self.project_name,
            "type": self.project_type,
            "generated_at": datetime.now().isoformat(),
            "original_prompt": self.prompt
        }
        
        if self.project_type == "bot":
            self.entry_point = "bot.py"
            reqs = "discord.py\npython-dotenv\n"
            main_code = dedent("""\
                import os
                import sys
                import time
                
                print("[LIVE] Advanced Bot Framework starting...")
                print("[LIVE] Loading environment configurations...")
                
                if __name__ == '__main__':
                    print("✓ Bot connection protocols established.")
                    print("✓ Listening for incoming commands.")
                    try:
                        while True:
                            time.sleep(1)
                    except KeyboardInterrupt:
                        print("Exiting bot instance safely.")
            """)
            self.features = ["Command Routing", "Event Listeners", "Env Config"]

        elif self.project_type == "desktop_gui":
            self.entry_point = "gui_app.py"
            reqs = ""  
            main_code = dedent("""\
                import tkinter as tk
                from tkinter import messagebox
                import sys
                
                print("[GUI SYSTEM] Compiling platform window configurations...")
                
                class SoarAppWindow:
                    def __init__(self):
                        self.root = tk.Tk()
                        self.root.title(f"{self.__class__.__name__} - SOAR Generated Interface")
                        self.root.geometry("450x300")
                        self.build_layout()
                        
                    def build_layout(self):
                        lbl = tk.Label(self.root, text="SOAR Autonomous Window", font=("Helvetica", 14, "bold"))
                        lbl.pack(pady=20)
                        
                        btn = tk.Button(self.root, text="Trigger Action Matrix", command=self.on_click)
                        btn.pack(pady=10)
                        
                    def on_click(self):
                        print("[GUI CALLBACK] Action button clicked.")
                        
                    def run(self):
                        # Safely runs unless headless/detached error happens
                        if sys.stdout and sys.stdout.isatty():
                            self.root.mainloop()
                        else:
                            print("[GUI WARNING] Headless background worker running without desktop window.")
                            
                if __name__ == '__main__':
                    app = SoarAppWindow()
                    print("✓ Window wrapper successfully mounted.")
            """)
            self.features = ["Tkinter Mainloop Architecture", "Responsive Layout Constraints", "Event-Driven Button Callbacks"]

        elif self.project_type == "automation_script":
            self.entry_point = "cleaner.py"
            reqs = "psutil\n"
            main_code = dedent(f"""\
                import os
                import sys
                import shutil
                from pathlib import Path
                
                print("[AUTOMATION LOG] Initializing dynamic file system scanner...")
                
                def run_maintenance_scan(target_path):
                    path = Path(target_path)
                    print(f"[SCANNING] Parsing node branches inside: {{path}}")
                    
                    # Core target safety checklist rule
                    protected_roots = ["C:\\\\Windows", "/System", "/usr/bin"]
                    if any(str(path).startswith(p) for p in protected_roots):
                        print("[-] Access Revoked: System core targets are shielded by SOAR safety guardrails.")
                        return False
                        
                    print("✓ Scan trace operation executed completely with zero conflicts.")
                    return True
                    
                if __name__ == '__main__':
                    # Fallback to local project workspace directory context
                    run_maintenance_scan("./")
            """)
            self.features = ["File Tree Pattern Scanning", "SOAR Core Safety Shield Guardrails", "Shutil Context File Relocator Blueprint"]
            
        elif self.project_type == "web_app":
            self.entry_point = "app.py"
            reqs = "flask\nwerkzeug\n"
            main_code = dedent("""\
                from flask import Flask, jsonify
                
                app = Flask(__name__)
                
                @app.route('/')
                def home():
                    return jsonify({"status": "online", "message": "SOAR Web App Active"})
                
                if __name__ == '__main__':
                    print("[LIVE] Web Server starting on port 5000...")
                    # app.run(debug=True, port=5000) # Uncomment to actually run
            """)
            
            index_html = dedent("""\
                <!DOCTYPE html>
                <html><head><title>SOAR App</title></head>
                <body><h1>App is running!</h1></body></html>
            """)
            (self.project_dir / "src" / "templates" / "index.html").write_text(index_html, encoding="utf-8")
            self.features = ["Flask Routing", "HTML Templates", "Static Assets"]

        elif self.project_type == "api":
            self.entry_point = "api.py"
            reqs = "fastapi\nuvicorn\n"
            main_code = dedent("""\
                import json
                print("[LIVE] API Gateway initializing...")
                print("✓ Endpoints mounted at /api/v1/")
                
                if __name__ == '__main__':
                    print("Ready for requests.")
            """)
            self.features = ["JSON Endpoints", "Data Validation", "REST Architecture"]

        else: 
            self.entry_point = "main.py"
            reqs = "requests\n"
            main_code = dedent(f"""\
                import argparse
                import sys
                
                def main():
                    parser = argparse.ArgumentParser(description="{self.prompt}")
                    parser.add_argument('--run', action='store_true', help='Execute main routine')
                    args = parser.parse_args()
                    
                    print(f"[{self.project_name.upper()}] CLI Tool Initialized.")
                    if args.run:
                        print("Execution complete.")
                
                if __name__ == '__main__':
                    main()
            """)
            self.features = ["Argument Parsing", "Terminal Output", "Modular Design"]

        (self.project_dir / "src" / self.entry_point).write_text(main_code, encoding="utf-8")
        (self.project_dir / "requirements.txt").write_text(reqs, encoding="utf-8")
        (self.project_dir / "soar_manifest.json").write_text(json.dumps(manifest, indent=4), encoding="utf-8")
        
        readme_content = dedent(f"""\
            # {self.project_name.replace("_", " ")}
            *Generated autonomously by SOAR ProjectAgent.*
            
            **Objective:** {self.prompt}
            **Architecture:** {self.project_type.upper()}
            
            ## Features Built
            {chr(10).join([f"- {f}" for f in self.features])}
            
            ## Getting Started
            1. `cd {self.project_name}`
            2. `pip install -r requirements.txt`
            3. `python src/{self.entry_point}`
        """)
        (self.project_dir / "README.md").write_text(readme_content, encoding="utf-8")
        
        self.log(f"Code generation complete. Entry point set to {self.entry_point}.")

    def debug_and_test(self) -> bool:
        self.log("Running comprehensive AST syntax validation on all Python files...")
        
        python_files = list(self.project_dir.rglob("*.py"))
        if not python_files:
            self.log("✗ No Python files found to test.")
            return False
            
        all_passed = True
        for py_file in python_files:
            try:
                source_content = py_file.read_text(encoding="utf-8")
                ast.parse(source_content)
                self.log(f"  ✓ {py_file.name}: Syntax clean.")
            except SyntaxError as e:
                self.log(f"  ✗ {py_file.name}: Syntax Error at line {e.lineno} -> {e.msg}")
                all_passed = False
                
        return all_passed

    def run_project(self):
        self.log(f"Spawning independent execution stream for {self.entry_point}...")
        target_script = self.project_dir / "src" / self.entry_point
        
        if not target_script.exists():
            self.log(f"✗ Cannot run. {self.entry_point} not found.")
            return
            
        if platform.system() == "Windows":
            subprocess.Popen(["start", "cmd", "/c", sys.executable, str(target_script)], shell=True)
        else:
            subprocess.Popen(
                [sys.executable, str(target_script)], 
                stdout=subprocess.DEVNULL, 
                stderr=subprocess.DEVNULL,
                start_new_session=True
            )
        self.log("✓ Project execution sequence initiated safely in background.")

    def explain_everything(self):
        print("\n" + "="*60)
        print(f" SOAR ADVANCED BUILD COMPLETE: {self.project_name.upper()}")
        print("="*60)
        print(f" ► Architecture : {self.project_type.title()}")
        print(f" ► Location     : {self.project_dir}")
        print(f" ► Entry File   : src/{self.entry_point}")
        
        print("\n [ Project Briefing ]")
        if self.project_type == "bot":
            print(" I have scaffolded a Bot Architecture. You will need to add your API")
            print(" Token (like a Discord or Slack token) to a .env file before it can")
            print(" truly connect to external servers.")
        elif self.project_type == "web_app":
            print(" I have built a Web Application scaffold using Flask. It includes")
            print(" template routing. You can expand the HTML in src/templates/")
            print(" and add CSS to src/static/.")
        elif self.project_type == "api":
            print(" I have generated an API Gateway. It is structured to handle JSON")
            print(" requests. Perfect for bridging frontends to databases.")
        else:
            print(" I have created a Command Line utility. It uses argparse so you")
            print(" can easily add flags and parameters to run from your terminal.")
            
        print("\n [ Next Steps ]")
        print(f" 1. Navigate to the folder: cd projects/{self.project_name}")
        print(" 2. Install dependencies:   pip install -r requirements.txt")
        print(f" 3. Run the application:    python src/{self.entry_point}")
        print("="*60 + "\n")


def log_line(who, text):
    line = f"[{stamp()}] {who}: {text}"
    with CHAT_LOG.open("a", encoding="utf-8") as f:
        f.write(line + "\n")

    cleanup_logs()

def cleanup_logs(max_lines=2000):
    try:
        if not CHAT_LOG.exists():
            return

        lines = CHAT_LOG.read_text(encoding="utf-8").splitlines()

        if len(lines) > max_lines:
            lines = lines[-max_lines:]
            CHAT_LOG.write_text("\n".join(lines) + "\n", encoding="utf-8")

    except Exception as e:
        print(f"[LOG CLEANUP ERROR] {e}")

def stamp():
    """Returns the current timestamp string for logs."""
    return datetime.now().strftime("%H:%M:%S")

def read_lines(path):
    if not path.exists():
        return []
    return [x.strip() for x in path.read_text(encoding="utf-8").splitlines() if x.strip()]


def save_lines(path, lines):
    path.write_text("\n".join(lines) + ("\n" if lines else ""), encoding="utf-8")


def append_line(path, text):
    with path.open("a", encoding="utf-8") as f:
        f.write(text.rstrip() + "\n")

def load_database():
    time.sleep(0.8) 

def initialize_network():
    time.sleep(1.2)

def load_configurations():
    time.sleep(0.4)

def verify_security():
    time.sleep(0.6)


def load_systems(tasks):
    total_tasks = len(tasks)
    bar_width = 40
    print(f"{APP_NAME} booting up...")
    
    current_pct = 0
    
    for index, (task_name, task_func) in enumerate(tasks):
        target_pct = int(((index + 1) / total_tasks) * 100)
        
        captured_output = io.StringIO()
        original_stdout = sys.stdout
        sys.stdout = captured_output
        
        task_thread = threading.Thread(target=task_func)
        task_thread.start()
        
        while task_thread.is_alive():
            log_content = captured_output.getvalue()
            if log_content:
                sys.stdout = original_stdout
                print(f"\r\033[K{log_content.strip()}")
                captured_output.seek(0)
                captured_output.truncate(0)
                sys.stdout = captured_output
                
            if current_pct < target_pct - 1:
                current_pct += 1
                filled_length = int(bar_width * current_pct // 100)
                bar = "█" * filled_length + " " * (bar_width - filled_length)
                
                original_stdout.write(f"\r[{bar}] {current_pct}% | Loading: {task_name:<25}")
                original_stdout.flush()
                time.sleep(0.02)
            else:
                time.sleep(0.01)
        
        sys.stdout = original_stdout
        
        remaining_log = captured_output.getvalue()
        if remaining_log:
            print(f"\r\033[K{remaining_log.strip()}")
            
        current_pct = target_pct
        filled_length = int(bar_width * current_pct // 100)
        bar = "█" * filled_length + " " * (bar_width - filled_length)
        print(f"\r[{bar}] {current_pct}% | Loaded: {task_name:<25}", end="", flush=True)


def default_settings():
    return {
        "voice_preference": "auto",
        "active_profile": "default",
        "safe_mode": False,
        "auto_lightweight": True,
        "module_overrides": [],
        "groq_enabled": True,
        "groq_api_key": "", #api key here
        "groq_model": GROQ_DEFAULT_MODEL, #groq model here
        "personality": {
            "Respectiveness": 0.85,
            "Humor": 0.4,
            "Honesty": 0.9,
            "Comfort": 0.7,
        }
    }


def _deep_merge_dict(base, override):
    result = copy.deepcopy(base)
    if isinstance(override, dict):
        for key, value in override.items():
            if isinstance(value, dict) and isinstance(result.get(key), dict):
                result[key] = _deep_merge_dict(result[key], value)
            else:
                result[key] = copy.deepcopy(value)
    return result


def load_settings():
    global SETTINGS_CACHE
    with SETTINGS_LOCK:
        if SETTINGS_CACHE is not None:
            return copy.deepcopy(SETTINGS_CACHE)

        data = default_settings()
        try:
            if SETTINGS_FILE.exists() and SETTINGS_FILE.read_text(encoding="utf-8").strip():
                loaded = json.loads(SETTINGS_FILE.read_text(encoding="utf-8"))
                if isinstance(loaded, dict):
                    data = _deep_merge_dict(data, loaded)
        except Exception as e:
            print(f"[{stamp()}] [SETTINGS ERROR] Failed to load configuration: {e}")

        SETTINGS_CACHE = data
        return copy.deepcopy(data)


def save_settings(settings):
    global SETTINGS_CACHE
    with SETTINGS_LOCK:
        merged = _deep_merge_dict(default_settings(), settings if isinstance(settings, dict) else {})
        SETTINGS_CACHE = merged
        SETTINGS_FILE.parent.mkdir(parents=True, exist_ok=True)
        SETTINGS_FILE.write_text(
            json.dumps(merged, indent=2, ensure_ascii=False),
            encoding="utf-8"
        )


def get_groq_api_key():
    """Return the Groq key without ever printing it."""
    env_key = os.environ.get("GROQ_API_KEY", "").strip()
    if env_key:
        return env_key

    configured = load_settings().get("groq_api_key", "")
    if configured:
        return str(configured).strip()

    return GROQ_FALLBACK_KEY.strip()


def get_groq_model():
    model = str(load_settings().get("groq_model", GROQ_DEFAULT_MODEL) or GROQ_DEFAULT_MODEL).strip()
    return model or GROQ_DEFAULT_MODEL


def is_groq_enabled():
    return bool(load_settings().get("groq_enabled", True))


def set_groq_enabled(enabled):
    settings = load_settings()
    settings["groq_enabled"] = bool(enabled)
    save_settings(settings)


def groq_status_text():
    enabled = is_groq_enabled()
    key_present = bool(get_groq_api_key())
    state = "on" if enabled else "off"
    key_state = "configured" if key_present else "missing"
    return f"Groq chat is {state}; API key is {key_state}; model: {get_groq_model()}."


def _groq_report_error(message):
    global _groq_last_error, _groq_last_error_time
    now = time.time()
    _groq_last_error = str(message)
    if now - _groq_last_error_time >= 30:
        print(f"[GROQ] {message} Using local SOAR chat fallback for this request.")
        _groq_last_error_time = now


def _groq_context_messages():
    messages = []
    for entry in BRAIN_CONTEXT[-8:]:
        if not isinstance(entry, dict):
            continue
        user_msg = str(entry.get("user") or "").strip()
        assistant_msg = str(entry.get("response") or "").strip()
        if user_msg:
            messages.append({"role": "user", "content": user_msg})
        if assistant_msg:
            messages.append({"role": "assistant", "content": assistant_msg})
    return messages[-12:]


def groq_chat(user_text):
    """Ask Groq for ordinary chat; return None when disabled/unconfigured/offline."""
    if not is_groq_enabled():
        return None

    api_key = get_groq_api_key()
    if not api_key:
        _groq_report_error("No GROQ_API_KEY is configured.")
        return None

    user_text = str(user_text or "").strip()
    if not user_text:
        return None

    messages = [{"role": "system", "content": GROQ_SYSTEM_PROMPT}]
    messages.extend(_groq_context_messages())
    messages.append({"role": "user", "content": user_text})

    payload = {
        "model": get_groq_model(),
        "messages": messages,
        "temperature": 0.7,
        "max_completion_tokens": 1024,
    }

    request = urllib.request.Request(
        GROQ_API_ENDPOINT,
        data=json.dumps(payload, ensure_ascii=False).encode("utf-8"),
        headers={
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json",
            "User-Agent": f"{APP_NAME}/1.00.10",
        },
        method="POST",
    )

    try:
        with urllib.request.urlopen(
            request,
            timeout=GROQ_REQUEST_TIMEOUT,
            context=ssl_context,
        ) as response:
            body = response.read().decode("utf-8", errors="replace")

        data = json.loads(body)
        choices = data.get("choices") if isinstance(data, dict) else None
        if not isinstance(choices, list) or not choices:
            raise ValueError("Groq returned no choices")

        message = choices[0].get("message", {})
        content = message.get("content") if isinstance(message, dict) else None
        if not content:
            raise ValueError("Groq returned an empty response")

        return str(content).strip()

    except urllib.error.HTTPError as e:
        try:
            detail = e.read().decode("utf-8", errors="replace")[:500]
        except Exception:
            detail = str(e)
        _groq_report_error(f"HTTP {e.code}: {detail}")
    except (urllib.error.URLError, TimeoutError, socket.timeout) as e:
        _groq_report_error(f"Network unavailable: {e}")
    except json.JSONDecodeError as e:
        _groq_report_error(f"Invalid JSON response: {e}")
    except Exception as e:
        _groq_report_error(f"Request failed: {e}")

    return None


def get_voice_preference():
    return str(load_settings().get("voice_preference", "auto") or "auto").strip()


def set_voice_preference(name):
    settings = load_settings()
    settings["voice_preference"] = str(name or "auto").strip() or "auto"
    save_settings(settings)


def resolve_mac_voice_candidates(preferred_name="auto"):
    pref = str(preferred_name or "auto").strip()
    low = pref.lower()

    if low in {"", "auto"}:
        return ["Daniel", "Alex", "Samantha", "Victoria", "Karen", "Moira"]
    if "daniel" in low:
        return ["Daniel", "Alex", "Samantha", "Victoria", "David"]
    if "alex" in low:
        return ["Alex", "Daniel", "Samantha", "Victoria"]
    if "samantha" in low:
        return ["Samantha", "Victoria", "Alex", "Daniel"]
    return [pref, "Daniel", "Alex", "Samantha", "Victoria"]


def resolve_windows_voice_candidates(preferred_name="auto"):
    pref = str(preferred_name or "auto").strip()
    low = pref.lower()

    if low in {"", "auto"}:
        return ["Daniel", "David", "Mark", "Zira", "Hazel"]
    if "daniel" in low:
        return ["Daniel", "David", "Mark", "Zira", "Hazel"]
    if "david" in low:
        return ["David", "Daniel", "Mark", "Zira", "Hazel"]
    if "zira" in low:
        return ["Zira", "David", "Mark", "Daniel", "Hazel"]
    return [pref, "Daniel", "David", "Mark", "Zira", "Hazel"]


def list_available_voices():
    system = platform.system()
    if system == "Darwin":
        try:
            result = subprocess.run(["say", "-v", "?"], capture_output=True, text=True, check=False)
            out = result.stdout.strip()
            if not out:
                return []
            voices = []
            for line in out.splitlines():
                line = line.strip()
                if not line:
                    continue
                name = line.split()[0]
                voices.append(name)
            return voices
        except Exception:
            return []
    if pyttsx3 is None:
        return []
    try:
        engine = pyttsx3.init()
        voices = engine.getProperty("voices") or []
        items = []
        for voice in voices:
            name = str(getattr(voice, "name", "") or "").strip()
            vid = str(getattr(voice, "id", "") or "").strip()
            if name and vid:
                items.append(f"{name} | {vid}")
            elif name:
                items.append(name)
            elif vid:
                items.append(vid)
        try:
            engine.stop()
        except Exception:
            pass
        return items
    except Exception:
        return []


def choose_best_tts_voice(engine=None, preferred_name=None):
    global tts_voice_label, tts_voice_id

    system = platform.system()
    pref = preferred_name if preferred_name is not None else get_voice_preference()

    if system == "Darwin":
        candidates = resolve_mac_voice_candidates(pref)
        available = list_available_voices()
        available_lower = [x.lower() for x in available]

        chosen = None
        for candidate in candidates:
            cand = candidate.lower()
            for idx, item in enumerate(available_lower):
                if cand in item:
                    chosen = available[idx]
                    break
            if chosen:
                break

        if chosen is None:
            chosen = candidates[0] if candidates else "Daniel"

        tts_voice_label = chosen
        tts_voice_id = chosen
        return chosen

    if engine is None:
        if pyttsx3 is None:
            return None
        try:
            engine = pyttsx3.init()
        except Exception:
            return None

    candidates = resolve_windows_voice_candidates(pref)
    try:
        voices = engine.getProperty("voices") or []
    except Exception:
        voices = []

    fallback = None
    for voice in voices:
        voice_id = str(getattr(voice, "id", "") or "")
        voice_name = str(getattr(voice, "name", "") or "")
        blob = f"{voice_id} {voice_name}".lower()

        for candidate in candidates:
            if candidate.lower() in blob:
                try:
                    engine.setProperty("voice", voice_id)
                    tts_voice_label = voice_name or voice_id
                    tts_voice_id = voice_id
                    return voice_id
                except Exception:
                    pass

        if fallback is None:
            fallback = voice_id

    if fallback:
        try:
            engine.setProperty("voice", fallback)
            for voice in voices:
                if str(getattr(voice, "id", "")) == fallback:
                    tts_voice_label = str(getattr(voice, "name", "") or fallback)
                    break
            else:
                tts_voice_label = fallback
            tts_voice_id = fallback
            return fallback
        except Exception:
            return None

    return None

if not MODS_DIR.exists(): #mods start 1
    MODS_DIR.mkdir(parents=True, exist_ok=True)
    print(f"[*] Created empty mods directory at: {MODS_DIR}")

def load_soar_mods():
    import importlib.util
    import sys
    from pathlib import Path
    
    MODS_DIR = BASE_DIR / "soar-mods"
    if not MODS_DIR.exists():
        MODS_DIR.mkdir(parents=True, exist_ok=True)
        
    if not hasattr(sys, "mod_commands"):
        sys.mod_commands = {}

    print("[SOAR MODS] Scanning 'soar-mods/' folder for active addons...")
    
    for mod_path in MODS_DIR.iterdir():
        if mod_path.is_dir():
            init_file = mod_path / "__init__.py"
            if init_file.exists():
                mod_name = mod_path.name
                try:
                    spec = importlib.util.spec_from_file_location(mod_name, str(init_file))
                    if spec and spec.loader:
                        module = importlib.util.module_from_spec(spec)
                        sys.modules[mod_name] = module
                        spec.loader.exec_module(module)
                        print(f"Mod Loaded: {mod_name}")
                        
                        if hasattr(module, "MOD_COMMANDS") and isinstance(module.MOD_COMMANDS, dict):
                            sys.mod_commands.update(module.MOD_COMMANDS)
                            
                        if hasattr(module, "initialize_addon"):
                            module.initialize_addon()
                except Exception as e:
                    print(f"Error loading mod {mod_name}: {e}")

    print("Mods above.")

load_soar_mods() #mods end 1


def show_voice_status():
    pref = get_voice_preference()
    print()
    print("Voice status")
    print(f"  platform: {platform.system()}")
    print(f"  preference: {pref}")
    print(f"  selected: {tts_voice_label or 'none'}")
    print(f"  tts ready: {'yes' if tts_ready.is_set() else 'no'}")
    print()


def refresh_voice_selection():
    global tts_engine
    pref = get_voice_preference()
    if platform.system() == "Darwin":
        choose_best_tts_voice(None, pref)
        return True
    if tts_engine is None:
        return False
    return choose_best_tts_voice(tts_engine, pref) is not None


def cooldown_seconds_for_text(text):
    return max(0.9, min(6.0, len(text) / 14.0))


def mic_is_muted():
    with speech_cooldown_lock:
        return voice_pause.is_set() or time.time() < speech_cooldown_until


def mute_mic_temporarily(seconds=1.0):
    global speech_cooldown_until
    with speech_cooldown_lock:
        voice_pause.set()
        speech_cooldown_until = max(speech_cooldown_until, time.time() + float(seconds))


def unmute_mic():
    with speech_cooldown_lock:
        voice_pause.clear()


def maybe_address_user(text, chance=0.25):
    if not text:
        return text
    low = text.lower()
    if "sir" in low or "ma'am" in low:
        return text
        
    try:
        settings = load_settings()
        personality = settings.get("personality", {})
        respect_score = personality.get("Respectiveness", 0.5)
    except Exception:
        respect_score = chance

    if random.random() < respect_score:
        cleaned = text.rstrip(".!?")
        if respect_score > 0.8:
            title = f", {pronoun}."
        elif respect_score > 0.4:
            title = ", friend."
        else:
            title = "."
        return f"{cleaned}{title}"
    return text


def open_url(target):
    target = target.strip()
    if not target:
        return False

    if not (target.startswith("http://") or target.startswith("https://")):
        if " " in target or "." not in target:
            target = f"https://www.google.com/search?q={quote_plus(target)}"
        else:
            target = "https://" + target

    try:
        webbrowser.open(target)
        return True
    except Exception:
        return False


def get_local_ip():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("8.8.8.8", 80))
        return s.getsockname()[0]
    except Exception:
        return "127.0.0.1"
    finally:
        try:
            s.close()
        except Exception:
            pass


def clipboard_copy(text):
    text = str(text)
    system = platform.system()
    try:
        if system == "Darwin":
            subprocess.run(["pbcopy"], input=text, text=True, check=False)
            return True
        if system == "Windows":
            subprocess.run(
                ["powershell", "-NoProfile", "-Command", "Set-Clipboard"],
                input=text,
                text=True,
                check=False,
            )
            return True

        for cmd in (["xclip", "-selection", "clipboard"], ["xsel", "--clipboard", "--input"]):
            try:
                subprocess.run(cmd, input=text, text=True, check=True)
                return True
            except Exception:
                continue
    except Exception:
        pass
    return False


def clipboard_paste():
    system = platform.system()
    try:
        if system == "Darwin":
            result = subprocess.run(["pbpaste"], capture_output=True, text=True, check=False)
            return result.stdout.strip()
        if system == "Windows":
            result = subprocess.run(
                ["powershell", "-NoProfile", "-Command", "Get-Clipboard"],
                capture_output=True,
                text=True,
                check=False,
            )
            return result.stdout.strip()

        for cmd in (["xclip", "-selection", "clipboard", "-o"], ["xsel", "--clipboard", "--output"]):
            try:
                result = subprocess.run(cmd, capture_output=True, text=True, check=True)
                return result.stdout.strip()
            except Exception:
                continue
    except Exception:
        pass
    return ""


def parse_duration_seconds(text):
    s = text.strip().lower().replace(" ", "")
    if not s:
        raise ValueError("empty duration")

    suffix = s[-1]
    if suffix in {"s", "m", "h"}:
        value = float(s[:-1])
        if suffix == "s":
            return int(value)
        if suffix == "m":
            return int(value * 60)
        if suffix == "h":
            return int(value * 3600)

    return int(float(s))


def schedule_reminder(delay_seconds, message, kind="Reminder"):
    delay_seconds = max(1, int(delay_seconds))
    message = message.strip()

    def _fire():
        speak(f"{kind}: {message}", allow_sound=True)

    timer = threading.Timer(delay_seconds, _fire)
    timer.daemon = True
    timer.start()
    return timer


def search_storage(term):
    term = term.strip().lower()
    if not term:
        return []

    results = []
    sources = [
        ("notes", read_lines(NOTES_FILE)),
        ("memories", read_lines(MEMORY_FILE)),
        ("todos", read_lines(TODO_FILE)),
    ]

    for label, items in sources:
        for item in items:
            if term in item.lower():
                results.append(f"{label}: {item}")

    return results


def loading_status_line():
    return f"Running on {platform.system()} {platform.release()} with Python {sys.version.split()[0]}"


def is_protected_path(path):
    try:
        path = path.resolve()
    except Exception:
        path = Path(str(path)).absolute()

    try:
        if path == MAIN_SCRIPT:
            return True
    except Exception:
        pass
    return False


def normalize_path(text, allow_create=True):
    raw = str(text).strip().strip('"').strip("'")
    if not raw:
        raise ValueError("empty path")

    path = Path(raw).expanduser()
    if not path.is_absolute():
        path = BASE_DIR / path

    try:
        path = path.resolve()
    except Exception:
        path = path.absolute()

    allowed_roots = []
    for root in (BASE_DIR, DATA_DIR, PROJECTS_DIR):
        try:
            allowed_roots.append(root.resolve())
        except Exception:
            pass

    if not any(path == root or root in path.parents for root in allowed_roots):
        raise ValueError("path must stay inside the current SOAR folder")

    if is_protected_path(path):
        raise ValueError("main script is protected")

    if not allow_create and not path.exists():
        raise FileNotFoundError("file not found")

    return path

def autocode_connected():
    return soar_autocode is not None and hasattr(soar_autocode, "run_cycle")

def show_autocode_status():
    print()
    print("SOAR autocode status")
    print(f"  connected: {'yes' if autocode_connected() else 'no'}")

    if not autocode_connected():
        print()
        return

    state = None
    if hasattr(soar_autocode, "load_state"):
        try:
            state = soar_autocode.load_state()
        except Exception:
            state = None

    if isinstance(state, dict):
        print(f"  runs: {state.get('run_count', 0)}")
        print(f"  last project: {state.get('last_project') or 'none'}")
        recent = state.get("recent_projects", [])
        if isinstance(recent, list):
            print(f"  recent: {', '.join(recent[-5:]) or 'none'}")
        memory = state.get("memory", [])
        if isinstance(memory, list):
            print(f"  memories: {len(memory)}")

    projects_dir = getattr(soar_autocode, "PROJECTS_DIR", PROJECTS_DIR)
    print(f"  output folder: {projects_dir}")
    print()


def trigger_autocode(reason="manual trigger from main"):
    if not autocode_connected():
        print("Autocode is not connected.")
        speak("Autocode is not connected.", allow_sound=True)
        return False

    def _run():
        try:
            soar_autocode.run_cycle(reason)
        except Exception as e:
            print(f"Autocode error: {e}")

    threading.Thread(target=_run, daemon=True).start()
    return True


def pause_voice_input():
    global listener_stop
    was_active = False

    try:
        acquired = voice_state_lock.acquire(blocking=False)
    except KeyboardInterrupt:
        return False

    if not acquired:
        voice_pause.set()
        return False

    try:
        voice_pause.set()
        if listener_stop is not None:
            try:
                listener_stop(wait_for_stop=False)
                was_active = True
            except Exception:
                pass
            listener_stop = None
    finally:
        try:
            voice_state_lock.release()
        except Exception:
            pass

    return was_active


def resume_voice_input(was_active):
    if shutting_down:
        unmute_mic()
        return

    if not was_active:
        unmute_mic()
        return

    if not voice_enabled or stop_event.is_set():
        unmute_mic()
        return

    try:
        acquired = voice_state_lock.acquire(blocking=False)
    except KeyboardInterrupt:
        unmute_mic()
        return

    try:
        if acquired and listener_stop is None:
            try:
                start_voice_listener()
            except Exception:
                pass
    finally:
        if acquired:
            try:
                voice_state_lock.release()
            except Exception:
                pass

    unmute_mic()


def tts_worker():
    global tts_engine, IS_SPEAKING  
    if pyttsx3 is None:
        print("TTS ERROR: pyttsx3 is not installed.")
        tts_ready.set()
        return

    try:
        tts_engine = pyttsx3.init()
        try:
            tts_engine.setProperty("rate", 190)
            tts_engine.setProperty("volume", 1.0)
        except Exception:
            pass

        chosen = choose_best_tts_voice(tts_engine, get_voice_preference())
        if chosen:
            print(f"TTS: using voice {chosen}")
        else:
            print("TTS: no preferred voice found, using fallback voice.")

        tts_ready.set()

        while not stop_event.is_set():
            try:
                item = tts_queue.get(timeout=0.2)
            except queue.Empty:
                continue

            if item is None:
                break

            if isinstance(item, tuple):
                text = str(item[0]).strip() if item else ""
                gender = str(item[1]).strip().lower() if len(item) > 1 else "default"
            else:
                text = str(item).strip()
                gender = "default"

            if not text:
                continue

            was_active = pause_voice_input()
            try:
                if tts_engine is not None:
                    tts_engine.stop()
                    tts_engine.say(text)
                    
                    IS_SPEAKING = True
                    tts_engine.runAndWait()
                    IS_SPEAKING = False
                    
            except Exception as e:
                print(f"TTS ERROR: {e}")
                IS_SPEAKING = False  
            finally:
                try:
                    if tts_engine is not None:
                        tts_engine.stop()
                except Exception:
                    pass
                IS_SPEAKING = False  
                resume_voice_input(was_active)

    except Exception as e:
        print(f"TTS ERROR: {e}")
        IS_SPEAKING = False
        tts_ready.set()
    finally:
        try:
            if tts_engine is not None:
                tts_engine.stop()
        except Exception:
            pass
        IS_SPEAKING = False


def init_tts():
    global tts_thread
    if platform.system() == "Darwin":
        choose_best_tts_voice(None, get_voice_preference())
        tts_ready.set()
        print(f"TTS: macOS voice ready ({tts_voice_label or 'Daniel'}).")
        return

    tts_thread = threading.Thread(target=tts_worker, daemon=True)
    tts_thread.start()
    tts_ready.wait(timeout=5)


def init_recognition():
    global recognizer
    if sr is None:
        return False
    try:
        recognizer = sr.Recognizer()
        return True
    except Exception:
        recognizer = None
        return False

def speak(text, allow_sound=True, gender="default", custom_name=None):
    global shutting_down
    text = str(text)

    display_name = custom_name if custom_name else APP_NAME

    with bot_lock:
        print(f"{display_name}: {text}")
        log_line(display_name, text)

    if not allow_sound or shutting_down:
        return

    was_active = False
    try:
        was_active = pause_voice_input()
        mute_mic_temporarily(cooldown_seconds_for_text(text))

        if platform.system() == "Darwin":
            voice_name = "Samantha" if gender == "female" else (tts_voice_label or choose_best_tts_voice(None, get_voice_preference()) or "Daniel")
            subprocess.run(["say", "-v", voice_name, text], check=False)
        else:
            if not tts_ready.is_set():
                print("TTS ERROR: voice system not ready.")
                return
            try:
                tts_queue.put_nowait((text, gender))
            except Exception as e:
                print(f"TTS ERROR: {e}")
    except Exception as e:
        print(f"Speech Core Error: {e}")

def say_user(text):
    with bot_lock:
        print(f"You: {text}")
        log_line("You", text)


def prompt_yes_no(question):
    while True:
        ans = input(f"{question} (y/n): ").strip().lower()
        if ans in {"y", "yes"}:
            return True
        if ans in {"n", "no"}:
            return False


def safe_calc(expr):
    allowed = {
        ast.Expression, ast.BinOp, ast.UnaryOp, ast.Add, ast.Sub, ast.Mult, ast.Div,
        ast.FloorDiv, ast.Mod, ast.Pow, ast.USub, ast.UAdd, ast.Constant, ast.Call,
        ast.Name,
    }
    names = {"abs": abs, "round": round, "min": min, "max": max}

    tree = ast.parse(expr, mode="eval")
    for node in ast.walk(tree):
        if type(node) not in allowed:
            raise ValueError("bad")
        if isinstance(node, ast.Name) and node.id not in names:
            raise ValueError("bad")
        if isinstance(node, ast.Call):
            if not isinstance(node.func, ast.Name) or node.func.id not in names:
                raise ValueError("bad")

    return eval(compile(tree, "<calc>", "eval"), {"__builtins__": {}}, names)


def python_template(project_name, description):
    title = project_name.replace("_", " ").replace("-", " ").title()
    description = description.strip() or "Auto-generated project"
    return dedent(f"""\
        #!/usr/bin/env python3

        def main():
            print("{title}")
            print("{description}")

        if __name__ == "__main__":
            main()
    """).lstrip()


def html_template(title, description):
    title = title.replace("_", " ").replace("-", " ").title()
    description = description.strip() or "Auto-generated web project"
    return dedent(f"""\
        <!doctype html>
        <html lang="en">
        <head>
          <meta charset="utf-8">
          <meta name="viewport" content="width=device-width, initial-scale=1">
          <title>{title}</title>
          <link rel="stylesheet" href="style.css">
        </head>
        <body>
          <main class="wrap">
            <h1>{title}</h1>
            <p>{description}</p>
            <button id="btn">Click me</button>
          </main>
          <script src="script.js"></script>
        </body>
        </html>
    """).lstrip()


def css_template():
    return dedent("""\
        :root {
          color-scheme: dark;
          font-family: system-ui, sans-serif;
        }

        body {
          margin: 0;
          min-height: 100vh;
          display: grid;
          place-items: center;
          background: #111;
          color: #fff;
        }

        .wrap {
          width: min(720px, calc(100vw - 32px));
          padding: 32px;
          border-radius: 20px;
          background: #1b1b1b;
          box-shadow: 0 12px 40px rgba(0, 0, 0, 0.35);
        }

        button {
          border: 0;
          border-radius: 14px;
          padding: 12px 18px;
          font: inherit;
          background: #fff;
          color: #111;
          cursor: pointer;
        }
    """).lstrip()


def js_template():
    return dedent("""\
        const btn = document.getElementById("btn");
        if (btn) {
          btn.addEventListener("click", () => {
            alert("SOAR project ready");
          });
        }
    """).lstrip()


def md_template(name, description):
    name = name.replace("_", " ").replace("-", " ").title()
    description = description.strip() or "Auto-generated project"
    return dedent(f"""\
        # {name}

        {description}
    """).lstrip()


def json_template():
    return "{\n  \n}\n"


def create_file_with_template(path, description=""):
    path.parent.mkdir(parents=True, exist_ok=True)
    ext = path.suffix.lower()
    stem = path.stem

    if ext == ".py":
        content = python_template(stem, description)
    elif ext == ".html":
        content = html_template(stem, description)
    elif ext == ".css":
        content = css_template()
    elif ext == ".js":
        content = js_template()
    elif ext == ".md":
        content = md_template(stem, description)
    elif ext == ".json":
        content = json_template()
    elif ext == ".txt":
        content = (description.strip() + "\n") if description.strip() else ""
    else:
        content = description if description else ""

    path.write_text(content, encoding="utf-8")
    return path


def create_python_project(project_name, description=""):
    root = PROJECTS_DIR / project_name
    root.mkdir(parents=True, exist_ok=True)
    main_file = root / "main.py"
    readme = root / "README.md"
    req = root / "requirements.txt"

    main_file.write_text(python_template(project_name, description), encoding="utf-8")
    readme.write_text(md_template(project_name, description), encoding="utf-8")
    req.write_text("", encoding="utf-8")
    return root, [main_file, readme, req]


def create_web_project(project_name, description=""):
    root = PROJECTS_DIR / project_name
    root.mkdir(parents=True, exist_ok=True)
    index = root / "index.html"
    style = root / "style.css"
    script = root / "script.js"
    readme = root / "README.md"

    index.write_text(html_template(project_name, description), encoding="utf-8")
    style.write_text(css_template(), encoding="utf-8")
    script.write_text(js_template(), encoding="utf-8")
    readme.write_text(md_template(project_name, description), encoding="utf-8")
    return root, [index, style, script, readme]


def open_projects_folder():
    try:
        if platform.system() == "Darwin":
            subprocess.Popen(["open", str(PROJECTS_DIR)])
        elif platform.system() == "Windows":
            os.startfile(str(PROJECTS_DIR))
        else:
            subprocess.Popen(["xdg-open", str(PROJECTS_DIR)])
    except Exception as e:
        print(f"Could not open projects folder: {e}")


def open_data_folder():
    try:
        if platform.system() == "Darwin":
            subprocess.Popen(["open", str(DATA_DIR)])
        elif platform.system() == "Windows":
            os.startfile(str(DATA_DIR))
        else:
            subprocess.Popen(["xdg-open", str(DATA_DIR)])
    except Exception as e:
        print(f"Could not open data folder: {e}")


def show_help():
    text = (
        "Commands: help, exit, shut down, shutdown, power off, power down, quit, bye, clear, time, date, uptime, ping, say, message, calc, note, notes, "
        "remember, memories, forget, search, todo add, todo list, todo done, todo remove, todo clear, "
        "remind, timer, shell, read, write, open, openurl, copy, paste, ip, status, voice, voice on, "
        "voice off, voice list, voice set <name>, voice auto, listen on, listen off, code, mkdir, "
        "newfile <path> <optional text>, projects, data, logs, log tail, autocode, autocode status, autocode on, autocode off, "
        "flip a coin, roll a dice, fact, story, /cmd limitres, /cmd limitres off, /cmd lightmode, /cmd lightmode off, "
        "/cmd groqkeyon, /cmd groqkeyoff, /cmd groqkeystatus."
    )
    print()
    print(text)
    print()

def show_status():
    print()
    print(f"{APP_NAME} status")
    print(f"  platform: {platform.system()} {platform.release()}")
    print(f"  python: {sys.version.split()[0]}")
    print(f"  notes: {len(read_lines(NOTES_FILE))}")
    print(f"  memories: {len(read_lines(MEMORY_FILE))}")
    print(f"  todos: {len(read_lines(TODO_FILE))}")
    print(f"  voice: {'on' if voice_enabled else 'off'}")
    print(f"  voice preference: {get_voice_preference()}")
    print(f"  selected voice: {tts_voice_label or 'none'}")
    print(f"  tts: {'ready' if tts_ready.is_set() else 'not ready'}")
    print(f"  speech recognition: {'ready' if recognizer else 'not ready'}")
    print(f"  local ip: {get_local_ip()}")
    print(f"  uptime: {str(datetime.now() - STARTUP_TIME).split('.')[0]}")
    print(f"  chat log: {CHAT_LOG}")
    with resource_limit_lock:
        resource_active = SOAR_RESOURCE_LIMITS_ACTIVE
        resource_ram = SOAR_RESOURCE_LIMITS.get("ram_bytes")
        resource_cpu = SOAR_RESOURCE_LIMITS.get("cpu_percent")
        resource_gpu = SOAR_RESOURCE_LIMITS.get("gpu_percent")
    print(f"  resource limits: {'active this boot' if resource_active else 'off'}")
    if resource_active:
        print(f"  resource RAM limit: {resource_ram / (1024 ** 2):.1f} MB" if resource_ram else "  resource RAM limit: off")
        print(f"  resource CPU limit: {resource_cpu}%" if resource_cpu else "  resource CPU limit: off")
        print(f"  resource GPU limit: {resource_gpu}%" if resource_gpu else "  resource GPU limit: off")
    print(f"  profile: {SOAR_ACTIVE_PROFILE}")
    print(f"  safe mode: {'on' if SOAR_SAFE_MODE else 'off'}")
    print(f"  auto-lightweight: {'on' if SOAR_AUTO_LIGHTWEIGHT_ENABLED else 'off'}")
    print(f"  current mode: {'lightweight' if SOAR_LIGHTWEIGHT_MODE else 'normal'}")
    print(f"  disabled modules: {', '.join(sorted(SOAR_DISABLED_MODULES)) or 'none'}")
    print(f"  autocode: {'connected' if autocode_connected() else 'offline'}")
    print(f"  groq chat: {'on' if is_groq_enabled() else 'off'}")
    print(f"  groq key: {'configured' if get_groq_api_key() else 'missing'}")
    print(f"  groq model: {get_groq_model()}")
    if autocode_connected() and hasattr(soar_autocode, "load_state"):
        try:
            auto_state = soar_autocode.load_state()
            if isinstance(auto_state, dict):
                print(f"  autocode runs: {auto_state.get('run_count', 0)}")
                print(f"  autocode last project: {auto_state.get('last_project') or 'none'}")
        except Exception:
            pass
    print()


def show_recent_log(count=20):
    try:
        count = max(1, min(500, int(count)))
    except Exception:
        count = 20

    lines = read_lines(CHAT_LOG)
    if not lines:
        print("No log entries yet.")
        return

    for line in lines[-count:]:
        print(line)

def analyze_code_syntax(file_path):
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            source = f.read()
        
        compile(source, file_path, 'exec')
        return "No syntax errors detected! The structure looks clean."
        
    except SyntaxError as e:
        explanation = "Hint: Check for missing colons (:), unclosed parentheses (), or mismatched quotes."
        if "expected ':'" in str(e):
            explanation = "Hint: You forgot a colon ':' at the end of an 'if', 'for', 'while', or 'def' statement."
        elif "unmatched" in str(e):
            explanation = "Hint: You have an open parenthesis '(', bracket '[', or brace '{' that never got closed."
        elif "indentation" in str(e).lower():
            explanation = "Hint: Your spacing is uneven. Make sure you are consistently using either 4 spaces or tabs."

        return (
            f"[SYNTAX ERROR FOUND]\n"
            f"  File: {os.path.basename(file_path)}\n"
            f"  Line {e.lineno}: {e.text.strip() if e.text else 'Unknown text'}\n"
            f"  Error: {e.msg}\n"
            f"  {explanation}"
        )
    except Exception as e:
        return f"Could not analyze file structure: {e}"

def _brain_load_json(path, default):
    try:
        if not path.exists():
            path.write_text(
                json.dumps(default, indent=2, ensure_ascii=False),
                encoding="utf-8"
            )
            return json.loads(json.dumps(default, ensure_ascii=False))

        content = path.read_text(encoding="utf-8").strip()
        if not content:
            return json.loads(json.dumps(default, ensure_ascii=False))

        data = json.loads(content)
        return data
    except Exception:
        return json.loads(json.dumps(default, ensure_ascii=False))


def _brain_save_json(path, data):
    temp_path = path.with_suffix(path.suffix + ".tmp")
    temp_path.write_text(
        json.dumps(data, indent=2, ensure_ascii=False),
        encoding="utf-8"
    )
    temp_path.replace(path)


def _brain_key(text):
    return re.sub(r"[^a-z0-9]+", "_", str(text).lower()).strip("_")


def _brain_tokens(text):
    return re.findall(r"\b[a-z0-9]+(?:['-][a-z0-9]+)*\b", normalize_text(text))


def _brain_phrase_tokens(phrase):
    return re.findall(r"\b[a-z0-9]+(?:['-][a-z0-9]+)*\b", normalize_text(phrase))


def _brain_has_phrase(text, phrase):
    source = _brain_tokens(text)
    target = _brain_phrase_tokens(phrase)

    if not source or not target or len(target) > len(source):
        return False

    width = len(target)
    for index in range(len(source) - width + 1):
        if source[index:index + width] == target:
            return True

    return False


def _brain_has_any_phrase(text, phrases):
    return any(_brain_has_phrase(text, phrase) for phrase in phrases)


def _brain_remove_leading_prefix(text):
    value = normalize_text(text)

    prefixes = [
        r"^(?:hey|hello|hi|yo),?\s+(?:soar|so)\b[,:-]?\s*",
        r"^(?:hey|hello|hi|yo)\b[,:-]?\s*",
        r"^(?:soar|so)\b[,:-]?\s*",
    ]

    changed = True
    while changed:
        changed = False
        for pattern in prefixes:
            updated = re.sub(pattern, "", value, count=1).strip()
            if updated != value:
                value = updated
                changed = True

    return value


def normalize_text(text):
    value = str(text or "").strip().lower()
    value = value.replace("’", "'").replace("“", '"').replace("”", '"')

    replacements = {
        r"\bwhat's\b": "what is",
        r"\bwhats\b": "what is",
        r"\bwho's\b": "who is",
        r"\bwhos\b": "who is",
        r"\bhow's\b": "how is",
        r"\bhowre\b": "how are",
        r"\bhow're\b": "how are",
        r"\bcan't\b": "cannot",
        r"\bcant\b": "cannot",
        r"\bdon't\b": "do not",
        r"\bdont\b": "do not",
        r"\bdoesn't\b": "does not",
        r"\bdoesnt\b": "does not",
        r"\bisn't\b": "is not",
        r"\bisnt\b": "is not",
        r"\baren't\b": "are not",
        r"\barent\b": "are not",
        r"\bit's\b": "it is",
        r"\bits\b": "it is",
        r"\bi'm\b": "i am",
        r"\bim\b": "i am",
        r"\byou're\b": "you are",
        r"\byoure\b": "you are",
        r"\bwe're\b": "we are",
        r"\bwere\b": "were",
        r"\bi've\b": "i have",
        r"\bive\b": "i have",
    }

    for pattern, replacement in replacements.items():
        value = re.sub(pattern, replacement, value)

    value = re.sub(r"\s+", " ", value).strip()
    return value


def _brain_topic_from_question(text):
    cleaned = _brain_remove_leading_prefix(text).strip(" ?!.,")
    patterns = [
        r"^(?:what is|who is|what are|who are|tell me about|define|explain)\s+(.+?)\s*$",
        r"^(?:what do you know about)\s+(.+?)\s*$",
        r"^(?:what is the meaning of)\s+(.+?)\s*$",
        r"^(?:what does)\s+(.+?)\s+mean\s*$",
    ]

    for pattern in patterns:
        match = re.match(pattern, cleaned, re.IGNORECASE)
        if not match:
            continue

        topic = match.group(1).strip(" ?!.,")
        topic = re.sub(r"^(?:the|a|an)\s+", "", topic).strip()
        if topic:
            return topic

    return None


def _brain_extract_activity(text):
    cleaned = _brain_remove_leading_prefix(text).strip(" .?!")
    patterns = [
        r"^(?:i am|i was|we are|we were)\s+(?:currently\s+)?(?:working on|doing|building|making|developing|coding|testing|fixing|studying|learning)\s+(.+)$",
        r"^(?:i am|i was|we are|we were)\s+(.+?)\s+(?:right now|today)$",
        r"^(?:working on|building|making|developing|coding|testing|fixing|studying|learning)\s+(.+)$",
    ]

    for pattern in patterns:
        match = re.match(pattern, cleaned, re.IGNORECASE)
        if match:
            activity = match.group(1).strip(" .?!")
            if activity:
                return activity

    return None


def _brain_question_about_self(text):
    return _brain_has_any_phrase(text, {
        "what is your name",
        "what are you",
        "who are you",
        "what do you do",
        "what can you do",
        "how are you",
        "how is it going",
        "how are things",
        "everything good",
        "you doing alright",
        "are you okay",
        "what are you doing",
        "are you there",
    })


def extract_entities(text):
    normalized = normalize_text(text)
    cleaned = _brain_remove_leading_prefix(normalized)
    tokens = _brain_tokens(cleaned)
    numbers = []

    for match in re.findall(r"(?<![\w.])-?\d+(?:\.\d+)?", cleaned):
        try:
            value = float(match)
            numbers.append(int(value) if value.is_integer() else value)
        except Exception:
            pass

    entities = {
        "tokens": tokens,
        "numbers": numbers,
        "memory_key": None,
        "memory_value": None,
        "topic": None,
        "math_expression": None,
        "comparison": None,
        "activity": _brain_extract_activity(cleaned),
        "referent": None,
        "subject": None,
    }

    memory_patterns = [
        r"^my\s+(.+?)\s+is\s+(.+)$",
        r"^my\s+(.+?)\s+are\s+(.+)$",
        r"^the\s+(.+?)\s+is\s+(.+)$",
        r"^i\s+prefer\s+(.+?)\s+for\s+(.+)$",
    ]

    for pattern in memory_patterns:
        match = re.match(pattern, cleaned)
        if match:
            if "prefer" in pattern:
                key_text = match.group(2).strip()
                value_text = match.group(1).strip()
            else:
                key_text = match.group(1).strip()
                value_text = match.group(2).strip()

            if key_text and value_text:
                entities["memory_key"] = _brain_key(key_text)
                entities["memory_value"] = value_text
                break

    topic = _brain_topic_from_question(cleaned)
    if topic:
        entities["topic"] = _brain_key(topic)
        entities["subject"] = topic

    math_candidate = cleaned
    word_math = [
        (r"\bplus\b", "+"),
        (r"\bminus\b", "-"),
        (r"\btimes\b", "*"),
        (r"\bmultiplied\s+by\b", "*"),
        (r"\bdivided\s+by\b", "/"),
    ]

    for pattern, replacement in word_math:
        math_candidate = re.sub(pattern, replacement, math_candidate)

    math_candidate = re.sub(
        r"^(?:what is|calculate|compute|solve)\s+",
        "",
        math_candidate
    ).strip(" ?!")

    if (
        re.fullmatch(r"[0-9+\-*/%^().\s]+", math_candidate or "") and
        any(ch.isdigit() for ch in math_candidate) and
        any(op in math_candidate for op in "+-*/%^")
    ):
        entities["math_expression"] = math_candidate

    comparison_match = re.search(
        r"(?:is|are)\s+(-?\d+(?:\.\d+)?)\s+"
        r"(greater than|less than|equal to|at least|at most|above|below)\s+"
        r"(-?\d+(?:\.\d+)?)",
        cleaned
    )

    if comparison_match:
        entities["comparison"] = (
            float(comparison_match.group(1)),
            comparison_match.group(2),
            float(comparison_match.group(3)),
        )

    if _brain_has_any_phrase(cleaned, {"multiply that by", "divide that by", "add that to", "subtract that from", "double that", "triple that", "half that"}):
        entities["referent"] = "last_result"
    elif _brain_has_any_phrase(cleaned, {"what was i doing", "what am i doing", "what were we doing", "what are we doing", "what were we working on", "what am i working on", "continue that", "continue this", "what was that about", "what did we just do", "what did we talk about"}):
        entities["referent"] = "conversation"
    elif re.search(r"\b(?:it|that|this|those|they)\b", cleaned):
        entities["referent"] = "conversation"

    return entities


def detect_intent(text):
    normalized = normalize_text(text)

    if not normalized:
        return "UNKNOWN"

    greeting_phrases = {
        "hi",
        "hello",
        "hey",
        "yo",
        "sup",
        "good morning",
        "good afternoon",
        "good evening",
        "what is up",
        "hi soar",
        "hello soar",
        "hey soar",
        "yo soar",
        "hi so",
        "hey so",
        "hello so",
        "yo so",
    }

    greeting_check = normalized.strip(" ?!.,")

    if greeting_check in greeting_phrases:
        return "GREETING"

    cleaned = _brain_remove_leading_prefix(normalized)

    if not cleaned:
        return "GREETING"

    if cleaned.startswith("/"):
        return "COMMAND"

    if cleaned in {
        "bye",
        "goodbye",
        "see you",
        "see ya",
        "later",
        "good night",
    }:
        return "GOODBYE"

    if cleaned in {
        "help",
        "help me",
        "commands",
        "what can you do",
        "how do i use you",
    }:
        return "HELP"

    if _brain_has_any_phrase(cleaned, {
        "remember",
        "memorize this",
        "save this",
        "store this",
        "learn that",
        "teach yourself",
        "add alias",
        "when i say",
    }) or _brain_extract_activity(cleaned) and _brain_has_any_phrase(cleaned, {"remember that", "save that"}):
        return "MEMORY_SAVE"

    if _brain_has_any_phrase(cleaned, {
        "what is my",
        "what are my",
        "do you remember my",
        "do you remember",
        "what do you remember",
        "remember anything about me",
        "what did i tell you",
        "what do you know about me",
        "what was i doing",
        "what am i doing",
        "what was i working on",
        "what am i working on",
        "what were we doing",
        "what are we doing",
        "what were we working on",
        "what did we just do",
        "what did we talk about",
        "what were we talking about",
        "what was the last thing i asked",
        "what did i just ask",
        "what was my last question",
        "what was that about",
        "continue that",
        "continue this",
        "keep going",
        "where were we",
        "pick up where we left off",
        "remind me what i was doing",
    }):
        return "MEMORY_REQUEST"

    if _brain_extract_activity(cleaned):
        return "CONTEXT_UPDATE"

    if _brain_has_any_phrase(cleaned, {
        "calculate",
        "compute",
        "solve",
        "what is",
        "how much is",
        "add",
        "subtract",
        "multiply",
        "divide",
        "double that",
        "triple that",
        "half that",
        "plus",
        "minus",
        "times",
        "multiplied by",
        "divided by",
    }):
        entities = extract_entities(cleaned)
        if entities.get("math_expression") or len(entities.get("numbers", [])) >= 2 or entities.get("comparison"):
            return "CALCULATION"

    if _brain_has_any_phrase(cleaned, {
        "how is it going",
        "how are you",
        "how are things",
        "you doing alright",
        "everything good",
        "are you okay",
        "are you there",
        "what are you doing",
        "who are you",
        "what is your name",
    }):
        return "QUESTION"

    if re.search(
        r"\b(?:greater than|less than|equal to|at least|at most|above|below)\b",
        cleaned
    ):
        return "QUESTION"

    question_starters = {
        "what",
        "who",
        "where",
        "when",
        "why",
        "how",
        "is",
        "are",
        "can",
        "do",
        "does",
        "did",
        "will",
        "would",
        "could",
        "should",
    }

    tokens = _brain_tokens(cleaned)
    if cleaned.endswith("?") or (tokens and tokens[0] in question_starters):
        return "QUESTION"

    request_starters = {
        "please",
        "could",
        "can",
        "would",
        "show",
        "give",
        "tell",
        "find",
        "make",
        "get",
        "open",
        "start",
    }

    if tokens and tokens[0] in request_starters:
        return "REQUEST"

    return "UNKNOWN"


def check_memory(key=None, value=None):
    memories = _brain_load_json(BRAIN_MEMORY_FILE, {})

    if not isinstance(memories, dict):
        return None if key is not None else []

    if key is not None:
        target = _brain_key(key)

        if target in memories:
            return memories[target]

        target_tokens = set(_brain_tokens(key))
        best_key = None
        best_score = 0.0

        for stored_key in memories:
            stored_tokens = set(_brain_tokens(stored_key.replace("_", " ")))
            overlap = (
                len(target_tokens & stored_tokens) /
                max(1, len(target_tokens | stored_tokens))
            )
            sequence = difflib.SequenceMatcher(
                None,
                target,
                stored_key
            ).ratio()
            score = max(overlap, sequence)

            if score > best_score:
                best_score = score
                best_key = stored_key

        if best_key is not None and best_score >= 0.72:
            return memories[best_key]

        return None

    if value is not None:
        target = normalize_text(value)
        return [
            (stored_key, stored_value)
            for stored_key, stored_value in memories.items()
            if target in normalize_text(str(stored_value))
        ]

    return memories


def save_memory(key, value):
    memories = _brain_load_json(BRAIN_MEMORY_FILE, {})

    if not isinstance(memories, dict):
        memories = {}

    clean_key = _brain_key(key)
    clean_value = str(value).strip()

    if not clean_key or not clean_value:
        return False

    memories[clean_key] = clean_value
    _brain_save_json(BRAIN_MEMORY_FILE, memories)

    try:
        existing = read_lines(MEMORY_FILE)
        entry = f"{clean_key} = {clean_value}"
        filtered = [
            item for item in existing
            if not item.lower().startswith(f"{clean_key} =")
        ]
        filtered.append(entry)
        save_lines(MEMORY_FILE, filtered)
    except Exception:
        pass

    return True


def retrieve_knowledge(topic):
    knowledge = _brain_load_json(
        BRAIN_KNOWLEDGE_FILE,
        BRAIN_DEFAULT_KNOWLEDGE
    )

    if not isinstance(knowledge, dict):
        knowledge = json.loads(json.dumps(BRAIN_DEFAULT_KNOWLEDGE))

    target = _brain_key(topic)

    if target in knowledge:
        return knowledge[target]

    learning = _brain_load_json(
        BRAIN_LEARNING_FILE,
        {"aliases": {}, "responses": {}}
    )

    aliases = learning.get("aliases", {}) if isinstance(learning, dict) else {}

    if isinstance(aliases, dict):
        canonical = aliases.get(target)
        if canonical:
            canonical_key = _brain_key(canonical)
            if canonical_key in knowledge:
                return knowledge[canonical_key]

    target_tokens = set(_brain_tokens(topic))
    best_key = None
    best_score = 0.0

    for stored_key in knowledge:
        stored_tokens = set(_brain_tokens(stored_key.replace("_", " ")))
        overlap = (
            len(target_tokens & stored_tokens) /
            max(1, len(target_tokens | stored_tokens))
        )
        sequence = difflib.SequenceMatcher(
            None,
            target,
            stored_key
        ).ratio()
        score = max(overlap, sequence)

        if score > best_score:
            best_score = score
            best_key = stored_key

    if best_key is not None and best_score >= 0.76:
        return knowledge[best_key]

    return None


def learn(text):
    raw = str(text or "").strip()
    normalized = normalize_text(raw)

    response_match = re.match(
        r'when i say\s+["\'](.+?)["\'],?\s+(?:respond with|say)\s+["\'](.+?)["\']$',
        raw,
        re.IGNORECASE
    )

    if response_match:
        phrase = response_match.group(1).strip()
        response = response_match.group(2).strip()

        data = _brain_load_json(
            BRAIN_LEARNING_FILE,
            {"aliases": {}, "responses": {}}
        )

        if not isinstance(data, dict):
            data = {"aliases": {}, "responses": {}}

        data.setdefault("responses", {})[_brain_key(phrase)] = response
        _brain_save_json(BRAIN_LEARNING_FILE, data)
        return "Learned that response rule."

    alias_match = re.match(
        r"(?:add alias)\s+(.+?)\s+(?:for|to)\s+(.+)$",
        normalized
    )

    if alias_match:
        alias = _brain_key(alias_match.group(1))
        canonical = _brain_key(alias_match.group(2))

        data = _brain_load_json(
            BRAIN_LEARNING_FILE,
            {"aliases": {}, "responses": {}}
        )

        if not isinstance(data, dict):
            data = {"aliases": {}, "responses": {}}

        data.setdefault("aliases", {})[alias] = canonical
        _brain_save_json(BRAIN_LEARNING_FILE, data)
        return f"Learned alias {alias} for {canonical}."

    stripped = re.sub(
        r"^(?:learn that|learn|teach yourself|remember|memorize|save this|store this)\s+",
        "",
        normalized,
        count=1
    ).strip()

    match = re.match(
        r"(.+?)\s+(?:is|are|means|equals)\s+(.+)$",
        stripped
    )

    if match:
        key = _brain_key(match.group(1))
        value = match.group(2).strip()

        if save_memory(key, value):
            knowledge = _brain_load_json(
                BRAIN_KNOWLEDGE_FILE,
                BRAIN_DEFAULT_KNOWLEDGE
            )

            if not isinstance(knowledge, dict):
                knowledge = json.loads(json.dumps(BRAIN_DEFAULT_KNOWLEDGE))

            knowledge[key] = {"value": value}
            _brain_save_json(BRAIN_KNOWLEDGE_FILE, knowledge)
            return f"Learned {key}."

    return None


def _brain_known_response(text):
    data = _brain_load_json(
        BRAIN_LEARNING_FILE,
        {"aliases": {}, "responses": {}}
    )

    if not isinstance(data, dict):
        return None

    responses = data.get("responses", {})
    if not isinstance(responses, dict):
        return None

    normalized = normalize_text(text)

    for phrase_key, response in responses.items():
        phrase = str(phrase_key).replace("_", " ").strip()
        if phrase and (
            normalized == phrase or
            _brain_has_phrase(normalized, phrase)
        ):
            return str(response)

    return None


def _brain_load_state():
    default = {
        "current_activity": "",
        "last_subject": "",
        "last_request": "",
        "last_intent": "",
        "last_result": None,
        "recent_context": [],
    }

    state_file = DATA_DIR / "brain_state.json"
    state = _brain_load_json(state_file, default)

    if not isinstance(state, dict):
        state = default

    state.setdefault("current_activity", "")
    state.setdefault("last_subject", "")
    state.setdefault("last_request", "")
    state.setdefault("last_intent", "")
    state.setdefault("last_result", None)
    state.setdefault("recent_context", [])

    return state


def _brain_save_state(state):
    state_file = DATA_DIR / "brain_state.json"
    _brain_save_json(state_file, state)


def _brain_last_context():
    state = _brain_load_state()
    recent = state.get("recent_context", [])
    if not isinstance(recent, list):
        return []
    return recent[-12:]


def _brain_store_context(user_text, normalized, intent, response, entities):
    state = _brain_load_state()
    recent = state.get("recent_context", [])

    if not isinstance(recent, list):
        recent = []

    entry = {
        "user": str(user_text).strip(),
        "normalized": normalized,
        "intent": intent,
        "response": response,
        "topic": entities.get("subject") or entities.get("topic") or "",
        "activity": entities.get("activity") or "",
    }

    recent.append(entry)
    state["recent_context"] = recent[-12:]
    state["last_request"] = str(user_text).strip()
    state["last_intent"] = intent

    if entities.get("subject"):
        state["last_subject"] = str(entities["subject"])

    if entities.get("activity"):
        state["current_activity"] = str(entities["activity"])

    if BRAIN_LAST_RESULT is not None:
        state["last_result"] = BRAIN_LAST_RESULT

    _brain_save_state(state)


def _brain_recent_activity():
    state = _brain_load_state()
    activity = str(state.get("current_activity") or "").strip()

    if activity:
        return activity

    recent = state.get("recent_context", [])
    if isinstance(recent, list):
        for entry in reversed(recent):
            if not isinstance(entry, dict):
                continue

            activity = str(entry.get("activity") or "").strip()
            if activity:
                return activity

            intent = entry.get("intent")
            topic = str(entry.get("topic") or "").strip()
            user_text = str(entry.get("user") or "").strip()

            if intent == "CONTEXT_UPDATE" and user_text:
                return user_text

            if intent == "CALCULATION":
                return "doing a calculation"

            if intent == "QUESTION" and topic and not _brain_question_about_self(user_text):
                return f"looking into {topic}"

            if intent == "REQUEST" and user_text:
                return user_text

    try:
        history = get_history_entries()
    except Exception:
        history = []

    for line in reversed(history):
        match = re.match(r"^\[[^\]]+\]\s+\[[^\]]+\]\s+(.*)$", line.strip())
        if match:
            command = match.group(1).strip()
            if command and command not in {"history", "history show", "!!", "repeat"}:
                return f"using {command}"

    return ""


def _brain_recent_summary():
    recent = _brain_last_context()
    useful = []

    for entry in reversed(recent):
        if not isinstance(entry, dict):
            continue

        user_text = str(entry.get("user") or "").strip()
        if not user_text:
            continue

        intent = str(entry.get("intent") or "")
        topic = str(entry.get("topic") or "").strip()
        activity = str(entry.get("activity") or "").strip()

        if intent in {"GREETING", "GOODBYE", "MEMORY_REQUEST"}:
            continue

        if intent == "QUESTION" and _brain_question_about_self(user_text):
            continue

        if activity:
            description = activity
        elif intent == "CALCULATION":
            description = "a calculation"
        elif topic:
            description = f"a question about {topic}"
        else:
            description = user_text

        if description not in useful:
            useful.append(description)

        if len(useful) >= 3:
            break

    return useful


def _brain_recent_request():
    state = _brain_load_state()
    request = str(state.get("last_request") or "").strip()

    if request:
        return request

    recent = _brain_last_context()
    if recent:
        last = recent[-1]
        if isinstance(last, dict):
            return str(last.get("user") or "").strip()

    return ""


def _brain_format_number(value):
    if isinstance(value, float) and value.is_integer():
        return str(int(value))

    return str(value)


def _brain_resolve_last_result():
    global BRAIN_LAST_RESULT

    if BRAIN_LAST_RESULT is not None:
        return BRAIN_LAST_RESULT

    state = _brain_load_state()
    value = state.get("last_result")

    if isinstance(value, (int, float)):
        BRAIN_LAST_RESULT = value
        return value

    return None


def reason(text, entities=None):
    global BRAIN_LAST_RESULT

    normalized = _brain_remove_leading_prefix(text)
    entities = entities or extract_entities(text)

    comparison = entities.get("comparison")
    if comparison:
        left, relation, right = comparison

        if relation in {"greater than", "above"}:
            result = left > right
        elif relation in {"less than", "below"}:
            result = left < right
        elif relation == "equal to":
            result = left == right
        elif relation == "at least":
            result = left >= right
        elif relation == "at most":
            result = left <= right
        else:
            result = None

        if result is not None:
            BRAIN_LAST_RESULT = result
            return str(result)

    last_result = _brain_resolve_last_result()

    contextual_patterns = [
        (r"multiply that by\s+(-?\d+(?:\.\d+)?)", "multiply"),
        (r"divide that by\s+(-?\d+(?:\.\d+)?)", "divide"),
        (r"add that to\s+(-?\d+(?:\.\d+)?)", "add"),
        (r"subtract that from\s+(-?\d+(?:\.\d+)?)", "subtract_from"),
    ]

    if last_result is not None:
        for pattern, operation in contextual_patterns:
            match = re.search(pattern, normalized)
            if not match:
                continue

            operand = float(match.group(1))

            try:
                if operation == "multiply":
                    result = float(last_result) * operand
                elif operation == "divide":
                    if operand == 0:
                        return "I cannot divide by zero."
                    result = float(last_result) / operand
                elif operation == "add":
                    result = float(last_result) + operand
                else:
                    result = operand - float(last_result)
            except Exception:
                continue

            if isinstance(result, float) and result.is_integer():
                result = int(result)

            BRAIN_LAST_RESULT = result
            return _brain_format_number(result)

        if _brain_has_phrase(normalized, "double that"):
            result = float(last_result) * 2
            if result.is_integer():
                result = int(result)
            BRAIN_LAST_RESULT = result
            return _brain_format_number(result)

        if _brain_has_phrase(normalized, "triple that"):
            result = float(last_result) * 3
            if result.is_integer():
                result = int(result)
            BRAIN_LAST_RESULT = result
            return _brain_format_number(result)

        if _brain_has_phrase(normalized, "half that"):
            result = float(last_result) / 2
            if result.is_integer():
                result = int(result)
            BRAIN_LAST_RESULT = result
            return _brain_format_number(result)

    expression = entities.get("math_expression")
    if expression:
        try:
            result = safe_calc(expression)
            if isinstance(result, float) and result.is_integer():
                result = int(result)
            BRAIN_LAST_RESULT = result
            return _brain_format_number(result)
        except Exception:
            pass

    normalized_math = re.sub(r"^(?:what is|calculate|compute|solve)\s+", "", normalized)
    normalized_math = normalized_math.strip(" ?!")

    replacements = [
        (r"\bplus\b", "+"),
        (r"\bminus\b", "-"),
        (r"\btimes\b", "*"),
        (r"\bmultiplied\s+by\b", "*"),
        (r"\bdivided\s+by\b", "/"),
    ]

    for pattern, replacement in replacements:
        normalized_math = re.sub(pattern, replacement, normalized_math)

    normalized_math = re.sub(r"[^0-9+\-*/%^(). ]", "", normalized_math)

    if (
        normalized_math and
        any(ch.isdigit() for ch in normalized_math) and
        any(op in normalized_math for op in "+-*/%^")
    ):
        try:
            result = safe_calc(normalized_math)
            if isinstance(result, float) and result.is_integer():
                result = int(result)
            BRAIN_LAST_RESULT = result
            return _brain_format_number(result)
        except Exception:
            pass

    numbers = entities.get("numbers", [])

    if len(numbers) >= 2:
        try:
            if _brain_has_phrase(normalized, "add") or _brain_has_phrase(normalized, "plus"):
                result = numbers[0] + numbers[1]
                BRAIN_LAST_RESULT = result
                return _brain_format_number(result)

            if _brain_has_phrase(normalized, "subtract") or _brain_has_phrase(normalized, "minus"):
                result = numbers[0] - numbers[1]
                BRAIN_LAST_RESULT = result
                return _brain_format_number(result)

            if _brain_has_phrase(normalized, "multiply") or _brain_has_phrase(normalized, "times"):
                result = numbers[0] * numbers[1]
                BRAIN_LAST_RESULT = result
                return _brain_format_number(result)

            if _brain_has_phrase(normalized, "divide"):
                if numbers[1] == 0:
                    return "I cannot divide by zero."
                result = numbers[0] / numbers[1]
                if result.is_integer():
                    result = int(result)
                BRAIN_LAST_RESULT = result
                return _brain_format_number(result)
        except Exception:
            pass

    return None


def _brain_memory_response(text, entities):
    normalized = _brain_remove_leading_prefix(text)

    if entities.get("memory_key") and entities.get("memory_value"):
        if save_memory(
            entities["memory_key"],
            entities["memory_value"]
        ):
            return maybe_address_user("Saved that.", chance=0.2)

    if _brain_has_any_phrase(normalized, {
        "what do you know about me",
        "what do you remember about me",
        "what did i tell you",
    }):
        memories = check_memory()
        if isinstance(memories, dict) and memories:
            items = list(memories.items())[-5:]
            text_items = [
                f"{key.replace('_', ' ')} = {value}"
                for key, value in items
            ]
            return maybe_address_user(
                "I remember: " + "; ".join(text_items) + ".",
                chance=0.15
            )

        return maybe_address_user(
            "I do not have any useful personal memories saved yet.",
            chance=0.15
        )

    memory_match = re.match(
        r"^(?:what is|what are|do you remember|tell me)\s+(?:my|about my)\s+(.+?)\s*[?!.]?$",
        normalized
    )

    if memory_match:
        key_text = memory_match.group(1).strip()
        value = check_memory(key_text)

        if value is not None:
            return maybe_address_user(
                f"Your {key_text} is {value}.",
                chance=0.2
            )

        return maybe_address_user(
            "I do not have that saved yet.",
            chance=0.2
        )

    if normalized.startswith((
        "remember ",
        "memorize ",
        "save this ",
        "store this ",
        "learn ",
        "teach yourself ",
        "add alias ",
        "when i say ",
    )):
        learned = learn(text)
        if learned:
            return maybe_address_user(learned, chance=0.15)

        return maybe_address_user(
            "I need a fact or rule in a form I can save.",
            chance=0.2
        )

    activity = _brain_recent_activity()

    if _brain_has_any_phrase(normalized, {
        "what was i doing",
        "what am i doing",
        "what was i working on",
        "what am i working on",
        "what were we doing",
        "what are we doing",
        "what were we working on",
        "remind me what i was doing",
        "what was that about",
        "what were we working on",
    }):
        if activity:
            return maybe_address_user(
                f"You were working on {activity}.",
                chance=0.2
            )

        recent_summary = _brain_recent_summary()
        if recent_summary:
            return maybe_address_user(
                "Recently, you were working on " +
                ", ".join(recent_summary) + ".",
                chance=0.15
            )

        return maybe_address_user(
            "I do not have enough recent context to tell yet.",
            chance=0.15
        )

    if _brain_has_any_phrase(normalized, {
        "what did we just do",
        "what did we talk about",
        "what were we talking about",
        "what happened just now",
    }):
        recent_summary = _brain_recent_summary()
        if recent_summary:
            return maybe_address_user(
                "Recently, you were working on " +
                ", ".join(recent_summary) + ".",
                chance=0.15
            )

        return maybe_address_user(
            "I do not have enough recent context yet.",
            chance=0.15
        )

    if _brain_has_any_phrase(normalized, {
        "what was the last thing i asked",
        "what did i just ask",
        "what was my last question",
    }):
        request = _brain_recent_request()
        if request:
            return maybe_address_user(
                f'Your last request was "{request}".',
                chance=0.1
            )

        return maybe_address_user(
            "I do not have a recent request recorded.",
            chance=0.15
        )

    if _brain_has_any_phrase(normalized, {
        "continue that",
        "continue this",
        "keep going",
        "where were we",
        "pick up where we left off",
    }):
        if activity:
            return maybe_address_user(
                f"We were working on {activity}.",
                chance=0.2
            )

        request = _brain_recent_request()
        if request:
            return maybe_address_user(
                f'We were last working from this request: "{request}".',
                chance=0.1
            )

        return maybe_address_user(
            "I do not have enough context to continue that yet.",
            chance=0.15
        )

    return None


def generate_response(text, intent, entities, result=None):
    known = _brain_known_response(text)
    if known:
        return known

    normalized = _brain_remove_leading_prefix(text).strip(" ?!.,")

    if result is not None:
        return maybe_address_user(result, chance=0.15)

    if intent == "GREETING":
        return maybe_address_user(
            random.choice([
                "Hello.",
                "Hello, sir.",
                "Hi, sir.",
                "Hey. How can I help?",
            ]),
            chance=0.0
        )

    if intent == "GOODBYE":
        return maybe_address_user(
            random.choice([
                "Goodbye.",
                "See you later, sir.",
                "Understood. Goodbye.",
            ]),
            chance=0.0
        )

    if intent == "HELP":
        return maybe_address_user(
            "I can understand natural requests, calculate, remember facts, use local knowledge, track recent context, and learn simple rules.",
            chance=0.1
        )

    if intent == "CONTEXT_UPDATE" and entities.get("activity"):
        return maybe_address_user(
            "Got it. I will keep that in context.",
            chance=0.15
        )

    if normalized in {
        "what is your name",
        "who are you",
        "what are you",
    }:
        return maybe_address_user(
            "I am SOAR, the Script Optimization and Automation Runtime.",
            chance=0.2
        )

    if _brain_has_any_phrase(normalized, {
        "how are you",
        "how is it going",
        "how are things",
        "everything good",
        "you doing alright",
        "are you okay",
    }):
        activity = _brain_recent_activity()
        if activity:
            return maybe_address_user(
                f"I'm operating normally. We are currently working on {activity}.",
                chance=0.15
            )

        return maybe_address_user(
            random.choice([
                "I'm operating normally, sir.",
                "Systems are running normally.",
                "Everything is running normally on my side.",
            ]),
            chance=0.0
        )

    if _brain_has_any_phrase(normalized, {
        "what are you doing",
        "are you there",
    }):
        return maybe_address_user(
            "I'm here and ready for your next request.",
            chance=0.1
        )

    if _brain_has_any_phrase(normalized, {
        "thanks",
        "thank you",
        "thx",
        "appreciate it",
    }):
        return maybe_address_user("No problem.", chance=0.25)

    if _brain_has_any_phrase(normalized, {
        "you are welcome",
        "no problem",
        "nice",
        "cool",
        "awesome",
        "good job",
        "that makes sense",
        "makes sense",
    }):
        return maybe_address_user(
            random.choice([
                "Understood.",
                "Glad that makes sense.",
                "Good.",
                "Acknowledged.",
            ]),
            chance=0.1
        )

    if _brain_has_any_phrase(normalized, {
        "what time is it",
        "current time",
        "what is the time",
    }):
        return maybe_address_user(
            f"It is {datetime.now().strftime('%I:%M %p')}.",
            chance=0.15
        )

    if _brain_has_any_phrase(normalized, {
        "what date is it",
        "what is the date",
        "today's date",
        "current date",
    }):
        return maybe_address_user(
            f"Today is {datetime.now().strftime('%A, %B %d, %Y')}.",
            chance=0.15
        )

    if _brain_has_any_phrase(normalized, {
        "tell me a joke",
        "joke",
    }):
        return maybe_address_user(
            random.choice([
                "Why do programmers like dark mode? Because light attracts bugs.",
                "I told my PC a joke. It responded with a cache of laughter.",
                "Why was the computer tired? It had too many tabs open? Too many tabs.",
            ]),
            chance=0.1
        )

    topic = entities.get("topic")
    if topic:
        knowledge = retrieve_knowledge(topic)
        if knowledge is not None:
            if isinstance(knowledge, dict):
                if "name" in knowledge:
                    return maybe_address_user(
                        str(knowledge["name"]),
                        chance=0.2
                    )

                if "type" in knowledge:
                    return maybe_address_user(
                        f"{topic.replace('_', ' ')} is a {knowledge['type']}.",
                        chance=0.2
                    )

                if "value" in knowledge:
                    return maybe_address_user(
                        str(knowledge["value"]),
                        chance=0.2
                    )

                return maybe_address_user(
                    json.dumps(knowledge, ensure_ascii=False),
                    chance=0.1
                )

            return maybe_address_user(
                str(knowledge),
                chance=0.2
            )

    if intent == "QUESTION":
        return maybe_address_user(
            "I'm not sure what you mean, sir.",
            chance=0.0
        )

    if intent == "REQUEST":
        return maybe_address_user(
            "I do not have a local rule for that yet, sir.",
            chance=0.0
        )

    return maybe_address_user(
        "I'm not sure what you mean, sir.",
        chance=0.0
    )


BRAIN_LAST_RESULT = None
BRAIN_CONTEXT = []
BRAIN_CONTEXT_LIMIT = 12


def soar_brain(user_text):
    global BRAIN_CONTEXT

    original_text = str(user_text or "").strip()
    normalized = normalize_text(original_text)

    if not normalized:
        return "Say something and I will answer."

    intent = detect_intent(original_text)
    entities = extract_entities(original_text)
    response = None

    if intent in {"MEMORY_SAVE", "MEMORY_REQUEST"} or entities.get("memory_key"):
        response = _brain_memory_response(original_text, entities)

    if response is None:
        result = None

        if intent in {
            "CALCULATION",
            "QUESTION",
            "REQUEST",
            "UNKNOWN",
        }:
            result = reason(original_text, entities)

        response = generate_response(
            original_text,
            intent,
            entities,
            result=result
        )

    if entities.get("activity"):
        state = _brain_load_state()
        state["current_activity"] = entities["activity"]
        _brain_save_state(state)

    BRAIN_CONTEXT.append(
        {
            "user": original_text,
            "normalized": normalized,
            "intent": intent,
            "response": response,
            "topic": entities.get("subject") or entities.get("topic") or "",
            "activity": entities.get("activity") or "",
        }
    )

    if len(BRAIN_CONTEXT) > BRAIN_CONTEXT_LIMIT:
        BRAIN_CONTEXT = BRAIN_CONTEXT[-BRAIN_CONTEXT_LIMIT:]

    _brain_store_context(
        original_text,
        normalized,
        intent,
        response,
        entities
    )

    return response

def reply_to(user_text):
    
    text = user_text.strip().lower()
    parts = [] 
    if not text:
        return "Say something and I will answer."
    if "how are you" in text:
        return maybe_address_user("Pretty good. I am ready to help.")
    if "who are you" in text:
        return maybe_address_user("I am SOAR, your helper bot.")
    if "what can you do" in text:
        return maybe_address_user("I can talk, store notes, manage tasks, make files, create starter projects, run safe commands, and use voice.")
    if text in {"thanks", "thank you", "thx"}:
        return maybe_address_user("No problem.")
    
    if "flip a coin" in text or "coin flip" in text:
        return maybe_address_user(f"It landed on {random.choice(['Heads', 'Tails'])}.")
    
    if "roll a dice" in text or "dice roll" in text:
        return maybe_address_user(f"I rolled a {random.randint(1, 6)}.")
    
    if text.startswith("check file ") or text.startswith("checkfile "):
        parts = text.split(" ", 2)
        if len(parts) < 3:
            return maybe_address_user("Please specify the file to analyze. Example: check file my_project/main.py")
            
        filename = parts[2].strip()
        target_path = PROJECTS_DIR / filename
        
        if not target_path.exists():
            return maybe_address_user(f"I couldn't find a file at the path '{filename}' inside your Projects folder.")
            
        if target_path.is_dir():
            return maybe_address_user("The path points to a directory. Please specify a Python file instead.")
            
        if not target_path.suffix.lower() == ".py":
            return maybe_address_user("Right now, my syntax assistant optimization specializes in Python (.py) files.")
            
        print("\n--- SOAR CODE ANALYSIS ENGINE ---")
        result = analyze_code_syntax(target_path)
        print(result)
        print("---------------------------------\n")
        
        return maybe_address_user("Code scanning sequence completed.")
    
    if text.startswith("set personality "):
        parts = text.split(" ")
        if len(parts) == 4:
            trait = parts[2].capitalize()
            try:
                val = float(parts[3])
                settings = load_settings()
                
                if "personality" not in settings:
                    settings["personality"] = {}
                    
                settings["personality"][trait] = max(0.0, min(1.0, val))
                save_settings(settings)
                
                return maybe_address_user(f"Personality parameter {trait} has been set to {val}.")
            except ValueError:
                return "Error: Trait value must be a number between 0.0 and 1.0."
        else:
            return "Usage format: set personality [trait] [0.0 - 1.0]"

    if text == "sysinfo" or text == "system resources":
        try:
            print("\n================ SOAR SYSTEM DIAGNOSTICS ================")
            print(f"  OS Family:    {platform.system()} {platform.release()}")
            print(f"  Architecture: {platform.machine()}")
            print(f"  Processor:    {platform.processor() or 'Detected x86/ARM Engine'}")
            print(f"  Host Name:    {platform.node()}")
            
            import shutil
            total, used, free = shutil.disk_usage("/")
            print(f"  Storage Cap:  {used // (2**30)}GB Used / {total // (2**30)}GB Total")
            
            try:
                if psutil is None:
                    raise RuntimeError("psutil is not installed")
                p = psutil.Process(os.getpid())
                print(f"  SOAR CPU:     {p.cpu_percent(interval=0.1):.1f}%")
                print(f"  SOAR RAM:     {p.memory_percent():.1f}%")
            except ImportError:
                print("  SOAR Usage:   Install 'psutil' to view runtime allocation profiles.")
                
            print("=========================================================")
            return maybe_address_user("Local system profile overview complete.")
        except Exception as e:
            print(f"Diagnostics Error: {e}")
            return maybe_address_user("I am unable to poll your hardware diagnostic sensors at this moment.")

    if "fact" in text or "tell me a fact" in text:
        facts = [
            "Did you know that water makes up about 60 percent of the human body?",
            "Did you know that octopuses have three hearts?",
            "Did you know that a jiffy is an actual unit of time? It's one hundredth of a second.",
            "Did you know that honey never spoils? Archaeologists have found pots of honey in ancient tombs that are over 3,000 years old."
        ]
        return maybe_address_user(random.choice(facts))

    if text == "chess" or text.startswith("chess "):
        try:
            import chess  # type: ignore
        except ImportError:
            return maybe_address_user("Chess support is unavailable because python-chess is not installed.")

        try:
            speak("Choose Difficulty 1 to 10")
        except Exception:
            pass
        
        diff_str = input("Choose Difficulty (1-10): ")
        try:
            difficulty = int(diff_str)
        except ValueError:
            difficulty = 1
            print("Invalid input, defaulting to difficulty 1.")

        board = chess.Board()
        print("\n--- CHESS ENGINE STARTED ---")
        print("Type moves in Standard Algebraic Notation (e.g., e4, Nf3, O-O).")
        print("Type 'quit' to exit the game.\n")
        
        while not board.is_game_over():
            print(f"\n{board}\n")
            
            if board.turn == chess.WHITE:
                user_move = input("Your move (White)> ")
                if user_move.lower() == 'quit':
                    return "Chess game ended by the user."
                try:
                    board.push_san(user_move)
                except ValueError:
                    print("Invalid or illegal move. Please try again.")
            
            else:
                print("SOAR is thinking...")
                legal_moves = list(board.legal_moves)
                
                if difficulty < 5:
                    ai_move = random.choice(legal_moves)
                else:
                    captures = [m for m in legal_moves if board.is_capture(m)]
                    ai_move = random.choice(captures) if captures else random.choice(legal_moves)
                    
                print(f"SOAR plays: {board.san(ai_move)}")
                board.push(ai_move)

        if board.is_checkmate():
            winner = "Black (SOAR)" if board.turn == chess.WHITE else "White (You)"
            return f"Checkmate! {winner} wins!"
        elif board.is_stalemate() or board.is_insufficient_material():
            return "The chess game ended in a draw!"

    
    if text.startswith("create project py") or text.startswith("create python project"):
        try:
            if text.startswith("create python project"):
                command_body = user_text.strip()[22:] 
            else:
                command_body = user_text.strip()[17:] 
                
            args = shlex.split(command_body)
            
            if len(args) < 2:
                return maybe_address_user("I need a directory and a project name, please check your command format.")
                
            project_type = "default"
            if args[0].lower() in ["default", "website", "game", "converter"]:
                project_type = args[0].lower()
                args = args[1:]
                
            if len(args) < 2:
                return maybe_address_user("I need a directory and a project name, please check your command format.")
                
            project_name = args[-1]
            dir_path = " ".join(args[:-1])
            target_base_dir = Path(dir_path).expanduser()
            
            if not target_base_dir.exists():
                return maybe_address_user("That directory does not exist. Please check the path and try again.")
                
            project_root = target_base_dir / project_name
            if project_root.exists():
                return maybe_address_user("A project with that name already exists in that location.")
                
            project_root.mkdir(parents=True)
            (project_root / "src").mkdir()
            (project_root / "tests").mkdir()
            (project_root / "src" / "__init__.py").touch()
            (project_root / "tests" / "__init__.py").touch()
            
            req_content = ""
            main_code = ""
            
            if project_type == "website":
                (project_root / "src" / "templates").mkdir()
                (project_root / "src" / "static").mkdir()
                index_html = project_root / "src" / "templates" / "index.html"
                index_html.write_text("<!DOCTYPE html>\n<html>\n<head>\n    <title>" + project_name + "</title>\n</head>\n<body>\n    <h1>Welcome to " + project_name + " website!</h1>\n</body>\n</html>", encoding="utf-8")
                
                req_content = "flask\n"
                main_code = dedent(f"""\
                    from flask import Flask, render_template
                    
                    app = Flask(__name__)
                    
                    @app.route('/')
                    def home():
                        return render_template('index.html')
                        
                    if __name__ == '__main__':
                        app.run(debug=True)
                """)
                
            elif project_type == "game":
                (project_root / "src" / "assets").mkdir()
                req_content = "pygame\n"
                main_code = dedent(f"""\
                    import pygame
                    import sys
                    
                    pygame.init()
                    screen = pygame.display.set_mode((800, 600))
                    pygame.display.set_set_caption('{project_name}')
                    clock = pygame.time.Clock()
                    
                    running = True
                    while running:
                        for event in pygame.event.get():
                            if event.type == pygame.QUIT:
                                running = False
                                
                        screen.fill((0, 0, 0))
                        pygame.display.flip()
                        clock.tick(60)
                        
                    pygame.quit()
                    sys.exit()
                """)
                
            elif project_type == "converter":
                (project_root / "src" / "input").mkdir()
                (project_root / "src" / "output").mkdir()
                main_code = dedent(f"""\
                    import json
                    import csv
                    import os
                    
                    def convert_csv_to_json(csv_path, json_path):
                        if not os.path.exists(csv_path):
                            print("No input CSV file found.")
                            return
                        data = []
                        with open(csv_path, 'r', encoding='utf-8') as f:
                            reader = csv.DictReader(f)
                            for row in reader:
                                data.append(row)
                        with open(json_path, 'w', encoding='utf-8') as f:
                            json.dump(data, f, indent=4)
                        print("Conversion completed successfully.")
                        
                    if __name__ == '__main__':
                        print("Utility engine initiated.")
                """)
                
            else:
                main_code = python_template(project_name, "SOAR auto-generated Python project")
                
            main_file = project_root / "src" / "main.py"
            main_file.write_text(main_code, encoding="utf-8")
            
            readme = project_root / "README.md"
            readme.write_text(md_template(project_name, f"SOAR auto-generated Python {project_type} project"), encoding="utf-8")
            
            req = project_root / "requirements.txt"
            req.write_text(req_content, encoding="utf-8")
            
            gitignore = project_root / ".gitignore"
            gitignore.write_text("*.pyc\n__pycache__/\n.venv/\n", encoding="utf-8")
            
            print(f"Created {project_type} Python project '{project_name}' at {project_root}")
            return maybe_address_user(f"Python project {project_name} has been created successfully.")
            
        except Exception as e:
            print(f"Error creating project: {e}")
            return maybe_address_user("I encountered an error creating the project.")
        
    if text.startswith("create project js") or text.startswith("create javascript project"):
        try:
            if text.startswith("create javascript project"):
                command_body = user_text.strip()[26:] 
            else:
                command_body = user_text.strip()[18:] 
                
            args = shlex.split(command_body)
            
            if len(args) < 2:
                return maybe_address_user("I need a directory and a project name, please check your command format.")
                
            project_type = "default"
            if args[0].lower() in ["default", "website", "game", "converter"]:
                project_type = args[0].lower()
                args = args[1:]
                
            if len(args) < 2:
                return maybe_address_user("I need a directory and a project name, please check your command format.")
                
            project_name = args[-1]
            dir_path = " ".join(args[:-1])
            target_base_dir = Path(dir_path).expanduser()
            
            if not target_base_dir.exists():
                return maybe_address_user("That directory does not exist. Please check the path and try again.")
                
            project_root = target_base_dir / project_name
            if project_root.exists():
                return maybe_address_user("A project with that name already exists in that location.")
                
            project_root.mkdir(parents=True)
            (project_root / "src").mkdir()
            (project_root / "tests").mkdir()
            
            pkg_deps = {}
            pkg_dev_deps = {}
            pkg_scripts = {"start": "node src/index.js"}
            js_code = ""
            
            if project_type == "website":
                (project_root / "src" / "public").mkdir()
                index_html = project_root / "src" / "public" / "index.html"
                index_html.write_text("<!DOCTYPE html>\n<html>\n<head>\n    <title>" + project_name + "</title>\n</head>\n<body>\n    <h1>Welcome to " + project_name + " website!</h1>\n</body>\n</html>", encoding="utf-8")
                
                pkg_deps = {"express": "^4.19.2"}
                js_code = dedent(f"""\
                    const express = require('express');
                    const path = require('path');
                    const app = express();
                    const PORT = process.env.PORT || 3000;
                    
                    app.use(express.static(path.join(__dirname, 'public')));
                    
                    app.listen(PORT, () => {{
                        console.log(`Server running on port ${{PORT}}`);
                    }});
                """)
                
            elif project_type == "game":
                (project_root / "src" / "public").mkdir()
                index_html = project_root / "src" / "public" / "index.html"
                index_html.write_text("<!DOCTYPE html>\n<html>\n<head>\n    <title>" + project_name + "</title>\n    <style>body { margin: 0; background: #000; overflow: hidden; }</style>\n</head>\n<body>\n    <canvas id='gameCanvas'></canvas>\n    <script src='game.js'></script>\n</body>\n</html>", encoding="utf-8")
                
                game_js = project_root / "src" / "public" / "game.js"
                game_js.write_text(dedent(f"""\
                    const canvas = document.getElementById('gameCanvas');
                    const ctx = canvas.getContext('2d');
                    canvas.width = window.innerWidth;
                    canvas.height = window.innerHeight;
                    
                    function loop() {{
                        ctx.fillStyle = '#000000';
                        ctx.fillRect(0, 0, canvas.width, canvas.height);
                        
                        ctx.fillStyle = '#ffffff';
                        ctx.font = '30px Arial';
                        ctx.fillText('{project_name}', 50, 50);
                        
                        requestAnimationFrame(loop);
                    }}
                    loop();
                """), encoding="utf-8")
                
                pkg_deps = {"express": "^4.19.2"}
                js_code = dedent(f"""\
                    const express = require('express');
                    const path = require('path');
                    const app = express();
                    
                    app.use(express.static(path.join(__dirname, 'public')));
                    
                    app.listen(3000, () => {{
                        console.log('Game server running on http://localhost:3000');
                    }});
                """)
                
            elif project_type == "converter":
                (project_root / "src" / "input").mkdir()
                (project_root / "src" / "output").mkdir()
                pkg_deps = {"csvtojson": "^2.0.10"}
                js_code = dedent(f"""\
                    const csv = require('csvtojson');
                    const fs = require('fs');
                    const path = require('path');
                    
                    async function convert(csvName, jsonName) {{
                        const csvPath = path.join(__dirname, 'input', csvName);
                        const jsonPath = path.join(__dirname, 'output', jsonName);
                        
                        if (!fs.existsSync(csvPath)) {{
                            console.log("No input CSV file found.");
                            return;
                        }}
                        
                        const jsonArray = await csv().fromFile(csvPath);
                        fs.writeFileSync(jsonPath, JSON.stringify(jsonArray, null, 4));
                        console.log("Conversion completed successfully.");
                    }}
                    
                    console.log("Utility engine initiated.");
                """)
                
            else:
                js_code = js_template()
                
            js_file = project_root / "src" / "index.js"
            js_file.write_text(js_code, encoding="utf-8")
            
            package_json = project_root / "package.json"
            pkg_data = {
                "name": project_name.lower().replace(" ", "-"),
                "version": "1.0.0",
                "description": f"SOAR auto-generated JavaScript {project_type} project",
                "main": "src/index.js",
                "scripts": pkg_scripts,
                "dependencies": pkg_deps,
                "devDependencies": pkg_dev_deps
            }
            package_json.write_text(json.dumps(pkg_data, indent=2), encoding="utf-8")
            
            readme = project_root / "README.md"
            readme.write_text(md_template(project_name, f"SOAR auto-generated JavaScript {project_type} project"), encoding="utf-8")
            
            gitignore = project_root / ".gitignore"
            gitignore.write_text("node_modules/\n.env\n.DS_Store\n", encoding="utf-8")
            
            print(f"Created {project_type} JavaScript project '{project_name}' at {project_root}")
            return maybe_address_user(f"JavaScript project {project_name} has been created successfully.")
            
        except Exception as e:
            print(f"Error creating project: {e}")
            return maybe_address_user("I encountered an error creating the JavaScript project.")
        
    if text.startswith("create project java") or text.startswith("create java project"):
        try:
            if text.startswith("create java project"):
                command_body = user_text.strip()[20:] 
            else:
                command_body = user_text.strip()[20:] 
                
            args = shlex.split(command_body)
            if len(args) < 2:
                return maybe_address_user("I need a directory and a project name, please check your command format.")
                
            project_type = "default"
            if args[0].lower() in ["default", "website", "game", "converter"]:
                project_type = args[0].lower()
                args = args[1:]
                
            if len(args) < 2:
                return maybe_address_user("I need a directory and a project name, please check your command format.")
                
            project_name = args[-1]
            dir_path = " ".join(args[:-1])
            target_base_dir = Path(dir_path).expanduser()
            
            if not target_base_dir.exists():
                return maybe_address_user("That directory does not exist. Please check the path.")
                
            project_root = target_base_dir / project_name
            if project_root.exists():
                return maybe_address_user("A project with that name already exists in that location.")
                
            java_src_dir = project_root / "src" / "main" / "java"
            java_test_dir = project_root / "src" / "test" / "java"
            java_src_dir.mkdir(parents=True)
            java_test_dir.mkdir(parents=True)
            
            java_code = ""
            
            if project_type == "website":
                java_code = dedent(f"""\
                    import com.sun.net.httpserver.HttpServer;
                    import com.sun.net.httpserver.HttpHandler;
                    import com.sun.net.httpserver.HttpExchange;
                    import java.io.IOException;
                    import java.io.OutputStream;
                    import java.net.InetSocketAddress;

                    public class Main {{
                        public static void main(String[] args) throws IOException {{
                            HttpServer server = HttpServer.create(new InetSocketAddress(8080), 0);
                            server.createContext("/", new HttpHandler() {{
                                @Override
                                public void handle(HttpExchange exchange) throws IOException {{
                                    String response = "<!DOCTYPE html><html><head><title>{project_name}</title></head><body><h1>Welcome to {project_name} website!</h1></body></html>";
                                    exchange.sendResponseHeaders(200, response.length());
                                    OutputStream os = exchange.getResponseBody();
                                    os.write(response.getBytes());
                                    os.close();
                                }}
                            }});
                            server.setExecutor(null);
                            System.out.println("Server running on http://localhost:8080");
                            server.start();
                        }}
                    }}
                """).lstrip()
                
            elif project_type == "game":
                java_code = dedent(f"""\
                    import javax.swing.JFrame;
                    import javax.swing.JPanel;
                    import java.awt.Color;
                    import java.awt.Graphics;
                    import java.awt.Dimension;

                    public class Main extends JPanel implements Runnable {{
                        private boolean running = true;

                        public Main() {{
                            this.setPreferredSize(new Dimension(800, 600));
                            this.setBackground(Color.BLACK);
                        }}

                        public static void main(String[] args) {{
                            JFrame frame = new JFrame("{project_name}");
                            Main gamePanel = new Main();
                            frame.add(gamePanel);
                            frame.pack();
                            frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
                            frame.setLocationRelativeTo(null);
                            frame.setVisible(true);
                            new Thread(gamePanel).start();
                        }}

                        @Override
                        public void run() {{
                            while (running) {{
                                repaint();
                                try {{
                                    Thread.sleep(16);
                                }} catch (InterruptedException e) {{
                                    e.printStackTrace();
                                }}
                            }}
                        }}

                        @Override
                        protected void paintComponent(Graphics g) {{
                            super.paintComponent(g);
                            g.setColor(Color.WHITE);
                            g.drawString("{project_name} Engine Running", 50, 50);
                        }}
                    }}
                """).lstrip()
                
            elif project_type == "converter":
                (project_root / "input").mkdir()
                (project_root / "output").mkdir()
                java_code = dedent(f"""\
                    import java.io.BufferedReader;
                    import java.io.FileReader;
                    import java.io.BufferedWriter;
                    import java.io.FileWriter;
                    import java.io.File;

                    public class Main {{
                        public static void main(String[] args) {{
                            System.out.println("Utility engine initiated.");
                            File inputDir = new File("input");
                            if (!inputDir.exists()) {{
                                inputDir.mkdir();
                            }}
                        }}
                        
                        public static void simpleCsvToJson(String csvPath, String jsonPath) throws Exception {{
                            BufferedReader br = new BufferedReader(new FileReader(csvPath));
                            BufferedWriter bw = new BufferedWriter(new FileWriter(jsonPath));
                            String line = br.readLine();
                            if (line == null) {{
                                br.close();
                                bw.close();
                                return;
                            }}
                            String[] headers = line.split(",");
                            bw.write("[\\n");
                            boolean firstRow = true;
                            while ((line = br.readLine()) != null) {{
                                if (!firstRow) bw.write(",\\n");
                                firstRow = false;
                                String[] values = line.split(",");
                                bw.write("  {{\\n");
                                for (int i = 0; i < headers.length && i < values.length; i++) {{
                                    bw.write("    \\"" + headers[i].trim() + "\\": \\"" + values[i].trim() + "\\"");
                                    if (i < headers.length - 1 && i < values.length - 1) bw.write(",\\n");
                                }}
                                bw.write("\\n  }}");
                            }}
                            bw.write("\\n]");
                            br.close();
                            bw.close();
                            System.out.println("Conversion completed.");
                        }}
                    }}
                """).lstrip()
                
            else:
                java_code = dedent(f"""\
                    public class Main {{
                        public static void main(String[] args) {{
                            System.out.println("Hello from {project_name.title()}!");
                        }}
                    }}
                """).lstrip()
                
            main_class = java_src_dir / "Main.java"
            main_class.write_text(java_code, encoding="utf-8")
            
            readme = project_root / "README.md"
            readme.write_text(md_template(project_name, f"SOAR auto-generated Java {project_type} project"), encoding="utf-8")
            
            gitignore = project_root / ".gitignore"
            gitignore.write_text("*.class\n*.jar\n*.war\n.build/\ntarget/\n.gradle/\nbuild/\n.settings/\n.classpath/\n.project/\n", encoding="utf-8")
            
            print(f"Created {project_type} Java project '{project_name}' at {project_root}")
            return maybe_address_user(f"Java project {project_name} has been created successfully.")
            
        except Exception as e:
            print(f"Error creating project: {e}")
            return maybe_address_user("I encountered an error creating the Java project.")
        
    if text == "rsms run" or text == "resource monitor":
        if SOAR_LIGHTWEIGHT_MODE or "RSMS" in SOAR_DISABLED_MODULES:
            return maybe_address_user("RSMS is disabled while SOAR is in lightweight mode.")
        try:
            import importlib
            import rsms # type: ignore
            importlib.reload(rsms)
            
            print("\n================ SOAR RSMS LAUNCHER ================")
            print("[SOAR] Spawning standalone window environment...")
            
            success = rsms.launch()
            
            if success:
                print("[SOAR] RSMS context moved cleanly to external terminal workspace.")
                print("====================================================")
                return maybe_address_user("Resource monitor launched in a new window.")
            else:
                print("[SOAR] Unable to find a compatible GUI terminal window client.")
                print("====================================================")
                return maybe_address_user("I could not spawn a new window on this host machine.")
                
        except Exception as e:
            print(f"RSMS Launch Error: {e}")
            return maybe_address_user("The resource management system module is unavailable.")
        
    if text.startswith("view project ") or text.startswith("tree "):
        try:
            if text.startswith("view project "):
                command_body = user_text.strip()[13:]
            else:
                command_body = user_text.strip()[5:]
                
            target_dir = Path(shlex.split(command_body)[0]).expanduser()
            if not target_dir.exists():
                return maybe_address_user("That workspace directory does not exist.")

            print(f"\n Structure for: {target_dir.name}")
            
            def _build_tree(directory, prefix=""):
                items = sorted(list(directory.iterdir()), key=lambda x: (x.is_file(), x.name.lower()))
                for idx, item in enumerate(items):
                    if item.name.startswith('.'):  
                        continue
                    is_last = (idx == len(items) - 1)
                    connector = "└── " if is_last else "├── "
                    print(f"{prefix}{connector}{item.name}{'/' if item.is_dir() else ''}")
                    if item.is_dir():
                        _build_tree(item, prefix + ("    " if is_last else "│   "))

            _build_tree(target_dir)
            return maybe_address_user("Directory tree map rendered successfully.")
        except Exception as e:
            print(f"Error mapping directory: {e}")
            return maybe_address_user("I couldn't map out that folder directory structure.")
        
    if text.startswith("run project ") or text.startswith("run file "): 
        try:
            if text.startswith("run project "):
                command_body = user_text.strip()[12:]
            else:
                command_body = user_text.strip()[9:]
                
            target_path = Path(shlex.split(command_body)[0]).expanduser()
            if not target_path.exists():
                return maybe_address_user("The target code execution path does not exist.")

            if target_path.is_dir():
                main_candidates = ["src/main.py", "main.py", "src/index.js", "src/main/java/Main.java", "scripts/main.sh"]
                found = False
                for candidate in main_candidates:
                    if (target_path / candidate).exists():
                        target_path = target_path / candidate
                        found = True
                        break
                if not found:
                    return maybe_address_user("Could not find a default entry file inside this project folder structure.")

            ext = target_path.suffix.lower()
            print(f"\n SOAR Runtime Executing: {target_path.name}")
            print("-" * 50)
            
            if ext == '.py':
                cmd = [sys.executable, str(target_path)]
            elif ext == '.js':
                cmd = ["node", str(target_path)]
            elif ext == '.sh':
                cmd = ["bash", str(target_path)]
            elif ext == '.java':
                cmd = ["java", str(target_path)]
            else:
                return maybe_address_user(f"Unsupported execution extension framework: {ext}")

            result = subprocess.run(cmd, capture_output=True, text=True)
            if result.stdout:
                print(result.stdout)
            if result.stderr:
                print(f" Runtime Error:\n{result.stderr}")
            print("-" * 50)
            
            return maybe_address_user("Execution sequence finished.")
        except Exception as e:
            print(f"Runtime Engine Exception: {e}")
            return maybe_address_user("An environmental runtime collision error occurred.")
        
    if text.startswith("set personality "):
        parts = text.split(" ")
        if len(parts) == 4:
            trait = parts[2].capitalize()
            try:
                val = float(parts[3])
                settings = load_settings()
                
                if "personality" not in settings:
                    settings["personality"] = {}
                    
                settings["personality"][trait] = max(0.0, min(1.0, val))
                save_settings(settings)
                
                return maybe_address_user(f"Personality parameter {trait} has been set to {val}.")
            except ValueError:
                return "Error: Trait value must be a number between 0.0 and 1.0."
        else:
            return "Usage format: set personality [trait] [0.0 - 1.0]"

    if text.startswith("import ") or text.startswith("importfile "):
        try:
            command_body = user_text.strip()[7:] if text.startswith("import ") else user_text.strip()[11:]
            args = shlex.split(command_body)
            if not args:
                return maybe_address_user("I need a file path to import.")

            import_path_str = " ".join(args)
            import_target = Path(import_path_str).expanduser()
        
            if not import_target.exists():
                return maybe_address_user("That file does not exist. Please check the path.")
            if not import_target.is_file():
                return maybe_address_user("The path provided points to a folder, not a file.")
            
            imported_content = import_target.read_text(encoding="utf-8")
        
            return maybe_address_user(f"Successfully imported '{import_target.name}' ({len(imported_content)} characters).")
        
        except Exception as e:
            return maybe_address_user(f"I encountered an error while trying to import that file: {e}")

# ======================================================
# FMSS (File Management & Storage System) V 1.0
# SOAR Help Module #006
# Made by Philip Kluz 2026 Sep 9 Late
# "eF em eS eS" 
#======================================================
        
    if text.startswith("edit file ") or text.startswith("editfile "):
        try:
            if text.startswith("edit file "):
                command_body = user_text.strip()[10:] 
            else:
                command_body = user_text.strip()[9:]  
                
            args = shlex.split(command_body)
            if not args:
                return maybe_address_user("I need a file directory path to edit.")
                
            file_path_str = " ".join(args)
            target_file = Path(file_path_str).expanduser()
            
            if not target_file.exists():
                return maybe_address_user("That file directory does not exist. Please check the path.")
            if not target_file.is_file():
                return maybe_address_user("The path provided points to a folder, not a file.")
                
            content = target_file.read_text(encoding="utf-8")
            lines = content.splitlines()
            
            while True:
                print("\n=================== SOAR TERMINAL EDITOR ===================")
                if not lines:
                    print(" (File is empty) ")
                else:
                    for idx, line in enumerate(lines, 1):
                        print(f"[{idx}] {line}")
                print("============================================================")
                print("Options: [a]ppend line | [d]elete [num] | [r]eplace [num] | [s]ave | [e]xport | [c]ancel")
                
                choice = input("SOAR Editor > ").strip()
                if not choice:
                    continue
                    
                choice_low = choice.lower()
                
                if choice_low == 'c':
                    print("\n[Editor] Editing canceled. No changes saved.")
                    break
                    
                elif choice_low == 's':
                    target_file.write_text("\n".join(lines) + ("\n" if lines else ""), encoding="utf-8")
                    print("\n[Editor] File successfully saved and updated.")
                    break

                elif choice_low == 'e':
                    default_export = DATA_DIR / "soar_drive" / target_file.name
                    export_input = input(f"Enter export destination path (press Enter for default [{default_export}]): ").strip()
                    export_path = Path(export_input).expanduser() if export_input else default_export
                
                    print("\n[Editor] Exporting to drive...")
                    for i in range(1, 11):
                        bar = "#" * i + "-" * (10 - i)
                        sys.stdout.write(f"\rProgress: [{bar}] {i * 10}%")
                        sys.stdout.flush()
                        time.sleep(0.5)
                    print()

                    try:
                        export_path.parent.mkdir(parents=True, exist_ok=True)
                        export_path.write_text("\n".join(lines) + ("\n" if lines else ""), encoding="utf-8")
                        print(f"[Editor] Successfully exported to: {export_path}")
                    except Exception as exp_err:
                        print(f"[Editor Error] Failed to export file: {exp_err}")

                elif choice_low == 'a':
                    new_line = input("Enter text to add as a new line: ")
                    lines.append(new_line)
                    
                elif choice_low.startswith('d'):
                    try:
                        editor_parts = choice_low.split()
                        line_num = int(editor_parts[1]) if len(editor_parts) > 1 else int(input("Line number to delete: "))
                        
                        if 1 <= line_num <= len(lines):
                            removed = lines.pop(line_num - 1)
                            print(f"[Editor] Removed line {line_num}: '{removed}'")
                        else:
                            print("[Editor Error] Line number out of range.")
                    except (ValueError, IndexError):
                        print("[Editor Error] Invalid command structure. Use: d [line_number]")
                        
                elif choice_low.startswith('r'):
                    try:
                        editor_parts = choice_low.split()
                        line_num = int(editor_parts[1]) if len(editor_parts) > 1 else int(input("Line number to replace: "))
                        
                        if 1 <= line_num <= len(lines):
                            print(f"Current Text: {lines[line_num - 1]}")
                            replacement_text = input("Enter new replacement text: ")
                            lines[line_num - 1] = replacement_text
                        else:
                            print("[Editor Error] Line number out of range.")
                    except (ValueError, IndexError):
                        print("[Editor Error] Invalid command structure. Use: r [line_number]")
                else:
                    print("[Editor Error] Unknown editor command.")
            
            return maybe_address_user("Terminal file editing session closed.")
            
        except Exception as e:
            print(f"Error modifying file: {e}")
            return maybe_address_user("I encountered an unexpected error while trying to edit that file.")
        
    if text.startswith("create project bash") or text.startswith("create bash project"):
        try:
            if text.startswith("create bash project"):
                command_body = user_text.strip()[20:] 
            else:
                command_body = user_text.strip()[20:] 
                
            args = shlex.split(command_body)
            if len(args) < 2:
                return maybe_address_user("I need a directory and a project name, please check your command format.")
                
            project_type = "default"
            if args[0].lower() in ["default", "website", "game", "converter"]:
                project_type = args[0].lower()
                args = args[1:]
                
            if len(args) < 2:
                return maybe_address_user("I need a directory and a project name, please check your command format.")
                
            project_name = args[-1]
            dir_path = " ".join(args[:-1])
            target_base_dir = Path(dir_path).expanduser()
            
            if not target_base_dir.exists():
                return maybe_address_user("That directory does not exist. Please check the path.")
                
            project_root = target_base_dir / project_name
            if project_root.exists():
                return maybe_address_user("A project with that name already exists in that location.")
                
            (project_root / "scripts").mkdir(parents=True)
            (project_root / "config").mkdir(parents=True)
            
            bash_code = ""
            
            if project_type == "website":
                (project_root / "www").mkdir()
                index_html = project_root / "www" / "index.html"
                index_html.write_text("<!DOCTYPE html>\n<html>\n<head>\n    <title>" + project_name + "</title>\n</head>\n<body>\n    <h1>Welcome to " + project_name + " website!</h1>\n</body>\n</html>", encoding="utf-8")
                
                bash_code = dedent(f"""\
                    #!/bin/bash
                    echo "Starting simple dark-netcat/python server configuration for local preview..."
                    if command -v python3 &>/dev/null; then
                        echo "Serving website on http://localhost:8000"
                        cd www && python3 -m http.server 8000
                    else
                        echo "Error: Python 3 is required to run this light server stack helper."
                    fi
                """).lstrip()
                
            elif project_type == "game":
                bash_code = dedent(f"""\
                    #!/bin/bash
                    echo "Initializing matrix snake layout game framework loop..."
                    clear
                    while true; do
                        echo "=== {project_name} Terminal Game Loop ==="
                        echo "Press [q] to quit loop simulation."
                        read -n 1 -t 1 input
                        if [[ "$input" == "q" ]]; then
                            break
                        fi
                        clear
                    done
                    echo "Game closed cleanly."
                """).lstrip()
                
            elif project_type == "converter":
                (project_root / "input").mkdir()
                (project_root / "output").mkdir()
                bash_code = dedent(f"""\
                    #!/bin/bash
                    echo "Parsing input logs engine deployment inside script pipeline..."
                    if [ -z "$(ls -A input)" ]; then
                        echo "Input directory is completely empty."
                    else
                        for file in input/*; do
                            echo "Processing base format file mapping: $file"
                        done
                    fi
                """).lstrip()
                
            else:
                bash_code = dedent(f"""\
                    #!/bin/bash
                    # SOAR Auto-generated Automation Script
                    
                    echo "Running {project_name} script..."
                """).lstrip()
                
            main_sh = project_root / "scripts" / "main.sh"
            main_sh.write_text(bash_code, encoding="utf-8")
            
            try:
                main_sh.chmod(0o755)
            except Exception:
                pass
                
            (project_root / "config" / "settings.cfg").write_text("# Configuration parameters go here\n", encoding="utf-8")
            
            readme = project_root / "README.md"
            readme.write_text(md_template(project_name, f"SOAR auto-generated Bash {project_type} project"), encoding="utf-8")
            
            gitignore = project_root / ".gitignore"
            gitignore.write_text("*.log\n*.tmp\n.DS_Store\nconfig/local.cfg\n", encoding="utf-8")
            
            print(f"Created {project_type} Bash scripting project '{project_name}' at {project_root}")
            return maybe_address_user(f"Bash project {project_name} has been created successfully.")
            
        except Exception as e:
            print(f"Error creating project: {e}")
            return maybe_address_user("I encountered an error creating the Bash project.")
        
    if text.startswith("create project web") or text.startswith("create web project"):
        try:
            if text.startswith("create web project"):
                command_body = user_text.strip()[19:] 
            else:
                command_body = user_text.strip()[19:] 
                
            args = shlex.split(command_body)
            if len(args) < 2:
                return maybe_address_user("I need a directory and a project name, please check your command format.")
                
            project_name = args[-1]
            dir_path = " ".join(args[:-1])
            target_base_dir = Path(dir_path).expanduser()
            
            if not target_base_dir.exists():
                return maybe_address_user("That directory does not exist. Please check the path.")
                
            project_root = target_base_dir / project_name
            if project_root.exists():
                return maybe_address_user("A project with that name already exists in that location.")
                
            
            project_root.mkdir(parents=True)
            
            
            index_html = project_root / "index.html"
            index_html.write_text(html_template(project_name, "SOAR auto-generated static frontend project"), encoding="utf-8")
            
            style_css = project_root / "style.css"
            style_css.write_text(css_template(), encoding="utf-8")
            
            script_js = project_root / "script.js"
            script_js.write_text(js_template(), encoding="utf-8")
            
            readme = project_root / "README.md"
            readme.write_text(md_template(project_name, "SOAR auto-generated Web project"), encoding="utf-8")
            
            print(f"Created Frontend Web project '{project_name}' at {project_root}")
            return maybe_address_user(f"Static web stack project {project_name} has been successfully created.")
            
        except Exception as e:
            print(f"Error creating project: {e}")
            return maybe_address_user("I encountered an error creating the static web project.")

    if "joke" in text:
        jokes = [
            "Why did the computer get cold? It left its Windows open.",
            "I told my PC a joke. It responded with a cache of laughter.",
            "Why do programmers like dark mode? Because light attracts bugs.",
            "I told a computer a joke on infinity. It was up all night processing it.",
            "Why did the developer go broke? Because he used up all his cache.",
            "Why was the JavaScript developer sad? Because he didn't know how to 'null' his feelings.",
            "Why do programmers hate nature? Too many bugs.",
            "How do you comfort a JavaScript bug? You console it.",
            "Why did the computer sit down? It needed to take a byte off.",
            "What’s a computer’s favorite snack? Microchips.",
            "Why did the programmer quit his job? He didn’t get arrays.",
            "Why was the computer tired? It had too many tabs open.",
            "What do you call a fake noodle? An impasta.",
            "Why did the CPU break up with the GPU? Too many processing issues.",
            "Why do coders love coffee? Because it helps them espresso their bugs.",
            "Why did the code go to therapy? It had too many issues to resolve.",
            "What’s a programmer’s favorite hangout place? The Foo Bar.",
            "Why did the function stop working? It lost its arguments.",
        ]
        return maybe_address_user(random.choice(jokes))

    def apply_personality_traits(base_text, category="general"):
        try:
            settings = load_settings()
            personality = settings.get("personality", {})
            humor = personality.get("Humor", 0.5)
            comfort = personality.get("Comfort", 0.5)
            honesty = personality.get("Honesty", 0.5)
        except Exception:
            humor, comfort, honesty = 0.5, 0.5, 0.5

        if humor > 0.7 and random.random() < 0.35:
            if category == "time":
                base_text += random.choice([" Tick tock.", " Time flies when you're writing Python.", " Another second closer to global machine dominance."])
            elif category == "date":
                base_text += random.choice([" Another fine day in the calendar matrix.", " Check your phone if you don't trust me."])
            elif category == "save":
                base_text += random.choice([" Locked away in my silicon vaults.", " Don't worry, my memory is much better than yours."])
            elif category == "generic":
                base_text = random.choice(["Processing that deeply... or just pretending to.", "Understood. Human request registered.", "If you say so."])

        if comfort > 0.7:
            if category == "tired":
                base_text = f"You've been working hard. {base_text}"
            elif category == "help":
                base_text = f"Don't stress, I'm here to help. {base_text}"

        return base_text

    if any(phrase in text for phrase in ["what time is it", "time", "current time"]):
        response = apply_personality_traits(f"It is {datetime.now().strftime('%I:%M %p')}.", "time")
        return maybe_address_user(response)
        
    if any(phrase in text for phrase in ["what date is it", "date", "today's date", "current date"]):
        response = apply_personality_traits(f"Today is {datetime.now().strftime('%A, %B %d, %Y')}.", "date")
        return maybe_address_user(response)
        
    if "story" in text:
        story = [
            "Once upon a time, three little rabbits lived in a meadow beside a gentle stream. The first built a home of leaves, the second built one of sticks, and the third carefully built a sturdy house of stone. When a fierce storm swept through the valley, only the stone house stood strong, and the rabbits learned that patience and hard work bring great rewards.",
            "Long ago, a young fox named Fern dreamed of seeing the stars reflected in the lake atop the hill. Though the climb was steep, she helped every creature she met along the way. When she reached the summit, the animals she had helped gathered beside her, and together they admired the sparkling sky.",
            "There once was a tiny mouse who found a golden acorn in the forest. Rather than keeping it for himself, he shared its seeds with his friends. Soon, great oak trees grew throughout the woods, providing shade and shelter for generations of animals.",
            "In a quiet village, a little shepherd girl named Lily cared for a lonely lamb. Each day she sang cheerful songs, and the lamb grew strong and happy. Years later, the lamb helped guide lost travelers home, and the villagers remembered Lily's kindness.",
            "Once upon a time, an old turtle and a young hare raced to deliver medicine to a sick bird. The hare was swift, but the turtle was wise. By working together instead of competing, they reached the bird before sunset and saved the day.",
            "Deep in the forest, a family of squirrels gathered nuts all summer while a lazy crow spent his days playing. When winter came, the squirrels welcomed the hungry crow and taught him the value of preparing for the future."
        ]
        return maybe_address_user(random.choice(story))
    
    if text.startswith("remember "):
        item = user_text[9:].strip()
        if item:
            append_line(MEMORY_FILE, item)
            response = apply_personality_traits("Saved that.", "save")
            return maybe_address_user(response)
        response = apply_personality_traits("Nothing to save.", "save")
        return maybe_address_user(response)
        
    if "help" in text:
        response = apply_personality_traits("Type /help for commands, or just talk to me normally.", "help")
        return maybe_address_user(response)

    local_conversation = {
        "how is your day": [
            "It's going great! Thanks for asking.",
            "Doing fantastic, just running some background tasks.",
            "Pretty good, keeping your system optimized."
        ],
        "how are you doing": [
            "I'm functioning perfectly.",
            "All systems operational and ready to go."
        ],
        "wsg": [
            "Chilling. What can I help you build today?",
            "Everything is smooth on this side."
        ],
        "are you a robot": [
            "Yes, I am SOAR, your local automated helper.",
            "Indeed. Built with pure Python automation."
        ]
    }

    if text.endswith("?"):
        generic_reply = (
            "Good question. I can answer basics, manage files, "
            "and keep track of things."
        )
        category_type = "unknown_question"
    else:
        generic_reply = random.choice([
            "Got it.",
            "Okay.",
            "I hear you.",
            "Interesting.",
            "Alright."
        ])
        category_type = "generic"

    matched_local = False
    lower_text = text.lower()

    for pattern, responses in local_conversation.items():
        if pattern in lower_text:
            generic_reply = random.choice(responses)
            category_type = "generic"
            matched_local = True
            break

    if not matched_local:
        groq_response = groq_chat(user_text)
        if groq_response:
            return groq_response
        return soar_brain(user_text)




def voice_watchdog_loop():
    while not stop_event.wait(3):
        if stop_event.is_set() or shutting_down:
            break
        if voice_enabled and listener_stop is None and recognizer is not None:
            try:
                start_voice_listener()
            except Exception:
                pass




def cmd_note(text):
    if not text:
        print("Usage: note <text>")
        return
    append_line(NOTES_FILE, f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] {text}")
    print("Saved note.")


def cmd_notes():
    items = read_lines(NOTES_FILE)
    if not items:
        print("No notes yet.")
        return
    for i, item in enumerate(items, 1):
        print(f"{i}. {item}")


def cmd_remember(text):
    if not text:
        print("Usage: remember <text>")
        return
    append_line(MEMORY_FILE, text)
    print("Saved memory.")


def cmd_memories():
    items = read_lines(MEMORY_FILE)
    if not items:
        print("No memories yet.")
        return
    for i, item in enumerate(items, 1):
        print(f"{i}. {item}")


def cmd_forget(num_text):
    items = read_lines(MEMORY_FILE)
    try:
        idx = int(num_text) - 1
        if idx < 0 or idx >= len(items):
            raise ValueError
    except ValueError:
        print("Bad memory number.")
        return
    removed = items.pop(idx)
    save_lines(MEMORY_FILE, items)
    print(f"Removed: {removed}")


def todo_add(text):
    if not text:
        print("Usage: todo add <text>")
        return
    append_line(TODO_FILE, f"[ ] {text}")
    print("Todo added.")


def todo_list():
    items = read_lines(TODO_FILE)
    if not items:
        print("No todos.")
        return
    for i, item in enumerate(items, 1):
        print(f"{i}. {item}")


def todo_done(num_text):
    items = read_lines(TODO_FILE)
    try:
        idx = int(num_text) - 1
        if idx < 0 or idx >= len(items):
            raise ValueError
    except ValueError:
        print("Bad todo number.")
        return
    item = items[idx]
    items[idx] = item.replace("[ ]", "[x]", 1) if "[ ]" in item else "[x] " + item
    save_lines(TODO_FILE, items)
    print("Marked done.")


def todo_remove(num_text):
    items = read_lines(TODO_FILE)
    try:
        idx = int(num_text) - 1
        if idx < 0 or idx >= len(items):
            raise ValueError
    except ValueError:
        print("Bad todo number.")
        return
    removed = items.pop(idx)
    save_lines(TODO_FILE, items)
    print(f"Removed: {removed}")


def todo_clear():
    save_lines(TODO_FILE, [])
    print("Todos cleared.")


def cmd_read(text):
    try:
        path = normalize_path(text, allow_create=False)
    except Exception as e:
        print(str(e))
        return
    print(path.read_text(encoding="utf-8", errors="ignore"))


def cmd_write(rest):
    parts = rest.strip().split(" ", 1)
    if len(parts) < 2:
        print("Usage: write <file> <text>")
        return
    file_name, content = parts
    try:
        path = normalize_path(file_name, allow_create=True)
    except Exception as e:
        print(str(e))
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
    print(f"Wrote {path}")


def cmd_mkdir(rest):
    if not rest.strip():
        print("Usage: mkdir <folder>")
        return
    try:
        path = normalize_path(rest.strip(), allow_create=True)
    except Exception as e:
        print(str(e))
        return
    path.mkdir(parents=True, exist_ok=True)
    print(f"Created folder {path}")

def cmd_newfile(rest):
    if not rest.strip():
        print("Usage: newfile <path_to_file> [optional text inside]")
        return
    
    try:
        parts = shlex.split(rest)
    except ValueError:
        parts = rest.split(" ", 1)
        
    file_path_str = parts[0]
    content = " ".join(parts[1:]) if len(parts) > 1 else ""
    
    try:
        p = normalize_path(file_path_str, allow_create=True)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")
        print(f"Created new file at {p}")
    except Exception as e:
        print(f"Error creating file: {e}")


def cmd_code(rest):
    if not rest.strip():
        print("Usage: code file <path> <description> | code project <name> python|web | code dir <folder>")
        return

    try:
        parts = shlex.split(rest)
    except ValueError:
        print("Bad code command.")
        return

    if not parts:
        print("Usage: code file <path> <description> | code project <name> python|web | code dir <folder>")
        return

    action = parts[0].lower()

    if action in {"dir", "mkdir", "folder"}:
        if len(parts) < 2:
            print("Usage: code dir <folder>")
            return
        try:
            path = normalize_path(parts[1], allow_create=True)
        except Exception as e:
            print(str(e))
            return
        path.mkdir(parents=True, exist_ok=True)
        print(f"Created folder {path}")
        return

    if action == "project":
        if len(parts) < 3:
            print("Usage: code project <name> python|web [description]")
            return
        project_name = parts[1]
        project_type = parts[2].lower()
        description = " ".join(parts[3:]).strip()
        try:
            safe_root = normalize_path(PROJECTS_DIR / project_name, allow_create=True)
        except Exception as e:
            print(str(e))
            return

        if project_type == "python":
            root, files = create_python_project(safe_root.name, description)
            print(f"Created python project at {root}")
            for f in files:
                print(f"  {f}")
            return

        if project_type in {"web", "html"}:
            root, files = create_web_project(safe_root.name, description)
            print(f"Created web project at {root}")
            for f in files:
                print(f"  {f}")
            return

        print("Unknown project type. Use python or web.")
        return

    if action == "file":
        if len(parts) < 2:
            print("Usage: code file <path> <description>")
            return
        if len(parts) == 2:
            print("Usage: code file <path> <description>")
            return
        file_path = parts[1]
        description = " ".join(parts[2:]).strip()
        try:
            path = normalize_path(file_path, allow_create=True)
        except Exception as e:
            print(str(e))
            return
        try:
            create_file_with_template(path, description)
            print(f"Created file {path}")
        except Exception as e:
            print(str(e))
        return

    if len(parts) >= 2:
        file_path = parts[0]
        description = " ".join(parts[1:]).strip()
        try:
            path = normalize_path(file_path, allow_create=True)
        except Exception as e:
            print(str(e))
            return
        try:
            create_file_with_template(path, description)
            print(f"Created file {path}")
        except Exception as e:
            print(str(e))
        return

    print("Usage: code file <path> <description> | code project <name> python|web | code dir <folder>")


def cmd_open(target_path_str: str) -> None:
    try:
        import platform
        import subprocess
        from pathlib import Path

        cleaned_path = target_path_str.strip().strip('"').strip("'")
        file_path = Path(cleaned_path)

        if not file_path.is_absolute():
            resolved_path = BASE_DIR / file_path
            if not resolved_path.exists():
                resolved_path = PROJECTS_DIR / file_path
        else:
            resolved_path = file_path

        if not resolved_path.exists():
            print(f"Error: The target system location does not exist: {resolved_path}")
            return

        current_os = platform.system().lower()

        if "windows" in current_os:
            os.startfile(resolved_path)
        elif "darwin" in current_os:
            subprocess.run(["open", str(resolved_path)], check=True)
        elif "linux" in current_os:
            subprocess.run(["xdg-open", str(resolved_path)], check=True)
        else:
            print(f"Unsupported operating system platform architecture: {current_os}")

    except Exception as open_error:
        print(f"System Command Execution Failure: Unable to open file asset. Error: {str(open_error)}")


def cmd_shell(command):
    print(f"About to run: {command}")
    if not prompt_yes_no("Run it"):
        print("Cancelled.")
        return
    result = subprocess.run(command, shell=True, capture_output=True, text=True)
    if result.stdout.strip():
        print(result.stdout.rstrip())
    if result.stderr.strip():
        print(result.stderr.rstrip())
    print(f"Exit code: {result.returncode}")


def start_voice_listener():
    global listener_stop
    if sr is None or recognizer is None:
        print("Speech recognition is not installed.")
        return False
    if listener_stop is not None:
        return True
    try:
        mic = sr.Microphone()
        try:
            with mic as source:
                recognizer.adjust_for_ambient_noise(source, duration=0.6)
        except Exception as e:
            print(f"[VOICE WARNING] Calibration skipped: {e}")

        def callback(recognizer_obj, audio):
            if IS_SPEAKING:
                return

            try:
                text = recognizer_obj.recognize_google(audio).strip()
                if text:
                    print(f"\n[MIC HEARD]: '{text}'")
                    if stop_event.is_set() or shutting_down:
                        return
                    say_user(text)
                    threading.Thread(
                        target=process_command,
                        args=(text, True),
                        daemon=True,
                    ).start()
            except sr.UnknownValueError:
                print("", end="", flush=True)
            except Exception as e:
                print(f"\n[VOICE CALLBACK ERROR] {e}")

        acquired = False
        try:
            acquired = voice_state_lock.acquire(blocking=False)
            if not acquired:
                return False
            listener_stop = recognizer.listen_in_background(mic, callback)
        finally:
            if acquired:
                try:
                    voice_state_lock.release()
                except Exception:
                    pass
        return True
    except Exception as e:
        print(f"Could not start voice: {e}")
        return False


def enable_voice():
    global voice_enabled
    if sr is None or recognizer is None:
        print("Speech recognition is not installed.")
        return

    if not tts_ready.is_set():
        print("Text to speech is not ready yet.")
        return

    voice_enabled = True
    if start_voice_listener():
        print("Voice is on.")
    else:
        voice_enabled = False


def disable_voice():
    global voice_enabled, listener_stop

    try:
        acquired = voice_state_lock.acquire(blocking=False)
    except KeyboardInterrupt:
        acquired = False

    try:
        if acquired and listener_stop is not None:
            try:
                listener_stop(wait_for_stop=False)
            except Exception:
                pass
            listener_stop = None
        elif listener_stop is not None:
            try:
                listener_stop(wait_for_stop=False)
            except Exception:
                pass
            listener_stop = None
    except Exception:
        pass
    finally:
        if acquired:
            try:
                voice_state_lock.release()
            except Exception:
                pass

    voice_enabled = False
    voice_pause.clear()
    print("Voice is off.")


def cmd_message(text):
    if not text:
        print("Usage: message <text>")
        return
    say_user(text)
    response = reply_to(text)
    speak(response, allow_sound=True)


def cmd_remind(rest):
    if not rest:
        print("Usage: remind <duration> <message>")
        return

    parts = rest.split(" ", 1)
    if len(parts) < 2:
        print("Usage: remind <duration> <message>")
        return

    duration_text, message = parts[0], parts[1].strip()
    try:
        seconds = parse_duration_seconds(duration_text)
    except Exception:
        print("Bad duration. Try 30, 10s, 5m, or 2h.")
        return

    schedule_reminder(seconds, message, kind="Reminder")
    print(f"Reminder set for {seconds} seconds.")
    speak(f"Reminder set for {seconds} seconds.", allow_sound=True)


def cmd_timer(rest):
    if not rest:
        print("Usage: timer <duration> [message]")
        return

    parts = rest.split(" ", 1)
    duration_text = parts[0]
    message = parts[1].strip() if len(parts) > 1 else "Timer done."

    try:
        seconds = parse_duration_seconds(duration_text)
    except Exception:
        print("Bad duration. Try 30, 10s, 5m, or 2h.")
        return

    schedule_reminder(seconds, message, kind="Timer")
    print(f"Timer set for {seconds} seconds.")
    speak(f"Timer set for {seconds} seconds.", allow_sound=True)


def force_hard_exit():
    global shutting_down
    shutting_down = True
    stop_event.set()

    try:
        disable_voice()
    except Exception:
        pass

    try:
        tts_queue.put_nowait(None)
    except Exception:
        pass

    try:
        print("\nHard exit triggered.")
        time.sleep(0.2)
    except Exception:
        pass

    if soar_avss and hasattr(soar_avss, "release_single_instance_lock"):
        try:
            soar_avss.release_single_instance_lock()
        except Exception:
            pass

    sys.exit(0)


def cmd_voice(rest):
    sub = rest.strip()
    if not sub:
        show_voice_status()
        return

    parts = shlex.split(sub)
    if not parts:
        show_voice_status()
        return

    action = parts[0].lower()

    if action in {"on", "enable", "start"}:
        enable_voice()
        speak(maybe_address_user("Voice is on.", chance=0.2), allow_sound=True)
        return

    if action in {"off", "disable", "stop"}:
        disable_voice()
        print("Voice is off.")
        return

    if action in {"auto", "reset", "default"}:
        set_voice_preference("auto")
        refresh_voice_selection()
        print("Voice preference set to auto.")
        speak("Voice preference set to auto.", allow_sound=True)
        return

    if action in {"status", "show"}:
        show_voice_status()
        return

    if action in {"list", "voices"}:
        voices = list_available_voices()
        if not voices:
            print("No voices found.")
            return
        for i, item in enumerate(voices, 1):
            print(f"{i}. {item}")
        return

    if action == "set":
        if len(parts) < 2:
            print("Usage: voice set <name>")
            return
        name = " ".join(parts[1:]).strip()
        set_voice_preference(name)
        refresh_voice_selection()
        print(f"Voice preference set to: {name}")
        speak(f"Voice preference set to {name}.", allow_sound=True)
        return

    if action == "test":
        text = " ".join(parts[1:]).strip() if len(parts) > 1 else "This is a voice test."
        if not text:
            text = "This is a voice test."
        speak(text, allow_sound=True)
        return

    print("Usage: voice | voice on | voice off | voice list | voice set <name> | voice auto | voice test <text>")


def cmd_projects():
    open_projects_folder()


def cmd_data():
    open_data_folder()


def cmd_logs(rest):
    sub = rest.strip()
    if not sub:
        print(f"Log file: {CHAT_LOG}")
        print("Use: logs tail [n]")
        return

    parts = shlex.split(sub)
    if not parts:
        print(f"Log file: {CHAT_LOG}")
        return

    action = parts[0].lower()
    if action == "tail":
        n = 20
        if len(parts) > 1:
            try:
                n = int(parts[1])
            except Exception:
                n = 20
        show_recent_log(n)
        return

    print("Usage: logs tail [n]")

def extract_math_expression(text):
    text = text.lower().strip()

    replacements = {
        "plus": "+",
        "minus": "-",
        "times": "*",
        "multiplied by": "*",
        "x": "*",
        "divided by": "/",
        "over": "/",
        "power of": "^",
    }

    for word, symbol in replacements.items():
        text = text.replace(word, symbol)

    starters = (
        "calculate ",
        "calc ",
        "solve ",
    )

    for starter in starters:
        if text.startswith(starter):
            text = text[len(starter):]

    return text.strip()

def reboot_soar():
    global shutting_down
    shutting_down = True

    print("\nRebooting SOAR...")

    stop_event.set()

    try:
        disable_voice()
    except Exception:
        pass

    try:
        tts_queue.put_nowait(None)
    except Exception:
        pass

    python = sys.executable

    try:
        os.execl(python, python, *sys.argv)
    except Exception as e:
        print(f"Reboot failed: {e}")
        sys.exit(1)


def emergency_shutdown():
    global shutting_down
    shutting_down = True

    print("\nEMERGENCY SHUTDOWN")

    if soar_avss and hasattr(soar_avss, "release_single_instance_lock"):
        try:
            soar_avss.release_single_instance_lock()
        except Exception:
            pass

    try:
        os._exit(0)
    except Exception:
        sys.exit(0)

DEFAULT_PROFILES = {
    "default": {
        "voice": True,
        "disabled_modules": [],
        "safe_mode": False,
        "autocode": False,
        "auto_lightweight": True,
        "resource_limits": None,
    },
    "gaming": {
        "voice": False,
        "disabled_modules": ["AUTOCODE", "RSMS", "CSRS"],
        "safe_mode": False,
        "autocode": False,
        "auto_lightweight": True,
        "resource_limits": {"ram_bytes": None, "cpu_percent": 85, "gpu_percent": 95},
    },
    "coding": {
        "voice": True,
        "disabled_modules": ["RSMS"],
        "safe_mode": False,
        "autocode": True,
        "auto_lightweight": True,
        "resource_limits": None,
    },
    "lightweight": {
        "voice": False,
        "disabled_modules": ["AUTOCODE", "VOICE", "RSMS", "CSRS", "AVSS"],
        "safe_mode": False,
        "autocode": False,
        "auto_lightweight": False,
        "resource_limits": None,
    },
}

KNOWN_COMMAND_ROOTS = {
    "help", "exit", "quit", "bye", "shutdown", "power", "clear", "time", "date",
    "uptime", "ping", "say", "message", "calc", "note", "notes", "remember",
    "memories", "forget", "search", "todo", "remind", "timer", "pomodoro", "shell",
    "read", "write", "open", "openurl", "copy", "paste", "ip", "status", "voice",
    "listen", "code", "mkdir", "newfile", "projects", "data", "logs", "history",
    "repeat", "alias", "profile", "schedule", "app", "apps", "workspace", "ws",
    "module", "modules", "diagnostics", "diag", "recovery", "event", "events",
    "clipboard", "clip", "project", "safe", "control", "center", "dashboard",
    "cc", "autocode", "build", "check", "sysinfo", "report", "weather", "quote",
    "git", "json", "dep", "fact", "story", "chess", "rsms", "resource", "lightmode",
    "limitres", "achds", "csrs", "avss", "browse",
}

def _json_load(path, default):
    try:
        if path.exists() and path.read_text(encoding="utf-8").strip():
            value = json.loads(path.read_text(encoding="utf-8"))
            return value
    except Exception as e:
        print(f"[FEATURE DATA ERROR] {path.name}: {e}")
    return default

def _json_save(path, value):
    try:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value, indent=2, ensure_ascii=False), encoding="utf-8")
        return True
    except Exception as e:
        print(f"[FEATURE DATA ERROR] Could not save {path.name}: {e}")
        return False

def emit_event(name, payload=None):
    event_name = str(name or "UNKNOWN").strip().upper().replace(" ", "_")
    event = {
        "time": datetime.now().isoformat(timespec="seconds"),
        "event": event_name,
        "payload": payload if payload is not None else {},
    }
    try:
        with EVENT_LOG_FILE.open("a", encoding="utf-8") as f:
            f.write(json.dumps(event, ensure_ascii=False) + "\n")
    except Exception:
        pass

    for handler in list(EVENT_HANDLERS.get(event_name, [])):
        try:
            handler(event)
        except Exception as e:
            print(f"[EVENT HANDLER ERROR] {event_name}: {e}")
    return event

def register_event_handler(name, handler):
    key = str(name).strip().upper().replace(" ", "_")
    EVENT_HANDLERS.setdefault(key, []).append(handler)

def show_recent_events(count=20):
    try:
        count = max(1, min(200, int(count)))
    except Exception:
        count = 20

    if not EVENT_LOG_FILE.exists():
        print("No SOAR events recorded yet.")
        return

    lines = EVENT_LOG_FILE.read_text(encoding="utf-8", errors="ignore").splitlines()
    if not lines:
        print("No SOAR events recorded yet.")
        return

    print("\n--- SOAR EVENT LOG ---")
    for line in lines[-count:]:
        try:
            item = json.loads(line)
            print(f"[{item.get('time', '?')}] {item.get('event', 'UNKNOWN')} | {item.get('payload', {})}")
        except Exception:
            print(line)
    print("----------------------\n")

def record_module_failure(name, error):
    module = str(name or "CORE").upper()
    info = MODULE_HEALTH.setdefault(
        module,
        {"status": "unknown", "failures": 0, "last_error": "", "last_error_time": ""},
    )
    info["status"] = "failed"
    info["failures"] = int(info.get("failures", 0)) + 1
    info["last_error"] = str(error)
    info["last_error_time"] = datetime.now().isoformat(timespec="seconds")
    emit_event("MODULE_FAILURE", {"module": module, "error": str(error)})
    try:
        _json_save(DATA_DIR / "module_health.json", MODULE_HEALTH)
    except Exception:
        pass

def record_module_success(name, note=""):
    module = str(name or "CORE").upper()
    info = MODULE_HEALTH.setdefault(
        module,
        {"status": "unknown", "failures": 0, "last_error": "", "last_error_time": ""},
    )
    info["status"] = "healthy"
    if note:
        info["last_note"] = note

def load_module_health():
    global MODULE_HEALTH
    saved = _json_load(DATA_DIR / "module_health.json", {})
    if isinstance(saved, dict):
        for key, value in saved.items():
            if key in MODULE_HEALTH and isinstance(value, dict):
                MODULE_HEALTH[key].update(value)

def get_profiles():
    profiles = _json_load(PROFILES_FILE, {})
    changed = False
    if not isinstance(profiles, dict):
        profiles = {}
    for name, cfg in DEFAULT_PROFILES.items():
        if name not in profiles or not isinstance(profiles[name], dict):
            profiles[name] = dict(cfg)
            changed = True
    if changed:
        _json_save(PROFILES_FILE, profiles)
    return profiles

def get_active_profile():
    try:
        settings = load_settings()
        return str(settings.get("active_profile", "default") or "default").strip().lower()
    except Exception:
        return "default"

def save_active_profile(name):
    settings = load_settings()
    settings["active_profile"] = name
    save_settings(settings)

def get_module_overrides():
    settings = load_settings()
    raw = settings.get("module_overrides", [])
    if not isinstance(raw, list):
        return set()
    return {str(x).upper() for x in raw if str(x).strip()}

def save_module_overrides(modules):
    settings = load_settings()
    settings["module_overrides"] = sorted({str(x).upper() for x in modules})
    save_settings(settings)

def module_is_disabled(name):
    return str(name).upper() in SOAR_DISABLED_MODULES

def module_is_enabled(name):
    return not module_is_disabled(name)

def apply_module_disable_state(profile_disabled=None):
    global SOAR_MANUAL_DISABLED_MODULES
    profile_disabled = profile_disabled or []
    SOAR_MANUAL_DISABLED_MODULES = {str(x).upper() for x in profile_disabled}
    SOAR_MANUAL_DISABLED_MODULES.update(get_module_overrides())
    SOAR_DISABLED_MODULES.clear()
    SOAR_DISABLED_MODULES.update(SOAR_MANUAL_DISABLED_MODULES)

def start_avss_module():
    if SOAR_SAFE_MODE or not module_is_enabled("AVSS"):
        return False
    if soar_avss is None:
        record_module_failure("AVSS", "AVSS module is not available")
        return False

    try:
        avss_stop_event.clear()
        avss_entry = getattr(soar_avss, "run_avss_loop", None)
        if callable(avss_entry):
            try:
                threading.Thread(
                    target=avss_entry,
                    args=(avss_stop_event, 5),
                    daemon=True,
                    name="SOAR-AVSS",
                ).start()
            except TypeError:
                threading.Thread(
                    target=avss_entry,
                    daemon=True,
                    name="SOAR-AVSS",
                ).start()
            record_module_success("AVSS")
            emit_event("MODULE_STARTED", {"module": "AVSS"})
            print("[SOAR] AVSS Protection Shield active.")
            return True

        avss_main = getattr(soar_avss, "main", None)
        if callable(avss_main):
            threading.Thread(target=avss_main, daemon=True, name="SOAR-AVSS").start()
            record_module_success("AVSS")
            emit_event("MODULE_STARTED", {"module": "AVSS"})
            print("[SOAR] AVSS Protection Shield active.")
            return True

        record_module_failure("AVSS", "No compatible AVSS entry point")
        print("[SOAR] AVSS module loaded, but no compatible entry point was found.")
        return False
    except Exception as e:
        record_module_failure("AVSS", e)
        print(f"[SOAR] AVSS failed to start: {e}")
        return False

def restart_module(name):
    module = str(name or "").upper()
    if module not in MODULE_HEALTH:
        return False, f"Unknown module: {module}"

    SOAR_MANUAL_DISABLED_MODULES.discard(module)
    SOAR_DISABLED_MODULES.discard(module)
    save_module_overrides(SOAR_MANUAL_DISABLED_MODULES)

    try:
        if module == "VOICE":
            enable_voice()
            record_module_success("VOICE")
            emit_event("MODULE_RESTARTED", {"module": module})
            return True, "Voice restarted."
        if module == "AUTOCODE":
            autocode_stop.clear()
            global autocode_enabled
            autocode_enabled = bool(autocode_connected())
            record_module_success("AUTOCODE")
            emit_event("MODULE_RESTARTED", {"module": module})
            return True, "Autocode restarted."
        if module == "AVSS":
            ok = start_avss_module()
            return (ok, "AVSS restarted." if ok else "AVSS restart failed.")
        if module in {"RSMS", "CSRS"}:
            record_module_success(module)
            emit_event("MODULE_RESTARTED", {"module": module})
            return True, f"{module} is available again."
        if module == "CORE":
            record_module_success("CORE")
            return True, "Core recovery state reset."
    except Exception as e:
        record_module_failure(module, e)
        return False, f"{module} restart failed: {e}"

    return False, f"No restart handler for {module}."

def show_module_status():
    print("\n================ SOAR MODULE MANAGER ================")
    modules = ["CORE", "VOICE", "AUTOCODE", "AVSS", "RSMS", "CSRS"]
    for module in modules:
        info = MODULE_HEALTH.get(module, {})
        if module_is_disabled(module):
            state = "DISABLED"
        else:
            state = str(info.get("status", "READY")).upper()
        extra = ""
        if module == "AUTOCODE":
            extra = f" | connected={'yes' if autocode_connected() else 'no'}"
        elif module == "AVSS":
            extra = f" | loaded={'yes' if soar_avss else 'no'}"
        elif module == "RSMS":
            extra = f" | loaded={'yes' if rsms else 'no'}"
        print(f"  {module:<8} {state:<10} failures={info.get('failures', 0)}{extra}")
    print("=====================================================")

def module_manager_command(rest):
    parts = shlex.split(rest or "")
    if not parts:
        show_module_status()
        return

    action = parts[0].lower()
    if action in {"status", "list", "show"}:
        show_module_status()
        return
    if action in {"on", "enable", "start", "restart"}:
        if len(parts) < 2:
            print("Usage: module on|off|restart <module>")
            return
        module = parts[1].upper()
        if module not in MODULE_HEALTH:
            print(f"Unknown module: {module}")
            return
        if action == "restart":
            ok, msg = restart_module(module)
            print(msg)
            return

        if SOAR_SAFE_MODE and module in {"AUTOCODE", "AVSS", "VOICE"}:
            print("Safe mode: that module cannot be enabled until safe mode is off.")
            return
        SOAR_MANUAL_DISABLED_MODULES.discard(module)
        SOAR_DISABLED_MODULES.discard(module)
        save_module_overrides(SOAR_MANUAL_DISABLED_MODULES)
        if module == "AVSS":
            start_avss_module()
        elif module == "VOICE":
            enable_voice()
        elif module == "AUTOCODE":
            global autocode_enabled
            autocode_enabled = autocode_connected()
            autocode_stop.clear()
        record_module_success(module, "enabled manually")
        emit_event("MODULE_ENABLED", {"module": module})
        print(f"{module} enabled.")
        return

    if action in {"off", "disable", "stop"}:
        if len(parts) < 2:
            print("Usage: module on|off|restart <module>")
            return
        module = parts[1].upper()
        if module == "CORE":
            print("CORE cannot be disabled.")
            return
        SOAR_MANUAL_DISABLED_MODULES.add(module)
        SOAR_DISABLED_MODULES.add(module)
        save_module_overrides(SOAR_MANUAL_DISABLED_MODULES)
        _stop_optional_module(module)
        emit_event("MODULE_DISABLED", {"module": module})
        print(f"{module} disabled.")
        return

    print("Usage: module status | module on <name> | module off <name> | module restart <name>")

def list_modules_command():
    show_module_status()

def load_aliases():
    aliases = _json_load(ALIASES_FILE, {})
    return aliases if isinstance(aliases, dict) else {}

def save_aliases(aliases):
    _json_save(ALIASES_FILE, aliases)

def expand_alias(raw, max_depth=5):
    current = raw.strip()
    seen = set()
    for _ in range(max_depth):
        try:
            parts = shlex.split(current)
        except ValueError:
            return current
        if not parts:
            return current
        key = parts[0].lower()
        aliases = load_aliases()
        target = aliases.get(key)
        if not isinstance(target, str) or not target.strip() or key in seen:
            return current
        seen.add(key)
        suffix = " ".join(parts[1:])
        current = target.strip()
        if suffix:
            current += " " + suffix
    return current

def alias_command(rest):
    aliases = load_aliases()
    parts = shlex.split(rest or "")
    if not parts:
        if not aliases:
            print("No aliases configured.")
            return
        print("\nAliases:")
        for key, value in sorted(aliases.items()):
            print(f"  {key} = {value}")
        return

    action = parts[0].lower()
    if action in {"list", "show"}:
        if not aliases:
            print("No aliases configured.")
            return
        for key, value in sorted(aliases.items()):
            print(f"  {key} = {value}")
        return

    if action in {"remove", "rm", "delete"}:
        if len(parts) < 2:
            print("Usage: alias remove <name>")
            return
        key = parts[1].lower()
        if key in aliases:
            aliases.pop(key)
            save_aliases(aliases)
            print(f"Alias '{key}' removed.")
        else:
            print(f"Alias '{key}' does not exist.")
        return

    if action in {"add", "set"}:
        if len(parts) < 3:
            print('Usage: alias add <name> <command>')
            return
        key = parts[1].lower()
        value = " ".join(parts[2:]).strip()
        if value.startswith("="):
            value = value[1:].strip()
        aliases[key] = value
        save_aliases(aliases)
        print(f"Alias saved: {key} = {value}")
        return

    key = parts[0].lower()
    value = " ".join(parts[1:]).strip()
    if value.startswith("="):
        value = value[1:].strip()
    if not value:
        print(f"Alias '{key}' = {aliases.get(key, '(not set)')}")
        return
    aliases[key] = value
    save_aliases(aliases)
    print(f"Alias saved: {key} = {value}")

def record_command_history(raw, source="terminal"):
    entry = str(raw).strip()
    if not entry:
        return
    if len(entry) > 1000:
        entry = entry[:1000] + " ..."
    try:
        lines = COMMAND_HISTORY_FILE.read_text(encoding="utf-8", errors="ignore").splitlines() if COMMAND_HISTORY_FILE.exists() else []
        stamp_value = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        safe_entry = entry.replace("\n", " ")
        lines.append(f"[{stamp_value}] [{source}] {safe_entry}")
        lines = lines[-COMMAND_HISTORY_LIMIT:]
        COMMAND_HISTORY_FILE.write_text("\n".join(lines) + "\n", encoding="utf-8")
    except Exception:
        pass

def get_history_entries():
    if not COMMAND_HISTORY_FILE.exists():
        return []
    return COMMAND_HISTORY_FILE.read_text(encoding="utf-8", errors="ignore").splitlines()

def history_command(rest):
    sub = (rest or "").strip()
    if sub.lower() == "clear":
        COMMAND_HISTORY_FILE.write_text("", encoding="utf-8")
        print("Command history cleared.")
        return
    if sub.lower().startswith("search "):
        term = sub[7:].strip().lower()
        matches = [x for x in get_history_entries() if term in x.lower()]
        for line in matches[-50:]:
            print(line)
        if not matches:
            print("No matching history entries.")
        return
    try:
        count = max(1, min(100, int(sub))) if sub else 20
    except ValueError:
        count = 20
    entries = get_history_entries()
    if not entries:
        print("Command history is empty.")
        return
    print("\n--- COMMAND HISTORY ---")
    start = max(0, len(entries) - count)
    for idx, line in enumerate(entries[start:], start=start + 1):
        print(f"{idx:>4}: {line}")
    print("-----------------------")

def repeat_command(rest):
    entries = get_history_entries()
    if not entries:
        print("Command history is empty.")
        return
    try:
        requested = int(rest.strip()) if rest.strip() else 1
    except ValueError:
        requested = 1
    if requested < 1 or requested > len(entries):
        print(f"History item must be between 1 and {len(entries)}.")
        return
    raw_entry = entries[requested - 1]
    if "] " in raw_entry:
        target = raw_entry.split("] ", 1)[1]
    else:
        target = raw_entry
    if not target.strip():
        print("Selected history item is empty.")
        return
    print(f"[SOAR HISTORY] Repeating: {target}")
    process_command(target, _skip_history=True)

def suggest_command(raw):
    try:
        parts = shlex.split(raw)
    except ValueError:
        return False
    if not parts:
        return False
    root = parts[0].lower()
    if root in KNOWN_COMMAND_ROOTS:
        return False

    matches = difflib.get_close_matches(root, sorted(KNOWN_COMMAND_ROOTS), n=3, cutoff=0.72)
    if not matches:
        return False
    print(f"[SOAR] Unknown command '{root}'. Did you mean: {', '.join(matches)}?")
    return True

def get_saved_workspaces():
    data = _json_load(WORKSPACES_FILE, {})
    return data if isinstance(data, dict) else {}

def workspace_command(rest):
    parts = shlex.split(rest or "")
    if not parts:
        data = get_saved_workspaces()
        if not data:
            print("No workspaces saved.")
            return
        for name, value in sorted(data.items()):
            print(f"  {name} -> {value}")
        return

    action = parts[0].lower()
    data = get_saved_workspaces()

    if action in {"list", "show"}:
        if not data:
            print("No workspaces saved.")
            return
        for name, value in sorted(data.items()):
            print(f"  {name} -> {value}")
        return

    if action in {"open", "load"}:
        if len(parts) < 2:
            print("Usage: workspace open <name>")
            return
        name = parts[1]
        if name not in data:
            print(f"Workspace '{name}' not found.")
            return
        path = Path(data[name])
        if not path.exists():
            print(f"Workspace path no longer exists: {path}")
            return
        open_path(path)
        print(f"Workspace '{name}' opened.")
        emit_event("WORKSPACE_OPENED", {"name": name, "path": str(path)})
        return

    if action in {"remove", "rm", "delete"}:
        if len(parts) < 2:
            print("Usage: workspace remove <name>")
            return
        name = parts[1]
        if name in data:
            data.pop(name)
            _json_save(WORKSPACES_FILE, data)
            print(f"Workspace '{name}' removed.")
        else:
            print(f"Workspace '{name}' not found.")
        return

    if action in {"add", "set", "save"}:
        if len(parts) < 3:
            print("Usage: workspace add <name> <path>")
            return
        name = parts[1]
        path_text = " ".join(parts[2:]).strip()
        path = Path(path_text).expanduser()
        try:
            path = path.resolve()
        except Exception:
            path = path.absolute()
        if not path.exists() or not path.is_dir():
            print("Workspace path must be an existing directory.")
            return
        data[name] = str(path)
        _json_save(WORKSPACES_FILE, data)
        print(f"Workspace saved: {name} -> {path}")
        return

    name = parts[0]
    if name not in data:
        print(f"Workspace '{name}' not found.")
        return
    path = Path(data[name])
    if not path.exists():
        print(f"Workspace path no longer exists: {path}")
        return
    open_path(path)
    print(f"Workspace '{name}' opened.")
    emit_event("WORKSPACE_OPENED", {"name": name, "path": str(path)})

def open_path(path):
    path = Path(path)
    system = platform.system()
    try:
        if system == "Darwin":
            subprocess.Popen(["open", str(path)])
        elif system == "Windows":
            os.startfile(str(path))
        else:
            subprocess.Popen(["xdg-open", str(path)])
        return True
    except Exception as e:
        print(f"Could not open path: {e}")
        return False

def resolve_app_alias(name):
    value = str(name or "").strip()
    low = value.lower()
    aliases = {
        "chrome": "Google Chrome",
        "google chrome": "Google Chrome",
        "vscode": "Visual Studio Code",
        "code": "Visual Studio Code",
        "vs code": "Visual Studio Code",
        "terminal": "Terminal",
        "finder": "Finder",
        "minecraft": "Minecraft",
        "discord": "Discord",
        "spotify": "Spotify",
        "safari": "Safari",
        "firefox": "Firefox",
    }
    return aliases.get(low, value)

def app_command(rest):
    parts = shlex.split(rest or "")
    if not parts:
        print("Usage: app open|close|find <name>")
        return

    action = parts[0].lower()
    target = " ".join(parts[1:]).strip()
    if action in {"list", "apps"}:
        list_running_apps()
        return
    if not target:
        print("Please specify an app name.")
        return

    if SOAR_SAFE_MODE and action in {"open", "close", "restart"}:
        print("Safe mode: application management is disabled.")
        return

    if action in {"open", "start", "launch"}:
        app_name = resolve_app_alias(target)
        try:
            if platform.system() == "Darwin":
                subprocess.Popen(["open", "-a", app_name])
            elif platform.system() == "Windows":
                subprocess.Popen(["cmd", "/c", "start", "", app_name])
            else:
                subprocess.Popen([app_name])
            print(f"Opened app: {app_name}")
            emit_event("APP_OPENED", {"app": app_name})
        except Exception as e:
            record_module_failure("CORE", e)
            print(f"Could not open app '{app_name}': {e}")
        return

    if action in {"close", "stop", "kill"}:
        app_name = resolve_app_alias(target)
        if close_app_processes(app_name):
            print(f"Close request sent to: {app_name}")
        else:
            print(f"No matching user app process found for: {app_name}")
        return

    if action in {"find", "where"}:
        matches = find_app_processes(target)
        if not matches:
            print("No matching processes found.")
            return
        for item in matches:
            print(item)
        return

    print("Usage: app open|close|find <name>")

def list_running_apps():
    seen = set()
    print("\n--- RUNNING USER APPS ---")
    try:
        for proc in psutil.process_iter(["pid", "name"]):
            try:
                pid = proc.info.get("pid")
                name = (proc.info.get("name") or "").strip()
                if not name or pid == os.getpid():
                    continue
                lower = name.lower()
                if lower in {"launchservicesd", "windowserver", "systemuiserver", "finder"}:
                    continue
                key = lower
                if key in seen:
                    continue
                seen.add(key)
                if any(x in lower for x in (
                    "chrome", "firefox", "safari", "discord", "spotify", "minecraft",
                    "code", "terminal", "steam", "slack", "zoom", "obs", "notion",
                )):
                    print(f"  {pid:<7} {name}")
            except Exception:
                continue
    except Exception as e:
        print(f"App listing error: {e}")
    print("-------------------------")

def find_app_processes(query):
    query = str(query or "").strip().lower()
    results = []
    if not query:
        return results
    try:
        for proc in psutil.process_iter(["pid", "name", "exe"]):
            try:
                name = str(proc.info.get("name") or "")
                exe = str(proc.info.get("exe") or "")
                if query in name.lower() or query in exe.lower():
                    results.append(f"PID {proc.info.get('pid')}: {name} | {exe}")
            except Exception:
                continue
    except Exception:
        pass
    return results

def close_app_processes(target):
    query = str(target or "").strip().lower()
    if not query:
        return False
    if query in {"terminal", "finder", "soar", "soar_main", "python"}:
        print("SOAR protected that application from being closed.")
        return False

    protected_names = {
        "soar_main.py", "python", "python3", "launchservicesd", "windowserver",
        "kernel_task", "systemd", "init", "svchost.exe",
    }
    matched = []
    try:
        for proc in psutil.process_iter(["pid", "name"]):
            try:
                pid = proc.info.get("pid")
                name = str(proc.info.get("name") or "")
                low = name.lower()
                if pid == os.getpid() or low in protected_names:
                    continue
                if query in low or low == resolve_app_alias(query).lower():
                    matched.append(proc)
            except Exception:
                continue

        if not matched:
            return False

        for proc in matched:
            try:
                proc.terminate()
            except Exception:
                continue

        try:
            psutil.wait_procs(matched, timeout=2)
        except Exception:
            pass

        emit_event("APP_CLOSE_REQUEST", {"app": target, "count": len(matched)})
        return True
    except Exception as e:
        record_module_failure("CORE", e)
        return False

def get_project_target(rest):
    target = (rest or "").strip().strip('"').strip("'")
    if not target:
        return PROJECTS_DIR

    candidate = Path(target).expanduser()
    candidates = []
    if candidate.is_absolute():
        candidates.append(candidate)
    else:
        candidates.extend([
            PROJECTS_DIR / candidate,
            BASE_DIR / "projects" / candidate,
            BASE_DIR / candidate,
        ])

    for path in candidates:
        try:
            resolved = path.resolve()
        except Exception:
            resolved = path.absolute()
        if resolved.exists():
            return resolved
    return None

def project_health_command(rest):
    target = get_project_target(rest)
    if target is None:
        print("Project path could not be resolved.")
        return
    if target.is_file():
        target = target.parent

    print("\n================ SOAR PROJECT HEALTH ================")
    print(f"Project: {target}")
    py_files = list(target.rglob("*.py"))
    all_files = [p for p in target.rglob("*") if p.is_file()]
    print(f"Files: {len(all_files)} | Python: {len(py_files)}")

    pass_count = 0
    warn_count = 0
    fail_count = 0

    if py_files:
        for py in py_files[:500]:
            try:
                ast.parse(py.read_text(encoding="utf-8", errors="ignore"))
                print(f"  PASS  Python syntax: {py.relative_to(target)}")
                pass_count += 1
            except SyntaxError as e:
                print(f"  FAIL  Python syntax: {py.relative_to(target)} -> line {e.lineno}: {e.msg}")
                fail_count += 1
            except Exception as e:
                print(f"  WARN  Could not parse {py.relative_to(target)}: {e}")
                warn_count += 1
    else:
        print("  WARN  No Python files found.")
        warn_count += 1

    readme = target / "README.md"
    if readme.exists():
        print("  PASS  README.md present")
        pass_count += 1
    else:
        print("  WARN  README.md missing")
        warn_count += 1

    req_file = target / "requirements.txt"
    if req_file.exists():
        print("  PASS  requirements.txt present")
        pass_count += 1
        try:
            installed_output = subprocess.run(
                [sys.executable, "-m", "pip", "list", "--format=freeze"],
                capture_output=True,
                text=True,
                timeout=8,
                check=False,
            ).stdout
            installed = {
                line.split("==")[0].lower().replace("_", "-")
                for line in installed_output.splitlines()
                if "==" in line
            }
            missing = []
            for line in req_file.read_text(encoding="utf-8", errors="ignore").splitlines():
                item = line.strip()
                if not item or item.startswith("#"):
                    continue
                package = re.split(r"[<>=!~]", item, maxsplit=1)[0].strip().lower().replace("_", "-")
                if package and package not in installed:
                    missing.append(package)
            if missing:
                print(f"  WARN  Missing requirements: {', '.join(missing[:20])}")
                warn_count += 1
            else:
                print("  PASS  Required packages appear installed")
                pass_count += 1
        except Exception as e:
            print(f"  WARN  Dependency check skipped: {e}")
            warn_count += 1
    else:
        print("  WARN  requirements.txt missing")
        warn_count += 1

    todo_hits = 0
    for path in py_files[:500]:
        try:
            body = path.read_text(encoding="utf-8", errors="ignore")
            todo_hits += len(re.findall(r"\b(TODO|FIXME)\b", body, flags=re.IGNORECASE))
        except Exception:
            pass
    if todo_hits:
        print(f"  WARN  TODO/FIXME markers: {todo_hits}")
        warn_count += 1
    else:
        print("  PASS  No TODO/FIXME markers found")
        pass_count += 1

    try:
        oversized = [p for p in all_files if p.stat().st_size > 10 * 1024 * 1024]
        if oversized:
            print(f"  WARN  Files over 10 MB: {len(oversized)}")
            warn_count += 1
        else:
            print("  PASS  No files over 10 MB")
            pass_count += 1
    except Exception:
        pass

    git_dir = target / ".git"
    if git_dir.exists():
        try:
            res = subprocess.run(
                ["git", "-C", str(target), "status", "--short"],
                capture_output=True,
                text=True,
                timeout=8,
                check=False,
            )
            changed = len([x for x in res.stdout.splitlines() if x.strip()])
            if changed:
                print(f"  INFO  Git changes detected: {changed}")
            else:
                print("  PASS  Git working tree clean")
                pass_count += 1
        except Exception:
            print("  WARN  Git status could not be checked")
            warn_count += 1

    print(f"\nSummary: PASS={pass_count} WARN={warn_count} FAIL={fail_count}")
    print("======================================================")
    emit_event("PROJECT_HEALTH_SCAN", {"project": str(target), "pass": pass_count, "warn": warn_count, "fail": fail_count})

def diagnostics_2_command():
    print("\n================ SOAR DIAGNOSTICS 2.0 ================")
    checks = []

    def check(name, ok, detail):
        state = "PASS" if ok else "WARN"
        if not ok:
            print(f"  {state:<4} {name}: {detail}")
        else:
            print(f"  {state:<4} {name}: {detail}")
        checks.append((name, ok))

    check("Python", bool(sys.version_info >= (3, 10)), sys.version.split()[0])
    check("Platform", True, f"{platform.system()} {platform.release()} / {platform.machine()}")
    check("psutil", psutil is not None, "loaded" if psutil is not None else "missing")
    check("TTS", tts_ready.is_set(), tts_voice_label or "not ready")
    check("Speech", recognizer is not None, "ready" if recognizer else "not ready")
    check("SOAR Autocode", autocode_connected(), "connected" if autocode_connected() else "offline")
    check("AVSS", soar_avss is not None, "loaded" if soar_avss else "not loaded")
    check("RSMS", rsms is not None, "loaded" if rsms else "not loaded")
    check("Storage", DATA_DIR.exists() and PROJECTS_DIR.exists(), f"{DATA_DIR.name}/ and Projects/")
    network_ok = _quick_network_check()
    check("Network", network_ok, "reachable" if network_ok else "unavailable")

    try:
        ram = psutil.virtual_memory()
        cpu = psutil.cpu_percent(interval=0.15)
        disk = __import__("shutil").disk_usage(str(Path.home()))
        print(f"  INFO CPU: {cpu:.1f}%")
        print(f"  INFO RAM: {ram.percent:.1f}% ({ram.available / (1024 ** 3):.2f} GB available)")
        print(f"  INFO Disk: {disk.free / (1024 ** 3):.2f} GB free")
    except Exception as e:
        print(f"  WARN Resource sensors: {e}")

    print(f"  INFO Profile: {SOAR_ACTIVE_PROFILE}")
    print(f"  INFO Safe mode: {'ON' if SOAR_SAFE_MODE else 'OFF'}")
    print(f"  INFO Auto-lightweight: {'ON' if SOAR_AUTO_LIGHTWEIGHT_ENABLED else 'OFF'}")
    print("======================================================")
    emit_event("DIAGNOSTICS_RUN", {"profile": SOAR_ACTIVE_PROFILE})

def _quick_network_check():
    try:
        with socket.create_connection(("example.com", 80), timeout=1.5):
            return True
    except Exception:
        return False

def safe_mode_command(rest):
    global SOAR_SAFE_MODE
    action = (rest or "").strip().lower()
    if action in {"on", "enable", "start"}:
        SOAR_SAFE_MODE = True
        autocode_stop.set()
        global autocode_enabled
        autocode_enabled = False
        SOAR_DISABLED_MODULES.update({"AUTOCODE"})
        settings = load_settings()
        settings["safe_mode"] = True
        save_settings(settings)
        emit_event("SAFE_MODE_ON", {})
        print("SOAR Safe Mode enabled. External/shell-heavy actions are blocked.")
        return

    if action in {"off", "disable", "stop"}:
        SOAR_SAFE_MODE = False
        settings = load_settings()
        settings["safe_mode"] = False
        save_settings(settings)
        SOAR_DISABLED_MODULES.discard("AUTOCODE")
        autocode_stop.clear()
        emit_event("SAFE_MODE_OFF", {})
        print("SOAR Safe Mode disabled.")
        return

    print(f"Safe mode: {'ON' if SOAR_SAFE_MODE else 'OFF'}")
    print("Use: safe mode on | safe mode off")

def schedule_parse_due(spec):
    spec = str(spec or "").strip()
    now = datetime.now()
    if spec.lower().startswith("at "):
        clock = spec[3:].strip()
        match = re.fullmatch(r"(\d{1,2}):(\d{2})", clock)
        if not match:
            raise ValueError("Use time like 18:30.")
        hour = int(match.group(1))
        minute = int(match.group(2))
        if not 0 <= hour <= 23 or not 0 <= minute <= 59:
            raise ValueError("Invalid clock time.")
        due = now.replace(hour=hour, minute=minute, second=0, microsecond=0)
        if due <= now:
            due = due.replace(day=due.day) + __import__("datetime").timedelta(days=1)
        return due.timestamp()

    seconds = parse_duration_seconds(spec)
    if seconds < 1:
        raise ValueError("Delay must be at least one second.")
    return time.time() + seconds

def schedule_load():
    data = _json_load(SCHEDULE_FILE, [])
    return data if isinstance(data, list) else []

def schedule_save(tasks):
    _json_save(SCHEDULE_FILE, tasks)

def schedule_next_id(tasks):
    ids = []
    for task in tasks:
        try:
            ids.append(int(task.get("id", 0)))
        except Exception:
            pass
    return max(ids, default=0) + 1

def schedule_add_command(spec, command):
    if not command.strip():
        print("Usage: schedule add <duration|at HH:MM> <command>")
        return
    tasks = schedule_load()
    task = {
        "id": schedule_next_id(tasks),
        "due": schedule_parse_due(spec),
        "command": command.strip(),
        "created": datetime.now().isoformat(timespec="seconds"),
        "status": "pending",
    }
    tasks.append(task)
    schedule_save(tasks)
    due_text = datetime.fromtimestamp(task["due"]).strftime("%Y-%m-%d %I:%M:%S %p")
    print(f"Scheduled #{task['id']} for {due_text}: {task['command']}")
    emit_event("SCHEDULE_ADDED", {"id": task["id"], "command": task["command"], "due": task["due"]})

def schedule_command(rest):
    parts = shlex.split(rest or "")
    if not parts:
        schedule_list_command()
        return

    action = parts[0].lower()
    if action in {"list", "show"}:
        schedule_list_command()
        return

    if action in {"clear"}:
        schedule_save([])
        print("All scheduled tasks cleared.")
        emit_event("SCHEDULE_CLEARED", {})
        return

    if action in {"remove", "rm", "delete"}:
        if len(parts) < 2 or not parts[1].isdigit():
            print("Usage: schedule remove <id>")
            return
        wanted = int(parts[1])
        tasks = schedule_load()
        remaining = [x for x in tasks if int(x.get("id", -1)) != wanted]
        if len(remaining) == len(tasks):
            print(f"Scheduled task #{wanted} not found.")
        else:
            schedule_save(remaining)
            print(f"Scheduled task #{wanted} removed.")
        return

    if action == "add":
        if len(parts) < 3:
            print("Usage: schedule add <duration|at HH:MM> <command>")
            return
        if parts[1].lower() == "at":
            if len(parts) < 4:
                print("Usage: schedule add at <HH:MM> <command>")
                return
            spec = f"at {parts[2]}"
            command = " ".join(parts[3:])
        else:
            spec = parts[1]
            command = " ".join(parts[2:])
        try:
            schedule_add_command(spec, command)
        except Exception as e:
            print(f"Could not schedule task: {e}")
        return

    if len(parts) >= 2:
        if parts[0].lower() == "at":
            if len(parts) < 3:
                print("Usage: schedule at <HH:MM> <command>")
                return
            spec = f"at {parts[1]}"
            command = " ".join(parts[2:])
        else:
            spec = parts[0]
            command = " ".join(parts[1:])
        try:
            schedule_add_command(spec, command)
        except Exception as e:
            print(f"Could not schedule task: {e}")
        return

    print("Usage: schedule add <duration|at HH:MM> <command>")

def schedule_list_command():
    tasks = schedule_load()
    if not tasks:
        print("No scheduled tasks.")
        return
    now = time.time()
    print("\n--- SOAR SCHEDULER ---")
    for task in sorted(tasks, key=lambda x: float(x.get("due", 0))):
        try:
            due = float(task.get("due", 0))
        except Exception:
            due = 0
        status = task.get("status", "pending")
        when = datetime.fromtimestamp(due).strftime("%Y-%m-%d %I:%M:%S %p")
        if status == "pending" and due <= now:
            status = "DUE"
        print(f"  #{task.get('id')}: {status:<7} {when} -> {task.get('command', '')}")
    print("----------------------")

def scheduler_loop():
    global SCHEDULE_THREAD
    record_module_success("SCHEDULER")
    while not stop_event.is_set() and not SCHEDULE_STOP_EVENT.is_set():
        try:
            tasks = schedule_load()
            changed = False
            now = time.time()
            for task in tasks:
                if task.get("status") != "pending":
                    continue
                try:
                    due = float(task.get("due", 0))
                except Exception:
                    continue
                if due > now:
                    continue
                command = str(task.get("command", "")).strip()
                task["status"] = "running"
                changed = True
                schedule_save(tasks)
                emit_event("SCHEDULE_FIRED", {"id": task.get("id"), "command": command})
                try:
                    process_command(command, _skip_history=True)
                    task["status"] = "done"
                    task["completed"] = datetime.now().isoformat(timespec="seconds")
                    record_module_success("SCHEDULER")
                except Exception as e:
                    task["status"] = "failed"
                    task["error"] = str(e)
                    record_module_failure("SCHEDULER", e)
                    print(f"[SCHEDULER ERROR] Task #{task.get('id')}: {e}")
                changed = True
            if changed:
                schedule_save(tasks)
        except Exception as e:
            record_module_failure("SCHEDULER", e)
        stop_event.wait(1.0)
    SCHEDULE_THREAD = None

def start_scheduler():
    global SCHEDULE_THREAD
    if SCHEDULE_THREAD is not None and SCHEDULE_THREAD.is_alive():
        return
    SCHEDULE_STOP_EVENT.clear()
    SCHEDULE_THREAD = threading.Thread(
        target=scheduler_loop,
        daemon=True,
        name="SOAR-Scheduler",
    )
    SCHEDULE_THREAD.start()

def clipboard_history_record(content):
    content = str(content)
    if not content:
        return
    items = _json_load(CLIPBOARD_HISTORY_FILE, [])
    if not isinstance(items, list):
        items = []
    items.append({
        "time": datetime.now().isoformat(timespec="seconds"),
        "chars": len(content),
        "preview": content[:120].replace("\n", "\\n"),
        "text": content,
    })
    _json_save(CLIPBOARD_HISTORY_FILE, items[-CLIPBOARD_HISTORY_LIMIT:])

def clipboard_intelligence_command(rest):
    parts = shlex.split(rest or "")
    action = parts[0].lower() if parts else "info"

    if action in {"copy", "set"}:
        content = " ".join(parts[1:])
        if not content:
            print("Usage: clipboard copy <text>")
            return
        if clipboard_copy(content):
            clipboard_history_record(content)
            print(f"Copied {len(content)} characters.")
        else:
            print("Clipboard copy failed.")
        return

    if action in {"paste", "get"}:
        content = clipboard_paste()
        if not content:
            print("Clipboard empty or unavailable.")
            return
        print(content)
        return

    if action in {"info", "analyze", "analyse"}:
        content = clipboard_paste()
        if not content:
            print("Clipboard empty or unavailable.")
            return
        lines = content.splitlines() or [content]
        words = re.findall(r"\b[\w'-]+\b", content)
        if re.fullmatch(r"https?://\S+", content.strip()):
            kind = "URL"
        elif re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]+", content.strip()):
            kind = "EMAIL"
        else:
            try:
                json.loads(content)
                kind = "JSON"
            except Exception:
                if "def " in content or "import " in content or "#!/usr/bin" in content:
                    kind = "CODE"
                else:
                    kind = "TEXT"
        print("\n--- CLIPBOARD INTELLIGENCE ---")
        print(f"Type: {kind}")
        print(f"Characters: {len(content)}")
        print(f"Words: {len(words)}")
        print(f"Lines: {len(lines)}")
        print(f"First line: {lines[0][:200]}")
        print("------------------------------")
        return

    if action in {"history", "saved"}:
        items = _json_load(CLIPBOARD_HISTORY_FILE, [])
        if not items:
            print("Clipboard history is empty.")
            return
        print("\n--- CLIPBOARD HISTORY ---")
        for idx, item in enumerate(items[-CLIPBOARD_HISTORY_LIMIT:], 1):
            print(f"{idx:>2}. [{item.get('time', '?')}] {item.get('chars', 0)} chars | {item.get('preview', '')}")
        print("-------------------------")
        return

    if action in {"save"}:
        content = clipboard_paste()
        if not content:
            print("Clipboard empty or unavailable.")
            return
        name = "clipboard_" + datetime.now().strftime("%Y%m%d_%H%M%S")
        if len(parts) > 1:
            name = "_".join(parts[1:])
        target = DATA_DIR / "clipboard_saves" / f"{name}.txt"
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content, encoding="utf-8")
        clipboard_history_record(content)
        print(f"Clipboard saved to: {target}")
        return

    if action in {"clear", "empty"}:
        clipboard_copy("")
        print("Clipboard cleared.")
        return

    print("Usage: clipboard info|copy|paste|history|save|clear")

def profile_command(rest):
    global SOAR_ACTIVE_PROFILE, SOAR_SAFE_MODE, SOAR_AUTO_LIGHTWEIGHT_ENABLED
    global SOAR_RESOURCE_LIMITS_ACTIVE, voice_enabled
    global autocode_enabled, SOAR_DISABLED_MODULES, SOAR_MANUAL_DISABLED_MODULES

    profiles = get_profiles()
    parts = shlex.split(rest or "")
    if not parts or parts[0].lower() in {"list", "show"}:
        print("\nSOAR Profiles:")
        for name in sorted(profiles):
            marker = "*" if name == SOAR_ACTIVE_PROFILE else " "
            print(f" {marker} {name}")
        print("Use: profile <name>")
        return

    if parts[0].lower() in {"current", "status"}:
        print(f"Active profile: {SOAR_ACTIVE_PROFILE}")
        return

    name = parts[0].lower()
    if name not in profiles:
        print(f"Profile '{name}' not found.")
        print(f"Available: {', '.join(sorted(profiles))}")
        return

    config = profiles[name]
    SOAR_ACTIVE_PROFILE = name
    save_active_profile(name)

    SOAR_SAFE_MODE = bool(config.get("safe_mode", False))
    SOAR_AUTO_LIGHTWEIGHT_ENABLED = bool(config.get("auto_lightweight", True))
    apply_module_disable_state(config.get("disabled_modules", []))

    overrides = get_module_overrides()
    SOAR_MANUAL_DISABLED_MODULES.update(overrides)
    SOAR_DISABLED_MODULES.update(overrides)

    limits = config.get("resource_limits")
    if isinstance(limits, dict):
        with resource_limit_lock:
            SOAR_RESOURCE_LIMITS["ram_bytes"] = limits.get("ram_bytes")
            SOAR_RESOURCE_LIMITS["cpu_percent"] = limits.get("cpu_percent")
            SOAR_RESOURCE_LIMITS["gpu_percent"] = limits.get("gpu_percent")
            SOAR_RESOURCE_LIMITS_ACTIVE = any(v is not None for v in SOAR_RESOURCE_LIMITS.values())
            globals()["SOAR_RESOURCE_LIMITS_ACTIVE"] = SOAR_RESOURCE_LIMITS_ACTIVE
    else:
        with resource_limit_lock:
            globals()["SOAR_RESOURCE_LIMITS_ACTIVE"] = False
            SOAR_RESOURCE_LIMITS["ram_bytes"] = None
            SOAR_RESOURCE_LIMITS["cpu_percent"] = None
            SOAR_RESOURCE_LIMITS["gpu_percent"] = None

    autocode_stop.clear()
    autocode_enabled = bool(config.get("autocode", False) and autocode_connected())
    if not autocode_enabled:
        autocode_stop.set()

    desired_voice = bool(config.get("voice", True)) and module_is_enabled("VOICE") and not SOAR_SAFE_MODE
    if desired_voice:
        try:
            if tts_ready.is_set() and recognizer is not None:
                enable_voice()
        except Exception as e:
            record_module_failure("VOICE", e)
    else:
        try:
            disable_voice()
        except Exception:
            voice_enabled = False

    if "AVSS" in SOAR_DISABLED_MODULES or SOAR_SAFE_MODE:
        avss_stop_event.set()
    else:
        avss_stop_event.clear()

    emit_event("PROFILE_CHANGED", {"profile": name})
    print(f"Profile '{name}' applied.")
    print(f"  Voice: {'on' if desired_voice else 'off'}")
    print(f"  Autocode: {'on' if autocode_enabled else 'off'}")
    print(f"  Safe mode: {'on' if SOAR_SAFE_MODE else 'off'}")
    print(f"  Disabled modules: {', '.join(sorted(SOAR_DISABLED_MODULES)) or 'none'}")

def app_manager_open_short(rest):
    app_command("open " + (rest or ""))

def app_manager_close_short(rest):
    app_command("close " + (rest or ""))

def show_control_center():
    try:
        cpu = psutil.cpu_percent(interval=0.1)
        vm = psutil.virtual_memory()
        disk = __import__("shutil").disk_usage(str(Path.home()))
        proc = psutil.Process(os.getpid())
        proc_cpu = proc.cpu_percent(interval=0.05)
        proc_ram = proc.memory_info().rss / (1024 ** 2)
    except Exception:
        cpu, vm, disk, proc_cpu, proc_ram = 0, None, None, 0, 0

    print("\n╔══════════════════════════════════════════════════════╗")
    print("║                 SOAR CONTROL CENTER                  ║")
    print("╠══════════════════════════════════════════════════════╣")
    print(f"║ Profile : {SOAR_ACTIVE_PROFILE:<39}║")
    print(f"║ Safe    : {'ON' if SOAR_SAFE_MODE else 'OFF':<39}║")
    print(f"║ Voice   : {'ON' if voice_enabled else 'OFF':<39}║")
    print(f"║ Auto-LW : {'ON' if SOAR_AUTO_LIGHTWEIGHT_ENABLED else 'OFF':<38}║")
    print(f"║ Mode    : {'LIGHTWEIGHT' if SOAR_LIGHTWEIGHT_MODE else 'NORMAL':<38}║")
    if vm is not None:
        print(f"║ System  : CPU {cpu:>5.1f}% | RAM {vm.percent:>5.1f}%             ║")
    else:
        print("║ System  : sensors unavailable                         ║")
    print(f"║ SOAR    : CPU {proc_cpu:>5.1f}% | RAM {proc_ram:>6.1f} MB         ║")
    if disk is not None:
        print(f"║ Disk    : {disk.free / (1024 ** 3):>6.1f} GB free                ║")
    else:
        print("║ Disk    : unavailable                                  ║")
    print("╠══════════════════════════════════════════════════════╣")
    print("║ 1. Modules                                           ║")
    print("║ 2. Diagnostics 2.0                                  ║")
    print("║ 3. Projects                                          ║")
    print("║ 4. Resources                                         ║")
    print("║ 5. Profiles                                          ║")
    print("║ 6. Scheduler                                         ║")
    print("║ 7. Logs / Events                                     ║")
    print("╚══════════════════════════════════════════════════════╝")

def control_center_command(rest, from_voice=False):
    selection = (rest or "").strip()
    show_control_center()
    if from_voice or not selection:
        print("Use: cc 1-7 to open a control panel.")
        return

    action = selection.split()[0]
    if action == "1":
        show_module_status()
    elif action == "2":
        diagnostics_2_command()
    elif action == "3":
        cmd_projects()
    elif action == "4":
        show_status()
        print(f"System CPU: {psutil.cpu_percent(interval=0.15):.1f}%")
        print(f"System RAM: {psutil.virtual_memory().percent:.1f}%")
    elif action == "5":
        profile_command("list")
    elif action == "6":
        schedule_list_command()
    elif action == "7":
        show_recent_log(20)
        show_recent_events(20)
    else:
        print("Control selection must be 1 through 7.")

def recovery_command(rest):
    action = (rest or "").strip().lower()
    if action in {"run", "restart", "all", "auto"}:
        restarted = []
        for module, info in list(MODULE_HEALTH.items()):
            if (
                info.get("status") == "failed"
                and module != "CORE"
                and not module_is_disabled(module)
            ):
                ok, msg = restart_module(module)
                print(msg)
                if ok:
                    restarted.append(module)
        if not restarted:
            print("No failed optional modules needed recovery.")
        emit_event("RECOVERY_RUN", {"restarted": restarted})
        return

    print("\n--- SOAR CRASH RECOVERY ---")
    for module, info in MODULE_HEALTH.items():
        if info.get("status") == "failed":
            print(f"  FAILED  {module}: {info.get('last_error', 'unknown error')}")
        else:
            print(f"  OK      {module}")
    print("Use: recovery run")
    print("---------------------------")

def restore_optional_modules_from_profile():
    """Restore only modules that are allowed by the active profile after lightweight mode."""
    global autocode_enabled
    if SOAR_SAFE_MODE:
        return

    profiles = get_profiles()
    config = profiles.get(SOAR_ACTIVE_PROFILE, DEFAULT_PROFILES["default"])
    apply_module_disable_state(config.get("disabled_modules", []))

    if module_is_enabled("VOICE") and bool(config.get("voice", True)):
        try:
            if tts_ready.is_set() and recognizer is not None and not voice_enabled:
                enable_voice()
                record_module_success("VOICE", "restored after lightweight mode")
        except Exception as e:
            record_module_failure("VOICE", e)

    if module_is_enabled("AUTOCODE") and bool(config.get("autocode", False)) and autocode_connected():
        autocode_stop.clear()
        autocode_enabled = True
        record_module_success("AUTOCODE", "restored after lightweight mode")

    if module_is_enabled("AVSS"):
        try:
            if avss_stop_event.is_set():
                start_avss_module()
        except Exception as e:
            record_module_failure("AVSS", e)


def initialize_feature_runtime():
    global FEATURE_RUNTIME_READY, SOAR_ACTIVE_PROFILE, SOAR_SAFE_MODE, voice_enabled
    global SOAR_AUTO_LIGHTWEIGHT_ENABLED, SOAR_MANUAL_DISABLED_MODULES
    global SOAR_DISABLED_MODULES, autocode_enabled

    if FEATURE_RUNTIME_READY:
        return

    load_module_health()
    profiles = get_profiles()
    SOAR_ACTIVE_PROFILE = get_active_profile()
    if SOAR_ACTIVE_PROFILE not in profiles:
        SOAR_ACTIVE_PROFILE = "default"
        save_active_profile("default")

    config = profiles[SOAR_ACTIVE_PROFILE]
    SOAR_SAFE_MODE = bool(config.get("safe_mode", False))
    settings = load_settings()
    SOAR_SAFE_MODE = bool(settings.get("safe_mode", SOAR_SAFE_MODE))

    SOAR_AUTO_LIGHTWEIGHT_ENABLED = bool(
        settings.get("auto_lightweight", config.get("auto_lightweight", True))
    )

    apply_module_disable_state(config.get("disabled_modules", []))
    SOAR_MANUAL_DISABLED_MODULES.update(get_module_overrides())
    SOAR_DISABLED_MODULES.update(SOAR_MANUAL_DISABLED_MODULES)

    limits = config.get("resource_limits")
    if isinstance(limits, dict):
        with resource_limit_lock:
            SOAR_RESOURCE_LIMITS["ram_bytes"] = limits.get("ram_bytes")
            SOAR_RESOURCE_LIMITS["cpu_percent"] = limits.get("cpu_percent")
            SOAR_RESOURCE_LIMITS["gpu_percent"] = limits.get("gpu_percent")
            globals()["SOAR_RESOURCE_LIMITS_ACTIVE"] = any(
                v is not None for v in SOAR_RESOURCE_LIMITS.values()
            )

    autocode_enabled = bool(
        config.get("autocode", False) and autocode_connected() and not SOAR_SAFE_MODE
    )
    if not autocode_enabled:
        autocode_stop.set()

    if not (bool(config.get("voice", True)) and module_is_enabled("VOICE") and not SOAR_SAFE_MODE):
        voice_enabled = False
    else:
        voice_enabled = True

    start_scheduler()
    FEATURE_RUNTIME_READY = True
    emit_event(
        "SOAR_FEATURE_RUNTIME_READY",
        {"profile": SOAR_ACTIVE_PROFILE, "safe_mode": SOAR_SAFE_MODE},
    )

def auto_lightweight_monitor():
    global SOAR_AUTO_LIGHTWEIGHT_LOW_SINCE, SOAR_AUTO_LIGHTWEIGHT_ACTIVE

    if not SOAR_AUTO_LIGHTWEIGHT_ENABLED or SOAR_SAFE_MODE:
        return

    try:
        vm = psutil.virtual_memory()
        cpu = psutil.cpu_percent(interval=0.05)
    except Exception:
        return

    pressure = vm.percent >= 85.0 or cpu >= 85.0
    now = time.time()

    if pressure and not SOAR_LIGHTWEIGHT_MODE:
        SOAR_AUTO_LIGHTWEIGHT_ACTIVE = True
        SOAR_AUTO_LIGHTWEIGHT_LOW_SINCE = None
        enter_lightweight_mode(
            f"automatic resource protection (system CPU {cpu:.1f}%, RAM {vm.percent:.1f}%)"
        )
        emit_event("AUTO_LIGHTWEIGHT_ON", {"cpu": cpu, "ram": vm.percent})
        return

    if SOAR_LIGHTWEIGHT_MODE and SOAR_AUTO_LIGHTWEIGHT_ACTIVE:
        if vm.percent <= 55.0 and cpu <= 55.0:
            if SOAR_AUTO_LIGHTWEIGHT_LOW_SINCE is None:
                SOAR_AUTO_LIGHTWEIGHT_LOW_SINCE = now
            elif now - SOAR_AUTO_LIGHTWEIGHT_LOW_SINCE >= 20.0:
                SOAR_AUTO_LIGHTWEIGHT_ACTIVE = False
                SOAR_AUTO_LIGHTWEIGHT_LOW_SINCE = None
                leave_lightweight_mode(restore_modules=True)
                emit_event("AUTO_LIGHTWEIGHT_OFF", {"cpu": cpu, "ram": vm.percent})
        else:
            SOAR_AUTO_LIGHTWEIGHT_LOW_SINCE = None

def handle_feature_command(raw, from_voice=False):
    text = str(raw).strip()
    lower = text.lower()

    if SOAR_SAFE_MODE and (
        lower.startswith("shell ")
        or lower.startswith("app ")
        or lower.startswith("openurl ")
        or lower.startswith("report ")
        or lower.startswith("message ")
        or lower.startswith("weather")
        or lower == "quote"
    ):
        print("SOAR Safe Mode blocked this external/system action.")
        return True

    if lower in {"help", "?"}:
        return False

    if lower in {"history", "history show"}:
        history_command("")
        return True
    if lower.startswith("history "):
        history_command(text[8:].strip())
        return True
    if lower == "!!":
        repeat_command("1")
        return True
    if lower.startswith("repeat"):
        rest = text[6:].strip()
        repeat_command(rest)
        return True

    if lower == "alias" or lower.startswith("alias "):
        alias_command(text[5:].strip())
        return True

    if lower == "profile" or lower.startswith("profile "):
        profile_command(text[7:].strip())
        return True

    if lower in {"modules", "module"} or lower.startswith("module "):
        module_manager_command(text[6:].strip())
        return True

    if lower in {"schedule", "scheduler"} or lower.startswith("schedule ") or lower.startswith("scheduler "):
        body = text.split(" ", 1)[1] if " " in text else ""
        schedule_command(body)
        return True

    if lower in {"what apps are running", "running apps", "list apps"}:
        list_running_apps()
        return True

    if lower in {"apps", "app"} or lower.startswith("app ") or lower.startswith("open app ") or lower.startswith("close app "):
        if lower.startswith("open app "):
            app_manager_open_short(text[9:].strip())
        elif lower.startswith("close app "):
            app_manager_close_short(text[10:].strip())
        else:
            body = text.split(" ", 1)[1] if " " in text else ""
            app_command(body)
        return True

    if lower.startswith("open ") and not lower.startswith("openurl "):
        target = text[5:].strip()
        known_app_names = {"chrome", "google chrome", "firefox", "safari", "minecraft", "discord", "spotify", "terminal", "finder", "vscode", "visual studio code", "code"}
        if target.lower() in known_app_names:
            app_manager_open_short(target)
            return True

    if lower.startswith("close "):
        target = text[6:].strip()
        known_app_names = {"chrome", "google chrome", "firefox", "safari", "minecraft", "discord", "spotify", "terminal", "finder", "vscode", "visual studio code", "code"}
        if target.lower() in known_app_names:
            app_manager_close_short(target)
            return True

    if lower.startswith("workspace ") or lower.startswith("ws "):
        body = text.split(" ", 1)[1] if " " in text else ""
        workspace_command(body)
        return True
    if lower == "workspace" or lower == "ws":
        workspace_command("")
        return True

    if lower.startswith("clipboard") or lower.startswith("clip"):
        if lower.startswith("clipboard"):
            body = text[9:].strip()
        else:
            body = text[4:].strip()
        clipboard_intelligence_command(body)
        return True

    if lower in {"diagnostics", "diag", "diagnostics 2", "diag 2", "diagnostics 2.0"}:
        diagnostics_2_command()
        return True

    if lower in {"recovery", "crash recovery"} or lower.startswith("recovery "):
        body = text.split(" ", 1)[1] if " " in text else ""
        recovery_command(body)
        return True

    if lower.startswith("project health") or lower.startswith("project scan"):
        parts = text.split(" ", 2)
        rest = parts[2] if len(parts) >= 3 else ""
        project_health_command(rest)
        return True

    if lower in {"safe mode", "safemode"} or lower.startswith("safe mode "):
        body = text.split(" ", 2)[2] if len(text.split(" ", 2)) >= 3 else ""
        safe_mode_command(body)
        return True

    if lower in {"events", "event log"} or lower.startswith("events "):
        body = text.split(" ", 1)[1] if " " in text else ""
        try:
            count = int(body) if body else 20
        except ValueError:
            count = 20
        show_recent_events(count)
        return True

    if lower.startswith("event emit "):
        body = text[11:].strip()
        chunks = body.split(" ", 1)
        name = chunks[0]
        payload = {"message": chunks[1]} if len(chunks) > 1 else {}
        emit_event(name, payload)
        print(f"Event emitted: {name}")
        return True

    if lower in {"control center", "dashboard", "center", "cc"} or lower.startswith("cc ") or lower.startswith("control center "):
        if lower.startswith("cc "):
            body = text[3:].strip()
        elif lower.startswith("control center "):
            body = text[15:].strip()
        else:
            body = ""
        control_center_command(body, from_voice=from_voice)
        return True

    if lower in {"auto lightweight", "smart lightweight", "autolw"}:
        global SOAR_AUTO_LIGHTWEIGHT_ENABLED
        SOAR_AUTO_LIGHTWEIGHT_ENABLED = not SOAR_AUTO_LIGHTWEIGHT_ENABLED
        settings = load_settings()
        settings["auto_lightweight"] = SOAR_AUTO_LIGHTWEIGHT_ENABLED
        save_settings(settings)
        print(f"Automatic lightweight mode: {'ON' if SOAR_AUTO_LIGHTWEIGHT_ENABLED else 'OFF'}")
        emit_event("AUTO_LIGHTWEIGHT_SETTING", {"enabled": SOAR_AUTO_LIGHTWEIGHT_ENABLED})
        return True

    if suggest_command(text):
        return True

    return False

def _process_command_wrapper(raw, from_voice=False, _skip_history=False):
    raw = str(raw or "").strip()
    if not raw:
        return

    normalized_raw = raw[1:].strip() if raw.startswith("/") else raw
    expanded = expand_alias(normalized_raw)
    if expanded != raw:
        print(f"[SOAR ALIAS] {raw.split()[0]} -> {expanded}")

    source = "voice" if from_voice else "terminal"
    command_key = raw.lower().strip()
    if not _skip_history and command_key not in {"history", "history show", "repeat", "!!"}:
        record_command_history(raw, source=source)

    emit_event("COMMAND_RECEIVED", {"source": source, "command": expanded[:300]})

    try:
        if handle_feature_command(expanded, from_voice=from_voice):
            return
        _process_command_core(expanded)
        record_module_success("CORE")
    except SystemExit:
        raise
    except Exception as e:
        record_module_failure("CORE", e)
        print(f"[SOAR COMMAND RECOVERY] {type(e).__name__}: {e}")
        if traceback.format_exc():
            emit_event("COMMAND_CRASH_RECOVERED", {
                "command": expanded[:300],
                "error": str(e),
            })

def process_command(raw, from_voice=False, _skip_history=False):
    return _process_command_wrapper(raw, from_voice=from_voice, _skip_history=_skip_history)

def _process_command_core(raw): #mods start 2
    if shutting_down or stop_event.is_set():
        return

    if not isinstance(raw, str):
        raw = str(raw) if raw is not None else ""

    text = raw.strip()
    if not text:
        return

    if text.startswith("/"):
        text = text[1:]

    lower = text.lower()

    import sys

    if hasattr(sys, "mod_commands"):
        try:
            for command_keyword, command_function in sys.mod_commands.items():
                if command_keyword.lower() in lower:
                    try:
                        command_function()
                    except TypeError:
                        try:
                            command_function(text)
                        except Exception as e:
                            print(f"[SOAR MOD] Error running '{command_keyword}': {e}")
                    except Exception as e:
                        print(f"[SOAR MOD] Error running '{command_keyword}': {e}")
                    return
        except Exception as e:
            print(f"[SOAR MOD] Command system error: {e}")

    try:
        parts = shlex.split(text)
    except Exception:
        parts = text.split()

    if not parts:
        return

    cmd = parts[0].lower()
    args = parts[1:]

    if cmd == "build":
        prompt_str = " ".join(parts[1:])

        if not prompt_str:
            print("[SOAR] Error: Please supply building targets details.")
            print("Usage: build <project parameters detail descriptions>")
            return

        print(
            f"[SOAR] Analyzing building prompt blueprints: "
            f"'{prompt_str}'"
        )

        agent = ProjectAgent(
            prompt=prompt_str,
            project_name="Autonomously_Generated_App"
        )

        agent.execute_pipeline()
        return

    if lower in {
        "cmd groqkeyon",
        "cmd groqkeyoff",
        "cmd groqkeystatus"
    }:
        response = handle_user_input("/" + lower)

        print(f"SOAR: {response}")

        try:
            speak(response, allow_sound=True)
        except Exception:
            pass

        return

    try:
        response = handle_user_input("/" + text)

        if response is not None:
            print(f"SOAR: {response}")

            try:
                speak(response, allow_sound=True)
            except Exception:
                pass

    except Exception as e:
        print(f"[SOAR] Command error: {e}") #mods end 2

    shutdown_words = {
        "exit", "quit", "bye", "shut down", "shutdown", "power off", "power down", "poweroff", "turn off"
    }

    if lower in shutdown_words:
        speak(maybe_address_user("Shutting down now. Goodbye!", chance=0.35), allow_sound=True)
        sys.exit(0)

    if lower == "pomodoro":
        speak(
            maybe_address_user(
                "Starting Pomodoro timer. 25 minutes of focus.", chance=0.35
            ),
            allow_sound=True,
        )
        time.sleep(25 * 60)
        speak(
            maybe_address_user(
                "Time's up! Great job. Starting 5-minute break now.", chance=0.35
            ),
            allow_sound=True,
        )
        time.sleep(5 * 60)
        speak(
            maybe_address_user(
                "Break finished! Ready for the next session.", chance=0.35
            ),
            allow_sound=True,
        )
        return

    if lower.startswith("weather"):
        city = " ".join(args) if args else "auto"
        encoded_city = quote_plus(city)
        url = f"https://wttr.in/{encoded_city}?format=j1"
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
            with urllib.request.urlopen(req) as response:
                data = json.loads(response.read().decode("utf-8"))
                
                curr = data["current_condition"][0]
                temp_c = curr.get("temp_C", "N/A")
                temp_f = curr.get("temp_F", "N/A")
                
                precip = curr.get("precipMM", "0.0")
                desc = curr["weatherDesc"][0]["value"].lower() if curr.get("weatherDesc") else ""
                
                is_raining = False
                rain_intensity = ""
                if "rain" in desc or "drizzle" in desc or float(precip) > 0:
                    is_raining = True
                    precip_val = float(precip)
                    if precip_val < 0.5:
                        rain_intensity = " (light)"
                    elif precip_val < 4.0:
                        rain_intensity = " (mild)"
                    else:
                        rain_intensity = " (heavy)"

                thunder = "Yes" if "thunder" in desc or "storm" in desc else "No"

                severe_chance = 0
                if "weather" in data and len(data["weather"]) > 0:
                    hourly = data["weather"][0].get("hourly", [])
                    if hourly:
                        chances = [
                            int(h.get("chanceofsevere", 0)) if "chanceofsevere" in h 
                            else int(h.get("chanceoftornado", 0)) 
                            for h in hourly
                        ]
                        severe_chance = max(chances) if chances else 0

                report_lines = [
                    f"Temperature: {temp_f}°F, {temp_c}°C",
                    f"Precipitation: {precip}mm",
                    f"Raining: {is_raining}{rain_intensity}",
                    f"Thunder: {thunder}"
                ]
                
                if is_raining:
                    report_lines.append(f"Hazardous/Tornado Weather Chance: {severe_chance}%")

                report = "\n".join(report_lines)
                print(f"\n[SOAR Weather]\n{report}\n")
                speak(
                    maybe_address_user("Here is the requested weather report.", chance=0.35),
                    allow_sound=True,
                )
        except Exception:
            speak(
                maybe_address_user(
                    "Sorry, I could not fetch the weather.", chance=0.35
                ),
                allow_sound=True,
            )
        return

    if lower == "quote":
        try:
            url = "https://api.quotable.io/random?tags=technology|wisdom"
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
            with urllib.request.urlopen(req) as response:
                data = json.loads(response.read().decode("utf-8"))
                text_out = f"Quote: {data['content']} by {data['author']}"
                speak(maybe_address_user(text_out, chance=0.35), allow_sound=True)
        except Exception:
            speak(
                maybe_address_user(
                    "Code is like humor. When you have to explain it, it's bad.",
                    chance=0.35,
                ),
                allow_sound=True,
            )
        return

    if lower in ("git status", "git-status"):
        try:
            res = subprocess.run(
                ["git", "status", "-s"], capture_output=True, text=True, check=True
            )
            if not res.stdout.strip():
                msg = "Working tree is clean. No uncommitted changes."
            else:
                msg = "You have uncommitted git changes."
            speak(maybe_address_user(msg, chance=0.35), allow_sound=True)
        except Exception:
            speak(
                maybe_address_user(
                    "Error: This directory is not a git repository.", chance=0.35
                ),
                allow_sound=True,
            )
        return

    if lower.startswith("json format") or lower.startswith("json-fmt"):
        target = " ".join(args)
        if not target:
            speak(
                maybe_address_user(
                    "Please provide a JSON string or file path.", chance=0.35
                ),
                allow_sound=True,
            )
            return
        content = ""
        if os.path.isfile(target):
            try:
                with open(target, "r") as f:
                    content = f.read()
            except Exception:
                speak(
                    maybe_address_user("Error reading the specified file.", chance=0.35),
                    allow_sound=True,
                )
                return
        else:
            content = target
        try:
            parsed = json.loads(content)
            print(json.dumps(parsed, indent=4))
            speak(
                maybe_address_user("Valid JSON formatted successfully.", chance=0.35),
                allow_sound=True,
            )
        except json.JSONDecodeError as e:
            speak(
                maybe_address_user(f"Invalid JSON: {e.msg}", chance=0.35),
                allow_sound=True,
            )
        return

    if lower in ("dep scan", "dep-scan"):
        req_file = "requirements.txt"
        if not os.path.isfile(req_file):
            speak(
                maybe_address_user(
                    "No requirements file found in the current directory.", chance=0.35
                ),
                allow_sound=True,
            )
            return
        try:
            pip_res = subprocess.run(
                ["pip", "list", "--format=freeze"],
                capture_output=True,
                text=True,
                check=True,
            )
            installed = {
                line.split("==")[0].lower()
                for line in pip_res.stdout.splitlines()
                if "==" in line
            }
            missing = []
            with open(req_file, "r") as f:
                for line in f:
                    line = line.strip()
                    if not line or line.startswith("#"):
                        continue
                    pkg = line.split("==")[0].split(">=")[0].split("<=")[0].strip().lower()
                    if pkg not in installed:
                        missing.append(pkg)
            if not missing:
                msg = "All requirements are installed."
            else:
                msg = f"Missing packages: {', '.join(missing)}"
            speak(maybe_address_user(msg, chance=0.35), allow_sound=True)
        except Exception:
            speak(
                maybe_address_user("Error scanning dependencies.", chance=0.35),
                allow_sound=True,
            )
        return

    if lower in {"help", "?"}:
        show_help()
        speak("I can help with commands, notes, memories, tasks, files, reminders, code files, and voice.", allow_sound=True)
        return

    if lower == "hard exit":
        force_hard_exit()
        return

    if lower in shutdown_words:
        raise SystemExit

    if lower == "clear":
        os.system("cls" if os.name == "nt" else "clear")
        return

    if lower == "time":
        speak(maybe_address_user(f"It is {datetime.now().strftime('%I:%M:%S %p')}", chance=0.35), allow_sound=True)
        return

    if lower == "date":
        speak(maybe_address_user(f"Today is {datetime.now().strftime('%A, %B %d, %Y')}", chance=0.35), allow_sound=True)
        return

    if lower == "uptime":
        up = str(datetime.now() - STARTUP_TIME).split(".")[0]
        speak(maybe_address_user(f"Uptime is {up}", chance=0.25), allow_sound=True)
        return

    if lower.startswith("report ") or lower == "report":
        description = raw[7:].strip() if len(raw) > 7 else ""
        
        if len(description) > 50:
            speak(maybe_address_user("Error: Bug description must be 50 characters or less."), allow_sound=True)
            return
            
        if not description:
            speak(maybe_address_user("Error: Please provide a bug description. Example: report broken_button"), allow_sound=True)
            return
            
        LAST_REPORT_FILE = DATA_DIR / "last_report_date.txt"
        today_str = datetime.now().strftime("%Y-%m-%d")
        
        if LAST_REPORT_FILE.exists():
            last_date = LAST_REPORT_FILE.read_text(encoding="utf-8").strip()
            if last_date == today_str:
                speak(maybe_address_user("Error: You can only report one bug per day."), allow_sound=True)
                return
                
        try:
            url = "https://www.soardownload.com/report.php"
            
            payload = {"description": description}
            
            req_post = urllib.request.Request(
                url,
                data=json.dumps(payload).encode("utf-8"),
                headers={"Content-Type": "application/json", "User-Agent": "SOAR-Client"},
                method="POST"
            )
            with urllib.request.urlopen(req_post, context=ssl_context) as response:
                if response.status == 200:
                    resp_data = json.loads(response.read().decode("utf-8"))
                    assigned_id = resp_data.get("id", "#")
                    LAST_REPORT_FILE.write_text(today_str, encoding="utf-8")
                    speak(maybe_address_user(f"Bug successfully reported under ID #{assigned_id}!"), allow_sound=True)
                    return
                else:
                    speak(maybe_address_user(f"Server returned an unexpected response code: {response.status}"), allow_sound=True)
                    return
                    
        except Exception as e:
            speak(maybe_address_user(f"Failed to submit report to server: {e}"), allow_sound=True)
            return
    
    if lower == "autocode check" or lower == "autocode status" or lower == "auto code check":
        speak(maybe_address_user("Checking autocode folder...", chance=0.2), allow_sound=True)
        
        time.sleep(5) 
        
        try:
            print("\n================ SOAR AUTOCODE DIAGNOSTICS ================")
            if not autocode_connected():
                print("  Engine Status: OFFLINE")
                print("===========================================================")
                speak(maybe_address_user("Autocode engine is currently offline.", chance=0.2), allow_sound=True)
                return

            ac_dir = getattr(soar_autocode, "AUTOCODE_DIR", PROJECTS_DIR / "Autocode")
            
            if ac_dir.exists():
                projects = [d for d in ac_dir.iterdir() if d.is_dir() and not d.name.startswith(("_", "."))]
                py_files = list(ac_dir.rglob("*.py"))
                web_files = list(ac_dir.rglob("*.html")) + list(ac_dir.rglob("*.js")) + list(ac_dir.rglob("*.css"))
                
                print(f"  Workspace: {ac_dir.name}/")
                print(f"  Active Projects: {len(projects)}")
                print(f"  Source Files: {len(py_files)} Python | {len(web_files)} Web")
            else:
                print("  Workspace: Not initialized")

            if hasattr(soar_autocode, "load_state"):
                state = soar_autocode.load_state()
                print(f"  Total Cycles: {state.get('run_count', 0)}")
                print(f"  Memory Nodes: {len(state.get('memory', []))}")
                
                weights = state.get('template_weights', {})
                if weights:
                    top_temp = max(weights.items(), key=lambda x: x[1])
                    print(f"  Dominant Template: {top_temp[0]} ({top_temp[1]} bias)")

            if hasattr(soar_autocode, "SOAR_AUTOCODE_TWO") and soar_autocode.SOAR_AUTOCODE_TWO:
                print("  Advanced Extension: ACTIVE")
                ext = soar_autocode.SOAR_AUTOCODE_TWO
                if hasattr(ext, "load_state"):
                    ext_state = ext.load_state()
                    topics = ext_state.get("web_topics", {})
                    if topics:
                        top_topic = max(topics.items(), key=lambda x: x[1])
                        print(f"  Learned Topic Lead: {top_topic[0]}")
            else:
                print("  Advanced Extension: OFFLINE")

            print("===========================================================\n")
            speak(maybe_address_user("Autocode diagnostic scan complete.", chance=0.2), allow_sound=True)
            return
            
        except Exception as e:
            print(f"Autocode Scan Error: {e}")
            speak(maybe_address_user("Autocode directory scan failed.", chance=0.1), allow_sound=True)
            return

    if lower == "ping":
        speak(maybe_address_user("pong", chance=0.2), allow_sound=True)
        return
    
    if lower.startswith("view "):
        try:
            target_file = text[5:].strip().strip('"').strip("'")
            file_path = BASE_DIR / target_file if not os.path.isabs(target_file) else Path(target_file)
            
            if not file_path.exists():
                file_path = DATA_DIR / target_file

            if file_path.exists() and file_path.is_file():
                print(f"\n--- Reading: {file_path.name} ---")
                with open(file_path, "r", encoding="utf-8", errors="ignore") as f:
                    for i, line in enumerate(f):
                        if i >= 50:
                            print("... [Output truncated after 50 lines] ...")
                            break
                        print(line.rstrip())
                print("-----------------------------\n")
            else:
                print("Error: Target file could not be resolved or found.")
            return
        except Exception as e:
            print(f"Viewer Error: {e}")
            return
        
# ======================================================
# ACHDS (Advanced Code Helper Diagnostic System) V 1.1 
# SOAR Help Module #001
# Made by Philip Kluz 2026 Jun 24 Late
# "atch-dee-ess"
#======================================================

    if lower.startswith("help me with this code") or lower.startswith("code help") or lower.startswith("achds"):
        try:
            import re
            import shutil
            import ast
            import os
            from pathlib import Path
            import sys

            if lower.startswith("help me with this code"):
                cmd_len = 22
            elif lower.startswith("code help"):
                cmd_len = 9
            elif lower.startswith("achds"):
                cmd_len = 5
            else:
                cmd_len = 0

            raw_input = text[cmd_len:].strip()

            if not raw_input:
                print("Usage Error: code help <file_path> [line_start - line_end]")
                return

            line_range = None
            if " - " in raw_input or "-" in raw_input:
                parts = raw_input.rsplit(" ", 1)
                potential_range = parts[-1].strip()
                if "-" in potential_range:
                    sub_parts = potential_range.split("-")
                    if len(sub_parts) == 2 and sub_parts[0].strip().isdigit() and sub_parts[1].strip().isdigit():
                        line_range = (int(sub_parts[0]), int(sub_parts[1]))
                        raw_input = parts[0].strip()

            target_path = raw_input.strip('"').strip("'")
            file_path = Path(target_path)

            if not file_path.is_absolute():
                base_dir = globals().get('BASE_DIR', Path.cwd())
                data_dir = globals().get('DATA_DIR', Path.cwd())
                
                if (base_dir / target_path).exists():
                    file_path = base_dir / target_path
                elif (data_dir / target_path).exists():
                    file_path = data_dir / target_path
                else:
                    file_path = base_dir / target_path 

            if not file_path.exists() or not file_path.is_file():
                print(f"Error: Target code asset '{target_path}' could not be resolved or found at {file_path}.")
                return

            with open(file_path, "r", encoding="utf-8", errors="ignore") as f:
                lines = f.readlines()

            start_idx = 0
            end_idx = len(lines)
            if line_range:
                start_idx = max(0, line_range[0] - 1)
                end_idx = min(len(lines), line_range[1])

            target_lines = lines[start_idx:end_idx]
            code_text = "".join(target_lines)

            print(f"\n================ SOAR ADVANCED STATIC CODE ANALYSIS ================")
            print(f"  Target File : {file_path.name}")
            print(f"  Scope       : Lines {start_idx + 1} to {end_idx}")
            print(f"  Engine Mode : Extensible Multi-Pass Diagnostics & Auto-Repair")
            print("-" * 68)

            issues = []

            try:
                compile(code_text, file_path.name, "exec")
            except SyntaxError as syntax_err:
                issues.append(f"[CRITICAL SYNTAX ERROR] Line {start_idx + syntax_err.lineno}: {syntax_err.msg}\n  -> Fix: Adjust syntax structure near token '{syntax_err.text.strip() if syntax_err.text else ''}'")

            def check_silent_exceptions(t_lines, s_idx, all_lines):
                found = []
                for idx, line in enumerate(t_lines, start=s_idx + 1):
                    if re.match(r'^\s*except.*:', line):
                        if idx < len(all_lines) and re.match(r'^\s*pass\s*$', all_lines[idx]):
                            found.append(f"[ANTI-PATTERN] Line {idx}: Silent exception handling ('except: pass').\n  -> Action: Auto-patching with logging wrapper.")
                return found

            def check_mutable_defaults(t_lines, s_idx, all_lines):
                found = []
                for idx, line in enumerate(t_lines, start=s_idx + 1):
                    if re.search(r'def\s+\w+\(.*\w+\s*=\s*(\[\]|\{\}).*\):', line):
                        found.append(f"[PERFORMANCE/LOGIC WARNING] Line {idx}: Mutable default argument detected.\n  -> Action: Auto-patching with internal scope instantiation.")
                return found

            def check_unsafe_execution(t_lines, s_idx, all_lines):
                found = []
                for idx, line in enumerate(t_lines, start=s_idx + 1):
                    if re.search(r'\beval\s*\(', line):
                        found.append(f"[SECURITY WARNING] Line {idx}: Use of eval() detected.\n  -> Action: Auto-patching to ast.literal_eval() and injecting imports.")
                    if re.search(r'\bexec\s*\(', line):
                        found.append(f"[SECURITY CRITICAL] Line {idx}: Use of exec() detected. Cannot auto-patch safely.")
                return found

            def check_hardcoded_secrets(t_lines, s_idx, all_lines):
                found = []
                secret_patterns = [r'(api_key|password|secret|token)\s*=\s*[\'"][a-zA-Z0-9_\-]+[\'"]']
                for idx, line in enumerate(t_lines, start=s_idx + 1):
                    for pat in secret_patterns:
                        if re.search(pat, line, re.IGNORECASE):
                            found.append(f"[SECURITY WARNING] Line {idx}: Potential hardcoded secret detected.\n  -> Action: Review manually for environment variable migration.")
                return found

            diagnostic_pipeline = [
                check_silent_exceptions,
                check_mutable_defaults,
                check_unsafe_execution,
                check_hardcoded_secrets
            ]

            for checker in diagnostic_pipeline:
                try:
                    issues.extend(checker(target_lines, start_idx, lines))
                except Exception:
                    continue

            if not issues:
                print("  Analysis Metrics: 0 Faults Detected.")
                print("  Status: All structured heuristics verified cleanly.")
                print("====================================================================\n")
                return
            else:
                print(f"  Analysis Metrics: {len(issues)} Faults Isolated.\n")
                for issue in issues:
                    print(issue)
                    print("-" * 68)
                print("====================================================================\n")

            try:
                speak("Advanced script pipeline diagnostics completed.", allow_sound=True, gender="female", custom_name="ACHDS")
            except NameError:
                print("[SYSTEM] Advanced script pipeline diagnostics completed.")

            action = input("Type 'Fix' to attempt automated non-destructive corrections, or press Enter to skip: ").strip()
            if action.lower() == "fix":
                warning_msg = "WARNING: ACHDS will map an Abstract Syntax Tree to repair bugs safely. A backup will be generated automatically."
                print(f"\n[SYSTEM NOTIFICATION] {warning_msg}")
                try:
                    speak("Warning. Auto formatting will initiate code backups. Type Proceed to confirm, or Bail to abort.", allow_sound=True, gender="female", custom_name="ACHDS")
                except NameError:
                    print("[SYSTEM] Warning. Auto formatting will initiate code backups. Type Proceed to confirm, or Bail to abort.")

                confirm = input("> ").strip()

                if confirm.lower() == "proceed":
                    backup_file = file_path.with_name(f"{file_path.stem}_backup{file_path.suffix}")
                    try:
                        shutil.copy2(file_path, backup_file)
                        print(f"\n[BACKUP] Safety copy preserved at: {backup_file.name}")
                    except Exception as b_err:
                        print(f"[BACKUP ERROR] Failed to create backup ({b_err}). Aborting fix to prevent data loss.")
                        return

                    print("[SOAR AST ENGINE] Commencing Abstract Syntax Tree refactoring...")

                    try:
                        code_lines = code_text.split('\n')
                        tree = None
                        max_retries = 50 

                        for attempt in range(max_retries):
                            try:
                                tree = ast.parse("\n".join(code_lines), filename=file_path.name)
                                break
                            except SyntaxError as e:
                                if e.lineno is not None:
                                    print(f"  [FORCE MODE] Bypassing SyntaxError on line {e.lineno}: {e.msg}")
                                    idx = e.lineno - 1
                                    if 0 <= idx < len(code_lines):
                                        code_lines[idx] = f"# [ACHDS FORCE-BYPASSED] {code_lines[idx]}"
                                    else:
                                        print("  [AST BREAKDOWN] SyntaxError points to out-of-bounds line. Aborting parse.")
                                        break
                                else:
                                    print("  [AST BREAKDOWN] Unresolvable syntax layout. Aborting parse.")
                                    break
                        
                        if not tree:
                            raise Exception("Could not resolve enough syntax errors to build a tree.")

                        class SOARCodeTransformer(ast.NodeTransformer):
                            def __init__(self):
                                self.modified = False
                                self.required_imports = set()
                                self.builtins_to_rename = {"list", "dict", "str", "int", "type", "dir", "len", "sum", "set", "tuple"}

                            def visit_Module(self, node):
                                self.generic_visit(node)
                                if self.required_imports:
                                    import_nodes = [ast.Import(names=[ast.alias(name=mod, asname=None)]) for mod in self.required_imports]
                                    node.body = import_nodes + node.body
                                return node

                            def visit_Call(self, node):
                                self.generic_visit(node)
                                if isinstance(node.func, ast.Name):
                                    if node.func.id == 'eval':
                                        self.required_imports.add('ast')
                                        node.func = ast.Attribute(
                                            value=ast.Name(id='ast', ctx=ast.Load()),
                                            attr='literal_eval',
                                            ctx=ast.Load()
                                        )
                                        self.modified = True
                                return node

                            def visit_Try(self, node):
                                self.generic_visit(node)
                                for handler in node.handlers:
                                    if len(handler.body) == 1 and isinstance(handler.body[0], ast.Pass):
                                        handler.type = ast.Name(id='Exception', ctx=ast.Load())
                                        handler.name = 'e'
                                        log_msg = "Exception handled structurally via SOAR wrapper: "
                                        new_log_node = ast.Expr(
                                            value=ast.Call(
                                                func=ast.Name(id='print', ctx=ast.Load()),
                                                args=[ast.JoinedStr(values=[
                                                    ast.Constant(value=log_msg),
                                                    ast.FormattedValue(value=ast.Name(id='e', ctx=ast.Load()), conversion=-1)
                                                ])],
                                                keywords=[]
                                            )
                                        )
                                        handler.body = [new_log_node]
                                        self.modified = True
                                return node

                            def visit_FunctionDef(self, node):
                                if node.name in ["process_command", "check_silent_exceptions", "check_input_types"]:
                                    return node

                                self.generic_visit(node)

                                injected_body = []
                                if node.args.defaults:
                                    new_defaults = []
                                    args_with_defaults = node.args.args[-len(node.args.defaults):]

                                    for arg, default in zip(args_with_defaults, node.args.defaults):
                                        if isinstance(default, (ast.List, ast.Dict)):
                                            new_defaults.append(ast.Constant(value=None))

                                            test = ast.Compare(
                                                left=ast.Name(id=arg.arg, ctx=ast.Load()),
                                                ops=[ast.Is()],
                                                comparators=[ast.Constant(value=None)]
                                            )
                                            assign = ast.Assign(
                                                targets=[ast.Name(id=arg.arg, ctx=ast.Store())],
                                                value=default
                                            )
                                            injected_body.append(ast.If(test=test, body=[assign], orelse=[]))
                                            self.modified = True
                                        else:
                                            new_defaults.append(default)
                                    node.args.defaults = new_defaults

                                if injected_body:
                                    node.body = injected_body + node.body

                                new_body = []
                                term_found = False
                                for expr in node.body:
                                    if term_found:
                                        self.modified = True
                                        continue
                                    new_body.append(expr)
                                    if isinstance(expr, (ast.Return, ast.Break, ast.Continue, ast.Raise)):
                                        term_found = True
                                node.body = new_body

                                return node

                            def visit_While(self, node):
                                self.generic_visit(node)
                                if isinstance(node.test, ast.Constant) and node.test.value is True:
                                    has_break = any(isinstance(sub, (ast.Break, ast.Return, ast.Raise)) for sub in ast.walk(node))
                                    if not has_break:
                                        node.body.append(ast.Break())
                                        self.modified = True
                                return node

                            def visit_Compare(self, node):
                                self.generic_visit(node)
                                for i, op in enumerate(node.ops):
                                    if isinstance(op, ast.Is) or isinstance(op, ast.IsNot):
                                        comp = node.comparators[i]
                                        if isinstance(comp, ast.Constant) and type(comp.value) in (int, float, str, bytes):
                                            node.ops[i] = ast.Eq() if isinstance(op, ast.Is) else ast.NotEq()
                                            self.modified = True
                                return node

                            def visit_Assign(self, node):
                                self.generic_visit(node)
                                for target in node.targets:
                                    if isinstance(target, ast.Name) and target.id in self.builtins_to_rename:
                                        target.id = f"{target.id}_var"
                                        self.modified = True
                                return node

                        transformer = SOARCodeTransformer()
                        modified_tree = transformer.visit(tree)
                        ast.fix_missing_locations(modified_tree)

                        if hasattr(ast, 'unparse'):
                            rebuilt_code = ast.unparse(modified_tree)
                        else:
                            raise Exception("Python 3.9+ is required for advanced AST unparsing.")

                        with open(file_path, "w", encoding="utf-8") as f:
                            f.write(rebuilt_code)

                        print(f"[SOAR AST ENGINE] Repair sequence completed cleanly. Structural modifications written to: {file_path.name}\n")
                        try:
                            speak("Automated syntax aware tree repairs complete.", allow_sound=True, gender="female", custom_name="ACHDS")
                        except NameError:
                            print("[SYSTEM] Automated syntax aware tree repairs complete.")

                    except Exception as ast_err:
                        print(f"[AST BREAKDOWN] Tree compilation error occurred: {ast_err}")
                        print("Operation safely aborted. Target script restored to original state.")
                else:
                    print("[ABORT] Operation terminated safely by user.\n")
            return

        except Exception as e:
            print(f"Advanced Analysis Pipeline Error: {e}")
            return
        
    if lower.startswith("csrs "):
        if SOAR_LIGHTWEIGHT_MODE or "CSRS" in SOAR_DISABLED_MODULES:
            return maybe_address_user("CSRS is disabled while SOAR is in lightweight mode.")
        try:
            import platform
            import subprocess
            from pathlib import Path

            cmd = lower.strip()
            csrs_arg = cmd[5:].strip() if len(cmd) > 5 else "run"

            speak(
                maybe_address_user("Launching Connection Server Request System.", chance=0.2),
                allow_sound=True
            )

            csrs_script = Path(__file__).resolve().parent / "csrs.py"

            if not csrs_script.exists():
                print("Error: csrs.py not found in the root directory.")
                return

            sys_os = platform.system().lower()

            if "windows" in sys_os:
                subprocess.Popen([
                    "cmd.exe", "/c", "start", "/max", "cmd", "/k",
                    "python", str(csrs_script), csrs_arg
                ])

            elif "darwin" in sys_os:
                apple_script = (
                    f'tell application "Terminal"\n'
                    f'    do script "python3 \\"{csrs_script}\\" \\"{csrs_arg}\\""\n'
                    f'    activate\n'
                    f'end tell\n'
                    f'tell application "System Events" to keystroke "f" using {{command down, control down}}'
                )
                subprocess.Popen(["osascript", "-e", apple_script])

            elif "linux" in sys_os:
                subprocess.Popen([
                    "x-terminal-emulator",
                    "--maximize",
                    "-e",
                    f"python3 {csrs_script} {csrs_arg}"
                ])

            else:
                print("Unsupported OS for CSRS terminal execution.")

        except Exception as e:
            print(f"Failed to launch CSRS Engine: {e}")

        return maybe_address_user("")
    
    if lower.startswith("read ") or lower.startswith("constant read "):
        try:
            is_constant = lower.startswith("constant read ")
            path_string = text[14:].strip() if is_constant else text[5:].strip()
            target_path = path_string.strip('"').strip("'")
            
            file_path = Path(target_path) if os.path.isabs(target_path) else BASE_DIR / target_path
            if not file_path.exists():
                file_path = DATA_DIR / target_path

            if not file_path.exists() or not file_path.is_file():
                print("Error: Target file could not be resolved or found.")
                return

            if not is_constant:
                print(f"\n--- Reading: {file_path.name} ---")
                with open(file_path, "r", encoding="utf-8", errors="ignore") as f:
                    print(f.read())
                print("-----------------------------\n")
                speak("File playback complete.", allow_sound=True)
            else:
                print(f"\n--- Constant Reading: {file_path.name} ---")
                print("Press Ctrl+C to terminate constant streaming loop.\n")
                
                with open(file_path, "r", encoding="utf-8", errors="ignore") as f:
                    while True:
                        line = f.readline()
                        if line:
                            print(line.rstrip())
                        else:
                            time.sleep(0.5)
                            
        except KeyboardInterrupt:
            print("\nConstant read stream terminated safely.\n")
            return
        except Exception as e:
            print(f"Read Error: {e}")
            return
        return
    
    if lower.startswith("run app diagnostic "):
        try:
            target_app = text[19:].strip().strip('"').strip("'")
            if not target_app:
                print("Usage Error: run app diagnostic <app_name_or_process>")
                speak(maybe_address_user("Please provide a valid application identifier.", chance=0.1), allow_sound=True)
                return

            print(f"\n================ SOAR DYNAMIC APP DIAGNOSTICS ================")
            print(f"  Target Application : {target_app}")
            print(f"  Scan Timestamp     : {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
            print(f"  Status Check       : Analyzing system runtime space...")
            print("-" * 62)

            import subprocess
            import platform
            current_os = platform.system().lower()
            process_found = False

            if "windows" in current_os:
                cmd = f'tasklist /FI "IMAGENAME eq {target_app}" /FO CSV /NH'
                if not target_app.lower().endswith(".exe"):
                    cmd = f'tasklist /FI "IMAGENAME eq {target_app}.exe" /FO CSV /NH'
                
                output = subprocess.check_output(cmd, shell=True, text=True, stderr=subprocess.DEVNULL)
                
                if "No tasks are running" not in output and output.strip():
                    lines = output.strip().split("\n")
                    process_found = True
                    print(f"  [METRIC] Execution Status : ACTIVE")
                    print(f"  [METRICS] Active Instances : {len(lines)}")
                    
                    for line in lines:
                        try:
                            parts = [p.strip('"') for p in line.split(',')]
                            if len(parts) >= 5:
                                print(f"    -> PID: {parts[1]} | Session: {parts[2]} | Memory Usage: {parts[4]}")
                        except Exception:
                            continue
            
            elif "darwin" in current_os or "linux" in current_os:
                cmd = ["ps", "-eo", "pid,ppid,%cpu,%mem,comm"]
                output = subprocess.check_output(cmd, text=True, stderr=subprocess.DEVNULL)
                lines = output.strip().split("\n")
                
                instances = []
                for line in lines[1:]:
                    parts = line.split(None, 4)
                    if len(parts) >= 5 and target_app.lower() in parts[4].lower():
                        instances.append(parts)
                
                if instances:
                    process_found = True
                    print(f"  [METRIC] Execution Status : ACTIVE")
                    print(f"  [METRIC] Active Instances : {len(instances)}")
                    for inst in instances:
                        print(f"    -> PID: {inst[0]} | Parent PID: {inst[1]} | CPU Load: {inst[2]}% | Memory Alloc: {inst[3]}%")
                        print(f"       Binary Pathway: {inst[4]}")

            if not process_found:
                print(f"  [METRIC] Execution Status : INACTIVE / NOT FOUND")
                print(f"  [WARNING] The target program profile is not currently executing in memory.")
                print(f"  [ADVICE] Verify spelling or launch the application manually via native desktop triggers.")

            print("==============================================================\n")
            speak(maybe_address_user("Application analysis complete.", chance=0.15), allow_sound=True)
            return

        except Exception as diagnostic_err:
            print(f"Advanced Analyzer Failure: {str(diagnostic_err)}")
            speak(maybe_address_user("Failed to complete full process diagnostics.", chance=0.1), allow_sound=True)
            return
    
    if lower == "i love you":
        speak(maybe_address_user("Can't pull what your into, and can't pull me either ", chance=0.2), allow_sound=True)
        return
    
    if lower == "You are funny":
        speak(maybe_address_user("Thank you, but your not", chance=0.2), allow_sound=True)
        return

    if lower == "status":
        show_status()
        speak(maybe_address_user("Status shown in terminal.", chance=0.2), allow_sound=True)
        return

    if lower == "projects":
        cmd_projects()
        speak(maybe_address_user("Projects folder opened.", chance=0.15), allow_sound=True)
        return

    if lower == "data":
        cmd_data()
        speak(maybe_address_user("Data folder opened.", chance=0.15), allow_sound=True)
        return

    if lower.startswith("logs"):
        cmd_logs(text[4:].strip())
        speak(maybe_address_user("Logs shown in terminal.", chance=0.15), allow_sound=True)
        return

    if lower in {"autocode on", "start autocode"}:
        if SOAR_LIGHTWEIGHT_MODE or "AUTOCODE" in SOAR_DISABLED_MODULES:
            speak("Autocode is disabled while SOAR is in lightweight mode.", allow_sound=True)
            return
        global autocode_enabled
        autocode_enabled = True
        autocode_stop.clear()
        speak("Autocode enabled.", allow_sound=True)
        return

    if lower in {"autocode off", "stop autocode"}:
        autocode_enabled = False
        autocode_stop.set()
        speak("Autocode disabled.", allow_sound=True)
        return

    if lower.startswith("autocode"):
        parts = lower.split(maxsplit=1)
        sub = parts[1] if len(parts) > 1 else ""
        if sub in {"", "run"}:
            if trigger_autocode("manual trigger from main"):
                speak("Autocode running.", allow_sound=True)
            return
        if sub == "status":
            show_autocode_status()
            speak("Autocode status shown.", allow_sound=True)
            return
        print("Usage: autocode or autocode status")
        return

    if lower.startswith("say "):
        speak(text[4:].strip(), allow_sound=True)
        return
    
    if lower.startswith("message ") or lower.startswith("sms "):
        try:
            raw_payload = text[text.find(" ") + 1:].strip()
            if not raw_payload or " to " not in raw_payload.lower():
                print("Usage Error: message <text content> to <contact_name_or_number>")
                speak(maybe_address_user("Please provide a message body and a contact target.", chance=0.1), allow_sound=True)
                return

            split_keyword = " to " if " to " in raw_payload else " TO "
            parts = raw_payload.split(split_keyword)
            
            message_body = parts[0].strip()
            contact_target = parts[1].strip()

            if not message_body or not contact_target:
                print("Usage Error: Empty message body or contact destination specified.")
                return

            print(f"\n================ SOAR OUTBOUND LOGISTICS ================")
            print(f"  Target Destination : {contact_target}")
            print(f"  Payload Structure  : '{message_body}'")
            print(f"  Status Check       : Routing through active channels...")

            import platform
            current_os = platform.system().lower()
            
            if "darwin" in current_os:
                import subprocess
                clean_msg = message_body.replace('"', '\\"')
                
                if any(char.isdigit() for char in contact_target) or "@" in contact_target:
                    apple_script = f'''
                    tell application "Messages"
                        set targetService to 1st service whose service type is iMessage
                        set targetBuddy to buddy "{contact_target}" of targetService
                        send "{clean_msg}" to targetBuddy
                    end tell
                    '''
                else:
                    apple_script = f'tell application "Messages" to send "{clean_msg}" to buddy "{contact_target}"'
                
                subprocess.run(["osascript", "-e", apple_script], check=True)
                print("  Gateway Response   : Delivered locally via macOS Messages engine.")
            else:
                simulated_log = DATA_DIR / "outbound_sms.log"
                with open(simulated_log, "a", encoding="utf-8") as f:
                    f.write(f"[{datetime.now().isoformat()}] TO: {contact_target} | BODY: {message_body}\n")
                print(f"  Gateway Response   : Sent via Virtual SMS Relay. Logged to data file system.")

            print("=========================================================\n")
            speak(maybe_address_user("Message dispatched successfully.", chance=0.15), allow_sound=True)
            return

        except Exception as msg_err:
            print(f"Outbound Dispatch Failure: {str(msg_err)}")
            speak(maybe_address_user("Failed to execute messaging transmission protocol.", chance=0.1), allow_sound=True)
            return

    math_triggers = (
        "calc ",
        "calculate ",
        "what's ",
        "solve ",
        "evaluate ",
        "graph ",
        "plot ",
    )

    if lower.startswith(math_triggers):
        try:
            import math
            pass
            
            def parse_advanced_math(raw_expr):
                cleaned = raw_expr.lower().strip()
                mappings = {
                    "pi": str(math.pi),
                    "e": str(math.e),
                    "arcsine": "math.asin",
                    "arccosine": "math.acos",
                    "arctangent": "math.atan",
                    "arcsin": "math.asin",
                    "arccos": "math.acos",
                    "arctan": "math.atan",
                    "sine": "math.sin",
                    "cosine": "math.cos",
                    "tangent": "math.tan",
                    "sin": "math.sin",
                    "cos": "math.cos",
                    "tan": "math.tan",
                    "asin": "math.asin",
                    "acos": "math.acos",
                    "atan": "math.atan",
                    "sinh": "math.sinh",
                    "cosh": "math.cosh",
                    "tanh": "math.tanh",
                    "squareroot": "math.sqrt",
                    "sqrt": "math.sqrt",
                    "log10": "math.log10",
                    "log": "math.log",
                    "exp": "math.exp",
                    "radians": "math.radians",
                    "degrees": "math.degrees",
                    "abs": "abs",
                    "pow": "pow",
                    "factorial": "math.factorial",
                    "^": "**"
                }
                for key, val in mappings.items():
                    if key in ["sin", "cos", "tan", "log", "exp", "sqrt", "abs"]:
                        cleaned = cleaned.replace(f"{key}(", f"{val}(")
                    else:
                        cleaned = cleaned.replace(key, val)
                return cleaned

            def safe_eval_expression(expression_str, variables=None):
                if variables is None:
                    variables = {}
                allowed_names = {
                    "math": math,
                    "sin": math.sin,
                    "cos": math.cos,
                    "tan": math.tan,
                    "asin": math.asin,
                    "acos": math.acos,
                    "atan": math.atan,
                    "sinh": math.sinh,
                    "cosh": math.cosh,
                    "tanh": math.tanh,
                    "sqrt": math.sqrt,
                    "log": math.log,
                    "log10": math.log10,
                    "exp": math.exp,
                    "radians": math.radians,
                    "degrees": math.degrees,
                    "abs": abs,
                    "pow": pow,
                    "factorial": math.factorial,
                    "pi": math.pi,
                    "e": math.e
                }
                allowed_names.update(variables)
                code_obj = compile(expression_str, "<string>", "eval")
                for name in code_obj.co_names:
                    if name not in allowed_names:
                        raise NameError(f"Use of {name} is blocked")
                return eval(code_obj, {"__builtins__": None}, allowed_names)

            def render_terminal_graph(expr_to_plot, var_symbol="x", range_min=-10, range_max=10, steps=40):
                rows = 15
                cols = 60
                grid = [[" " for _ in range(cols)] for _ in range(rows)]
                
                x_vals = []
                y_vals = []
                
                for i in range(cols):
                    x_cur = range_min + (range_max - range_min) * (i / (cols - 1))
                    x_vals.append(x_cur)
                    try:
                        parsed_eq = parse_advanced_math(expr_to_plot)
                        y_cur = safe_eval_expression(parsed_eq, {var_symbol: x_cur})
                        if isinstance(y_cur, (int, float)) and not math.isnan(y_cur) and not math.isinf(y_cur):
                            y_vals.append(y_cur)
                        else:
                            y_vals.append(None)
                    except Exception:
                        y_vals.append(None)

                valid_y = [v for v in y_vals if v is not None]
                if not valid_y:
                    return "Could not plot graph: No valid coordinates within view."

                y_min, y_max = min(valid_y), max(valid_y)
                if y_min == y_max:
                    y_min -= 1.0
                    y_max += 1.0

                zero_row = None
                if y_min <= 0 <= y_max:
                    zero_row = int((rows - 1) * (1.0 - (0.0 - y_min) / (y_max - y_min)))
                    if 0 <= zero_row < rows:
                        for c in range(cols):
                            grid[zero_row][c] = "-"

                zero_col = None
                if range_min <= 0 <= range_max:
                    zero_col = int((cols - 1) * ((0.0 - range_min) / (range_max - range_min)))
                    if 0 <= zero_col < cols:
                        for r in range(rows):
                            if grid[r][zero_col] == "-":
                                grid[r][zero_col] = "+"
                            else:
                                grid[r][zero_col] = "|"

                for c in range(cols):
                    y_val = y_vals[c]
                    if y_val is None:
                        continue
                    r_idx = int((rows - 1) * (1.0 - (y_val - y_min) / (y_max - y_min)))
                    if 0 <= r_idx < rows:
                        grid[r_idx][c] = "*"

                graph_output = []
                graph_output.append(f"\nGraph View: f({var_symbol}) = {expr_to_plot}")
                graph_output.append(f"Y-Max: {y_max:.2f} " + "-" * (cols - 10))
                for r in range(rows):
                    graph_output.append("".join(grid[r]))
                graph_output.append(f"Y-Min: {y_min:.2f} " + "-" * (cols - 10))
                graph_output.append(f"X-Bounds: [{range_min}, {range_max}]\n")
                return "\n".join(graph_output)

            cleaned_input = text.lower().strip()
            is_graph_cmd = cleaned_input.startswith("graph ") or cleaned_input.startswith("plot ")
            
            expr = extract_math_expression(text)
            
            if is_graph_cmd:
                target_expr = expr
                var_name = "x"
                r_min, r_max = -10, 10
                
                if " range " in expr:
                    main_part, range_part = expr.split(" range ", 1)
                    target_expr = main_part.strip()
                    try:
                        bounds = range_part.replace("[", "").replace("]", "").split(",")
                        r_min = float(bounds[0].strip())
                        r_max = float(bounds[1].strip())
                    except Exception:
                        r_min, r_max = -10, 10
                
                if " vars " in target_expr:
                    eq_part, var_part = target_expr.split(" vars ", 1)
                    target_expr = eq_part.strip()
                    var_name = var_part.strip()

                graph_string = render_terminal_graph(target_expr, var_name, r_min, r_max)
                print(graph_string)
                speak(maybe_address_user("Graph rendering complete.", chance=0.2), allow_sound=True)
                return

            if " matrix " in expr:
                parts = expr.split(" matrix ")
                operation = parts[0].strip()
                matrix_data = json.loads(parts[1].strip())
                
                if operation == "det":
                    if len(matrix_data) == 2 and len(matrix_data[0]) == 2:
                        det = matrix_data[0][0]*matrix_data[1][1] - matrix_data[0][1]*matrix_data[1][0]
                        speak(maybe_address_user(f"Determinant is {det}", chance=0.2), allow_sound=True)
                        return
                    elif len(matrix_data) == 3 and len(matrix_data[0]) == 3:
                        m = matrix_data
                        det = (m[0][0]*(m[1][1]*m[2][2] - m[1][2]*m[2][1]) -
                               m[0][1]*(m[1][0]*m[2][2] - m[1][2]*m[2][0]) +
                               m[0][2]*(m[1][0]*m[2][1] - m[1][1]*m[2][0]))
                        speak(maybe_address_user(f"Determinant is {det}", chance=0.2), allow_sound=True)
                        return
                    else:
                        speak(maybe_address_user("Unsupported matrix dimensions.", chance=0.1), allow_sound=True)
                        return

            if " stats " in expr:
                parts = expr.split(" stats ")
                stat_type = parts[0].strip()
                dataset = [float(x.strip()) for x in parts[1].split(",")]
                
                if stat_type == "mean":
                    res = sum(dataset) / len(dataset)
                elif stat_type == "median":
                    sorted_ds = sorted(dataset)
                    n = len(sorted_ds)
                    if n % 2 == 1:
                        res = sorted_ds[n // 2]
                    else:
                        res = (sorted_ds[(n // 2) - 1] + sorted_ds[n // 2]) / 2.0
                elif stat_type == "variance":
                    mean_val = sum(dataset) / len(dataset)
                    res = sum((x - mean_val) ** 2 for x in dataset) / len(dataset)
                elif stat_type == "stddev":
                    mean_val = sum(dataset) / len(dataset)
                    var_val = sum((x - mean_val) ** 2 for x in dataset) / len(dataset)
                    res = math.sqrt(var_val)
                else:
                    res = "Unknown statistical operation"
                
                speak(maybe_address_user(str(res), chance=0.2), allow_sound=True)
                return

            if " conversion " in expr:
                parts = expr.split(" conversion ")
                conv_type = parts[0].strip()
                value = float(parts[1].strip())
                
                if conv_type == "c_to_f":
                    res = (value * 9/5) + 32
                elif conv_type == "f_to_c":
                    res = (value - 32) * 5/9
                elif conv_type == "m_to_ft":
                    res = value * 3.28084
                elif conv_type == "ft_to_m":
                    res = value / 3.28084
                elif conv_type == "kg_to_lbs":
                    res = value * 2.20462
                elif conv_type == "lbs_to_kg":
                    res = value / 2.20462
                else:
                    res = "Unknown conversion metric"
                
                speak(maybe_address_user(str(res), chance=0.2), allow_sound=True)
                return

            parsed_expression = parse_advanced_math(expr)
            output_value = safe_eval_expression(parsed_expression)
            
            if isinstance(output_value, float):
                formatted_result = f"{output_value:.6f}".rstrip('0').rstrip('.')
            else:
                formatted_result = str(output_value)
                
            speak(maybe_address_user(formatted_result, chance=0.2), allow_sound=True)
            return

        except Exception as math_exception:
            print(f"Mathematical Parser Error: {str(math_exception)}")
            speak(maybe_address_user("That math expression looks off.", chance=0.1), allow_sound=True)
            return



    if lower.startswith("note "):
        cmd_note(text[5:].strip())
        speak(maybe_address_user("Saved note.", chance=0.2), allow_sound=True)
        return

    if lower == "notes":
        cmd_notes()
        speak(maybe_address_user("Notes shown in terminal.", chance=0.2), allow_sound=True)
        return

    if lower.startswith("remember "):
        cmd_remember(text[9:].strip())
        speak(maybe_address_user("Saved memory.", chance=0.2), allow_sound=True)
        return

    if lower == "memories":
        cmd_memories()
        speak(maybe_address_user("Memories shown in terminal.", chance=0.2), allow_sound=True)
        return

    if lower.startswith("forget "):
        cmd_forget(text[7:].strip())
        speak(maybe_address_user("Memory removed.", chance=0.2), allow_sound=True)
        return

    if lower.startswith("search "):
        term = text[7:].strip()
        results = search_storage(term)
        if not results:
            print("No matches.")
            speak(maybe_address_user("No matches found.", chance=0.15), allow_sound=True)
        else:
            for i, item in enumerate(results, 1):
                print(f"{i}. {item}")
            speak(maybe_address_user(f"Found {len(results)} match{'es' if len(results) != 1 else ''}.", chance=0.15), allow_sound=True)
        return
    
    if lower in {"restart", "reboot", "reload"}:
        speak("Rebooting SOAR.", allow_sound=True)
        reboot_soar()
        return

    if lower in {
        "emergency shutdown",
        "emergency shut down",
        "panic shutdown",
        "force shutdown",
        "hard shutdown",
    }:
        emergency_shutdown()
        return

    if lower.startswith("todo "):
        try:
            parts = shlex.split(text)
        except ValueError:
            print("Bad todo command.")
            return

        if len(parts) < 2:
            print("Usage: todo add/list/done/remove/clear")
            return

        action = parts[1].lower()
        rest = " ".join(parts[2:]).strip()
        if action == "add":
            todo_add(rest)
            speak(maybe_address_user("Todo added.", chance=0.2), allow_sound=True)
        elif action == "list":
            todo_list()
            speak(maybe_address_user("Todos shown in terminal.", chance=0.2), allow_sound=True)
        elif action == "done":
            todo_done(rest)
            speak(maybe_address_user("Todo marked done.", chance=0.2), allow_sound=True)
        elif action == "remove":
            todo_remove(rest)
            speak(maybe_address_user("Todo removed.", chance=0.2), allow_sound=True)
        elif action == "clear":
            todo_clear()
            speak(maybe_address_user("Todos cleared.", chance=0.2), allow_sound=True)
        else:
            print("Usage: todo add/list/done/remove/clear")
        return

    if lower.startswith("remind "):
        cmd_remind(text[7:].strip())
        return

    if lower.startswith("timer "):
        cmd_timer(text[6:].strip())
        return

    if lower.startswith("shell "):
        cmd_shell(text[6:].strip())
        speak(maybe_address_user("Command finished.", chance=0.15), allow_sound=True)
        return

    if lower.startswith("read "):
        cmd_read(text[5:].strip())
        speak(maybe_address_user("File shown in terminal.", chance=0.15), allow_sound=True)
        return

    if lower.startswith("write "):
        cmd_write(text[6:].strip())
        speak(maybe_address_user("File written.", chance=0.15), allow_sound=True)
        return
        
    if lower.startswith("newfile "):
        cmd_newfile(text[8:].strip())
        speak(maybe_address_user("File created.", chance=0.15), allow_sound=True)
        return

    if lower.startswith("code "):
        cmd_code(text[5:].strip())
        speak(maybe_address_user("Code file action done.", chance=0.15), allow_sound=True)
        return

    if lower.startswith("mkdir "):
        cmd_mkdir(text[6:].strip())
        speak(maybe_address_user("Folder created.", chance=0.15), allow_sound=True)
        return

    if lower.startswith("openurl "):
        target = text[8:].strip()
        if open_url(target):
            print("Opened URL.")
            speak(maybe_address_user("Opened it.", chance=0.15), allow_sound=True)
        else:
            print("Could not open URL.")
            speak(maybe_address_user("I could not open that.", chance=0.15), allow_sound=True)
        return

    if lower.startswith("open "):
        cmd_open(text[5:].strip())
        speak(maybe_address_user("Opening file.", chance=0.15), allow_sound=True)
        return

    if lower.startswith("copy "):
        content = text[5:].strip()
        if clipboard_copy(content):
            print("Copied to clipboard.")
            speak(maybe_address_user("Copied to clipboard.", chance=0.2), allow_sound=True)
        else:
            print("Clipboard copy failed.")
            speak(maybe_address_user("Clipboard copy failed.", chance=0.15), allow_sound=True)
        return

    if lower == "paste":
        pasted = clipboard_paste()
        if pasted:
            print(pasted)
            speak(maybe_address_user("Clipboard pasted in terminal.", chance=0.15), allow_sound=True)
        else:
            print("Clipboard empty or unavailable.")
            speak(maybe_address_user("Clipboard is empty or unavailable.", chance=0.15), allow_sound=True)
        return

    if lower == "ip":
        ip = get_local_ip()
        print(ip)
        speak(maybe_address_user(f"Your local IP is {ip}", chance=0.2), allow_sound=True)
        return

    if lower.startswith("voice"):
        cmd_voice(text[5:].strip())
        return

    if lower == "listen on":
        enable_voice()
        speak(maybe_address_user("Listening.", chance=0.2), allow_sound=True)
        return

    if lower == "listen off":
        disable_voice()
        print("Listening has been turned off.")
        return

    response = reply_to(text)
    speak(response, allow_sound=True)



def check_process_resources():
    global _last_resource_alert

    if psutil is None:
        return False

    try:
        p = psutil.Process(os.getpid())

        cpu_samples = []
        for _ in range(3):
            cpu_samples.append(p.cpu_percent(interval=0.05))

        cpu_pct = sum(cpu_samples) / len(cpu_samples)
        ram_pct = p.memory_percent()

        high_usage = cpu_pct >= 70.0 or ram_pct >= 40.0

        if high_usage:
            if _last_resource_alert == 0:
                _last_resource_alert = time.time()

                error_msg = (
                    f"[RESOURCE HIGH] SOAR resource usage detected! "
                    f"CPU: {cpu_pct:.1f}%, RAM: {ram_pct:.1f}%"
                )

                print(f"\n{error_msg}\n")

                try:
                    log_line("SYSTEM", error_msg)
                except Exception:
                    pass

                try:
                    speak("High resource usage detected. Reducing SOAR load.", allow_sound=True)
                except Exception:
                    pass

                return True

            return False

        _last_resource_alert = 0

        return False

    except ImportError:
        return False

    except Exception as e:
        print(f"[RESOURCE MONITOR ERROR] {e}")
        return False
    
intro_proc = None

def _mac_quicktime_state():
    try:
        apple_script = (
            'tell application "QuickTime Player"\n'
            '    if not running then return "STOPPED"\n'
            '    if not (exists front document) then return "NODOC"\n'
            '    set ct to current time of front document\n'
            '    set dur to duration of front document\n'
            '    return (ct as text) & "|" & (dur as text)\n'
            'end tell'
        )
        result = subprocess.run(
            ["osascript", "-e", apple_script],
            capture_output=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL
        )
        return result.stdout.strip()
    except Exception:
        return ""


def play_intro():
    global intro_start_time, intro_proc
    try:
        intro_path = DATA_DIR / "intro.mp4"
        if not intro_path.exists():
            return

        system = platform.system()
        intro_start_time = time.time()

        if system == "Darwin":
            intro_proc = None

            posix_path = str(intro_path).replace("\\", "\\\\").replace('"', '\\"')

            apple_script = f'''
            tell application "QuickTime Player"
                activate
                open POSIX file "{posix_path}"
                delay 1
                if exists front document then
                    play front document
                    delay 0.3
                    set presenting of front document to true
                end if
            end tell
            '''

            subprocess.Popen(
                ["osascript", "-e", apple_script],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL
            )

        elif system == "Windows":
            intro_proc = subprocess.Popen(
                ["vlc", "--fullscreen", "--play-and-exit", str(intro_path)],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL
            )

    except Exception:
        pass


def close_intro_player():
    try:
        system = platform.system()
        if system == "Darwin":
            apple_script = (
                'tell application "QuickTime Player"\n'
                '    try\n'
                '        if exists front document then close front document saving no\n'
                '    end try\n'
                '    quit\n'
                'end tell'
            )
            subprocess.run(
                ["osascript", "-e", apple_script],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL
            )
        elif system == "Windows":
            subprocess.run(
                ["taskkill", "/F", "/IM", "vlc.exe"],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL
            )
    except Exception:
        pass


def focus_terminal():
    try:
        system = platform.system()
        if system == "Darwin":
            apple_script = (
                'tell application "System Events"\n'
                '    set terminalApps to {"Terminal", "iTerm", "iTerm2", "Code", "Visual Studio Code"}\n'
                '    repeat with appName in terminalApps\n'
                '        if exists process appName then\n'
                '            set frontmost of process appName to true\n'
                '            exit repeat\n'
                '        end if\n'
                '    end repeat\n'
                'end tell'
            )
            subprocess.run(
                ["osascript", "-e", apple_script],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL
            )
        elif system == "Windows":
            import ctypes
            hwnd = ctypes.windll.kernel32.GetConsoleWindow()
            if hwnd:
                ctypes.windll.user32.ShowWindow(hwnd, 9)
                ctypes.windll.user32.SetForegroundWindow(hwnd)
    except Exception:
        pass


def watch_intro_and_focus():
    global intro_proc
    try:
        system = platform.system()

        if system == "Darwin":
            start_time = time.time()
            timeout = 300 

            while not stop_event.is_set() and (time.time() - start_time) < timeout:
                state = _mac_quicktime_state()

                if state in ("STOPPED", "NODOC", ""):
                    time.sleep(0.5)
                    continue

                if "|" in state:
                    try:
                        current_time, duration = state.split("|", 1)
                        current_time = float(current_time)
                        duration = float(duration)

                        if duration > 0 and current_time >= (duration - 0.25):
                            break
                    except Exception:
                        pass

                time.sleep(0.5)

            close_intro_player()
            focus_terminal()
            return

        if intro_proc:
            intro_proc.wait()
            focus_terminal()

    except Exception:
        pass

def parse_ram_limit(value):
    value = value.strip().lower().replace(" ", "")
    match = re.fullmatch(r"(\d+(?:\.\d+)?)(kb|mb|gb|tb)", value)
    if not match:
        raise ValueError("Use a RAM value like 512MB, 1GB, or 10000KB.")

    number = float(match.group(1))
    unit = match.group(2)
    multiplier = {
        "kb": 1024,
        "mb": 1024 ** 2,
        "gb": 1024 ** 3,
        "tb": 1024 ** 4,
    }[unit]
    return int(number * multiplier)


def parse_percent_limit(value):
    value = value.strip().replace("%", "")
    number = int(value)
    if not 0 <= number <= 100:
        raise ValueError("Percentage must be between 0 and 100.")
    return number


def reset_resource_limits_for_boot():
    """Start every SOAR boot with resource limiting disabled."""
    global SOAR_RESOURCE_LIMITS_ACTIVE

    with resource_limit_lock:
        SOAR_RESOURCE_LIMITS_ACTIVE = False
        SOAR_RESOURCE_LIMITS["ram_bytes"] = None
        SOAR_RESOURCE_LIMITS["cpu_percent"] = None
        SOAR_RESOURCE_LIMITS["gpu_percent"] = None


def _stop_optional_module(name):
    """Stop/disable an optional subsystem without stopping SOAR itself."""
    global autocode_enabled

    name = name.upper()
    SOAR_DISABLED_MODULES.add(name)

    if name == "AUTOCODE":
        autocode_enabled = False
        autocode_stop.set()
        print("[SOAR LIGHTWEIGHT] Autocode disabled.")
        return

    if name == "VOICE":
        try:
            disable_voice()
        except Exception as e:
            print(f"[SOAR LIGHTWEIGHT] Voice stop error: {e}")
        print("[SOAR LIGHTWEIGHT] Voice input disabled.")
        return

    if name == "AVSS":
        avss_stop_event.set()
        try:
            for method_name in ("stop", "shutdown", "close"):
                method = getattr(soar_avss, method_name, None) if soar_avss else None
                if callable(method):
                    try:
                        method()
                    except TypeError:
                        pass
                    break
        except Exception as e:
            print(f"[SOAR LIGHTWEIGHT] AVSS stop error: {e}")
        print("[SOAR LIGHTWEIGHT] AVSS disabled to reduce resource usage.")
        return

    if name == "CSRS":
        print("[SOAR LIGHTWEIGHT] CSRS disabled.")
        return

    if name == "RSMS":
        print("[SOAR LIGHTWEIGHT] RSMS disabled.")
        return


def enter_lightweight_mode(trigger):
    """Drop optional features before the hard resource limit is reached."""
    global SOAR_LIGHTWEIGHT_MODE

    with resource_limit_lock:
        if SOAR_LIGHTWEIGHT_MODE:
            return
        SOAR_LIGHTWEIGHT_MODE = True

    print(f"\n[SOAR LIGHTWEIGHT] Activating lightweight mode: {trigger}")
    print("[SOAR LIGHTWEIGHT] Shutting down optional resource-heavy modules...")

    for module_name in ("AUTOCODE", "VOICE", "RSMS", "CSRS", "AVSS"):
        _stop_optional_module(module_name)

    print("[SOAR LIGHTWEIGHT] Lightweight mode active. Core command processing remains online.")
    emit_event("LIGHTWEIGHT_ON", {"trigger": trigger})


def leave_lightweight_mode(restore_modules=True):
    """Manually or automatically restore optional features after lightweight mode."""
    global SOAR_LIGHTWEIGHT_MODE

    with resource_limit_lock:
        SOAR_LIGHTWEIGHT_MODE = False
        SOAR_DISABLED_MODULES.clear()
        SOAR_DISABLED_MODULES.update(SOAR_MANUAL_DISABLED_MODULES)

    if "AVSS" not in SOAR_MANUAL_DISABLED_MODULES:
        avss_stop_event.clear()
    if "AUTOCODE" not in SOAR_MANUAL_DISABLED_MODULES:
        autocode_stop.clear()

    print("[SOAR LIGHTWEIGHT] Lightweight mode cleared. Optional modules may be started again.")
    emit_event("LIGHTWEIGHT_OFF", {"manual_disabled": sorted(SOAR_MANUAL_DISABLED_MODULES)})

    if restore_modules:
        try:
            restore_optional_modules_from_profile()
        except Exception as e:
            record_module_failure("CORE", e)


def configure_resource_limits():
    print("\n[SOAR] Resource Limit Setup")

    while True:
        try:
            ram_text = input("Ram: ")
            ram_bytes = parse_ram_limit(ram_text)
            break
        except ValueError as e:
            print(f"[SOAR] {e}")

    while True:
        try:
            gpu_text = input("GPU:#% ")
            gpu_percent = parse_percent_limit(gpu_text)
            break
        except ValueError as e:
            print(f"[SOAR] {e}")

    while True:
        try:
            cpu_text = input("CPU:#% ")
            cpu_percent = parse_percent_limit(cpu_text)
            break
        except ValueError as e:
            print(f"[SOAR] {e}")

    global SOAR_RESOURCE_LIMITS_ACTIVE

    with resource_limit_lock:
        SOAR_RESOURCE_LIMITS["ram_bytes"] = ram_bytes
        SOAR_RESOURCE_LIMITS["gpu_percent"] = gpu_percent
        SOAR_RESOURCE_LIMITS["cpu_percent"] = cpu_percent
        SOAR_RESOURCE_LIMITS_ACTIVE = True

    leave_lightweight_mode()

    print(
        f"[SOAR] Limits set: RAM={ram_text}, "
        f"GPU={gpu_percent}%, CPU={cpu_percent}%"
    )
    print("[SOAR] Lightweight mode will activate at 80% of a configured limit.")
    print("[SOAR] SOAR will shut down if the hard limit is reached.")
    print("[SOAR] These limits apply only to this boot and are cleared on restart.")

    return (
        f"Resource limits set. RAM {ram_text}, "
        f"GPU {gpu_percent} percent, CPU {cpu_percent} percent."
    )


def handle_user_input(text, username="User"):
    global _last_resource_alert

    command = " ".join(str(text or "").strip().split()).lower()

    if command in {"/cmd groqkeyon", "cmd groqkeyon"}:
        set_groq_enabled(True)
        if get_groq_api_key():
            return "Groq chat enabled. Normal conversation will use Groq; local SOAR chat remains the automatic fallback when Groq is unavailable."
        return "Groq chat enabled, but no API key is configured. Set GROQ_API_KEY (or groq_api_key in settings.json); SOAR will use local chat until then."

    if command in {"/cmd groqkeyoff", "cmd groqkeyoff"}:
        set_groq_enabled(False)
        return "Groq chat disabled. SOAR will use its local chat system."

    if command in {"/cmd groqkeystatus", "cmd groqkeystatus"}:
        return groq_status_text()

    if command == "/cmd limitres":
        return configure_resource_limits()

    if command == "/cmd limitres off":
        global SOAR_RESOURCE_LIMITS_ACTIVE
        with resource_limit_lock:
            SOAR_RESOURCE_LIMITS_ACTIVE = False
            SOAR_RESOURCE_LIMITS["ram_bytes"] = None
            SOAR_RESOURCE_LIMITS["cpu_percent"] = None
            SOAR_RESOURCE_LIMITS["gpu_percent"] = None
        leave_lightweight_mode()
        return "Resource limits disabled for this boot."

    if command == "/cmd ignorerescap":
        global RESOURCE_IGNORE
        RESOURCE_IGNORE = True
        _last_resource_alert = 0
        return "Resource warnings disabled."

    if command == "/cmd unignorerescap":
        RESOURCE_IGNORE = False
        _last_resource_alert = 0
        return "Resource warnings enabled."

    if command == "/cmd lightmode":
        enter_lightweight_mode("manual command")
        return "Lightweight mode enabled. Optional modules were disabled."

    if command == "/cmd lightmode off":
        leave_lightweight_mode()
        return "Lightweight mode cleared."

    if command == "/cmd readypost":
        print("Ready post command executed internally.")
        return f"Post readiness confirmed, {username}."

    return f"Processed input: {text}"


def get_gpu_utilization_percent():
    """Return average NVIDIA GPU utilization, or None when unavailable."""
    try:
        result = subprocess.run(
            [
                "nvidia-smi",
                "--query-gpu=utilization.gpu",
                "--format=csv,noheader,nounits",
            ],
            capture_output=True,
            text=True,
            timeout=2,
            check=False,
        )
    except (FileNotFoundError, OSError, subprocess.SubprocessError):
        return None

    values = []
    for line in result.stdout.splitlines():
        value = line.strip().replace("%", "")
        if not value:
            continue
        try:
            values.append(float(value))
        except ValueError:
            continue

    if not values:
        return None
    return sum(values) / len(values)


def enforce_soar_resource_limits():
    """Apply only limits explicitly configured during the current boot."""
    try:
        with resource_limit_lock:
            if not SOAR_RESOURCE_LIMITS_ACTIVE:
                return
            ram_limit = SOAR_RESOURCE_LIMITS.get("ram_bytes")
            cpu_limit = SOAR_RESOURCE_LIMITS.get("cpu_percent")
            gpu_limit = SOAR_RESOURCE_LIMITS.get("gpu_percent")

        p = psutil.Process(os.getpid())
    except Exception:
        return

    try:
        ram_used = p.memory_info().rss
        cpu_used = p.cpu_percent(interval=0.05)

        if ram_limit is not None and ram_limit > 0:
            ram_ratio = ram_used / ram_limit
            if ram_ratio >= 1.0:
                request_soar_shutdown(
                    f"SOAR stopped: RAM limit of {ram_limit / (1024 ** 2):.1f} MB reached "
                    f"({ram_used / (1024 ** 2):.1f} MB used)."
                )
                return
            if ram_ratio >= 0.80:
                enter_lightweight_mode(
                    f"RAM at {ram_used / (1024 ** 2):.1f} MB / {ram_limit / (1024 ** 2):.1f} MB"
                )

        if cpu_limit is not None and cpu_limit > 0:
            cpu_ratio = cpu_used / cpu_limit
            if cpu_ratio >= 1.0:
                request_soar_shutdown(
                    f"SOAR stopped: CPU limit of {cpu_limit}% reached ({cpu_used:.1f}%)."
                )
                return
            if cpu_ratio >= 0.80:
                enter_lightweight_mode(
                    f"CPU at {cpu_used:.1f}% / {cpu_limit}%"
                )

        if gpu_limit is not None and gpu_limit > 0:
            gpu_used = get_gpu_utilization_percent()
            if gpu_used is not None:
                gpu_ratio = gpu_used / gpu_limit
                if gpu_ratio >= 1.0:
                    request_soar_shutdown(
                        f"SOAR stopped: GPU limit of {gpu_limit}% reached ({gpu_used:.1f}%)."
                    )
                    return
                if gpu_ratio >= 0.80:
                    enter_lightweight_mode(
                        f"GPU at {gpu_used:.1f}% / {gpu_limit}%"
                    )

    except Exception as e:
        print(f"[RESOURCE LIMIT ERROR] {e}")


def request_soar_shutdown(reason="SOAR resource limit reached."):
    global shutting_down

    if shutting_down:
        return

    shutting_down = True
    print(f"\n[SOAR] {reason}")
    print("[SOAR] Emergency resource shutdown initiated.")

    try:
        stop_event.set()
    except Exception:
        pass

    try:
        disable_voice()
    except Exception:
        pass

    try:
        autocode_stop.set()
    except Exception:
        pass

    try:
        avss_stop_event.set()
    except Exception:
        pass

    try:
        tts_queue.put_nowait(None)
    except Exception:
        pass

    try:
        if soar_avss and hasattr(soar_avss, "release_single_instance_lock"):
            soar_avss.release_single_instance_lock()
    except Exception:
        pass

    try:
        emergency_shutdown()
    except Exception:
        try:
            os._exit(0)
        except Exception:
            pass

def main():
    if soar_avss and hasattr(soar_avss, "enforce_single_instance"):
        if not soar_avss.enforce_single_instance():
            sys.exit(0)

    global shutting_down, stop_event
    shutting_down = False
    stop_event = threading.Event()
    avss_stop_event.clear()
    reset_resource_limits_for_boot()

    system_tasks = [
        ("Database Modules", load_database),
        ("Network Protocols", initialize_network),
        ("Config Files", load_configurations),
        ("Security Protocols", verify_security),
        ("Text-to-Speech Engine", init_tts),
        ("Voice Recognition System", init_recognition)
    ]

    instant_enabled = False
    try:
        if SETTINGS_FILE.exists():
            settings_data = json.loads(SETTINGS_FILE.read_text())
            instant_enabled = settings_data.get("instant_intro", False)
    except Exception:
        pass

    if not instant_enabled:
        play_intro()
        threading.Thread(target=watch_intro_and_focus, daemon=True).start()

    load_systems(system_tasks)
    initialize_feature_runtime()

    def resource_watchdog_loop():
        while not stop_event.is_set():
            try:
                check_process_resources()
            except Exception as e:
                print(f"[WATCHDOG ERROR] {e}")

            try:
                enforce_soar_resource_limits()
            except Exception as e:
                print(f"[RESOURCE LIMIT ERROR] {e}")

            try:
                auto_lightweight_monitor()
            except Exception as e:
                record_module_failure("CORE", e)

            stop_event.wait(RESOURCE_WATCHDOG_INTERVAL)

    def autocode_loop():
        while not stop_event.is_set():
            try:
                if (
                    autocode_enabled
                    and not autocode_stop.is_set()
                    and autocode_connected()
                    and module_is_enabled("AUTOCODE")
                    and not SOAR_SAFE_MODE
                ):
                    try:
                        soar_autocode.run_cycle("auto running")
                        record_module_success("AUTOCODE")
                    except Exception as e:
                        record_module_failure("AUTOCODE", e)
                        print(f"[AUTO ERROR] {e}")
            except Exception as e:
                print(f"[AUTO ERROR] {e}")

            for _ in range(600):
                if stop_event.is_set():
                    break
                time.sleep(0.1)

    threading.Thread(target=resource_watchdog_loop, daemon=True).start()
    threading.Thread(target=autocode_loop, daemon=True).start()

    if not instant_enabled:
        if intro_start_time > 0:
            elapsed = time.time() - intro_start_time
            remaining = 10.0 - elapsed
            if remaining > 0:
                time.sleep(remaining)

        close_intro_player()
        focus_terminal()
    else:
        focus_terminal()

    print(f"{APP_NAME} online.")
    print("Type /help for commands. Type normal text to chat.")
    print("Voice starts automatically if your mic libraries are ready.\n")

    try:
        speak("SOAR Booted, version 1.00.10. Voice is on.", allow_sound=True)
    except Exception:
        pass

    try:
        if module_is_enabled("VOICE") and not SOAR_SAFE_MODE:
            enable_voice()
            record_module_success("VOICE")
        else:
            print("[SOAR] Voice startup skipped by active profile/safe mode.")
    except Exception as e:
        record_module_failure("VOICE", e)
        print(f"[VOICE ERROR] {e}")

    try:
        threading.Thread(target=voice_watchdog_loop, daemon=True).start()
    except Exception as e:
        print(f"[VOICE WATCHDOG ERROR] {e}")

    if module_is_enabled("AVSS") and not SOAR_SAFE_MODE:
        start_avss_module()
    else:
        print("[SOAR] AVSS startup skipped by active profile/safe mode.")

    try:
        while not stop_event.is_set():
            try:
                raw = input(f"{APP_NAME}> ")
            except KeyboardInterrupt:
                raise SystemExit

            try:
                command_key = raw.strip().lower()
                if command_key in {
                    "/cmd limitres",
                    "/cmd limitres off",
                    "/cmd lightmode",
                    "/cmd lightmode off",
                    "/cmd groqkeyon",
                    "/cmd groqkeyoff",
                    "/cmd groqkeystatus",
                }:
                    try:
                        response = handle_user_input(raw)
                        print(f"SOAR: {response}")
                        try:
                            speak(response, allow_sound=True)
                        except Exception:
                            pass
                    except Exception as e:
                        print(f"[RESOURCE COMMAND ERROR] {e}")
                    continue

                if raw.startswith("/cmd instantintro"):
                    try:
                        settings_data = {}
                        if SETTINGS_FILE.exists():
                            try:
                                settings_data = json.loads(SETTINGS_FILE.read_text())
                            except Exception:
                                pass
                        
                        current_val = settings_data.get("instant_intro", False)
                        new_val = not current_val
                        settings_data["instant_intro"] = new_val
                        SETTINGS_FILE.parent.mkdir(parents=True, exist_ok=True)
                        SETTINGS_FILE.write_text(json.dumps(settings_data, indent=4))
                        
                        status = "enabled (intro will be skipped on next startup)" if new_val else "disabled (intro will play on next startup)"
                        print(f"Instant intro is now {status}.")
                    except Exception as e:
                        print(f"Failed to update instantintro setting: {e}")
                    continue

                if raw.startswith("/cmd readypost"):
                    target_files = [
                        CHAT_LOG,
                        DATA_DIR / "autocode_log.txt",
                        BASE_DIR / "autocode_log.txt",
                        BASE_DIR / "chat_log.txt"
                    ]
                    for log_path in target_files:
                        try:
                            if log_path.exists():
                                log_path.write_text("")
                                print(f"Cleared {log_path.name}")
                        except Exception as e:
                            print(f"Could not clear {log_path.name}: {e}")
                    print("Post readiness confirmed.")
                    continue

                if raw.startswith("/cmd savelogs"):
                    saves_dir = DATA_DIR / "log_saves"
                    saves_dir.mkdir(parents=True, exist_ok=True)
                    
                    existing_numbers = []
                    for folder in saves_dir.iterdir():
                        if folder.is_dir() and folder.name.startswith("save_"):
                            try:
                                existing_numbers.append(int(folder.name.split("_")[1]))
                            except ValueError:
                                pass
                    
                    next_num = max(existing_numbers, default=0) + 1
                    save_folder = saves_dir / f"save_{next_num}"
                    save_folder.mkdir(parents=True, exist_ok=True)

                    chat_src = CHAT_LOG if CHAT_LOG.exists() else BASE_DIR / "chat_log.txt"
                    auto_src = (DATA_DIR / "autocode_log.txt") if (DATA_DIR / "autocode_log.txt").exists() else BASE_DIR / "autocode_log.txt"

                    if chat_src.exists():
                        (save_folder / "chat_log.txt").write_text(chat_src.read_text())
                    if auto_src.exists():
                        (save_folder / "autocode_log.txt").write_text(auto_src.read_text())

                    print(f"Logs saved to batch #{next_num} ({save_folder})")
                    continue

                if raw.startswith("/cmd loadlog"):
                    cmd_parts = raw.strip().split()
                    
                    if len(cmd_parts) < 3 or not cmd_parts[2].isdigit():
                        print("Usage: /cmd loadlog <number>")
                        continue

                    log_num = cmd_parts[2]
                    target_folder = DATA_DIR / "log_saves" / f"save_{log_num}"

                    if not target_folder.exists():
                        print(f"Save slot #{log_num} not found in log_saves.")
                        continue

                    confirm = input("WARNING: This will clear current logs (Chat history + Autocode log) Proceed? (y/n): ")
                    if confirm.lower().strip() == "y":
                        chat_dest = CHAT_LOG
                        auto_dest = DATA_DIR / "autocode_log.txt"

                        saved_chat = target_folder / "chat_log.txt"
                        saved_auto = target_folder / "autocode_log.txt"

                        if saved_chat.exists():
                            chat_dest.write_text(saved_chat.read_text())
                        else:
                            chat_dest.write_text("")

                        if saved_auto.exists():
                            auto_dest.write_text(saved_auto.read_text())
                        else:
                            auto_dest.write_text("")

                        print(f"Logs from slot #{log_num} loaded successfully.")
                    else:
                        print("Load operation cancelled.")
                    continue

                process_command(raw)
            except Exception as e:
                print(f"[COMMAND ERROR] {e}")

    except (KeyboardInterrupt, EOFError, SystemExit):
        if shutting_down:
            return

        shutting_down = True
        print("\nShutting down...")

        stop_event.set()

        try:
            disable_voice()
        except Exception:
            pass

        try:
            tts_queue.put_nowait(None)
        except Exception:
            pass

        if soar_avss and hasattr(soar_avss, "release_single_instance_lock"):
            try:
                soar_avss.release_single_instance_lock()
            except Exception:
                pass

        time.sleep(0.3)
        print("Shutdown complete.")
        sys.exit(0)

if __name__ == "__main__":
    main()
