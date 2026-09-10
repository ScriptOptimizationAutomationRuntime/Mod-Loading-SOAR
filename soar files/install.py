import subprocess
import sys
import platform
import os

def run(command):
    try:
        subprocess.check_call(command)
        return True
    except subprocess.CalledProcessError:
        return False

def install_linux_system_deps():
    print("Detecting Linux distribution and installing system dependencies...")
    
    if os.geteuid() != 0:
        print("\nWARNING: You need root privileges to install system dependencies.")
        print("Please restart this script with 'sudo python3 install.py'\n")
        return False
    
    if run(["which", "apt-get"]):
        print("Using apt-get...")
        run(["apt-get", "update"])
        return run(["apt-get", "install", "-y", "portaudio19-dev", "python3-dev", "espeak", "libespeak-dev"])
    elif run(["which", "dnf"]):
        print("Using dnf...")
        return run(["dnf", "install", "-y", "portaudio-devel", "python3-devel", "espeak-ng-devel"])
    elif run(["which", "pacman"]):
        print("Using pacman...")
        return run(["pacman", "-S", "--noconfirm", "portaudio", "espeak"])
    else:
        print("Could not identify package manager. Please install portaudio manually.")
        return False

print("====================================")
print("SOAR Dependency Installer")
print("====================================\n")

# Use Homebrew Python on macOS if available, matching explicit path requirements
python_exec = sys.executable
if platform.system() == "Darwin" and os.path.exists("/opt/homebrew/bin/python3"):
    python_exec = "/opt/homebrew/bin/python3"
    print(f"Using Homebrew Python: {python_exec}")

print("Upgrading pip...")
run([python_exec, "-m", "pip", "install", "--upgrade", "pip"])

packages = [
    "pyttsx3",
    "SpeechRecognition",
    "psutil",
    "chess"
]

# Set flag for modern externally managed environments (PEP 668) on Mac/Linux
extra_args = []
if platform.system() in ["Darwin", "Linux"]:
    extra_args = ["--break-system-packages"]

for package in packages:
    print(f"\nInstalling {package}...")
    cmd = [python_exec, "-m", "pip", "install", package] + extra_args
    if run(cmd):
        print(f"✓ {package} installed")
    else:
        # Fallback attempt without extra args if needed
        if extra_args and run([python_exec, "-m", "pip", "install", package]):
            print(f"✓ {package} installed")
        else:
            print(f"✗ Failed to install {package}")

system = platform.system()

print("\nInstalling PyAudio...")

if system == "Windows":
    if not run([python_exec, "-m", "pip", "install", "pyaudio"]):
        print("Trying pipwin...")
        run([python_exec, "-m", "pip", "install", "pipwin"])
        run([python_exec, "-m", "pipwin", "install", "pyaudio"])

elif system == "Darwin":  
    if run(["which", "brew"]):
        print("Ensuring portaudio is installed via Homebrew...")
        run(["brew", "install", "portaudio"])
    else:
        print("Homebrew not found. If PyAudio fails, install portaudio manually.")
    
    if not run([python_exec, "-m", "pip", "install", "pyaudio"] + extra_args):
        run([python_exec, "-m", "pip", "install", "pyaudio"])

elif system == "Linux":  
    deps_installed = install_linux_system_deps()
    if not deps_installed:
        print("System dependencies installation skipped or failed. PyAudio pip install might fail.")
    
    if not run([python_exec, "-m", "pip", "install", "pyaudio"] + extra_args):
        run([python_exec, "-m", "pip", "install", "pyaudio"])

print("\n====================================")
print("Installation Complete!")
print("====================================")

input("\nPress Enter to exit...")
