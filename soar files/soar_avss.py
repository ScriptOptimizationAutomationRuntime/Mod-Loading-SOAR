# ======================================
# SOAR AVSS (Anti Virus SOAR Software)
# V 1.2
# Made by Philip Kluz 2026 Jun 25 Late
# # SOAR Help Module #002
# "ay ve es es"
# ======================================

import os
import sys
import time
import shutil
import hashlib
import threading
import subprocess
from pathlib import Path
from copy import deepcopy

import psutil

KNOWN_MALWARE_FAMILIES = {
    "njrat": "Remote Access Trojan (RAT)",
    "quasarrat": "Remote Access Trojan (RAT)",
    "asyncrat": "Remote Access Trojan (RAT)",
    "darkcomet": "Remote Access Trojan (RAT)",
    "emotet": "Banking Trojan / Loader",
    "trickbot": "Banking Trojan",
    "wannacry": "Ransomware",
    "lockbit": "Ransomware",
    "mimikatz": "Credential Theft Tool",
    "xmrig": "Cryptocurrency Miner",
}

KNOWN_BAD_HASHES = {

    "275a021bbfb6489e54d471899f7db9d1663fc695ec2fe2a2c4538aabf651fd0": "EICAR-Test-File",
}

SUSPICIOUS_PORTS = [4444, 6667, 1337, 31337]
SUSPICIOUS_IPS = []

MONITOR_INTERVAL = 5
DEDUP_TTL = 60
MAX_REPORT_ITEMS = 200

MAX_FILE_SCAN_SIZE = 50 * 1024 * 1024

DESKTOP = Path.home() / "Desktop"
if not DESKTOP.exists():
    DESKTOP = Path.home()

LOCKFILE_PATH = Path.home() / ".soar_main.lock"

_report_lock = threading.Lock()
_report = {
    "running": False,
    "last_scan": None,
    "scan_count": 0,
    "suspicious_count": 0,
    "file_hits": 0,
    "process_hits": 0,
    "network_hits": 0,
    "terminated_count": 0,
    "failed_terminations": 0,
    "errors": 0,
    "items": [],
}

_recent_hits = {}
_recent_lock = threading.Lock()

_pending_lock = threading.Lock()
_pending_actions = {}
_next_action_id = [1]

def _now():
    return time.time()

def _prune_recent():
    cutoff = _now() - DEDUP_TTL
    stale = [key for key, ts in _recent_hits.items() if ts < cutoff]
    for key in stale:
        _recent_hits.pop(key, None)

def _should_emit(key):
    with _recent_lock:
        _prune_recent()
        if key in _recent_hits:
            return False
        _recent_hits[key] = _now()
        return True

def _append_report(item):
    with _report_lock:
        _report["items"].append(item)
        if len(_report["items"]) > MAX_REPORT_ITEMS:
            _report["items"] = _report["items"][-MAX_REPORT_ITEMS:]

def _record_item(kind, severity, title, details, action=None, status=None):
    item = {
        "time": _now(),
        "kind": kind,
        "severity": severity,
        "title": title,
        "details": details,
        "action": action,
        "status": status,
    }
    _append_report(item)
    return item

def _family_label(hash_hex=None, clam_signature=None):
    if clam_signature:
        lowered = clam_signature.lower()
        for family, description in KNOWN_MALWARE_FAMILIES.items():
            if family in lowered:
                return f"{clam_signature} ({description})"
        return clam_signature
    if hash_hex and hash_hex in KNOWN_BAD_HASHES:
        return KNOWN_BAD_HASHES[hash_hex]
    return "Unknown"

def sha256_of_file(path, chunk_size=1024 * 1024):
    try:
        h = hashlib.sha256()
        with open(path, "rb") as f:
            while True:
                chunk = f.read(chunk_size)
                if not chunk:
                    break
                h.update(chunk)
        return h.hexdigest()
    except Exception:
        return None

def load_external_hash_feed(path_or_url=None):
    if not path_or_url:
        return 0

    added = 0
    try:
        p = Path(path_or_url)
        if p.exists():
            with open(p, "r") as f:
                for line in f:
                    line = line.strip()
                    if not line or line.startswith("#"):
                        continue
                    parts = line.split(",", 1)
                    if len(parts) == 2:
                        digest, family = parts[0].strip().lower(), parts[1].strip()
                        if len(digest) == 64:
                            KNOWN_BAD_HASHES[digest] = family
                            added += 1
    except Exception:
        pass
    return added

_clamav_checked = False
_clamav_available = False
_clamav_mode = None
_clamd_socket = None

def _detect_clamav():
    global _clamav_checked, _clamav_available, _clamav_mode, _clamd_socket
    if _clamav_checked:
        return _clamav_available

    _clamav_checked = True

    try:
        import pyclamd  # type: ignore
        try:
            cd = pyclamd.ClamdUnixSocket()
            cd.ping()
            _clamd_socket = cd
            _clamav_available = True
            _clamav_mode = "clamd"
            return True
        except Exception:
            try:
                cd = pyclamd.ClamdNetworkSocket()
                cd.ping()
                _clamd_socket = cd
                _clamav_available = True
                _clamav_mode = "clamd"
                return True
            except Exception:
                pass
    except ImportError:
        pass

    if shutil.which("clamscan"):
        _clamav_available = True
        _clamav_mode = "cli"
        return True

    _clamav_available = False
    return False

def clamav_scan_file(path):
    if not _detect_clamav():
        return False, None

    try:
        if _clamav_mode == "clamd":
            result = _clamd_socket.scan_file(str(path))
            if result:
                status, signature = list(result.values())[0]
                if status == "FOUND":
                    return True, signature
            return False, None

        elif _clamav_mode == "cli":
            proc = subprocess.run(
                ["clamscan", "--no-summary", str(path)],
                capture_output=True,
                text=True,
                timeout=30,
            )
            if "FOUND" in proc.stdout:
                line = proc.stdout.strip().splitlines()[-1]
                signature = line.split(":", 1)[-1].replace("FOUND", "").strip()
                return True, signature
            return False, None

    except Exception:
        return False, None

    return False, None

def clamav_status():
    available = _detect_clamav()
    return {
        "available": available,
        "mode": _clamav_mode if available else None,
    }

def _queue_action(kind, payload, details):
    with _pending_lock:
        action_id = _next_action_id[0]
        _next_action_id[0] += 1
        _pending_actions[action_id] = {
            "kind": kind,
            "payload": payload,
            "details": details,
            "queued_at": _now(),
        }
    return action_id

def get_pending_confirmations():
    with _pending_lock:
        return deepcopy(_pending_actions)

def confirm_action(action_id, approve):
    with _pending_lock:
        action = _pending_actions.pop(action_id, None)

    if action is None:
        return {"ok": False, "reason": "no such pending action"}

    if not approve:
        _record_item(
            kind=action["kind"],
            severity="info",
            title="Action rejected by user",
            details=action["details"],
            action=action["kind"],
            status="rejected",
        )
        return {"ok": True, "action": "rejected"}

    if action["kind"] == "terminate_process":
        pid = action["payload"]
        terminated = terminate_process(pid)
        with _report_lock:
            if terminated:
                _report["terminated_count"] += 1
            else:
                _report["failed_terminations"] += 1
        _record_item(
            kind="process",
            severity="extreme",
            title="Process termination confirmed by user",
            details=action["details"],
            action="terminate",
            status="terminated" if terminated else "failed",
        )
        return {"ok": True, "action": "terminated" if terminated else "failed"}

    if action["kind"] == "delete_file":
        file_path = action["payload"]
        try:
            os.remove(file_path)
            _record_item(
                kind="file",
                severity="extreme",
                title="File deletion confirmed by user",
                details=action["details"],
                action="delete",
                status="deleted",
            )
            return {"ok": True, "action": "deleted"}
        except Exception as e:
            _record_item(
                kind="file",
                severity="low",
                title="File deletion failed",
                details={**action["details"], "error": str(e)},
                action="delete",
                status="failed",
            )
            return {"ok": False, "reason": str(e)}

    return {"ok": False, "reason": "unknown action kind"}

def terminate_process(proc_pid):
    try:
        proc = psutil.Process(proc_pid)

        children = []
        try:
            children = proc.children(recursive=True)
            for child in children:
                try:
                    child.terminate()
                except Exception:
                    pass
        except Exception:
            pass

        try:
            proc.terminate()
        except Exception:
            pass

        targets = [proc, *children]
        gone, alive = psutil.wait_procs(targets, timeout=3)

        for alive_proc in alive:
            try:
                alive_proc.kill()
            except Exception:
                pass

        psutil.wait_procs(alive, timeout=3)

        return not psutil.pid_exists(proc_pid)
    except Exception:
        return False

def enforce_single_instance():
    my_pid = os.getpid()

    if LOCKFILE_PATH.exists():
        try:
            existing_pid = int(LOCKFILE_PATH.read_text().strip())
            if psutil.pid_exists(existing_pid):
                print("\n\033[33m[AVSS] SOAR is already running (PID {}).\033[0m".format(existing_pid))
                print("\033[33mExiting this instance.\033[0m\n")
                return False
        except (ValueError, OSError):
            pass

    try:
        LOCKFILE_PATH.write_text(str(my_pid))
    except OSError:
        pass

    return True

def release_single_instance_lock():
    try:
        if LOCKFILE_PATH.exists():
            existing_pid = int(LOCKFILE_PATH.read_text().strip())
            if existing_pid == os.getpid():
                LOCKFILE_PATH.unlink()
    except (ValueError, OSError):
        pass

def _scan_network_connections_once():
    network_hits = 0
    try:
        for conn in psutil.net_connections(kind="inet"):
            if conn.status == "ESTABLISHED" and conn.raddr:
                remote_ip = conn.raddr.ip
                remote_port = conn.raddr.port

                if remote_ip in SUSPICIOUS_IPS or remote_port in SUSPICIOUS_PORTS:
                    key = f"suspicious-net::{remote_ip}::{remote_port}"
                    if _should_emit(key):
                        network_hits += 1
                        _record_item(
                            kind="network",
                            severity="critical",
                            title="Suspicious Network Connection Detected",
                            details={"ip": remote_ip, "port": remote_port, "pid": conn.pid},
                            action="queued_for_review",
                            status="pending",
                        )
    except psutil.AccessDenied:
        pass
    except Exception:
        with _report_lock:
            _report["errors"] += 1

    return {"network_hits": network_hits}

def _scan_processes_once():
    process_hits = 0

    for proc in psutil.process_iter(["pid", "name", "exe"]):
        try:
            proc_pid = proc.info.get("pid")
            proc_name = proc.info.get("name") or ""
            proc_exe = proc.info.get("exe") or ""

            if not proc_exe or not os.path.isfile(proc_exe):
                continue

            try:
                if os.path.getsize(proc_exe) > MAX_FILE_SCAN_SIZE:
                    continue
            except OSError:
                continue

            digest = sha256_of_file(proc_exe)
            hash_hit = digest in KNOWN_BAD_HASHES if digest else False

            clam_infected, clam_signature = False, None
            if not hash_hit:
                clam_infected, clam_signature = clamav_scan_file(proc_exe)

            if hash_hit or clam_infected:
                key = f"proc-detect::{proc_pid}::{digest}"
                if _should_emit(key):
                    process_hits += 1
                    label = _family_label(hash_hex=digest, clam_signature=clam_signature)
                    details = {
                        "pid": proc_pid,
                        "name": proc_name,
                        "exe": proc_exe,
                        "sha256": digest,
                        "detection": label,
                        "detection_method": "clamav" if clam_infected else "hash_match",
                    }
                    action_id = _queue_action(
                        kind="terminate_process",
                        payload=proc_pid,
                        details=details,
                    )
                    _record_item(
                        kind="process",
                        severity="extreme",
                        title=f"Known malicious executable detected: {label}",
                        details={**details, "confirmation_id": action_id},
                        action="awaiting_confirmation",
                        status="pending",
                    )

        except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
            continue
        except Exception as e:
            with _report_lock:
                _report["errors"] += 1
            _record_item(
                kind="error",
                severity="low",
                title="Process scan error",
                details={"error": str(e)},
                action="scan",
                status="failed",
            )

    return {"process_hits": process_hits}

def _scan_files_once(root=None):
    file_hits = 0
    scan_root = root or DESKTOP

    if scan_root is None or not scan_root.exists():
        return {"file_hits": 0}

    try:
        for path in scan_root.rglob("*"):
            try:
                if not path.is_file():
                    continue
                if path.stat().st_size > MAX_FILE_SCAN_SIZE:
                    continue

                digest = sha256_of_file(path)
                hash_hit = digest in KNOWN_BAD_HASHES if digest else False

                clam_infected, clam_signature = False, None
                if not hash_hit:
                    clam_infected, clam_signature = clamav_scan_file(path)

                if hash_hit or clam_infected:
                    key = f"file-detect::{str(path).lower()}::{digest}"
                    if _should_emit(key):
                        file_hits += 1
                        label = _family_label(hash_hex=digest, clam_signature=clam_signature)
                        details = {
                            "name": path.name,
                            "path": str(path),
                            "sha256": digest,
                            "detection": label,
                            "detection_method": "clamav" if clam_infected else "hash_match",
                        }
                        action_id = _queue_action(
                            kind="delete_file",
                            payload=str(path),
                            details=details,
                        )
                        _record_item(
                            kind="file",
                            severity="extreme",
                            title=f"Known malicious file detected: {label}",
                            details={**details, "confirmation_id": action_id},
                            action="awaiting_confirmation",
                            status="pending",
                        )

            except Exception as e:
                with _report_lock:
                    _report["errors"] += 1
                _record_item(
                    kind="error",
                    severity="low",
                    title="File scan error",
                    details={"path": str(path), "error": str(e)},
                    action="scan",
                    status="failed",
                )
    except Exception as e:
        with _report_lock:
            _report["errors"] += 1
        _record_item(
            kind="error",
            severity="low",
            title="Directory scan error",
            details={"error": str(e), "root": str(scan_root)},
            action="scan",
            status="failed",
        )

    return {"file_hits": file_hits}

def scan_once(file_scan_root=None):
    process_result = _scan_processes_once()
    file_result = _scan_files_once(root=file_scan_root)
    network_result = _scan_network_connections_once()

    with _report_lock:
        _report["scan_count"] += 1
        _report["process_hits"] += process_result["process_hits"]
        _report["file_hits"] += file_result["file_hits"]
        _report["network_hits"] += network_result["network_hits"]
        _report["suspicious_count"] += (
            process_result["process_hits"]
            + file_result["file_hits"]
            + network_result["network_hits"]
        )
        _report["last_scan"] = _now()

    return get_report(clear=False)

def run_avss_loop(stop_event, interval=MONITOR_INTERVAL, file_scan_root=None):
    with _report_lock:
        _report["running"] = True

    try:
        while not stop_event.is_set():
            try:
                scan_once(file_scan_root=file_scan_root)
            except Exception as e:
                with _report_lock:
                    _report["errors"] += 1
                _record_item(
                    kind="error",
                    severity="low",
                    title="Scan loop error",
                    details={"error": str(e)},
                    action="scan_loop",
                    status="failed",
                )

            for _ in range(int(interval * 10)):
                if stop_event.is_set():
                    break
                time.sleep(0.1)
    finally:
        with _report_lock:
            _report["running"] = False

def get_report(clear=False):
    with _report_lock:
        snapshot = deepcopy(_report)
        if clear:
            _report["items"].clear()
            _report["scan_count"] = 0
            _report["suspicious_count"] = 0
            _report["file_hits"] = 0
            _report["process_hits"] = 0
            _report["network_hits"] = 0
            _report["terminated_count"] = 0
            _report["failed_terminations"] = 0
            _report["errors"] = 0
            _report["last_scan"] = None
    return snapshot

def clear_report():
    return get_report(clear=True)

def start_background_monitor(stop_event=None, interval=MONITOR_INTERVAL, file_scan_root=None):
    if stop_event is None:
        stop_event = threading.Event()

    thread = threading.Thread(
        target=run_avss_loop,
        args=(stop_event, interval, file_scan_root),
        daemon=True,
    )
    thread.start()
    return stop_event, thread

def has_pending_items():
    with _report_lock:
        return len(_report["items"]) > 0

def get_pending_items():
    with _report_lock:
        return deepcopy(_report["items"])

def pop_pending_items():
    with _report_lock:
        items = deepcopy(_report["items"])
        _report["items"].clear()
    return items

if __name__ == "__main__":
    print("SOAR AVSS v1.2 - standalone scan")
    status = clamav_status()
    if status["available"]:
        print(f"ClamAV integration active ({status['mode']})")
    else:
        print("ClamAV not found - falling back to hash-only detection.")
        print("Install ClamAV (e.g. `apt install clamav` / `brew install clamav`) for full coverage.")

    report = scan_once()
    print(f"\nScan complete. {report['suspicious_count']} item(s) flagged.")

    pending = get_pending_confirmations()
    if pending:
        print(f"\n{len(pending)} action(s) awaiting confirmation:")
        for action_id, action in pending.items():
            print(f"  [{action_id}] {action['kind']} -> {action['details'].get('detection', 'N/A')}")
        print("\nUse confirm_action(action_id, approve=True/False) to resolve.")
