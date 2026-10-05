#!/usr/bin/env python3
"""Replay the exact auxiliary checker and retain reproducibility evidence."""
import hashlib
import pathlib
import subprocess
import sys

directory = pathlib.Path(__file__).resolve().parent
completed = subprocess.run([sys.executable, str(directory / "verify.py")],
                           cwd=directory, capture_output=True, check=False)
output = directory / "certificate.replay.json"
output.write_bytes(completed.stdout)
equal = completed.stdout == (directory / "certificate.json").read_bytes()
log = (
    "Interpreter: " + sys.executable + "\n"
    "Version: " + sys.version.replace("\n", " ") + "\n"
    "Command: python3 verify.py\n"
    "Exit status: " + str(completed.returncode) + "\n"
    "Stderr: " + repr(completed.stderr.decode()) + "\n"
    "Byte-identical to first output: " + str(equal) + "\n"
    "Output SHA256: " + hashlib.sha256(completed.stdout).hexdigest() + "\n"
)
(directory / "replay.log").write_text(log)
names = ["verify.py", "replay.py", "REPORT.txt", "certificate.json",
         "certificate.replay.json", "replay.log"]
manifest = "".join(hashlib.sha256((directory / name).read_bytes()).hexdigest()
                   + "  " + name + "\n" for name in names)
(directory / "SHA256SUMS").write_text(manifest)
print(log, end="")
print(manifest, end="")
if completed.returncode != 0 or completed.stderr or not equal:
    raise SystemExit("FAIL: replay did not reproduce the first certificate")
