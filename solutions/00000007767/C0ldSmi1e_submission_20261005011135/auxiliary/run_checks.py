#!/usr/bin/env python3
"""Run the complete finite checker normally and under -O."""

from hashlib import sha256
import json
from pathlib import Path
import platform
import subprocess
import sys
from time import perf_counter


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    directory = Path(__file__).resolve().parent
    runs = []
    outputs = []
    for options, output_name in (
        ([], "check.json"),
        (["-O"], "check_optimized.json"),
    ):
        command = [sys.executable, "-B", *options, "check.py"]
        start = perf_counter()
        completed = subprocess.run(
            command, cwd=directory, capture_output=True, check=False
        )
        elapsed = perf_counter() - start
        (directory / output_name).write_bytes(completed.stdout)
        error_name = output_name.replace(".json", ".stderr.txt")
        (directory / error_name).write_bytes(completed.stderr)
        if completed.returncode != 0:
            raise RuntimeError(
                f"Checker failed: {command!r}; inspect {error_name}"
            )
        if completed.stderr:
            raise RuntimeError(f"Unexpected stderr: inspect {error_name}")
        payload = json.loads(completed.stdout)
        if (
            payload["status"] != "PASS"
            or payload["explicit_runtime_check_count"] <= 0
        ):
            raise RuntimeError("Output does not confirm executed checks")
        outputs.append(completed.stdout)
        runs.append({
            "command_argv": command,
            "working_directory": str(directory),
            "exit_code": completed.returncode,
            "elapsed_seconds": round(elapsed, 6),
            "stdout_file": output_name,
            "stdout_sha256": sha256(completed.stdout).hexdigest(),
            "stderr_file": error_name,
            "explicit_runtime_check_count": payload["explicit_runtime_check_count"],
        })
    if outputs[0] != outputs[1]:
        raise RuntimeError("Normal and optimized results differ")
    metadata = {
        "python_version": sys.version,
        "python_implementation": platform.python_implementation(),
        "python_executable": sys.executable,
        "platform": platform.platform(),
        "runner_command_argv": [sys.executable, "-B", "run_checks.py"],
        "normal_and_optimized_outputs_byte_identical": True,
        "source_sha256": {
            name: digest(directory / name)
            for name in ("check.py", "run_checks.py")
        },
        "runs": runs,
    }
    (directory / "run_metadata.json").write_text(
        json.dumps(metadata, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    names = (
        "check.py", "run_checks.py", "check.json", "check.stderr.txt",
        "check_optimized.json", "check_optimized.stderr.txt", "run_metadata.json",
    )
    (directory / "SHA256SUMS.txt").write_text(
        "".join(f"{digest(directory / name)}  {name}\n" for name in names),
        encoding="utf-8",
    )
    print(json.dumps({
        "status": "PASS",
        "normal_and_optimized_outputs_byte_identical": True,
        "runtime_checks_per_run": runs[0]["explicit_runtime_check_count"],
        "checker_output_sha256": runs[0]["stdout_sha256"],
        "elapsed_seconds": [run["elapsed_seconds"] for run in runs],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
