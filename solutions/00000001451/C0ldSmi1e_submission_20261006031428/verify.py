#!/usr/bin/env python3
"""Independently rebuild the frozen conjecture 1451 project (Python stdlib)."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MODULES = {"Geometry", "Vanishing", "Solution"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalized_inventory(value):
    if set(value["modules"]) != MODULES or len(value["modules"]) != len(MODULES):
        raise ValueError("Wrong compiled module inventory")
    rows = value["declarations"]
    if value["declaration_count"] != len(rows) or not rows:
        raise ValueError("Incorrect declaration count")
    result = {}
    for row in rows:
        if row["name"] in result:
            raise ValueError("Duplicate compiled declaration")
        if row["module"] not in MODULES or row["kind"] == "axiom":
            raise ValueError("Unexpected module or authored axiom")
        if not set(row["axioms"]) <= ALLOWED:
            raise ValueError("Disallowed axiom dependency")
        if not isinstance(row["type"], str) or not row["type"]:
            raise ValueError("Missing declaration type")
        result[row["name"]] = {
            **row, "axioms": sorted(set(row["axioms"]))
        }
    if {r["module"] for r in rows} != MODULES:
        raise ValueError("Missing authored module")
    return result


def validate_inventory(actual, expected):
    if normalized_inventory(actual) != normalized_inventory(expected):
        raise ValueError("Compiled declarations differ from the frozen inventory")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="New directory for all execution records")
    parser.add_argument("--lake", default="lake", help="Lake executable for Lean 4.19.0")
    args = parser.parse_args()
    base = Path(__file__).resolve().parent
    frozen = json.loads((base / "verification/source-manifest.json").read_text())
    pins = json.loads((base / "verification/pinned-dependencies.json").read_text())["packages"]
    manifest = json.loads((base / "lean/lake-manifest.json").read_text())["packages"]
    if {p["name"]: p["rev"] for p in pins} != {p["name"]: p["rev"] for p in manifest}:
        raise ValueError("Pinned dependency manifests disagree")
    expected = json.loads((base / "verification/compiled-inventory.json").read_text())
    normalized_inventory(expected)
    inputs = frozen["source_sha256"]
    if any(sha(base / name) != digest for name, digest in inputs.items()):
        raise ValueError("Frozen original/source/configuration identity mismatch")
    lean_names = {p.name for p in (base / "lean").glob("*.lean")}
    if lean_names != {"Geometry.lean", "Vanishing.lean", "Solution.lean", "Audit.lean", "lakefile.lean"}:
        raise ValueError("Unexpected or missing authored Lean file")
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix="tlmc1451-verification-"))
    if args.output:
        out.mkdir(parents=True, exist_ok=False)
    project = out / "fresh-project"
    (project / ".lake/packages").mkdir(parents=True)
    (project / "evidence").mkdir()
    for name in inputs:
        if name.startswith("lean/"):
            shutil.copyfile(base / name, project / Path(name).name)
    for package in pins:
        dependency = (base / "lean/.lake/packages" / package["name"]).resolve(strict=True)
        (project / ".lake/packages" / package["name"]).symlink_to(dependency, target_is_directory=True)
    env = os.environ.copy()
    removed = [key for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LAKE_ENV") if key in env]
    for key in removed:
        env.pop(key)
    env["GIT_OPTIONAL_LOCKS"] = "0"
    records = []

    def run(label, argv):
        dest = out / label
        dest.mkdir()
        record = {"label": label, "argv": argv, "cwd": str(project),
                  "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat()}
        proc = subprocess.run(argv, cwd=project, env=env, capture_output=True)
        record.update({"completed_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                       "exit_code": proc.returncode,
                       "stdout": proc.stdout.decode(errors="replace"),
                       "stderr": proc.stderr.decode(errors="replace")})
        records.append(record)
        (dest / "command.json").write_text(json.dumps(record, indent=2) + "\n")
        (dest / "stdout.txt").write_bytes(proc.stdout)
        (dest / "stderr.txt").write_bytes(proc.stderr)
        print(label, "PASS" if proc.returncode == 0 else "FAIL", flush=True)
        if proc.returncode:
            raise RuntimeError(record["stdout"] + record["stderr"])
        return record["stdout"]

    def check_pins(stage):
        for package in pins:
            path = project / ".lake/packages" / package["name"]
            rev = run(stage + "-revision-" + package["name"],
                      ["git", "-C", str(path), "rev-parse", "HEAD"]).strip()
            dirty = run(stage + "-tracked-" + package["name"],
                        ["git", "-C", str(path), "status", "--porcelain", "--untracked-files=no"])
            if rev != package["rev"] or dirty:
                raise ValueError("Wrong revision or modified dependency: " + package["name"])

    version = run("lean-version", [args.lake, "env", "lean", "--version"])
    if "version 4.19.0," not in version:
        raise ValueError("Lean 4.19.0 required")
    check_pins("before")
    run("fresh-full-build", [args.lake, "build"])
    for module in frozen["replay_modules"]:
        run("strict-" + module, [args.lake, "env", "lean", "-DwarningAsError=true", module + ".lean"])
    actual = json.loads((project / "evidence/compiled-inventory.json").read_text())
    validate_inventory(actual, expected)
    check_pins("after")
    if any(sha(base / name) != digest for name, digest in inputs.items()):
        raise ValueError("Inputs changed during verification")
    result = {"result": "PASS", "candidate": "00000001451", "fresh_authored_build": True,
              "source_sha256": inputs, "compiled_inventory": actual,
              "strict_modules": frozen["replay_modules"], "dependency_pins": pins,
              "pins_clean_before_and_after": True, "removed_environment_variable_names": removed,
              "auxiliary_mathematical_computations": "None; the argument is symbolic.",
              "maintainer_acceptance": False, "records": records}
    (out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    shutil.copyfile(Path(__file__), out / "verify.py")
    files = {str(p.relative_to(out)): sha(p) for p in out.rglob("*")
             if p.is_file() and ".lake" not in p.parts}
    (out / "SHA256SUMS.json").write_text(json.dumps(files, indent=2) + "\n")
    print("PASS: fresh build, strict source replay, complete compiled inventory and pinned dependencies.")
    print("Execution records:", out)


if __name__ == "__main__":
    main()
