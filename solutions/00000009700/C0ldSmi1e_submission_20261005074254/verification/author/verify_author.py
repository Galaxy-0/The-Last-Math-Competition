"""Repeat the author checks; no numerical computation enters the proof."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--project", required=True, type=Path)
parser.add_argument("--lake", required=True, type=Path)
parser.add_argument("--output", required=True, type=Path)
args = parser.parse_args()
project = args.project.resolve()
lake = args.lake.resolve()
output = args.output.resolve()
output.mkdir(parents=True, exist_ok=True)
auxiliary = Path(__file__).resolve().parent
environment = dict(os.environ)
environment["PATH"] = str(lake.parent) + os.pathsep + environment.get("PATH", "")
environment.pop("LEAN_PATH", None)
environment.pop("LEAN_SRC_PATH", None)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(label, command):
    result = subprocess.run(
        [str(arg) for arg in command], cwd=project, env=environment,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, check=False,
    )
    text = "Command: " + repr([str(arg) for arg in command]) + "\n"
    text += "Working directory: " + str(project) + "\n"
    text += "Exit status: " + str(result.returncode) + "\n\n" + result.stdout
    (output / (label + ".txt")).write_text(text.rstrip() + "\n")
    if result.returncode != 0:
        raise RuntimeError(label + " failed; see its text log")
    return result.stdout


check_file = project / "Check.lean"
source_files = sorted(p for p in project.glob("*.lean") if p.name != "Check.lean")
source_files += sorted((project / "Conjecture9700").rglob("*.lean"))
assert source_files == [project / "Conjecture9700.lean"], source_files
declarations = []
for path in source_files:
    raw = path.read_bytes()
    assert raw.endswith(b"\n") and not raw.endswith(b"\n\n"), path
    text = raw.decode("utf-8")
    assert all(line == line.rstrip() for line in text.splitlines()), path
    assert not re.search(r"\b(sorry|admit|native_decide|unsafe|partial)\b", text)
    assert not re.search(r"^\s*(private|axiom|example)\b", text, re.MULTILINE)
    for name in re.findall(r"^(?:def|theorem|lemma|abbrev)\s+(\S+)", text, re.MULTILINE):
        assert name.isascii(), name
        declarations.append("Conjecture9700." + name)

assert (project / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.19.0"
manifest = json.loads((project / "lake-manifest.json").read_text())
mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
assert mathlib["rev"] == "c44e0c8ee63ca166450922a373c7409c5d26b00b"
configuration = (project / "lakefile.toml").read_text()
assert 'defaultTargets = ["Conjecture9700"]' in configuration
assert 'moreLeanArgs = ["-DwarningAsError=true"]' in configuration

run("lean-version", [lake.parent / "lean", "--version"])
run("default-build", [lake, "build"])
for source in source_files:
    run("warning-replay-" + source.stem,
        [lake, "env", "lean", "-DwarningAsError=true", source])
if check_file.exists():
    check_lines = [line.strip() for line in check_file.read_text().splitlines() if line.strip()]
    assert check_lines[0] == "import Conjecture9700"
    assert all(line.startswith(("#check ", "#print ")) for line in check_lines[1:])
    run("warning-replay-Check", [lake, "env", "lean", "-DwarningAsError=true", check_file])
inspection = run("types-and-axioms",
    [lake, "env", "lean", "-DwarningAsError=true", auxiliary / "Inspect.lean"])

allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
for name in declarations:
    assert "#print axioms " + name in (auxiliary / "Inspect.lean").read_text()
parsed_axioms = []
for match in re.finditer(
        r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$",
        inspection, re.MULTILINE):
    name, entry = match.groups()
    axioms = set() if entry is None else {item.strip() for item in entry.split(",") if item.strip()}
    assert axioms <= allowed_axioms
    parsed_axioms.append(name)
assert parsed_axioms == declarations, (parsed_axioms, declarations)

summary = {
    "result": "PASS",
    "default_build_covers_all_proof_sources": True,
    "proof_sources": {str(p.relative_to(project)): sha256(p) for p in source_files},
    "configuration": {name: sha256(project / name) for name in
        ["lakefile.toml", "lean-toolchain", "lake-manifest.json"]},
    "all_public_declarations": declarations,
    "parsed_axiom_declarations": parsed_axioms,
    "inspection_file_replayed": check_file.exists(),
    "checker_sha256": sha256(Path(__file__).resolve()),
    "axiom_allowlist": sorted(allowed_axioms),
    "mathematical_auxiliary_computation": "None required",
}
(output / "verification-summary.txt").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps(summary, indent=2))
