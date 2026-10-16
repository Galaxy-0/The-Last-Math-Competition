#!/usr/bin/env python3
"""Bounded #8502 reproduction, not final review or a general Lean sandbox.

Python 3.10+; --skip-update uses only existing exact physical Git checkouts.
Only this project's .lake/build is cleared. Dependency build caches and the
installed compiler remain trust inputs, not a clean-machine bootstrap claim.
"""
from __future__ import annotations

import argparse
from collections import Counter
from contextlib import contextmanager
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import time

CID = "00000008502"
PIN = "leanprover/lean4:v4.33.1"
SOURCE_COMMIT = "cce2d90cb298de9595798eb674d2c80712100532"
SOURCE_BLOB = "a2f2c93606d87db922691efc471572a32355e881"
SOURCE_SHA256 = "717cfea39448d0f7480d109d734bcb31293b73fe6d97a7bd0530462ac2402c2f"
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NAME = r"[A-Za-z_][A-Za-z_0-9]*"
QUALIFIED = NAME + r"(?:\." + NAME + r")*"
MODULES = {
    "RationalDerivative": "Rational8502",
    "DifferentialMatrix": "Differential8502",
    "PointClosure": "PointClosure8502",
    "ConcretePV": "Concrete8502"
}
ROOTS = (*MODULES, "Main", "Check")
MATH_HASHES = {
    "RationalDerivative": "08ab9b3fed9a7ee230f57774f0970d4e7ea43a1b9ae0a9803a61f642afa91969",
    "DifferentialMatrix": "d03dfd6d4fdcad00e1d37c594f9861abcc060cc276fe51c591e844ebca5c942a",
    "PointClosure": "9ccfab85602671af6a6c081deef56a7b04b345d3d4f52b261ba951344d06ae33",
    "ConcretePV": "e0d1dc8d259eee3660c990e1c58454cdc646bea7bbf3a07106fa3c250f9d96e6"
}
THEOREMS = (
    "Rational8502.fractionDerivative_zero_denominator",
    "Rational8502.fractionDerivative_scaling",
    "Rational8502.derivative_fraction",
    "Rational8502.derivative_polynomial",
    "Rational8502.derivative_zero",
    "Rational8502.derivative_one",
    "Rational8502.derivative_X",
    "Rational8502.derivative_add",
    "Rational8502.derivative_mul",
    "Rational8502.derivative_constant",
    "Rational8502.derivative_smul",
    "Rational8502.derivative_zero_iff_constant",
    "Rational8502.concrete_D_X",
    "Rational8502.concrete_constants",
    "Differential8502.fundamental_det",
    "Differential8502.fundamental_equation",
    "Differential8502.one_second_derivative",
    "Differential8502.t_second_derivative",
    "Differential8502.self_base_automorphism",
    "Differential8502.differential_self_group_eq_bot",
    "PointClosure8502.coordinateIdeal_le_vanishingIdeal",
    "PointClosure8502.zeroLocus_coordinateIdeal",
    "PointClosure8502.zeroLocus_vanishingIdeal_singleton",
    "PointClosure8502.subset_algebraicClosure",
    "PointClosure8502.algebraicClosure_le_zeroLocus_iff",
    "PointClosure8502.algebraicClosure_zeroLocus",
    "PointClosure8502.algebraicClosure_idempotent",
    "PointClosure8502.algebraicClosure_singleton",
    "PointClosure8502.pointToPoint_preimage_zeroLocus",
    "PointClosure8502.zariski_isClosed_zeroLocus",
    "PointClosure8502.zariski_isClosed_iff",
    "PointClosure8502.zariskiClosure_eq_algebraicClosure",
    "PointClosure8502.zariskiClosure_singleton",
    "PointClosure8502.vanishingIdeal_singleton_eq_kernel",
    "PointClosure8502.evaluation_surjective",
    "PointClosure8502.pointCoordinateRingEquiv_mk",
    "PointClosure8502.pointCoordinateRing_krullDim",
    "PointClosure8502.closurePointCoordinateRing_krullDim",
    "PointClosure8502.identity_matrixCoords",
    "PointClosure8502.matrixOfPoint_identity",
    "PointClosure8502.matrixOfPoint_matrixCoords",
    "PointClosure8502.matrixCoords_injective",
    "PointClosure8502.determinantRelation_eval_identity",
    "PointClosure8502.determinantRelation_mem_pointIdeal",
    "PointClosure8502.determinantRelation_eval_matrixCoords",
    "PointClosure8502.identity_zeroLocus_coordinateIdeal",
    "PointClosure8502.identity_algebraicClosure",
    "PointClosure8502.identity_matrix_closure",
    "PointClosure8502.identity_coordinateRing_krullDim",
    "PointClosure8502.identity_matrix_closure_krullDim",
    "PointClosure8502.identity_matrix_zariskiClosure",
    "PointClosure8502.identity_matrix_zariskiClosure_krullDim",
    "PointClosure8502.glPointCoords_identity",
    "PointClosure8502.glPointCoords_injective",
    "PointClosure8502.glPointCoords_satisfies_relation",
    "PointClosure8502.matrixCoords_matrixOfPoint_of_relation",
    "PointClosure8502.matrixOfPoint_det_ne_zero_of_relation",
    "PointClosure8502.glPointCoords_range",
    "PointClosure8502.glPointCoords_preimage_identity",
    "PointClosure8502.identity_GL_isClosed",
    "PointClosure8502.identity_GL_zariskiClosure",
    "PointClosure8502.identity_GL_closure_coordinateRing_krullDim",
    "Concrete8502.Dt",
    "Concrete8502.base_constants",
    "Concrete8502.algebraically_closed_constants",
    "Concrete8502.self_field_generated",
    "Concrete8502.U_det",
    "Concrete8502.U_equation",
    "Concrete8502.generatedPVRing_eq_top",
    "Concrete8502.self_ring_differential_simple",
    "Concrete8502.self_automorphism_identity",
    "Concrete8502.self_action_identity",
    "Concrete8502.self_represented_image",
    "Concrete8502.self_galois_dimension_zero",
    "Concrete8502.counterexample_not_in_asserted_spectrum",
    "Concrete8502.no_uniform_second_order_spectrum",
)
DEPENDENCIES = (
    ("mathlib", "https://github.com/leanprover-community/mathlib4.git", MATHLIB, MATHLIB, "", "lakefile.lean"),
    ("plausible", "https://github.com/leanprover-community/plausible", "b7eb3304aeae834b12dda98993a37f6a41f6f0bb", "main", "leanprover-community", "lakefile.toml"),
    ("LeanSearchClient", "https://github.com/leanprover-community/LeanSearchClient", "5f4d51b81cbd3f6b32b156bfad9056621a040404", "main", "leanprover-community", "lakefile.toml"),
    ("importGraph", "https://github.com/leanprover-community/import-graph", "16f02aa7642864af59f1ff0e384a015994db9118", "main", "leanprover-community", "lakefile.toml"),
    ("proofwidgets", "https://github.com/leanprover-community/ProofWidgets4", "4be2e3d5087eeb272cf5a8853b8f9dd025ef5957", "main", "leanprover-community", "lakefile.lean"),
    ("aesop", "https://github.com/leanprover-community/aesop", "3448c0bcc5ce01b2d1546e483ec3620e32df3d0e", "master", "leanprover-community", "lakefile.toml"),
    ("Qq", "https://github.com/leanprover-community/quote4", "92c15be17b7caf78c2ad767ec40f89052d908d81", "master", "leanprover-community", "lakefile.toml"),
    ("batteries", "https://github.com/leanprover-community/batteries", "4488d40d070b9700d4d5a6aa342f0d40c31b2a2d", "main", "leanprover-community", "lakefile.toml"),
    ("Cli", "https://github.com/leanprover/lean4-cli", "6130a47896ce867c6a4a55373441e59e565bad0f", "v4.33.0", "leanprover", "lakefile.toml"),
)
LAKEFILE = '''import Lake
open Lake DSL

package tlmc8502 where
  srcDir := "."

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target]
lean_lib TLMC8502 where
  roots := #[`RationalDerivative, `DifferentialMatrix, `PointClosure, `ConcretePV, `Main, `Check]
  moreLeanArgs := #["-DwarningAsError=true"]'''
LAKE_BIN: Path | None = None
DEADLINE: float | None = None
PROFILE_RECORDS: list[dict] = []
WINDOWS_LINKTEXT = {
    "mathlib": {
        b"scripts/bench/build/fake-root/bin/lean.py": b"819298943e1a8c331413fb55e2c4bbc98d05e562",
        b"scripts/bench/size/run.py": b"e5224d533ef27b001224859a9b36696846a7e7fe",
    },
    "batteries": {b"docs/README.md": b"32d46ee883b58d6a383eed06eb98f33aa6530ded"},
}


class ReproductionError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ReproductionError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def check_deadline() -> None:
    require(DEADLINE is None or time.monotonic() < DEADLINE, "Reproduction wall-clock budget exceeded")


@contextmanager
def phase(name: str):
    started = time.monotonic_ns()
    status = "error"
    try:
        yield
        status = "ok"
    finally:
        record = {"phase": name, "status": status,
                  "duration_ms": (time.monotonic_ns() - started) // 1_000_000}
        PROFILE_RECORDS.append(record)
        print("[PROFILE] " + json.dumps(record, ensure_ascii=True), flush=True)


def lexical_component(name: str) -> None:
    require(name not in {"", ".", ".."}, "Dot/empty path alias rejected")
    if os.name == "nt":
        require(not name.endswith((".", " ")) and ":" not in name,
                "Windows path alias/stream rejected: " + name)
        require(name.split(".", 1)[0].upper() not in
                {"CON", "PRN", "AUX", "NUL", *("COM" + str(i) for i in range(1, 10)),
                 *("LPT" + str(i) for i in range(1, 10))}, "Windows device path rejected")


def safe_path(path: Path, checked_parents: set[Path] | None = None) -> Path:
    """Generic paths resolve fully; only canonical ordinary directories are memoized."""
    for component in path.parts:
        if component != path.anchor:
            lexical_component(component)
    absolute = Path(os.path.abspath(path))
    part, directories = absolute, []
    while True:
        # The requested entry is never cached, including on repeated calls.
        if part != absolute and checked_parents is not None and part in checked_parents:
            break
        try:
            info = part.lstat()
        except FileNotFoundError:
            info = None
        if info is not None:
            require(not stat.S_ISLNK(info.st_mode) and not
                    (getattr(info, "st_file_attributes", 0) & 0x400),
                    "Symlink/reparse path rejected: " + str(part))
            if stat.S_ISDIR(info.st_mode):
                directories.append(part)
        if part.parent == part:
            break
        part = part.parent
    require(absolute.resolve() == absolute, "Path resolution changed the checked boundary")
    if checked_parents is not None:
        checked_parents.update(directories)
    return absolute


def audit_tree_entries(root: Path, checked_parents: set[Path]) -> set[Path]:
    """Walk every entry, including caches/.git, without resolving each ordinary file.

    scandir's non-following stat supplies lstat metadata for each freshly enumerated
    entry. Exact names under resolved directories establish the file boundary.
    Only directory canonicality is memoized within this invocation's audit pass.
    """
    root = safe_path(root, checked_parents)
    require(root.is_dir(), "Audit tree root is not a directory")
    pending, files = [root], set()
    entries_count, directories_count = 0, 0
    while pending:
        check_deadline()
        parent = safe_path(pending.pop(), checked_parents)
        require(parent.is_relative_to(root), "Audit directory escaped checked boundary")
        directories_count += 1
        with os.scandir(parent) as entries:
            for entry in entries:
                check_deadline()
                lexical_component(entry.name)
                info = entry.stat(follow_symlinks=False)
                require(not stat.S_ISLNK(info.st_mode) and not
                        (getattr(info, "st_file_attributes", 0) & 0x400),
                        "Symlink/reparse path rejected: " + str(parent / entry.name))
                path = parent / entry.name
                require(path.is_relative_to(root), "Audit entry escaped checked boundary")
                entries_count += 1
                if stat.S_ISDIR(info.st_mode):
                    pending.append(path)
                else:
                    require(stat.S_ISREG(info.st_mode), "Non-regular audit tree entry")
                    files.add(path)
    print("[PROFILE] " + json.dumps({"phase": "tree.entries", "root": str(root),
          "entries": entries_count, "directories": directories_count}, ensure_ascii=True), flush=True)
    return files


def tracked_file_path(checkout: Path, relative: bytes, files: set[Path],
                      checked_parents: set[Path]) -> Path:
    text = relative.decode("utf-8", errors="strict")
    require("\\" not in text and not text.startswith("/"), "Aliased tracked path rejected")
    for component in text.split("/"):
        lexical_component(component)
    path = checkout / text
    require(path.is_relative_to(checkout) and path in files and path.parent in checked_parents,
            "Tracked path not an exact enumerated file under a canonical parent")
    # Never reuse a file's scan stat or bytes for the independent tracked check.
    info = path.lstat()
    require(stat.S_ISREG(info.st_mode) and not (getattr(info, "st_file_attributes", 0) & 0x400),
            "Unsafe/missing tracked dependency file")
    return path


def child_env() -> dict[str, str]:
    # Filter names before reading values; never inspect or log credential values.
    env = {key: os.environ[key] for key in os.environ
           if not key.upper().startswith(("GH_", "GITHUB_", "GIT_", "GCM_", "SSH_", "LEAN_"))
           and not any(word in key.upper() for word in ("TOKEN", "SECRET", "PASSWORD", "CREDENTIAL", "API_KEY"))}
    env.update(PYTHONUTF8="1", PYTHONIOENCODING="utf-8", PYTHONDONTWRITEBYTECODE="1",
               LANG="C.UTF-8", LC_ALL="C.UTF-8", NO_COLOR="1", GIT_TERMINAL_PROMPT="0",
               GCM_INTERACTIVE="Never", GCM_GUI_PROMPT="Never", GIT_NO_LAZY_FETCH="1",
               GIT_OPTIONAL_LOCKS="0", GIT_NO_REPLACE_OBJECTS="1",
               GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
               GIT_CONFIG_COUNT="2", GIT_CONFIG_KEY_0="credential.helper", GIT_CONFIG_VALUE_0="",
               GIT_CONFIG_KEY_1="core.fsmonitor", GIT_CONFIG_VALUE_1="false",
               MATHLIB_NO_CACHE_ON_UPDATE="1")
    if LAKE_BIN is not None:
        env["PATH"] = str(LAKE_BIN) + os.pathsep + env.get("PATH", "")
    return env


def run(args: list[str], cwd: Path, timeout: int = 120, show_output: bool = False) -> bytes:
    if DEADLINE is not None:
        remaining = DEADLINE - time.monotonic()
        require(remaining > 0, "Reproduction wall-clock budget exceeded")
        timeout = min(timeout, remaining)
    try:
        result = subprocess.run(args, cwd=cwd, env=child_env(), stdin=subprocess.DEVNULL,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                timeout=timeout, check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ReproductionError("Local tool failed or timed out: " + Path(args[0]).name) from exc
    if show_output:
        print((result.stdout + result.stderr).decode("utf-8", errors="replace"), flush=True)
    require(result.returncode == 0, "Local command failed (exit " + str(result.returncode) +
            "): " + Path(args[0]).name)
    return result.stdout


def git(repo: Path, *args: str) -> bytes:
    return run(["git", "--no-pager", "-c", "credential.helper=", "-c", "core.fsmonitor=false",
                "-C", str(repo), *args], repo)


def validate_source(package: Path, repo: Path, m: dict) -> dict:
    for key, expected in (("source_commit", SOURCE_COMMIT), ("source_git_blob", SOURCE_BLOB),
                          ("source_sha256", SOURCE_SHA256)):
        require(m.get(key) == expected, "Frozen source manifest mismatch: " + key)
    source_name = "conjectures/" + CID + ".md"
    require(git(repo, "cat-file", "-t", SOURCE_COMMIT).strip() == b"commit", "Source object is not a commit")
    require(git(repo, "rev-parse", SOURCE_COMMIT + ":" + source_name).strip().decode() == SOURCE_BLOB,
            "Source commit does not bind the advertised blob")
    require(git(repo, "cat-file", "-t", SOURCE_BLOB).strip() == b"blob", "Source object is not a blob")
    raw = git(repo, "cat-file", "blob", SOURCE_BLOB)
    require(sha256(raw) == SOURCE_SHA256, "Raw source SHA-256 mismatch")
    require(hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest() == SOURCE_BLOB,
            "Raw source Git-blob hash mismatch")
    require(safe_path(package / "source.md").read_bytes() == raw, "Frozen source differs from raw Git blob")
    current = safe_path(repo / source_name).read_bytes()
    require(current.replace(b"\r\n", b"\n") == raw.replace(b"\r\n", b"\n"),
            "Current bilingual source differs (CRLF-to-LF comparison)")
    raw.decode("utf-8", errors="strict")
    return {"commit": SOURCE_COMMIT, "blob": SOURCE_BLOB, "raw_sha256": SOURCE_SHA256}


def expected_lock() -> dict:
    return {"version": "1.2.0", "packagesDir": ".lake/packages", "name": "tlmc8502",
            "lakeDir": ".lake", "fixedToolchain": False, "packages": [
                {"name": name, "type": "git", "url": url, "rev": rev, "inputRev": input_rev,
                 "subDir": None, "scope": scope, "manifestFile": "lake-manifest.json",
                 "inherited": name != "mathlib", "configFile": config}
                for name, url, rev, input_rev, scope, config in DEPENDENCIES]}


def validate_config(lean: Path) -> dict:
    require(safe_path(lean / "lean-toolchain").read_text(encoding="utf-8").strip() == PIN,
            "Exact Lean toolchain pin required")
    require(not os.path.lexists(lean / "lakefile.toml"), "Unexpected alternate Lake configuration")
    require(safe_path(lean / "lakefile.lean").read_text(encoding="utf-8").strip() == LAKEFILE,
            "Declarative Lake configuration/roots changed")
    lock = json.loads(safe_path(lean / "lake-manifest.json").read_text(encoding="utf-8"))
    require(lock == expected_lock(), "Exact nine-package Lake lock/configuration mismatch")
    return lock


def dependency_mode_allowed(name: str, mode: bytes, relative: bytes) -> bool:
    # Three fixed inert Git links must be exact ordinary Windows link-text files,
    # never physical symlinks/reparse points; benchmark scripts are not executed.
    return mode in {b"100644", b"100755"} or (
        os.name == "nt" and mode == b"120000" and relative in WINDOWS_LINKTEXT.get(name, set()))


def materialized_dependencies(lean: Path, lock: dict) -> dict:
    require(lock == expected_lock(), "Refuse non-frozen dependency specifications")
    reports = {}
    checked_parents: set[Path] = set()
    for spec in lock["packages"]:
        name = spec["name"]
        checkout = safe_path(lean / ".lake" / "packages" / name, checked_parents)
        require(checkout.is_dir(), "Missing physical dependency checkout: " + name)
        git_dir = safe_path(checkout / ".git", checked_parents)
        require(git_dir.is_dir(), "Dependency must own a physical .git directory: " + name)
        with phase("dependency." + name + ".walk"):
            files = audit_tree_entries(checkout, checked_parents)
        with phase("dependency." + name + ".git_metadata"):
            require(safe_path(Path(git(checkout, "rev-parse", "--show-toplevel").decode().strip())) == checkout,
                    "Dependency inherited/redirected a parent Git checkout: " + name)
            require(safe_path(Path(git(checkout, "rev-parse", "--absolute-git-dir").decode().strip())) == git_dir,
                    "Dependency Git metadata redirected: " + name)
            require(git(checkout, "rev-parse", "HEAD").decode().strip() == spec["rev"], "Dependency HEAD mismatch: " + name)
            require(git(checkout, "remote", "get-url", "origin").decode().strip() == spec["url"],
                    "Dependency origin mismatch: " + name)
            require(not git(checkout, "status", "--porcelain=v1", "-z", "--untracked-files=no",
                            "--ignore-submodules=none").strip(), "Modified tracked dependency source: " + name)
        with phase("dependency." + name + ".tracked_bytes_and_tree"):
            tracked = git(checkout, "ls-files", "--stage", "-z").split(b"\0")
            require(any(tracked), "Empty tracked dependency inventory: " + name)
            tree = {}
            for record in git(checkout, "ls-tree", "-r", "-z", "--full-tree", "HEAD").split(b"\0"):
                if record:
                    header, relative = record.split(b"\t", 1)
                    mode, kind, oid = header.split()
                    require(kind == b"blob" and dependency_mode_allowed(name, mode, relative),
                            "Non-regular dependency Git tree: " + name)
                    if mode == b"120000":
                        require(oid == WINDOWS_LINKTEXT[name][relative], "Fixed inert-link Git blob mismatch")
                    require(relative not in tree, "Duplicate dependency tree file: " + name)
                    tree[relative] = (mode, oid)
            indexed = {}
            count = 0
            for record in tracked:
                if not record:
                    continue
                header, relative = record.split(b"\t", 1)
                mode, oid, stage = header.split()
                require(dependency_mode_allowed(name, mode, relative) and stage == b"0",
                        "Symlink/submodule/unmerged tracked dependency source: " + name)
                if mode == b"120000":
                    require(oid == WINDOWS_LINKTEXT[name][relative], "Fixed inert-link index blob mismatch")
                require(relative not in indexed, "Duplicate tracked dependency file: " + name)
                indexed[relative] = (mode, oid)
                check_deadline()
                path = tracked_file_path(checkout, relative, files, checked_parents)
                data = path.read_bytes()
                def blob_hash(raw: bytes) -> bytes:
                    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest().encode()
                if blob_hash(data) != oid:
                    require(mode != b"120000", "Inert link-text placeholder changed: " + name)
                    # Permit ordinary UTF-8 text checkout EOL conversion, never binary normalization.
                    require(b"\0" not in data, "Tracked binary dependency source changed: " + name)
                    data.decode("utf-8", errors="strict")
                    require(blob_hash(data.replace(b"\r\n", b"\n")) == oid,
                            "Tracked dependency bytes changed despite Git status: " + name)
                count += 1
            require(indexed == tree, "Dependency index differs from the fixed HEAD tree: " + name)
        reports[name] = {"head": spec["rev"], "origin": spec["url"], "clean_tracked_files": count}
    return reports


def scrub_comments(text: str) -> str:
    """Bounded comment lexer; strings are not accepted in authored math/Check."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            out.extend("  ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            out.extend("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.extend(" " * (end - i))
            i = end
        else:
            require(text[i] != '"', "String outside bounded authored Lean dialect")
            out.append(text[i])
            i += 1
    require(depth == 0, "Unterminated Lean comment")
    return "".join(out)


def theorem_names(m: dict) -> list[str]:
    names = m.get("theorems")
    require(isinstance(names, list) and all(isinstance(n, str) for n in names)
            and Counter(names) == Counter(THEOREMS), "Manifest must contain the exact 76 public theorems")
    return names


def source_commands(code: str, namespace: str, module: str) -> dict:
    """Bounded command tree for this frozen dialect, not a general Lean parser.

    Indented case proofs and structure/class data/Prop fields are term bodies;
    exact raw source hashes are an independent execution gate, not AST claims.
    """
    forbidden = r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|run_tac|run_elab|elab|macro|syntax|initialize|builtin_initialize|IO|System|private|protected|attribute|opaque)\b"
    require(re.search(forbidden, code) is None and "#" not in code,
            "Prohibited authored Lean command/token: " + module)
    stack, public, symbols, nodes = [], [], set(), []
    namespaces, pending = 0, False
    body = False
    declaration = r"(?:(?:noncomputable) )?(abbrev|def|theorem|lemma|structure|class|instance) (" + NAME + r")\b"
    for number, line in enumerate(code.splitlines(), 1):
        if not line.strip():
            continue
        if line[0].isspace():
            require(body, "Indented command outside a declaration: " + module)
            continue
        text = line.strip()
        node = {"line": number, "command": text.split()[0]}
        nodes.append(node)
        if text == "@[instance_reducible]":
            require(not pending, "Repeated declaration attribute")
            pending = True
            body = False
            continue
        match = re.match(declaration, text)
        if match:
            require(any(kind == "namespace" for kind, _ in stack),
                    "Declaration outside exact namespace: " + module)
            kind, name = match[1], match[2]
            require(name not in symbols, "Duplicate authored declaration: " + module)
            require(not pending or kind == "def", "Unsupported attributed declaration")
            symbols.add(name)
            node.update(kind=kind, name=namespace + "." + name)
            if kind in {"theorem", "lemma"}:
                public.append(namespace + "." + name)
            pending, body = False, True
            continue
        require(not pending, "Attribute not followed by declaration")
        body = False
        if match := re.fullmatch(r"namespace (" + QUALIFIED + r")", text):
            require(match[1] == namespace and namespaces == 0, "Unsupported namespace layout: " + module)
            namespaces += 1
            stack.append(("namespace", namespace))
        elif match := re.fullmatch(r"(?:noncomputable )?section(?: (" + NAME + r"))?", text):
            stack.append(("section", match[1] or ""))
        elif match := re.fullmatch(r"end(?: (" + QUALIFIED + r"))?", text):
            require(bool(stack) and (match[1] or "") == stack[-1][1], "Mismatched namespace/section end")
            stack.pop()
        elif match := re.fullmatch(r"import (" + QUALIFIED + r")", text):
            require(not stack and (match[1].startswith("Mathlib.") or match[1] in MODULES),
                    "Unsupported source import: " + module)
        elif text.startswith("open "):
            require(re.fullmatch(r"open (?:scoped )?" + QUALIFIED + r"(?: " + QUALIFIED + r")*", text) is not None,
                    "Unsupported open command")
        elif text.startswith("variable ") or text.startswith("universe "):
            require(bool(stack), "Variable/universe outside source section")
            body = True
        elif text.startswith("omit ") or text.startswith("include "):
            require(text.endswith(" in") and bool(stack), "Unsupported scoped variable command")
        elif text == "set_option autoImplicit false":
            pass
        else:
            require(False, "Unsupported top-level authored command: " + module + ":" + str(number))
    # Lean closes outer anonymous sections at EOF (PointClosure uses this form).
    require(all(kind == "section" and name == "" for kind, name in stack)
            and namespaces == 1 and not pending, "Unclosed source command tree: " + module)
    return {"public": public, "commands": nodes}


def validate_lean(lean: Path, names: list[str]) -> dict:
    require(Counter(names) == Counter(THEOREMS), "Wrong theorem inventory")
    authored = []
    for root, dirs, files in os.walk(lean, followlinks=False):
        parent = Path(root)
        for directory in dirs:
            safe_path(parent / directory)
        if parent == lean:
            dirs[:] = [d for d in dirs if d != ".lake"]
        authored.extend(safe_path(parent / n).relative_to(lean).as_posix() for n in files if n.endswith(".lean"))
    require(set(authored) == {n + ".lean" for n in ROOTS} | {"lakefile.lean"},
            "Unexpected/missing authored Lean module")
    actual, inventories = [], {}
    for module, namespace in MODULES.items():
        raw = safe_path(lean / (module + ".lean")).read_bytes()
        require(sha256(raw) == MATH_HASHES[module], "Frozen mathematical source raw hash mismatch: " + module)
        tree = source_commands(scrub_comments(raw.decode("utf-8", errors="strict")), namespace, module)
        inventories[module] = tree["public"]
        actual.extend(tree["public"])
    require(Counter(actual) == Counter(names), "All four modules/public theorem exact-set mismatch")
    require(scrub_comments((lean / "Main.lean").read_text(encoding="utf-8")).strip() == "import ConcretePV",
            "Main must only import ConcretePV")
    checks, prints, imports = [], [], 0
    lines = [line.strip() for line in scrub_comments((lean / "Check.lean").read_text(encoding="utf-8")).splitlines() if line.strip()]
    require(bool(lines) and lines[0] == "import Main", "Check must start with import Main")
    for line in lines:
        if line == "import Main":
            imports += 1
        elif match := re.fullmatch(r"#check (" + QUALIFIED + r")", line):
            checks.append(match[1])
        elif match := re.fullmatch(r"#print axioms (" + QUALIFIED + r")", line):
            prints.append(match[1])
        else:
            require(False, "Unsafe/additional Check command")
    require(imports == 1 and Counter(checks) == Counter(names) and Counter(prints) == Counter(names),
            "Check/check/axiom inventory must each exactly match all 76 theorems")
    return {"count": len(names), "names": names, "modules": inventories, "source_hashes": dict(MATH_HASHES)}


def frozen_files(package: Path) -> dict[str, str]:
    checked_parents: set[Path] = set()
    package = safe_path(package, checked_parents)
    files = {}
    for root, dirs, names in os.walk(package, followlinks=False):
        parent = Path(root)
        for directory in dirs:
            safe_path(parent / directory, checked_parents)
        dirs[:] = [d for d in dirs if d != "__pycache__" and not (parent == package / "lean4" and d == ".lake")]
        for name in names:
            if parent == package and name in {"review.json", "validation.json"}:
                continue
            path = safe_path(parent / name, checked_parents)
            require(stat.S_ISREG(path.stat().st_mode), "Non-regular authored package file")
            files[path.relative_to(package).as_posix()] = sha256(path.read_bytes())
    return files


def clean_project_build(lean: Path, target: Path | None = None) -> None:
    lean = safe_path(lean)
    expected = lean / ".lake" / "build"
    target = safe_path(expected if target is None else target)
    require(target == expected and target.is_relative_to(lean), "Unsafe project cache deletion boundary")
    if not target.exists():
        return
    require(target.is_dir(), "Project build cache is not a directory")
    checked_parents: set[Path] = set()
    safe_path(target, checked_parents)
    audit_tree_entries(target, checked_parents)
    require(safe_path(target) == expected, "Deletion boundary changed")
    shutil.rmtree(target)


def regression() -> dict:
    def value(p, t):
        return sum((Fraction(c) * t ** i for i, c in enumerate(p)), Fraction(0))
    def differentiated(p):
        return [i * Fraction(c) for i, c in enumerate(p)][1:]
    def multiplied(p, q):
        out = [Fraction(0)] * (len(p) + len(q) - 1)
        for i, c in enumerate(p):
            for j, d in enumerate(q):
                out[i + j] += c * d
        return out
    def added(p, q):
        return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0)
                for i in range(max(len(p), len(q)))]
    def D(p, q, t):
        denominator = value(q, t)
        require(denominator != 0, "Regression pole in rational function")
        return (value(differentiated(p), t) * denominator -
                value(p, t) * value(differentiated(q), t)) / denominator ** 2
    scaling, leibniz, addition, matrix, coordinates = 0, 0, 0, 0, 0
    examples = (([0], [1]), ([1], [1]), ([0, 1], [1]), ([1, 2, 3], [1, 0, 1]),
                ([Fraction(1, 2), -2, 1], [2, 0, 1]))
    for t in (Fraction(-2), Fraction(-1, 2), Fraction(0), Fraction(1, 3), Fraction(2)):
        for p, q in examples:
            a = [2, 1, 1]
            require(D(multiplied(a, p), multiplied(a, q), t) == D(p, q, t),
                    "Exact quotient scaling regression failed")
            scaling += 1
            for r, s in examples:
                x, y = value(p, t) / value(q, t), value(r, t) / value(s, t)
                require(D(multiplied(p, r), multiplied(q, s), t) ==
                        x * D(r, s, t) + y * D(p, q, t), "Exact Leibniz regression failed")
                require(D(added(multiplied(p, s), multiplied(r, q)), multiplied(q, s), t) ==
                        D(p, q, t) + D(r, s, t), "Exact derivative addition failed")
                leibniz += 1
                addition += 1
        require(D([0, 1], [1], t) == 1 and D([1], [1], t) == 0, "D(t)/constant regression failed")
        U = [[Fraction(1), t], [Fraction(0), Fraction(1)]]
        A = [[Fraction(0), Fraction(1)], [Fraction(0), Fraction(0)]]
        derivativeU = [[Fraction(0), D([0, 1], [1], t)], [Fraction(0), Fraction(0)]]
        AU = [[sum((A[i][k] * U[k][j] for k in range(2)), Fraction(0)) for j in range(2)] for i in range(2)]
        require(derivativeU == AU and U[0][0] * U[1][1] - U[0][1] * U[1][0] == 1,
                "Fundamental matrix det=1 / derivative(U)=A*U regression failed")
        matrix += 1
        for M in (U, [[Fraction(2), t], [Fraction(0), Fraction(3)]],
                  [[Fraction(1), t], [Fraction(-1), Fraction(2)]]):
            determinant = M[0][0] * M[1][1] - M[0][1] * M[1][0]
            if determinant == 0:
                continue
            point = [M[0][0], M[0][1], M[1][0], M[1][1], 1 / determinant]
            require(point[4] * (point[0] * point[3] - point[1] * point[2]) - 1 == 0,
                    "Exact matrix-coordinate determinant relation failed")
            require([[point[0], point[1]], [point[2], point[3]]] == M,
                    "Matrix/point coordinate inverse bridge failed")
            coordinates += 1
    identity = [Fraction(1), Fraction(0), Fraction(0), Fraction(1), Fraction(1)]
    require(identity[4] * (identity[0] * identity[3] - identity[1] * identity[2]) == 1,
            "Identity point relation failed")
    return {"quotient_scaling_cases": scaling, "leibniz_cases": leibniz, "addition_cases": addition,
            "fundamental_matrix_cases": matrix, "point_coordinate_cases": coordinates,
            "scope": "Finite exact Fraction regressions only; not universality, PV/Zariski proof or final mathematical review"}


def audit_axioms(output: str, names: list[str]) -> dict:
    audits = {}
    pattern = r"^'(" + QUALIFIED + r")' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])\s*$"
    for match in re.finditer(pattern, output, re.M):
        name, footprint = match[1], match[2]
        require(name in names and name not in audits, "Unexpected/duplicate actual axiom audit")
        used = [] if footprint is None else [a.strip() for a in footprint.split(",")]
        require(set(used) <= ALLOWED_AXIOMS, "Nonstandard axiom footprint: " + name)
        audits[name] = sorted(used)
    require(set(audits) == set(names), "Missing/malformed actual axiom audit")
    return audits


def audit_theorem_types(output: str, names: list[str]) -> dict[str, str]:
    """Capture every actual #check type, rejecting extra or missing output."""
    types, cursor = {}, 0
    pattern = r"^'(" + QUALIFIED + r")' (?:does not depend on any axioms|depends on axioms:\s*\[[^\]]*\])\s*$"
    for audit in re.finditer(pattern, output, re.M):
        name = audit[1]
        require(name in names and name not in types, "Unexpected/duplicate actual theorem type")
        chunk = output[cursor:audit.start()].strip()
        require(re.match(re.escape(name) + r"(?:\.\{[^}\n]+\})?(?=\s|:)", chunk) is not None
                and ":" in chunk, "Missing/malformed actual theorem type: " + name)
        require(all(line[:1].isspace() for line in chunk.splitlines()[1:]),
                "Additional diagnostic mixed into theorem type: " + name)
        types[name] = chunk
        cursor = audit.end()
    require(set(types) == set(names) and not output[cursor:].strip(), "Incomplete/additional theorem type output")
    return types


def preflight(package: Path, repo: Path) -> dict:
    package, repo = safe_path(package), safe_path(repo)
    frozen = frozen_files(package)
    m = json.loads((package / "submission.json").read_text(encoding="utf-8-sig"))
    require(m.get("id") == CID and m.get("solver") == "idealistichacker", "Submission identity mismatch")
    source = validate_source(package, repo, m)
    lock = validate_config(package / "lean4")
    names = theorem_names(m)
    inventory = validate_lean(package / "lean4", names)
    require(frozen_files(package) == frozen, "Frozen package changed during preflight")
    return {"source": source, "lock": lock, "theorems": inventory, "files": frozen}


def reproduce(package: Path, repo: Path, lake: str, skip_update: bool) -> dict:
    global LAKE_BIN
    package, repo = safe_path(package), safe_path(repo)
    with phase("preflight.before"):
        before = preflight(package, repo)
    lean = package / "lean4"
    dependencies = None
    try:
        if skip_update:
            with phase("dependencies.before"):
                dependencies = materialized_dependencies(lean, before["lock"])
        report = {"id": CID, "source": before["source"], "theorems": before["theorems"],
                  "regression": regression(), "skip_update": skip_update}
        executable = shutil.which(lake)
        require(executable is not None, "Local Lake executable not found")
        lake_path = safe_path(Path(executable))
        require(not (lake_path.parent.name == "bin" and lake_path.parent.parent.name == ".elan"),
                "Use installed toolchain Lake, not an auto-installing elan shim")
        LAKE_BIN = lake_path.parent
        with phase("lake.version"):
            version = run([str(lake_path), "--version"], lean).decode("utf-8")
        require(re.fullmatch(r"Lake version 5\.0\.0-src(?:\+[0-9a-f]+)? \(Lean version 4\.33\.1\)\s*", version) is not None,
                "Exact Lake/Lean release mismatch")
        if not skip_update:
            # Source/config/lock are validated before any explicitly requested update.
            with phase("lake.update"):
                run([str(lake_path), "update"], lean, 900)
        with phase("preflight.before_cleanup"):
            require(preflight(package, repo) == before, "Frozen inputs changed before project cache cleanup")
        if dependencies is None:
            dependencies = materialized_dependencies(lean, before["lock"])
        with phase("lean.version"):
            version = run([str(lake_path), "--offline", "env", "lean", "--version"], lean).decode("utf-8")
        require(re.search(r"\bversion\s+4\.33\.1(?=,|\s|\)|$)", version) is not None, "Exact Lean version mismatch")
        with phase("own_build.cleanup"):
            clean_project_build(lean)
        print("[RUN] Clean project Main build (offline, warnings are errors)", flush=True)
        with phase("own_build.Main"):
            run([str(lake_path), "--offline", "--wfail", "build", "Main"], lean, 900, show_output=True)
        for module in (*MODULES, "Main"):
            print("[RUN] Source replay: " + module, flush=True)
            with phase("source.replay." + module):
                run([str(lake_path), "--offline", "env", "lean", "-DwarningAsError=true", module + ".lean"], lean, 900, show_output=True)
        print("[RUN] Exact 76-theorem Check axiom audit", flush=True)
        with phase("source.Check76"):
            output = run([str(lake_path), "--offline", "env", "lean", "-DwarningAsError=true", "Check.lean"], lean, 900, show_output=True).decode("utf-8")
        report["axioms"] = audit_axioms(output, before["theorems"]["names"])
        report["types"] = audit_theorem_types(output, before["theorems"]["names"])
        report["build"] = "clean own-project Main + four mathematical modules/Main source replay; warningAsError"
    finally:
        with phase("preflight.after"):
            require(preflight(package, repo) == before, "Frozen authored files/manifest/source changed during reproduction")
        if dependencies is not None:
            with phase("dependencies.after"):
                require(materialized_dependencies(lean, before["lock"]) == dependencies, "Exact dependency state changed during reproduction")
    check_deadline()
    report["status"] = "PASS"
    report["timings"] = list(PROFILE_RECORDS)
    report["dependencies"] = dependencies
    report["windows_linktext_exception"] = {
        "scope": "Only three fixed inert Git-link blobs as exact ordinary Windows files (two Mathlib benchmarks, one batteries document); never execute these scripts; real links remain BLOCKED, including on Linux",
        "blobs": {name: {path.decode(): oid.decode() for path, oid in entries.items()}
                  for name, entries in WINDOWS_LINKTEXT.items()},
    }
    report["frozen_files"] = before["files"]
    report["boundaries"] = "Local reproduction only; no final review, PDF recompile, full dependency clean or empty-machine bootstrap"
    return report


def main() -> int:
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="backslashreplace")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", required=True)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--skip-update", action="store_true", help="Offline exact dependency audit; never update/fetch/cache-download")
    parser.add_argument("--preflight-only", action="store_true", help="Static source/config/inventory checks only; no Lake execution or dependency preparation")
    parser.add_argument("--timeout-seconds", type=int, default=285, help="Total subprocess wall-clock budget (default 285s for coordinator 300s limit)")
    args = parser.parse_args()
    started = time.monotonic_ns()
    global DEADLINE, PROFILE_RECORDS
    PROFILE_RECORDS = []
    DEADLINE = time.monotonic() + args.timeout_seconds
    try:
        require(args.timeout_seconds > 0, "Timeout must be positive")
        package = Path(__file__).absolute().parent
        if args.preflight_only:
            report = preflight(package, args.repo)
            report["status"] = "PREFLIGHT_ONLY"
            report["boundaries"] = "No physical dependency verification, Lean execution, PDF rebuild or final review"
        else:
            report = reproduce(package, args.repo, args.lake, args.skip_update)
        report["duration_ms"] = (time.monotonic_ns() - started) // 1_000_000
        print(json.dumps(report, ensure_ascii=True, indent=2))
        return 0
    except (ReproductionError, OSError, ValueError, subprocess.SubprocessError) as exc:
        print("BLOCKED: " + str(exc), file=sys.stderr, flush=True)
        print("duration_ms: " + str((time.monotonic_ns() - started) // 1_000_000), file=sys.stderr, flush=True)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
