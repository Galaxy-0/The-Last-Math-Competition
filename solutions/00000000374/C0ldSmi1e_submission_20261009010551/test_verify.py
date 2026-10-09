#!/usr/bin/env python3
"""Negative controls for the portable verifier; optional compiled Lean controls.

python3 test_verify.py
python3 test_verify.py --compiled-controls --lake /path/to/lake
    --dependency-root /path/to/pinned/packages --output /new/control-results
"""
import argparse
import copy
import io
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

import verify

BASE = Path(__file__).resolve().parent


class VerifierControls(unittest.TestCase):
    def setUp(self):
        self.expected = verify.load_json(BASE / "verification/compiled-inventory.json")
        self.actual = copy.deepcopy(self.expected)

    def reject(self):
        with self.assertRaises(ValueError):
            verify.validate_inventory(self.actual, self.expected)

    def test_reordering_preserves_meaning(self):
        self.actual.reverse()
        for row in self.actual:
            row["transitive_axioms"].reverse()
            row["direct_constants"].reverse()
        verify.validate_inventory(self.actual, self.expected)

    def test_sorry_axiom(self):
        self.actual[0]["transitive_axioms"].append("sorryAx")
        self.reject()

    def test_custom_transitive_axiom(self):
        self.actual[0]["transitive_axioms"].append("AssumedConclusion")
        self.reject()

    def test_authored_axiom(self):
        self.actual[0]["kind"] = "axiom"
        self.reject()

    def test_unsafe_declaration(self):
        self.actual[0]["unsafe"] = True
        self.reject()
        # A compiler-shaped name receives no wildcard exemption.
        for module in ["Counterexample", "HeightRoots"]:
            spoof = copy.deepcopy(self.expected[0])
            spoof.update(name="Spoof.match_1._cstage1", module=module,
                         unsafe=True, role="compiler_execution")
            with self.subTest(module=module), self.assertRaises(ValueError):
                verify.normalized_inventory(self.expected + [spoof])

    def test_false_like_unsafe_flag(self):
        self.actual[0]["unsafe"] = 0
        self.reject()

    def test_missing_generated_declaration(self):
        row = next((row for row in self.actual if "._proof_" in row["name"] or row["name"].startswith("_private.")), self.actual[0])
        self.actual.remove(row)
        self.reject()

    def test_extra_declaration(self):
        extra = copy.deepcopy(self.actual[0])
        extra["name"] = "OutsideExpectedNamespace.unreviewed"
        self.actual.append(extra)
        self.reject()

    def test_duplicate_replacing_declaration(self):
        self.actual[-1] = copy.deepcopy(self.actual[0])
        self.reject()

    def test_missing_helper_module(self):
        self.actual = [r for r in self.actual if r["module"] != "HeightRoots"]
        self.reject()

    def test_missing_main_module(self):
        self.actual = [r for r in self.actual if r["module"] != "Counterexample"]
        self.reject()

    def test_wrong_module(self):
        self.actual[0]["module"] = "Unreviewed"
        self.reject()

    def test_changed_type(self):
        self.actual[0]["type"] = "True"
        self.reject()
        self.actual = copy.deepcopy(self.expected)
        next(r for r in self.actual if r["unsafe"])["type"] = "Nat"
        self.reject()

    def test_changed_direct_dependency(self):
        self.actual[0]["direct_constants"].append("Unreviewed.dependency")
        self.reject()
        # Even if a tampered expected inventory were supplied too, a safe root
        # cannot bridge through an owned helper to an unsafe execution node.
        self.actual = copy.deepcopy(self.expected)
        safe = [row for row in self.actual if not row["unsafe"]]
        safe[0]["direct_constants"].append(safe[1]["name"])
        safe[1]["direct_constants"].append(sorted(verify.COMPILER_ARTIFACTS)[0])
        with self.assertRaisesRegex(ValueError, "Unsafe proof dependency"):
            verify.normalized_inventory(self.actual)
        self.actual = copy.deepcopy(self.expected)
        next(r for r in self.actual if r["unsafe"])["direct_constants"].append("Unreviewed.dependency")
        self.reject()

    def test_duplicate_axiom_is_rejected_not_hidden(self):
        row = next(row for row in self.actual if row["transitive_axioms"])
        row["transitive_axioms"].append(row["transitive_axioms"][0])
        self.reject()

    def test_missing_type(self):
        del self.actual[0]["type"]
        self.reject()
        roots = sorted(r["name"] for r in self.expected if not r["unsafe"])
        closure = {"root_names": roots, "reachable_constant_names": roots.copy(),
                   "reachable_constant_count": len(roots), "unsafe_count": 0,
                   "axioms": [], "edge_sources": ["types", "values_including_theorem_proofs"]}
        verify.validate_closure(closure, self.expected)
        for field, value in [("root_names", roots[:-1]), ("unsafe_count", 1),
                             ("edge_sources", ["types"]), ("axioms", ["sorryAx"])]:
            broken = {**closure, field: value}
            with self.subTest(field=field), self.assertRaises(ValueError):
                verify.validate_closure(broken, self.expected)

    def test_forbidden_source_tokens(self):
        for token in ["sorry", "sorryAx", "admit", "axiom", "unsafe", "native_decide",
                      "implemented_by", "extern", "run_cmd", "elab", "macro", "initialize"]:
            with self.subTest(token=token), self.assertRaises(ValueError):
                verify.scan_source("def rejected := " + token)
        for name in ["Counterexample.lean", "HeightRoots.lean"]:
            verify.scan_source((BASE / "lean" / name).read_text())

    def test_exact_dependency_manifest(self):
        pins = verify.load_json(BASE / "verification/pinned-dependencies.json")
        verify.validate_pins(pins, copy.deepcopy(pins))
        altered = copy.deepcopy(pins)
        altered["packages"][0]["rev"] = "0" * 40
        with self.assertRaises(ValueError):
            verify.validate_pins(pins, altered)
        altered = copy.deepcopy(pins)
        altered["packages"][-1] = copy.deepcopy(altered["packages"][0])
        with self.assertRaises(ValueError):
            verify.validate_pins(altered, altered)

    def test_frozen_source_tamper(self):
        with tempfile.TemporaryDirectory(prefix="tlmc374-source-control-") as work:
            root = Path(work)
            for name in verify.INPUT_FILES:
                (root / name).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(BASE / name, root / name)
            manifest = verify.load_json(BASE / "verification/source-manifest.json")
            verify.validate_inputs(root, manifest)
            with (root / "lean/Counterexample.lean").open("a") as file:
                file.write("\n-- unexpected alteration\n")
            with self.assertRaisesRegex(ValueError, "Frozen input identity mismatch"):
                verify.validate_inputs(root, manifest)

    def test_failed_subprocess_record_is_preserved(self):
        with tempfile.TemporaryDirectory(prefix="tlmc374-record-control-") as work:
            root = Path(work)
            recorder = verify.Recorder(root, root, os.environ.copy())
            with self.assertRaises(RuntimeError):
                recorder.run("intentional-failure", [sys.executable, "-I", "-c",
                             "import sys; print('actual output'); print('actual error', file=sys.stderr); sys.exit(7)"])
            record = verify.load_json(root / "intentional-failure/command.json")
            self.assertEqual(record["exit_code"], 7)
            self.assertEqual((root / "intentional-failure/stdout.txt").read_text(), "actual output\n")
            self.assertEqual((root / "intentional-failure/stderr.txt").read_text(), "actual error\n")

    def test_failed_launch_record_is_preserved(self):
        with tempfile.TemporaryDirectory(prefix="tlmc374-launch-control-") as work:
            root = Path(work)
            recorder = verify.Recorder(root, root, os.environ.copy())
            with self.assertRaises(RuntimeError):
                recorder.run("missing-executable", [str(root / "absent")])
            record = verify.load_json(root / "missing-executable/command.json")
            self.assertIsNone(record["exit_code"])
            self.assertTrue(record["launch_error"])


def compiled_controls(args, out):
    pins = verify.load_json(BASE / "verification/pinned-dependencies.json")["packages"]
    dependency_root = (args.dependency_root or BASE / "lean/.lake/packages").resolve(strict=True)
    fixtures = [
        ("custom-axiom", "axiom OutsideNamespace.assumed : False\n", "Authored axiom declaration"),
        ("unsafe-definition", "unsafe def OutsideNamespace.unchecked : Nat := 1\n", "Unsafe authored declaration"),
        ("sorry-proof", "theorem OutsideNamespace.unsound : False := by sorry\n", "Forbidden transitive axiom sorryAx"),
    ]
    results = []
    pin_project = out / "dependency-check-project"
    (pin_project / ".lake/packages").mkdir(parents=True)
    for pin in pins:
        (pin_project / ".lake/packages" / pin["name"]).symlink_to(
            (dependency_root / pin["name"]).resolve(strict=True), target_is_directory=True)
    pin_env = {k: v for k, v in os.environ.items()
               if not k.startswith(("LEAN_", "LAKE_", "PYTHON")) and k != "ELAN_TOOLCHAIN"}
    pin_env["GIT_OPTIONAL_LOCKS"] = "0"
    pin_recorder = verify.Recorder(out, pin_project, pin_env)
    verify.check_pins("controls-before", pins, pin_project, pin_recorder)
    fixtures = [(label + "-" + module, source, diagnostic, module)
                for label, source, diagnostic in fixtures
                for module in ["HeightRoots", "Counterexample"]]
    for label, source, diagnostic, target_module in fixtures:
        dest = out / label
        project = dest / "fresh-project"
        (project / ".lake/packages").mkdir(parents=True)
        (project / "logs").mkdir()
        for name in ["lakefile.toml", "lake-manifest.json", "lean-toolchain", "Audit.lean"]:
            shutil.copyfile(BASE / "lean" / name, project / name)
        (project / "HeightRoots.lean").write_text("theorem HelperControl.ok : True := by trivial\n" + (source if target_module == "HeightRoots" else ""))
        (project / "Counterexample.lean").write_text("import HeightRoots\ntheorem MainControl.ok : True := by trivial\n" + (source if target_module == "Counterexample" else ""))
        for pin in pins:
            (project / ".lake/packages" / pin["name"]).symlink_to(
                (dependency_root / pin["name"]).resolve(strict=True), target_is_directory=True)
        env = {k: v for k, v in os.environ.items()
               if not k.startswith(("LEAN_", "LAKE_", "PYTHON")) and k != "ELAN_TOOLCHAIN"}
        env["GIT_OPTIONAL_LOCKS"] = "0"
        recorder = verify.Recorder(dest, project, env)
        recorder.run("compile-fixture", [args.lake, "build"])
        rejected = False
        try:
            recorder.run("audit-fixture", [args.lake, "env", "lean", "-DwarningAsError=true", "Audit.lean"])
        except RuntimeError:
            record = recorder.records[-1]
            rejected = record["exit_code"] != 0 and diagnostic in record["stdout"] + record["stderr"]
        if not rejected:
            raise RuntimeError("Compiled negative control did not produce expected rejection: " + label)
        if label.startswith("sorry-proof-"):
            strict_rejected = False
            try:
                recorder.run("strict-replay-fixture", [args.lake, "env", "lean",
                                                       "-DwarningAsError=true", target_module + ".lean"])
            except RuntimeError:
                record = recorder.records[-1]
                strict_rejected = record["exit_code"] != 0 and "declaration uses 'sorry'" in record["stdout"] + record["stderr"]
            if not strict_rejected:
                raise RuntimeError("Strict replay did not reject sorry fixture")
        result = {"control": label, "expected_rejection": diagnostic, "result": "PASS",
                  "source": source, "target_module": target_module, "records": recorder.records}
        verify.write_json(dest / "result.json", result)
        results.append(result)
    verify.check_pins("controls-after", pins, pin_project, pin_recorder)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiled-controls", action="store_true")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--dependency-root", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix="tlmc374-controls-"))
    if args.output:
        out.mkdir(parents=True, exist_ok=False)
    frozen = verify.load_json(BASE / "verification/source-manifest.json")
    frozen_sha = verify.sha(BASE / "verification/source-manifest.json")
    input_hashes = verify.validate_inputs(BASE, frozen)
    stream = io.StringIO()
    result = unittest.TextTestRunner(stream=stream, verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(VerifierControls))
    (out / "unit-tests.txt").write_text(stream.getvalue())
    print(stream.getvalue())
    report = {"result": "FAIL", "unit_test_count": result.testsRun, "unit_tests_pass": result.wasSuccessful(),
              "compiled_controls": [], "errors": []}
    try:
        if not result.wasSuccessful():
            raise RuntimeError("Unit controls failed")
        if args.compiled_controls:
            report["compiled_controls"] = compiled_controls(args, out)
        verify.validate_inputs(BASE, frozen)
        if verify.sha(BASE / "verification/source-manifest.json") != frozen_sha:
            raise ValueError("Control input manifest changed during execution")
        report.update(result="PASS", input_sha256=input_hashes, inputs_unchanged=True,
                      pins_clean_before_and_after=bool(args.compiled_controls))
    except Exception as error:
        report["errors"].append(type(error).__name__ + ": " + str(error))
    verify.write_json(out / "result.json", report)
    verify.write_json(out / "SHA256SUMS.json", {
        str(p.relative_to(out)): verify.sha(p) for p in out.rglob("*")
        if p.is_file() and ".lake" not in p.relative_to(out).parts and p.name != "SHA256SUMS.json"})
    print(report["result"] + ": negative controls; records: " + str(out))
    return 0 if report["result"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
