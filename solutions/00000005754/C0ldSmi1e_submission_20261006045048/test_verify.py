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

    def test_wrong_module(self):
        self.actual[0]["module"] = "Unreviewed"
        self.reject()

    def test_changed_type(self):
        self.actual[0]["type"] = "True"
        self.reject()

    def test_changed_direct_dependency(self):
        self.actual[0]["direct_constants"].append("Unreviewed.dependency")
        self.reject()

    def test_duplicate_axiom_is_rejected_not_hidden(self):
        row = next(row for row in self.actual if row["transitive_axioms"])
        row["transitive_axioms"].append(row["transitive_axioms"][0])
        self.reject()

    def test_missing_type(self):
        del self.actual[0]["type"]
        self.reject()

    def test_forbidden_source_tokens(self):
        for token in ["sorry", "sorryAx", "admit", "axiom", "unsafe", "native_decide",
                      "implemented_by", "extern", "run_cmd", "elab", "macro", "initialize"]:
            with self.subTest(token=token), self.assertRaises(ValueError):
                verify.scan_source("def rejected := " + token)
        verify.scan_source((BASE / "lean/Counterexample.lean").read_text())

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
        with tempfile.TemporaryDirectory(prefix="tlmc5754-source-control-") as work:
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
        with tempfile.TemporaryDirectory(prefix="tlmc5754-record-control-") as work:
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
        with tempfile.TemporaryDirectory(prefix="tlmc5754-launch-control-") as work:
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
    for label, source, diagnostic in fixtures:
        dest = out / label
        project = dest / "fresh-project"
        (project / ".lake/packages").mkdir(parents=True)
        (project / "logs").mkdir()
        for name in ["lakefile.toml", "lake-manifest.json", "lean-toolchain", "Audit.lean"]:
            shutil.copyfile(BASE / "lean" / name, project / name)
        (project / "Counterexample.lean").write_text(source)
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
        if label == "sorry-proof":
            strict_rejected = False
            try:
                recorder.run("strict-replay-fixture", [args.lake, "env", "lean",
                                                       "-DwarningAsError=true", "Counterexample.lean"])
            except RuntimeError:
                record = recorder.records[-1]
                strict_rejected = record["exit_code"] != 0 and "declaration uses 'sorry'" in record["stdout"] + record["stderr"]
            if not strict_rejected:
                raise RuntimeError("Strict replay did not reject sorry fixture")
        result = {"control": label, "expected_rejection": diagnostic, "result": "PASS",
                  "source": source, "records": recorder.records}
        verify.write_json(dest / "result.json", result)
        results.append(result)
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiled-controls", action="store_true")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--dependency-root", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix="tlmc5754-controls-"))
    if args.output:
        out.mkdir(parents=True, exist_ok=False)
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
        report["result"] = "PASS"
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
