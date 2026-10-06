"""Negative controls for the published compiled-inventory validator."""
import copy
import json
from pathlib import Path
import unittest
from verify import validate_inventory


class InventoryValidation(unittest.TestCase):
    def setUp(self):
        self.expected = json.loads((Path(__file__).parent / "verification/compiled-inventory.json").read_text())
        self.actual = copy.deepcopy(self.expected)

    def test_exact_inventory_and_reordered_axioms(self):
        for row in self.actual["declarations"]:
            row["axioms"].reverse()
        self.actual["declarations"].reverse()
        validate_inventory(self.actual, self.expected)

    def reject(self):
        with self.assertRaises(ValueError):
            validate_inventory(self.actual, self.expected)

    def test_forbidden_axiom(self):
        self.actual["declarations"][0]["axioms"].append("sorryAx")
        self.reject()

    def test_custom_axiom(self):
        self.actual["declarations"][0]["kind"] = "axiom"
        self.reject()

    def test_missing_declaration_with_matching_count(self):
        self.actual["declarations"].pop()
        self.actual["declaration_count"] -= 1
        self.reject()

    def test_duplicate_declaration_with_matching_count(self):
        self.actual["declarations"].append(self.actual["declarations"][0])
        self.actual["declaration_count"] += 1
        self.reject()

    def test_unexpected_module(self):
        self.actual["declarations"][0]["module"] = "Unexpected"
        self.reject()

    def test_changed_theorem_type(self):
        self.actual["declarations"][0]["type"] = "True"
        self.reject()

    def test_missing_authored_module(self):
        self.actual["declarations"] = [r for r in self.actual["declarations"] if r["module"] != "Geometry"]
        self.actual["declaration_count"] = len(self.actual["declarations"])
        self.reject()


if __name__ == "__main__":
    unittest.main()
