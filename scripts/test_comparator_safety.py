#!/usr/bin/env python3
"""Offline negative controls for the exact Palomar Comparator configuration."""
import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

def strict_config(value):
    if not isinstance(value, dict):
        raise ValueError("Comparator config must be a JSON object")
    expected = {
        "challenge_module": "Challenge",
        "solution_module": "Solution",
        "theorem_names": ["VaalerETKChallenge.signed_torus_box_discrepancy"],
        "definition_names": [],
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    }
    if value != expected:
        raise ValueError("Comparator config differs from the strict approved contract")
    return True

class ComparatorSecurityTest(unittest.TestCase):
    def test_shipped_config_is_strict(self):
        self.assertTrue(strict_config(json.loads((ROOT / "comparator.json").read_text())))

    def test_vulnerable_nine_hole_config_rejected(self):
        config = json.loads((ROOT / "comparator.json").read_text())
        config["definition_names"] = [
            "RML.Fourier.Vaaler.Internal.h3VaalerJHat",
            "RML.Fourier.Vaaler.Positive.yevorin_vaalerMainCoeff",
            "RML.Fourier.Vaaler.Positive.yevorin_vaalerErrorCoeff",
            "RML.Fourier.Vaaler.Positive.mainCoeff",
            "RML.Fourier.Vaaler.Positive.errorCoeff",
            "RML.Fourier.Vaaler.Positive.intervalMain",
            "RML.Fourier.Vaaler.Positive.intervalError",
            "RML.Fourier.Vaaler.Positive.torusArcLength",
            "RML.Fourier.Vaaler.Positive.torusArcIndicator",
        ]
        with self.assertRaises(ValueError):
            strict_config(config)

    def test_single_definition_hole_rejected(self):
        config = json.loads((ROOT / "comparator.json").read_text())
        config["definition_names"] = ["RML.Fourier.Vaaler.Positive.torusArcIndicator"]
        with self.assertRaises(ValueError):
            strict_config(config)

    def test_missing_definition_field_allowed_only_as_explicit_strict_contract(self):
        config = json.loads((ROOT / "comparator.json").read_text())
        del config["definition_names"]
        with self.assertRaises(ValueError):
            strict_config(config)

    def test_extra_unknown_configuration_rejected(self):
        config = json.loads((ROOT / "comparator.json").read_text())
        config["enable_nanoda"] = False
        with self.assertRaises(ValueError):
            strict_config(config)

if __name__ == "__main__":
    unittest.main()
