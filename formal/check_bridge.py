#!/usr/bin/env python3
"""Check local bridge lemmas after the pinned dependency audit has passed."""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import shutil
import sys

from audit_bridge import (
    MATHLIB_REV, SOURCE_REV, TARGET, TOOLCHAIN, TOOLCHAIN_SHA256,
    run, sha256, verify_axioms, verify_sources,
)

HERE = Path(__file__).resolve().parent
MODULES = (
    "BarnesWall.BlockPhase",
    "BarnesWall.IntegerPhase",
    "BarnesWall.Lattice128",
    "BarnesWall.KRRBlocks",
    "BarnesWall.KRRPauli",
    "BarnesWall.KRRQ16",
    "BarnesWall.CocycleTransport",
    "BarnesWall.LatticeComposition",
    "BarnesWall.CanonicalLift",
    "BarnesWall.CanonicalFaithfulness",
    "BarnesWall.KRRCanonical",
    "BarnesWall.QuaternionLift",
    "BarnesWall.KRRQuaternionAction",
)
UPSTREAM_IMPORTS = {TARGET, "VOA.Foundations.Lattices", "Lean.Elab.Tactic.Omega"}
PROBE = HERE / "LocalAxiomProbe.lean"


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python3 formal/check_bridge.py /completed/audit/work-directory")
    work = Path(sys.argv[1]).resolve()
    previous = json.loads((work / "bridge-audit.json").read_text())
    required = {
        "status": "dependency_bridge_audit_passed",
        "source_revision": SOURCE_REV,
        "mathlib_revision": MATHLIB_REV,
        "toolchain_sha256": TOOLCHAIN_SHA256,
        "target": TARGET,
    }
    if any(previous.get(key) != value for key, value in required.items()):
        raise RuntimeError("The preceding dependency audit does not match this source pin")
    source = work / "Lean_VOA"
    packages = json.loads((source / "lake-manifest.json").read_text())["packages"]
    env = os.environ.copy()
    for key in (
        "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "ELAN_TOOLCHAIN",
        "MATHLIB_CACHE_GET_URL", "MATHLIB_CACHE_DEBUG_USE_LEGACY",
        "MATHLIB_CACHE_BASE_URL", "MATHLIB_CACHE_FROM", "MATHLIB_CACHE_REPO_SCOPE",
    ):
        env.pop(key, None)
    env["PATH"] = str(work / TOOLCHAIN / "bin") + os.pathsep + env["PATH"]
    env["LEAN_NUM_THREADS"] = "2"
    env["MATHLIB_CACHE_DIR"] = str(work / "mathlib-cache")
    verify_sources(source, packages, env)

    inputs: dict[str, str] = {}
    cache_roots: set[str] = set()
    available: set[str] = set()
    for module in MODULES:
        relative = Path(module.replace(".", "/") + ".lean")
        origin = HERE / relative
        text = origin.read_text()
        for imported in re.findall(r"^import\s+([A-Za-z0-9_.]+)", text, re.MULTILINE):
            if imported.startswith("Mathlib."):
                cache_roots.add(imported)
            elif imported not in UPSTREAM_IMPORTS and imported not in available:
                raise RuntimeError(f"Unplanned import in {module}: {imported}")
        destination = source / relative
        if destination.exists():
            raise RuntimeError(f"Local module destination already exists: {module}")
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(origin, destination)
        inputs[module] = sha256(origin)
        available.add(module)
    if cache_roots:
        run(["lake", "exe", "cache", "get", "--cache-from=master", *sorted(cache_roots)],
            cwd=source, env=env)

    for module in MODULES:
        relative = Path(module.replace(".", "/"))
        output = source / ".lake" / "build" / "lib" / "lean" / relative.with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        run(["lake", "env", "lean", str(source / relative.with_suffix(".lean")),
             "-o", str(output)], cwd=source, env=env)

    probe_hash = sha256(PROBE)
    expected = re.findall(r"^#print axioms (\S+)$", PROBE.read_text(), re.MULTILINE)
    if not expected or len(set(expected)) != len(expected):
        raise RuntimeError("The local probe must request distinct declarations")
    if any(not name.startswith("BarnesWall.") for name in expected):
        raise RuntimeError("The local probe must inspect the new bridge declarations")
    probe_dest = source / "LocalAxiomProbe.lean"
    shutil.copyfile(PROBE, probe_dest)
    output = run(["lake", "env", "lean", str(probe_dest)], cwd=source, env=env, capture=True)
    print(output, flush=True)
    reports = verify_axioms(output, expected)
    (work / "local-axioms.txt").write_text(output)
    verify_sources(source, packages, env)
    if sha256(PROBE) != probe_hash or sha256(probe_dest) != probe_hash:
        raise RuntimeError("Local axiom probe changed during compilation")
    for module, expected_hash in inputs.items():
        relative = Path(module.replace(".", "/") + ".lean")
        if sha256(source / relative) != expected_hash or sha256(HERE / relative) != expected_hash:
            raise RuntimeError(f"Local source changed during compilation: {module}")
    receipt = {
        "status": "lattice_and_lift_lemmas_checked",
        "source_revision": SOURCE_REV,
        "mathlib_revision": MATHLIB_REV,
        "modules_sha256": inputs,
        "probe_sha256": probe_hash,
        "axioms": reports,
        "scope": "Concrete rank-128 even positive coordinate lattice, integral quaternion matrices, canonical phases, coherent full-state lifts and a faithful ordinary quaternion action with explicit generator images.",
        "concrete_coordinate_lattice_formalized": True,
        "krr_tensor_formula_identification_formalized": False,
        "krr_pauli_isometries_formalized": True,
        "krr_quaternion_matrix_relations_formalized": True,
        "canonical_matrix_lift_formalized": True,
        "generic_lift_faithfulness_formalized": True,
        "concrete_lattice_canonical_lifts_formalized": True,
        "canonical_q16_action_formalized": True,
        "canonical_q16_action_faithful": True,
        "prescribed_central_involution_identification_formalized": False,
        "krr_full_extraspecial_action_formalized": False,
        "barnes_wall_anomaly_theorem_formalized": False,
    }
    rendered = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    (work / "local-bridge-check.json").write_text(rendered)
    print(rendered, flush=True)


if __name__ == "__main__":
    main()
