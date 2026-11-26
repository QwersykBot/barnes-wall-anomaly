#!/usr/bin/env python3
"""Build a pinned LeanVOA dependency target and check its transitive axiom reports."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

SOURCE_URL = "https://github.com/Fedor-Popov/Lean_VOA"
SOURCE_REV = "faedf8eb9e3fe275d3ac09e645aac694e496e965"
MATHLIB_REV = "b63f6e8a68d220e3b3bc4f3792bb53650d375f24"
TOOLCHAIN = "lean-4.35.0-rc3-linux"
TOOLCHAIN_URL = (
    "https://github.com/leanprover/lean4/releases/download/v4.35.0-rc3/"
    + TOOLCHAIN + ".tar.zst"
)
TOOLCHAIN_SHA256 = "1526de16c0496f16b46a168f26c990af4e3796505273c3342fec17d72d763997"
MANIFEST_SHA256 = "0c4fde4eaadf0b55a31704bcb6cfcf570084b6ac3b768d39c0e882a2c2e94ca0"
TARGET = "VOA.Moonshine.LatticeMorph"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
HERE = Path(__file__).resolve().parent
PROBE = HERE / "BridgeAxiomProbe.lean"


def sha256(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def run(args: list[str], *, cwd: Path, env: dict[str, str], capture=False) -> str:
    print("+", " ".join(map(str, args)), flush=True)
    result = subprocess.run(
        args, cwd=cwd, env=env, text=True, check=False, timeout=2700,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.STDOUT if capture else None,
    )
    if result.returncode:
        if capture:
            print(result.stdout, flush=True)
        result.check_returncode()
    return result.stdout or ""


def checkout(url: str, revision: str, dest: Path, env: dict[str, str]) -> None:
    dest.mkdir(parents=True)
    run(["git", "init", "--quiet"], cwd=dest, env=env)
    run(["git", "remote", "add", "origin", url], cwd=dest, env=env)
    run(["git", "fetch", "--quiet", "--depth=1", "origin", revision], cwd=dest, env=env)
    run(["git", "checkout", "--quiet", "--detach", "FETCH_HEAD"], cwd=dest, env=env)
    actual = run(["git", "rev-parse", "HEAD"], cwd=dest, env=env, capture=True).strip()
    if actual != revision:
        raise RuntimeError(f"Unexpected source revision: {url}: {actual}")


def import_closure(source: Path) -> tuple[list[str], list[str]]:
    """Select cache roots only; Lean/Lake remains responsible for actual imports."""
    seen: set[str] = set()
    external: set[str] = set()
    pending = [TARGET]
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        text = (source / (module.replace(".", "/") + ".lean")).read_text()
        for name in re.findall(r"^import\s+([A-Za-z0-9_.]+)", text, re.MULTILINE):
            if name.startswith("VOA."):
                pending.append(name)
            elif name.startswith("Mathlib."):
                external.add(name)
            else:
                raise RuntimeError(f"Unexpected import root: {module}: {name}")
    if (len(seen), len(external)) != (152, 92):
        raise RuntimeError(f"Pinned import inventory changed: {len(seen)}, {len(external)}")
    return sorted(seen), sorted(external)


def verify_axioms(output: str, expected: list[str]) -> dict[str, list[str]]:
    pattern = re.compile(
        r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]"
        r"|does not depend on any axioms)"
    )
    reports: dict[str, list[str]] = {}
    for match in pattern.finditer(output):
        name, raw = match.groups()
        if name in reports:
            raise RuntimeError(f"Duplicate axiom report: {name}")
        axioms = sorted(x.strip() for x in (raw or "").split(",") if x.strip())
        if not set(axioms) <= ALLOWED_AXIOMS:
            raise RuntimeError(f"Unexpected axioms: {name}: {axioms}")
        reports[name] = axioms
    if set(reports) != set(expected) or len(reports) != len(expected):
        raise RuntimeError(f"Missing or unexpected reports: expected {expected}; got {list(reports)}")
    return reports


def verify_sources(source: Path, packages: list[dict], env: dict[str, str]) -> None:
    revisions = [(source, SOURCE_REV)]
    revisions.extend(
        (source / ".lake" / "packages" / p["name"], p["rev"]) for p in packages
    )
    for directory, expected in revisions:
        actual = run(["git", "rev-parse", "HEAD"], cwd=directory, env=env, capture=True).strip()
        if actual != expected:
            raise RuntimeError(f"Source revision changed: {directory.name}")
        status = run(["git", "status", "--porcelain", "--untracked-files=no"],
                     cwd=directory, env=env, capture=True).strip()
        if status:
            raise RuntimeError(f"Tracked sources were modified: {directory.name}: {status}")


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python3 formal/audit_bridge.py /absolute/new/work-directory")
    work = Path(sys.argv[1]).resolve()
    if work.exists():
        raise RuntimeError("The work directory must be new")
    work.mkdir(parents=True)
    if shutil.disk_usage(work).free < 9 * 1024**3:
        raise RuntimeError("At least 9 GiB free disk space is required")
    started = time.monotonic()
    env = os.environ.copy()
    for key in (
        "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "ELAN_TOOLCHAIN",
        "MATHLIB_CACHE_GET_URL", "MATHLIB_CACHE_DEBUG_USE_LEGACY",
        "MATHLIB_CACHE_BASE_URL", "MATHLIB_CACHE_FROM", "MATHLIB_CACHE_REPO_SCOPE",
    ):
        env.pop(key, None)
    env["LEAN_NUM_THREADS"] = "2"
    env["MATHLIB_CACHE_DIR"] = str(work / "mathlib-cache")
    archive = work / (TOOLCHAIN + ".tar.zst")
    run(
        ["curl", "--fail", "--location", "--connect-timeout", "20", "--max-time", "300",
         "--output", str(archive), TOOLCHAIN_URL],
        cwd=work, env=env,
    )
    if sha256(archive) != TOOLCHAIN_SHA256:
        raise RuntimeError("Official Lean archive checksum mismatch")
    run(["tar", "--zstd", "-xf", str(archive), "-C", str(work)], cwd=work, env=env)
    archive.unlink()
    env["PATH"] = str(work / TOOLCHAIN / "bin") + os.pathsep + env["PATH"]
    version = run(["lean", "--version"], cwd=work, env=env, capture=True).strip()
    if "4.35.0-rc3" not in version or "470d5ce1400764999581fd26d5d72b00d990b0f4" not in version:
        raise RuntimeError(f"Unexpected Lean runtime: {version}")
    source = work / "Lean_VOA"
    checkout(SOURCE_URL, SOURCE_REV, source, env)
    manifest_path = source / "lake-manifest.json"
    if sha256(manifest_path) != MANIFEST_SHA256:
        raise RuntimeError("Pinned Lake manifest changed")
    manifest = json.loads(manifest_path.read_text())
    if len(manifest["packages"]) != 9:
        raise RuntimeError("Unexpected dependency count")
    for package in manifest["packages"]:
        if package["type"] != "git" or package["subDir"] is not None:
            raise RuntimeError("Unexpected dependency format")
        if not re.fullmatch(r"[A-Za-z0-9_]+", package["name"]):
            raise RuntimeError("Unexpected package name")
        if not package["url"].startswith("https://github.com/"):
            raise RuntimeError("Unexpected package host")
        checkout(package["url"], package["rev"],
                 source / ".lake" / "packages" / package["name"], env)
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    if mathlib["rev"] != MATHLIB_REV:
        raise RuntimeError("Unexpected Mathlib revision")
    local, external = import_closure(source)
    run(["lake", "exe", "cache", "get", "--cache-from=master", *external], cwd=source, env=env)
    run(["lake", "build", "+" + TARGET + ":olean"], cwd=source, env=env)
    verify_sources(source, manifest["packages"], env)
    probe_dest = source / "BridgeAxiomProbe.lean"
    shutil.copyfile(PROBE, probe_dest)
    expected = re.findall(r"^#print axioms (\S+)$", PROBE.read_text(), re.MULTILINE)
    if len(expected) != 14 or len(set(expected)) != 14:
        raise RuntimeError("Unexpected probe declaration inventory")
    output = run(["lake", "env", "lean", str(probe_dest)], cwd=source, env=env, capture=True)
    print(output, flush=True)
    (work / "axioms.txt").write_text(output)
    reports = verify_axioms(output, expected)
    verify_sources(source, manifest["packages"], env)
    receipt = {
        "status": "dependency_bridge_audit_passed",
        "source_url": SOURCE_URL, "source_revision": SOURCE_REV,
        "mathlib_revision": MATHLIB_REV, "lean_version": version,
        "toolchain_sha256": TOOLCHAIN_SHA256, "probe_sha256": sha256(PROBE),
        "target": TARGET, "local_source_modules": len(local),
        "external_cache_roots": len(external), "axioms": reports,
        "elapsed_seconds": round(time.monotonic() - started, 2),
        "scope": "Upstream generic lattice-VOA dependency declarations only.",
        "krr_lattice_or_lift_formalized": False,
        "barnes_wall_anomaly_theorem_formalized": False,
    }
    rendered = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    (work / "bridge-audit.json").write_text(rendered)
    print(rendered, flush=True)
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with Path(summary).open("a") as stream:
            stream.write("## Lattice-VOA dependency audit\n\n")
            stream.write("Built the pinned target and checked all 14 axiom reports.\n\n")
            stream.write("This check does not formalize the KRR lifts or the anomaly theorem.\n")


if __name__ == "__main__":
    main()
