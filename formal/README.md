# Lattice VOA dependency audit

This directory prepares an execution gate for a possible formalization of the
specific KRR Barnes–Wall lifts in sections 4.2–4.3 of the accompanying proof.
It contains no formal proof of that lattice, those lifts, or the anomaly theorem.

The audited dependency is [LeanVOA](https://github.com/Fedor-Popov/Lean_VOA)
at commit faedf8eb9e3fe275d3ac09e645aac694e496e965, by Fedor K. Popov
and contributors, released under Apache 2.0. Its exact manifest pins Mathlib
b63f6e8a68d220e3b3bc4f3792bb53650d375f24 and Lean 4.35.0-rc3.
The upstream source is downloaded at execution time and left unchanged.

## What the check establishes

The script verifies the official Lean distribution hash, obtains the exact
upstream source and nine dependency revisions, restores the official Mathlib
master cache for the target's imports, and builds VOA.Moonshine.LatticeMorph
from source with the upstream Lake configuration.

The probe prints the transitive axioms of fourteen declarations covering the
full lattice VOA, its cocycle comparison, oscillator-map composition,
vertex-product preservation, conformal-vector preservation, and injectivity
and image of the general lattice map. The parser requires one report for
every requested declaration and allows only propext, Classical.choice and
Quot.sound. An unexpected axiom, missing report, build failure, changed pin
or changed tracked upstream source makes the check fail.

The ordinary Lean compiler and official Mathlib compiled cache are part of
the trust boundary. This does not rebuild Mathlib from source or run a
second independent proof kernel.

## Mathematical work still required

LeanVOA's lattice basis is chosen noncomputably; its cocycle and oscillator
frame are not definitionally the KRR coordinate conventions. A later
formalization must establish the concrete rank-128 even positive lattice,
its integral isometries and inverses, and one coherent basis/cocycle
transport for the prescribed phases.

The generic homomorphism theorem preserves vacuum and all vertex products.
Conformal preservation and bijectivity require additional results before
constructing an actual VOA automorphism. The exact Q16 relations,
faithfulness and agreement with the prescribed common Q8 must then be
proved with the correct right-action composition convention.

Passing this dependency audit alone establishes none of those specialized
claims, nor the anomaly, orbifold, unitarity or spectrum statements.

## Reproduction

On a Linux x86-64 machine with Python 3.11 or later, Git, curl, tar and zstd:

    python3 formal/audit_bridge.py /absolute/path/to/new/work-directory

Use a machine with at least 9 GiB free disk space and sufficient RAM for
the pinned target; the public CI job uses a standard Ubuntu runner and
has a 60-minute limit. The script requires a new work directory, keeps
the full runtime and dependency artifacts, and uses two Lean threads.
It does not install global tools, request user-supplied credentials, upload
caches or change account settings. The CI checkout uses the automatic
read-only GitHub token without persisting it; no token is passed to the
audit script.

The raw axiom output and JSON receipt are written to the supplied work
directory and printed in the job log. No build binaries are committed
or uploaded as CI artifacts.
