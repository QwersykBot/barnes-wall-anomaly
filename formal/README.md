# Lattice VOA bridge checks

This directory contains a pinned dependency audit and generic bridge lemmas
toward a formalization of the specific KRR Barnes–Wall lifts in sections 4.2–4.3
of the accompanying proof. It contains no formal proof of that concrete lattice,
those prescribed lifts, or the anomaly theorem.

The dependency-only audit passed in
[run 45848409773](https://github.com/QwersykBot/barnes-wall-anomaly/actions/runs/45848409773),
at commit 338b74f5c5eeb02fcd0bd889f63f4cc1f5a77103. That result predates the
new local bridge module. The workflow checks the local lemmas in a separate
second stage; each run's result applies to its exact source commit.

The audited dependency is [LeanVOA](https://github.com/Fedor-Popov/Lean_VOA)
at commit faedf8eb9e3fe275d3ac09e645aac694e496e965, by Fedor K. Popov
and contributors, released under Apache 2.0. Its exact manifest pins Mathlib
b63f6e8a68d220e3b3bc4f3792bb53650d375f24 and Lean 4.35.0-rc3.
The upstream source is downloaded at execution time and left unchanged.

The local `CocycleTransport.lean` module is released under Apache 2.0, with
the upstream notice retained for its adapted automorphism wrapper. The license
is included in `LICENSE-Apache-2.0.txt`. Its additions and generalizations are
identified in the source header.

## What the dependency check establishes

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

## Generic bridge lemmas

`BarnesWall/CocycleTransport.lean` imports only the audited upstream target.
Given an integral bilinear form H whose symmetrization is the lattice form,
it constructs one global change of cocycle and proves the exact transport
identity. The same change is used for every isometry and phase.

The module transports a supplied explicit-cocycle phase identity to the
upstream convention. It also packages an integral isometry equivalence and
a normalized, nonzero compatible phase as a conformal automorphism of the
full lattice VOA. Integral surjectivity is supplied by the equivalence;
vacuum, all vertex products and the conformal vector are preserved.

`check_bridge.py` runs after the dependency audit. It compiles the local source
into the audited environment, prints the types and transitive axioms of
fourteen new declarations, and checks source pins and unchanged inputs again.
Its parser applies the same standard-axiom restriction. The mathematical
assumptions remain visible in `LocalAxiomProbe.lean`'s type output.

These generic statements still take an actual isometry and its explicit phase
identity as inputs. They do not prove canonical phases compose, identify the
KRR lattice, construct Q16, or establish unitarity of an automorphism.

## Mathematical work still required

LeanVOA's lattice basis is chosen noncomputably; its cocycle and oscillator
frame are not definitionally the KRR coordinate conventions. A later
formalization must establish the concrete rank-128 even positive lattice,
its integral isometries and inverses, and instantiate the generic transport
with the prescribed half-Gram form and phases.

The new wrapper supplies conformal preservation and bijectivity from its
explicit hypotheses. The exact Q16 relations,
faithfulness and agreement with the prescribed common Q8 must then be
proved with the correct right-action composition convention.

Passing this dependency audit alone establishes none of those specialized
claims, nor the anomaly, orbifold, unitarity or spectrum statements.

## Reproduction

On a Linux x86-64 machine with Python 3.11 or later, Git, curl, tar and zstd:

    python3 formal/audit_bridge.py /absolute/path/to/new/work-directory
    python3 formal/check_bridge.py /absolute/path/to/new/work-directory

Use a machine with at least 9 GiB free disk space and sufficient RAM for
the pinned target; the public CI job uses a standard Ubuntu runner and
has a 60-minute limit. The script requires a new work directory, keeps
the full runtime and dependency artifacts, and uses two Lean threads.
It does not install global tools, request user-supplied credentials, upload
caches or change account settings. The CI checkout uses the automatic
read-only GitHub token without persisting it; no token is passed to the
audit script.

Each stage writes its raw axiom output and JSON receipt to the supplied work
directory and prints them in the job log. No build binaries are committed
or uploaded as CI artifacts.
