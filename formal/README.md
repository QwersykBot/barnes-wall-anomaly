# Lattice VOA bridge checks

This directory contains a pinned dependency audit, a concrete rank-128 even
positive lattice, and generic bridge lemmas toward the specific KRR Barnes–Wall
lifts in sections 4.2–4.3 of the accompanying proof. The KRR matrix actions,
prescribed quaternion lifts and anomaly theorem are not yet formalized.

The dependency-only audit passed in
[run 45848409773](https://github.com/QwersykBot/barnes-wall-anomaly/actions/runs/45848409773),
at commit 338b74f5c5eeb02fcd0bd889f63f4cc1f5a77103. That result predates the
local bridge modules. The first transport candidate failed compilation because
an upstream type name was ambiguous; the binders now explicitly name
`VOA.IntegralLattice`. `BlockPhase`, `IntegerPhase` and `Lattice128` have passed
separate local checks using the pinned Lean kernel, with only the standard
axioms listed below. The public workflow checks all five local modules together
in a separate second stage; each run's result applies to its exact source commit.
The local checks do not establish that the combined transport stage has passed.

The audited dependency is [LeanVOA](https://github.com/Fedor-Popov/Lean_VOA)
at commit faedf8eb9e3fe275d3ac09e645aac694e496e965, by Fedor K. Popov
and contributors, released under Apache 2.0. Its exact manifest pins Mathlib
b63f6e8a68d220e3b3bc4f3792bb53650d375f24 and Lean 4.35.0-rc3.
The upstream source is downloaded at execution time and left unchanged.

The local `CocycleTransport.lean`, `LatticeComposition.lean` and `Lattice128.lean`
modules are released under Apache 2.0, with the upstream notice retained for the adapted
automorphism wrapper. The license is included in `LICENSE-Apache-2.0.txt`.
Additions and generalizations are identified in the source. `BlockPhase.lean`
and `IntegerPhase.lean` use the repository's MIT license.

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
second independent proof kernel. The local additions were generated and
reviewed by AI agents; no independent human review is claimed.

## Concrete coordinate lattice

`BarnesWall/Lattice128.lean` defines the carrier literally as `Fin 128 → ℤ`,
with its standard ordered basis. For binary supports Iᵢ and
tᵢ = ⌈(7 − |Iᵢ|)/2⌉, the integer matrix has entries
Bᵢⱼ = 2ᵗⁱ when Iⱼ ⊆ Iᵢ and zero otherwise. The Cartesian row basis is B/4.
A powerset count proves B Bᵀ = 16 G, including an explicit proof that the
integer Gram exponents are nonnegative. Lower triangularity gives a nonzero
determinant, and a sum of squares proves positive definiteness. The prescribed
half-Gram matrix satisfies H + Hᵀ = G and proves evenness. The rank is 128.

The identification with KRR's tensor expression is documented in
[Lattice128-notes.md](Lattice128-notes.md); Lean checks the explicit coordinate
construction and its properties, not a parsed version of the paper's tensor
formula. Unimodularity, minimum norm and the particular KRR isometries are
outside this increment.

## Generic bridge lemmas

`BarnesWall/BlockPhase.lean` proves the canonical quadratic phase composition
identity over `ZMod 2`. Its hypotheses say that H vanishes within each block,
that R and S preserve the blocks, and that they preserve H + Hᵀ. The proof
derives both symmetry and zero diagonal of the composition defect, then proves
that its quadratic expression vanishes. The second phase is evaluated at vR,
as required for row vectors acting from the right.

`BarnesWall/IntegerPhase.lean` defines the same strict-lower exponent over ℤ
and the actual sign (−1) raised to that integer exponent in a field, including
ℂ. It proves the explicit-cocycle identity from an integral isometry of
H + Hᵀ. It then derives sign composition from `BlockPhase` when H is even
within blocks and R and S have zero entries between blocks. Both conclusions
are proved; neither desired phase equation is an assumption.

`BarnesWall/CocycleTransport.lean` imports only the audited upstream target.
Given an integral bilinear form H whose symmetrization is the lattice form,
it constructs one global change of cocycle and proves the exact transport
identity. The same change is used for every isometry and phase.

The module transports a supplied explicit-cocycle phase identity to the
upstream convention. It also packages an integral isometry equivalence and
a normalized, nonzero compatible phase as a conformal automorphism of the
full lattice VOA. Integral surjectivity is supplied by the equivalence;
vacuum, all vertex products and the conformal vector are preserved.

`BarnesWall/LatticeComposition.lean` proves composition for the chosen-basis,
frame and oscillator matrices, using the proved positive-definite frame
invertibility. It then proves composition on every state of the full lattice
module and shows that the global cocycle change preserves a supplied phase
composition equation. In right-action notation, the lift of RS is the lift of
S after the lift of R.

`check_bridge.py` runs after the dependency audit. It compiles all five local
modules into the audited environment, prints the types and transitive axioms of
fifty-three new declarations, and checks source pins and unchanged inputs again.
Its parser applies the same standard-axiom restriction. The mathematical
assumptions remain visible in `LocalAxiomProbe.lean`'s type output.

The integer module supplies explicit-cocycle compatibility and phase composition
under its stated hypotheses. The VOA bridge accepts an actual integral isometry
and compatible phase; a coordinate adapter must still connect those interfaces.
The concrete KRR matrices must supply the integral isometry and block hypotheses.
These statements do not construct Q16 or establish unitarity of an automorphism.

## Mathematical work still required

LeanVOA's lattice basis is chosen noncomputably; its cocycle and oscillator
frame are not definitionally the KRR coordinate conventions. A later
formalization must establish the concrete integral isometries and inverses,
prove their block support and the half-Gram parity conditions, and instantiate
the generic transport with the coordinate lattice and prescribed phases.

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
