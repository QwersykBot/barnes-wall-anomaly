# Lattice VOA bridge checks

This directory contains a pinned dependency audit, a concrete rank-128 even
positive lattice, the concrete KRR Pauli matrices, and generic bridge lemmas
toward the specific Barnes–Wall lifts in sections 4.2–4.3 of the accompanying
proof. The additional quaternion generator, its prescribed lift relations and
the anomaly theorem are not yet formalized.

The dependency-only audit passed in
[run 45848409773](https://github.com/QwersykBot/barnes-wall-anomaly/actions/runs/45848409773),
at commit 338b74f5c5eeb02fcd0bd889f63f4cc1f5a77103. That result predates the
local bridge modules. The first five modules then passed together in
[run 45854804934](https://github.com/QwersykBot/barnes-wall-anomaly/actions/runs/45854804934),
at commit 644efcb33a7ca3e75929b71035fe7cf5a89bf373: all 53 requested local
declarations had only the standard axioms listed below. That run includes
`BlockPhase`, `IntegerPhase`, `Lattice128`, `CocycleTransport` and
`LatticeComposition`. Three redundant trailing tactics reported by its linter
have been removed in this increment.

The next two concrete modules, `KRRBlocks` and `KRRPauli`, passed separate local
kernel and axiom checks. `CanonicalLift` and `CanonicalFaithfulness` are new
integration candidates. The public workflow now checks all nine modules in
a separate second stage; each run's result applies to its exact source commit.
The five-module result does not certify these four additions.

The audited dependency is [LeanVOA](https://github.com/Fedor-Popov/Lean_VOA)
at commit faedf8eb9e3fe275d3ac09e645aac694e496e965, by Fedor K. Popov
and contributors, released under Apache 2.0. Its exact manifest pins Mathlib
b63f6e8a68d220e3b3bc4f3792bb53650d375f24 and Lean 4.35.0-rc3.
The upstream source is downloaded at execution time and left unchanged.

The local modules use Apache 2.0, except `BlockPhase.lean` and
`IntegerPhase.lean`, which use the repository's MIT license. The upstream
notice is retained for the adapted automorphism wrapper. The Apache license
is included in `LICENSE-Apache-2.0.txt`; additions and generalizations are
identified in the source.

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
tᵢ = ⌈(7 − |Iᵢ|)/2⌉, the integer matrix has entry `B_ij = 2^(t_i)`
when Iⱼ ⊆ Iᵢ and zero otherwise. The Cartesian row basis is B/4.
A powerset count proves B Bᵀ = 16 G, including an explicit proof that the
integer Gram exponents are nonnegative. Lower triangularity gives a nonzero
determinant, and a sum of squares proves positive definiteness. The prescribed
half-Gram matrix satisfies H + Hᵀ = G and proves evenness. The rank is 128.

The identification with KRR's tensor expression is documented in
[Lattice128-notes.md](Lattice128-notes.md); Lean checks the explicit coordinate
construction and its properties, not a parsed version of the paper's tensor
formula. Unimodularity and minimum norm are outside this increment.

`BarnesWall/KRRBlocks.lean` fixes the actual block key `i.val % 16`, preserving
the four low numerical bits. Equal keys force the two binary supports to differ
in at most three positions. The resulting exponent bound proves that both G
and H have entries divisible by four within a block, hence the required evenness.
This is a structural argument, without enumerating index pairs.

`BarnesWall/KRRPauli.lean` defines KRR's exact integral X and Z rows. It proves
`X * B = B * cartX` and `Z * B = B * cartZ`, where the Cartesian matrices are
the bit-toggle permutation and diagonal sign. These identities prove full form
preservation, including pairings between different blocks. The integral
matrices square to one and are bundled with their actual integral inverses.
Numerical bits 6, 5 and 4 are KRR tensor positions 1, 2 and 3; their matrices
preserve the low-four-bit blocks.

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

`BarnesWall/CanonicalLift.lean` connects the integer phases to the VOA bridge
using an actual integral coordinate equivalence. It derives lattice isometry,
phase compatibility and a conformal automorphism from a matrix unit preserving
G and the half-Gram identity. Under the block hypotheses it proves composition
on all states and in `VOA.Aut`, with the correct reversed multiplication order.
The desired phase or lift composition equation is not an input.

`BarnesWall/CanonicalFaithfulness.lean` uses the upstream pure-charge action and
actual charge-coordinate projection to recover the lattice map from a full
state map with nonzero phases. The coordinate equivalence then recovers its
integer matrix. Thus the canonical full-state maps distinguish their matrices;
this does not by itself identify a concrete quaternion group representation.

`check_bridge.py` runs after the dependency audit. It compiles all nine local
modules into the audited environment, prints the types and transitive axioms of
ninety-seven local declarations, and checks source pins and unchanged inputs again.
Its parser applies the same standard-axiom restriction. The mathematical
assumptions remain visible in `LocalAxiomProbe.lean`'s type output.

The integer module and coordinate adapter derive explicit-cocycle compatibility
and coherent lift composition under their stated matrix hypotheses. The block
and Pauli modules supply concrete inputs for the source generators. These
statements do not construct Q16 or establish unitarity of an automorphism.

## Mathematical work still required

LeanVOA's lattice basis is chosen noncomputably; its cocycle and oscillator
frame are not definitionally the KRR coordinate conventions. A later
formalization must instantiate the generic transport with the concrete coordinate
lattice and prescribed phases, then add the integral quaternion generator,
its inverse and its full form isometry.

The wrapper supplies conformal preservation and bijectivity from its explicit
hypotheses, and the charge-state argument supplies generic matrix faithfulness.
The exact Q16 matrix and lift relations, the concrete group's faithful order,
and agreement with the prescribed common Q8 must still be proved with the
correct right-action convention.

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
