# Lattice VOA bridge checks

This directory contains a pinned dependency audit, a concrete rank-128 even
positive lattice, concrete integral quaternion matrices, and canonical full-state
lifts toward sections 4.2–4.3 of the accompanying proof. A faithful quaternion
action and equality of its central lift with the prescribed lattice involution
are included as integration candidates. The anomaly theorem is separate work.

The complete five-module baseline passed in
[run 45854804934](https://github.com/QwersykBot/barnes-wall-anomaly/actions/runs/45854804934),
at commit 644efcb33a7ca3e75929b71035fe7cf5a89bf373: all 53 requested local
declarations had only the standard axioms listed below. That run includes
`BlockPhase`, `IntegerPhase`, `Lattice128`, `CocycleTransport` and
`LatticeComposition`.

The latest completed integration,
[run 45859088010](https://github.com/QwersykBot/barnes-wall-anomaly/actions/runs/45859088010)
at commit 26559d56bfec5b55b094756e6999ca7d69bf9e09, passed the upstream audit
including Jacobi and compiled the first ten local modules through
`CanonicalFaithfulness`. It then failed on a multiline proof-term layout in
`KRRCanonical`, before the action modules or combined local axiom probe ran.
This increment repairs that layout and removes four reported unused arguments
or section instances; the mathematical content is unchanged.

`KRRQ16` has passed a separate local kernel check and twenty standard-axiom
reports. `QuaternionLift` has likewise passed its local check and seven reports.
`KRRBlocks` and `KRRPauli` also passed separate local kernel and axiom checks.
The action and two central-comparison modules remain source-reviewed candidates.
The public workflow now checks fifteen modules in a second stage; each result
applies to its exact source commit. Earlier runs do not certify the additions
or the latest repairs.

The audited dependency is [LeanVOA](https://github.com/Fedor-Popov/Lean_VOA)
at commit faedf8eb9e3fe275d3ac09e645aac694e496e965, by Fedor K. Popov
and contributors, released under Apache 2.0. Its exact manifest pins Mathlib
b63f6e8a68d220e3b3bc4f3792bb53650d375f24 and Lean 4.35.0-rc3.
The upstream source is downloaded at execution time and left unchanged.

The local modules use Apache 2.0, except `BlockPhase.lean`,
`IntegerPhase.lean` and `QuaternionLift.lean`, which use the repository's MIT
license. The upstream notice is retained for the adapted automorphism wrapper.
The Apache license
is included in `LICENSE-Apache-2.0.txt`; additions and generalizations are
identified in the source.

## What the dependency check establishes

The script verifies the official Lean distribution hash, obtains the exact
upstream source and nine dependency revisions, restores the official Mathlib
master cache for the target's imports, and builds VOA.Moonshine.LatticeMorph
from source with the upstream Lake configuration.

The probe prints the transitive axioms of fifteen declarations covering the
full lattice VOA, its cocycle comparison, oscillator-map composition,
vertex-product preservation, conformal-vector preservation, and injectivity
and image of the general lattice map. It also checks the type and transitive
axioms of `VOA.VertexOperatorAlgebra.jacobi`, the all-integer mode-form Jacobi
identity. That theorem is already in the pinned target's import closure;
adding its explicit probe does not change the dependency sources.
The parser requires one report for
every requested declaration and allows only propext, Classical.choice and
Quot.sound. An unexpected axiom, missing report, build failure, changed pin
or changed tracked upstream source makes the check fail.

The ordinary Lean compiler and official Mathlib compiled cache are part of
the trust boundary. This does not rebuild Mathlib from source or run a
second independent proof kernel. The local additions were generated and
reviewed by AI agents; no independent human review is claimed.

The target's carrier contains every polynomial oscillator state and every
lattice charge, with no finite-state cutoff. The resulting VOA includes its
integer grading, finite-dimensional graded pieces, vertex-product truncation,
vacuum and creation laws, locality, Virasoro action and translation covariance.
The explicit Jacobi probe checks the corresponding mode identity. These
algebraic results do not provide a Hermitian form or prove unitarity,
rationality, holomorphicity, twisted modules or the orbifold theorem.

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

`BarnesWall/KRRQ16.lean` defines the additional generator g directly by integral
rows and proves `2g = (I + a)(X₄ + Z₄)`, where `a = X₆Z₆` and `b = Z₆X₅Z₅`.
Intertwining with an explicit Cartesian numerator proves full Gram preservation.
Pauli algebra and nonzero integer-scalar cancellation give
`g² = a`, `g⁴ = a² = b² = −I`, `bgbg = −I`, and `g⁸ = I`.
The actual integral inverses are `g⁷` and `−b`, and both matrices preserve
the concrete blocks. The proof also shows `−I ≠ I`. No rational inverse,
assumed quaternion relation, or enumeration of all matrix entries is used.
These matrix results do not yet construct an abstract group action on the VOA.

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

`BarnesWall/KRRCanonical.lean` specializes the coordinate equivalence to the
identity on the concrete rank-128 lattice, identifies the prescribed half-form,
and supplies its proved evenness, positivity and within-block evenness to the
generic lift. It exports full-state and conformal-automorphism composition,
as well as recovery of an actual matrix from equality of lifts. Its remaining
matrix premises are explicit isometry and block-support conditions.

`BarnesWall/QuaternionLift.lean` uses Mathlib's existing `QuaternionGroup 4`.
It constructs a homomorphism into any group from `A⁸ = 1`, `B² = A⁴`, and
`AB = BA⁻¹`, by descending powers through `ZMod 8` and checking all four
normal-form products. If `A⁴ ≠ 1`, it proves that the homomorphism is injective.
There is no assumed faithfulness premise.

`BarnesWall/KRRQuaternionAction.lean` supplies those relations using the
concrete canonical lifts, derives identity and powers from full-state
composition, and proves nontriviality of the central lift by recovering its
matrix. The ordinary action maps `a 1`, `xa 0`, `a 2` and `a 4` to the literal
canonical lifts of g, b, a and −I. Neither generator is inverted.

The order convention matters: `action (xa k) = lift(b) * lift(g)^k` corresponds
under anti-composition to the matrix word `g^k b`, not the standard matrix label
`b g^k`. The module does not identify this ordinary action elementwise with
the raw matrix-labelled anti-action. The central comparison is supplied separately
below.

`BarnesWall/CentralLift.lean` proves that the canonical full-state map for −I
is exactly upstream `thetaLat`. Its integer phase is one, the global cocycle
ratio is one by evenness under negation, and its oscillator map negates every
polynomial generator. Equality on the spanning elementary lattice states
gives equality on all states. Only positive definiteness is needed for the
linear-map comparison; the automorphism corollary retains the existing evenness,
Gram and integral-unit hypotheses.

`BarnesWall/KRRCentralLift.lean` specializes that comparison to the concrete
quaternion action: its `centralLift`, and hence the image of `a 4`, is exactly
`thetaAut` on this lattice VOA. Both comparison modules await combined CI.

`check_bridge.py` runs after the dependency audit. It compiles all fifteen local
modules into the audited environment, prints the types and transitive axioms of
159 local declarations, and checks source pins and unchanged inputs again.
It continues independent module checks after a source failure, skips affected
dependents, and fails before the axiom stage if any module failed or was skipped.
Its parser applies the same standard-axiom restriction. The mathematical
assumptions remain visible in `LocalAxiomProbe.lean`'s type output.

The integer module and coordinate adapter derive explicit-cocycle compatibility
and coherent lift composition under their stated matrix hypotheses. The block
and quaternion matrix modules supply concrete generator inputs. The action
candidate connects these to a faithful `QuaternionGroup 4` representation;
its combined check is pending. No module establishes unitarity of an automorphism.

## Mathematical work still required

LeanVOA's lattice basis is chosen noncomputably; its cocycle and oscillator
frame are not definitionally the KRR coordinate conventions. The concrete
specialization, quaternion action and central comparison must first pass the
combined gate.

The wrapper supplies conformal preservation and bijectivity from its explicit
hypotheses, and the charge-state argument supplies generic matrix faithfulness.
Literal common-Q8 generator images are stated in the candidate action, but
agreement with an independently formalized prescribed extraspecial-group
action remains to be established. The general group
cohomology, anomaly and orbifold arguments are not formalized by this increment.

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
