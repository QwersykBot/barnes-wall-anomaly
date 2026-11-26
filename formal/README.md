# Lattice VOA bridge checks

This directory contains a pinned dependency audit, a concrete rank-128 even
positive lattice, concrete integral quaternion matrices, and canonical full-state
lifts toward sections 4.2–4.3 of the accompanying proof. Its checked quaternion
action is faithful, and its central lift equals the prescribed lattice involution.
A separate Boolean-cubic factorization lemma supplies one combinatorial
ingredient. The anomaly theorem is separate work.

The latest complete public integration passed nineteen modules in
[run 45866546569](https://github.com/QwersykBot/barnes-wall-anomaly/actions/runs/45866546569)
at commit 2677b16b8f547fd09eb5a2345ce6a994e59050b7. All 15 upstream reports,
including Jacobi, and all 187 requested local declaration reports contained
only the standard axioms listed below. The local modules compiled without
warnings or errors; their source hashes and the probe hash match the public
commit. This includes the faithful quaternion action, its exact central
comparison and `BooleanCubic`, as well as arbitrary small-support composition
and the concrete full-state Pauli relations in `KRRPauliLift`.

The next candidate adds `PauliPresentation` and `KRRPauliAction`: twenty-one
modules and 204 local declaration reports, adding nine generic and eight
concrete reports. The repaired generic presentation passed a separate local
compile and axiom audit. The full twenty-one-module public integration and
concrete adapter check are still pending; the nineteen-module run does not
certify these additions. See [PauliPresentation-notes.md](PauliPresentation-notes.md)
for the exact source and verification provenance.

The audited dependency is [LeanVOA](https://github.com/Fedor-Popov/Lean_VOA)
at commit faedf8eb9e3fe275d3ac09e645aac694e496e965, by Fedor K. Popov
and contributors, released under Apache 2.0. Its exact manifest pins Mathlib
b63f6e8a68d220e3b3bc4f3792bb53650d375f24 and Lean 4.35.0-rc3.
The upstream source is downloaded at execution time and left unchanged.

The local modules use Apache 2.0, except `BlockPhase.lean`,
`IntegerPhase.lean`, `QuaternionLift.lean` and `BooleanCubic.lean`, which use the repository's MIT
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

`BarnesWall/KRRSupport.lean` generalizes the block key to the support outside
any chosen set of numerical bit positions. With at most three chosen positions,
the same prescribed H is even within every block. The literal X and Z matrices
preserve these blocks whenever their active position is chosen. The argument
keeps the ordered basis and global H unchanged. See
[KRRSupport-notes.md](KRRSupport-notes.md) for its precise scope and local check.

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

`BarnesWall/KRRSupportedLift.lean` specializes the generic full-state and
automorphism composition theorems to those arbitrary small-support blocks.
It retains the same coordinates and cocycle transport, explicit isometry
premises, and reversed multiplication order. This permits local arguments
at different positions without asserting global multiplication for all words.

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
`thetaAut` on this lattice VOA. Both comparison modules passed the complete
integration above.

`BarnesWall/KRRPauliLift.lean` defines the literal canonical X and Z lifts at
all seven positions. It derives their squares and commutators, including the
same-position sign given by the actual `thetaAut`, from the checked matrix
relations and one-/two-position composition. It proves that theta has order
two and states the literal reversed-word expressions for the common Q8
generators. These relations passed the nineteen-module public integration.
The module itself supplies relations, not a full-group construction. Its
earlier source-review record is [KRRPauliLift-notes.md](KRRPauliLift-notes.md);
the current integration status is recorded above.

`BarnesWall/PauliPresentation.lean` uses Mathlib's existing `PresentedGroup`
with a central generator and two families indexed by `Fin n`. Its eight
relation families impose squares, central commutation, same-family
commutation, and the central sign in equal-index cross commutation. It proves
existence of reduced-list words, the universal homomorphism and its uniqueness,
and injectivity whenever the central image is nonidentity. The normal-form
existence required by the kernel argument is proved, not assumed; sorted
normal-form uniqueness and group cardinality are not asserted.

`BarnesWall/KRRPauliAction.lean` specializes that presentation to `n = 7`.
Its generator images are literally `thetaAut`, `xLift` and `zLift`, with all
relations and central nontriviality supplied by `KRRPauliLift`. It constructs
an injective ordinary homomorphism into the full lattice-VOA automorphism
group. The named quaternion words are `z 6 * x 6` and `(z 5 * x 5) * z 6`;
their images are the existing `aLift` and `bLift`. This candidate is a faithful
action of the presented `Pauli 7`; it does not identify that presentation
with the prescribed matrix-generated E. The concrete adapter still awaits
the full public integration. [PauliPresentation-notes.md](PauliPresentation-notes.md)
records its source review and the separate generic local PASS.

## Boolean-cubic factorization

`BarnesWall/BooleanCubic.lean` represents a squarefree Boolean polynomial by a
coefficient for each finite support. Evaluation sums the coefficients of all
subsets of the input support. For every m ≥ 2, a polynomial of degree at most
three that vanishes wherever Q(x,y) = Σᵢ xᵢyᵢ is zero has a unique affine
multiplier: F = Q(δ + Σᵢ βᵢxᵢ + Σᵢ γᵢyᵢ). Both the function identity and
equality of reduced squarefree coefficient families are proved. The latter
uses Boolean reduction of repeated variables, not an unreduced polynomial
identity.

The version using only nonzero singular inputs retains the explicit condition
that the constant coefficient is zero. The source proves this uniform theorem
schematically; it does not enumerate a fixed dimension's input table.
[BooleanCubic-notes.md](BooleanCubic-notes.md) records the representation,
verification provenance and the remaining cohomological interfaces. In
particular, this module does not identify cohomology classes with the represented
polynomials or prove anomaly detection.

## Combined local check

`check_bridge.py` runs after the dependency audit. The next candidate compiles
twenty-one local modules into the audited environment, prints the types and
transitive axioms of 204 local declarations, and checks source pins and unchanged
inputs again. This expanded public result is pending; the latest completed
public run checked nineteen modules and 187 local declarations.
It continues independent module checks after a source failure, skips affected
dependents, and fails before the axiom stage if any module failed or was skipped.
Its parser applies the same standard-axiom restriction. The mathematical
assumptions remain visible in `LocalAxiomProbe.lean`'s type output.

The integer module and coordinate adapter derive explicit-cocycle compatibility
and coherent lift composition under their stated matrix hypotheses. The block
and quaternion matrix modules supply concrete generator inputs. The action
module connects these to a faithful `QuaternionGroup 4` representation and has
passed the combined check. No module establishes unitarity of an automorphism.

## Mathematical work still required

LeanVOA's lattice basis is chosen noncomputably; its cocycle and oscillator
frame are not definitionally the KRR coordinate conventions. The checked
coordinate specialization and global cocycle transport connect those conventions
for the stated lattice and quaternion action. Arbitrary small-support
composition and the concrete Pauli relations have also passed the combined
check. The next presentation/action candidate still requires its full public
integration; its generic presentation has a separate local PASS.

The wrapper supplies conformal preservation and bijectivity from its explicit
hypotheses, and the charge-state argument supplies generic matrix faithfulness.
The new adapter supplies literal common-Q8 word images in the presented
`Pauli 7` action. Identification with the prescribed matrix-generated E,
including its cardinality and extraspecial plus type, remains to be formalized.
No global multiplicativity of the canonical section on arbitrary matrix words
is assumed or proved by this increment. The general group
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
