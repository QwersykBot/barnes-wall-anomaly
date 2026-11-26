# Concrete lattice increment: checked source and scope

Date: 2026-11-26.

**Status: the complete source passed local Lean checking and a 15-declaration
transitive axiom audit; independent CI integration is pending.** The file is
`BarnesWall/Lattice128.lean`, SHA256
`2d8f73cb33a9ccfed376bfbecc9ab7e32f804227c7c6b8fda323ccf1c4e0ab1d`.
The clean source check completed in 3.361 seconds. A separate copy containing
the unchanged source followed by the 15 `#print axioms` commands checked in
3.113 seconds. Both returned exit code zero without warnings. Every report
listed only `propext`, `Classical.choice`, and `Quot.sound`; none listed
`sorryAx` or a native decision axiom.

This is a checked concrete lattice increment, not a completed formalization of
the anomaly proof. The identification with the published KRR tensor formula
remains the explicit mathematical correspondence below.

## Mathematical content

The carrier is exactly `Fin 128 → ℤ`, and `orderedBasis` is `Pi.basisFun` in the
ordinary numerical order. `support i` is the set of numerical one-bit positions
of `i.val`. In the source tensor order, position `a` (numbered 1–7) is numerical
bit `7-a`; no arbitrary equivalence with a 128-element type is used.

For each index, write

\[
z_i=7-|I_i|,\quad p_i=z_i\bmod 2,\quad t_i=(z_i+1)/2.
\]

The definitions are

\[
B_{ij}=2^{t_i}\mathbf1_{I_j\subseteq I_i},\qquad
G_{ij}=2^{t_i+t_j+|I_i\cap I_j|-4},
\]

and `basisMatrix` is the rational matrix `B/4`. This is KRR (A.1.1) at `m=7`:
each zero tensor bit contributes `√2`, the source prefactor contributes
`(√2)^(p_i-4)`, and `z_i+p_i=2t_i`. Its nonzero Cartesian coordinates are exactly
the subsets of `I_i`. This paper-to-coordinate identification is documented
mathematics, not a claim that Lean has parsed the source's tensor formula.

The code proves the exponent lower bound before using truncated natural
subtraction. The identities `2t_i+|I_i|=7+p_i` and
`|I_i∪I_j|+|I_i∩I_j|=|I_i|+|I_j|`, together with `|I_i∪I_j|≤7`, imply
`t_i+t_j+|I_i∩I_j|≥4`.

The main coefficient identity is structural. Binary support bijects the
retained numerical indices with the powerset of any subset of `{0,…,6}`.
Consequently the `(i,j)` coefficient of `BBᵀ` is

\[
2^{t_i+t_j}\,2^{|I_i\cap I_j|}=16G_{ij}.
\]

There is no enumeration of all 16,384 coefficient pairs. The only closed finite
count used by that argument is the seven-term identity
`1+2+4+8+16+32+64=127`, proved by ordinary `decide`. The small constant
inequalities/nonzero facts likewise use ordinary kernel reduction. No
`native_decide`, floating point, external decision oracle, new axiom, or admitted
proof is present.

Subset inclusion implies numerical index order by summing powers of two. Thus
`B` is lower triangular with diagonal `2^t_i`, and its determinant is nonzero.
The existing integer-matrix theorem then makes row multiplication by `B`
injective. The proof of positive definiteness reduces to

\[
16\langle v,v\rangle=\sum_j(vB)_j^2>0\quad(v\ne0).
\]

The half-Gram matrix uses the strict lower triangle of `G` and diagonal
`2^(2+p_i)`. The proved diagonal formula for `G` gives `H+Hᵀ=G`. This yields a
concrete integer bilinear `halfForm` with the exact symmetrization needed by the
separate cocycle-transport module and proves evenness.

## Completed local audit and CI audit points

The definitions and all source proofs are unconditional at this dimension.
The following 15 declarations were actually axiom-audited, under namespace
`BarnesWall.Lattice128`; the same audit can be repeated in CI:

| Declaration | Intended check |
|---|---|
| `support_injective`, `card_support_subsets` | Exact binary indexing and powerset count |
| `gramPower_ge_four` | No hidden negative-exponent truncation |
| `B_mul_transpose`, `basisMatrix_gram` | Integer identity and exact rational scale |
| `B_lower_triangular`, `B_det_ne_zero` | Integral injectivity input |
| `H_add_transpose`, `halfForm_symmetrization` | Prescribed ordered half-Gram convention |
| `form_orderedBasis`, `halfForm_orderedBasis` | Basis entries agree with `G` and `H` |
| `scaled_form` | Exact row-oriented form identity for every pair of vectors |
| `lattice_rank`, `lattice_even`, `lattice_posDef` | Concrete rank-128 positive even lattice |

The only upstream VOA import is `VOA.Foundations.Lattices`. Additional Mathlib
imports supply binary-support enumeration (`Combinatorics.Colex`), powersets,
dimension, and triangular/nondegenerate matrices. Ring and core Omega tactics
construct ordinary proof terms. The bounded local restore added only the
identified lattice dependency closure while preserving all 18,210 existing
Phase artifacts. It verified and restored 648 pinned official cache archives,
then used normal Lake `:olean` targets to compile the three pinned Mathlib
sources `Data.Nat.BitIndices`, `Data.Finset.Slice`, and `Combinatorics.Colex`, and
the single upstream VOA source `Foundations.Lattices`. No unexpected source or
native build was requested. The final checks used one Lean worker with a
3,072 MiB artificial heap cap and the recorded operating-system resource guards.
The final axiom audit's minimum available memory was 2,965,983,232 bytes, above
the 2 GiB early-stop threshold; no memory or filesystem guard was violated.

The first own-source check found two elaboration failures caused by the bundled
carrier's transparency at rewrite sites. Declaring the existing coordinate type
locally resolved those failures; the mathematical statements and proofs' strategy
were unchanged. Deprecated conditional simplification names were also updated.
The failed check, subsequent successful check, exact invocation/environment,
resource samples, and axiom output are retained in the internal execution receipt.

## Pins and boundaries

- KRR: Christoph A. Keller, Ashley Winter Roberts, Jeremy Roberts,
  *CFTs with Large Gap from Barnes-Wall Lattice Orbifolds*,
  [arXiv:2411.13646v2](https://arxiv.org/pdf/2411.13646v2), 17 March 2026,
  Appendix A.1; JHEP 04 (2026), 009. The previously inspected PDF SHA256 is
  `034fd7025a50b70da292daa52464fe73841cb69108ccb84bf82e0e83a88bab21`.
- LeanVOA: `faedf8eb9e3fe275d3ac09e645aac694e496e965`.
- Mathlib: `b63f6e8a68d220e3b3bc4f3792bb53650d375f24`.
- Lean 4.35.0-rc3: `470d5ce1400764999581fd26d5d72b00d990b0f4`.

This increment does not assert unimodularity, minimum norm, integral isometries
or inverses, block preservation, canonical lift identities, quaternion group
relations, faithfulness, agreement on Q8, or an orbifold theorem. It does not
replace the earlier dependency audit with a fresh Mathlib source rebuild.
The source intentionally exports a coordinate basis separately from LeanVOA's
noncomputably chosen basis; the established global-cocycle bridge handles that
difference in a later specialization.
