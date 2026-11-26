# Exact KRR block divisibility

Date: 2026-11-26.

**Status: complete local source check and 11 transitive axiom reports passed;
independent CI integration is pending.** `BarnesWall/KRRBlocks.lean` has SHA256
`ccf0a76c65df197c886ccac96086a5b3b1afb82c3317ff2fdcac3fa5ef00fb9f`.
It imports the unchanged, checked `BarnesWall/Lattice128.lean` at SHA256
`2d8f73cb33a9ccfed376bfbecc9ab7e32f804227c7c6b8fda323ccf1c4e0ab1d`.

## Statement and argument

The block function is literally
`block (i : Fin 128) : Fin 16 := ⟨i.val % 16, …⟩`, and it is proved surjective.
It fixes numerical bits 0–3 and lets bits 4–6 vary. In the documented KRR order,
these are fixed tensor positions 4–7 and varying positions 1–3, respectively.

Lean's existing `Nat.testBit_mod_two_pow` proves that equal residues modulo 16
have equal bits below position 4. `Nat.mem_bitIndices` transfers that equality
to the actual `Lattice128.support` definition. Thus, writing $I,J$ for the two
supports,

$$
(I\cup J)\setminus(I\cap J)\subseteq\{4,5,6\},
\qquad |I\cup J|\le |I\cap J|+3.
$$

Let $N=\operatorname{gramPower}(i,j)$, $u=|I\cup J|$, and $c=|I\cap J|$.
The previously checked half-power identities and the union/intersection
cardinality identity give

$$2N+u=14+p_i+p_j+c.$$

Consequently $2N\ge11$, so $N\ge6$. The exponent in $G_{ij}=2^{N-4}$ is
therefore at least two. This proves **$4\mid G_{ij}$ within every block**.
The same stronger statement holds for $H$: its strict lower entries equal
$G$, upper entries vanish, and diagonal entries are $2^{2+p_i}$. In particular,
`H_even_of_same_block` supplies the evenness premise for the separate integer
phase-composition theorem.

This is a symbolic proof for arbitrary indices, with no enumeration of the
16,384 pairs, no assumed parity bound, and no `native_decide`, `sorry`, or new
axioms. The only closed decisions concern small natural/integer constants.

## Checked interface

All declarations have prefix `BarnesWall.KRRBlocks`:

- `block_val`, `block_eq_iff`, `block_surjective`;
- `low_testBit_eq`, `mem_support_low_iff`;
- `support_difference_subset`, `support_union_card_le`;
- `gramPower_ge_six_of_same_block`;
- `four_dvd_G_of_same_block`, `four_dvd_H_of_same_block`;
- `H_even_of_same_block`.

The first two reports use no axioms; the remaining reports use only subsets of
`propext`, `Classical.choice`, and `Quot.sound`. The full-source axiom audit
took 2.136 seconds, with exit zero and no warnings. A separate 2.298-second
check emitted the real `KRRBlocks.olean` for downstream imports. The complete
task's generated files occupied approximately 1 MiB, below the 20 MiB cap.
The shared compiler lock, one-worker limit, 2.75 GiB admission threshold,
3,072 MiB Lean heap cap, resource watchdog, and ten-minute phase bound were
retained. No guard was triggered, and no dependency download or upstream
rebuild occurred.

The result concerns only the exact block labels and the Gram divisibility
premise. It does not establish that any proposed isometry preserves these
blocks, or prove any lattice, VOA, or quaternion group action. Those are
separate obligations. The paper-to-coordinate correspondence retains the
scope stated in `Lattice128-notes.md`.
