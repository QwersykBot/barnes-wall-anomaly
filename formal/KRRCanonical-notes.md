# Concrete KRR128 canonical lifts

Date: 2026-11-26.

**Status: this exact source and all its requested axiom reports passed in the
complete public run 45863204593.**
`BarnesWall/KRRCanonical.lean` has SHA256
`f1e5306b4014813bbcc26285dc5d642f273d133fef1eb8eec92f732a66c3ca44`.

## Independent Pauli source review

I read the entire checked `KRRPauli.lean` at SHA256
`8a86c02482b286a3c250e8a89aae04639eac14b25e213a165e96a4e5c1bbafca`
against KRR Appendix A.1 and equations (A.2.5)–(A.2.6), including the retained
original TeX. The primary version is
[arXiv:2411.13646v2](https://arxiv.org/pdf/2411.13646v2), whose inspected PDF
SHA256 is `034fd7025a50b70da292daa52464fe73841cb69108ccb84bf82e0e83a88bab21`.
No mathematical or convention blocker was found.

For numerical bit $k$, tensor position is $7-k$. The `X` row is the identity
row when that bit is one and $-e_i+2^{p(i)}e_{\operatorname{toggle}(i)}$ when
it is zero. `Z` has the complementary case split. These are precisely the two
published formulas. The support-based toggle inserts or erases the bit, so
it implements the indicated addition or subtraction of $e_k$.

The orientation is also correct: Cartesian basis rows are $W=B/4$. An integral
coordinate row $v$ therefore transforms compatibly exactly when
$R W=W C$, or **$R B=B C$**. `cartX` uses the equivalent condition
$i=\operatorname{toggle}(j)$; the proved toggle involution makes this the
right-action permutation of row $i$ to row $\operatorname{toggle}(i)$.
`cartZ` has the published diagonal signs. The full intertwining identities,
not a diagonal-only Gram comparison, give $RGR^T=G$ from $BB^T=16G$.

Finally, `XUnit` and `ZUnit` use the same integral matrix as inverse and supply
both inverse equations from `X_sq` and `Z_sq`. Nonzero determinant of $B$ is
used only to cancel right multiplication by $B$ in proving those equations.
There is no claim that $B$ itself has an integral inverse, and no hidden use of
unimodularity. The block-support statements correctly require $k\ge4$.

## Concrete specialization

`coordinates` is the identity equivalence on `Fin 128 → ℤ`.
`gram_in_coordinates` is the actual `Matrix.toBilin' G` evaluation, and
`canonicalHalfForm_eq` identifies the adapter's pulled-back half-form with the
same `Lattice128.halfForm`. The constructor

```lean
KRRCanonical.lift (R : (Matrix Index Index ℤ)ˣ) (hR : ↑R * G * (↑R)ᵀ = G)
```

therefore returns a conformal automorphism of the concrete positive even
lattice VOA using the checked `lattice_even`, `lattice_posDef`, and
`H_add_transpose`. The same global cocycle transport is used for every matrix.

`liftMap_mul` and `lift_mul` insert the proved
`KRRBlocks.H_even_of_same_block` into the generic composition theorem. Their
remaining premises are actual matrix isometries and zero entries across the
concrete modulo-16 blocks. The result is the right-action order
$\operatorname{lift}(RS)=\operatorname{lift}(S)\operatorname{lift}(R)$.

`liftMap_injective` specializes the charge-state adapter, and
`matrix_eq_of_lift_eq` recovers matrix equality from equality of conformal
automorphisms. No subgroup or concrete Q16 relation is introduced.

Suggested CI theorem reports, all under `BarnesWall.KRRCanonical`, are
`coordinates_apply`, `gram_in_coordinates`, `canonicalHalfForm_eq`,
`lift_apply`, `liftMap_mul`, `lift_mul`, `liftMap_injective`, and
`matrix_eq_of_lift_eq`; the `lift` definition can also be audited directly.
The faithfulness adapter compiled in public run 45859088010; the combined
axiom gate was not reached. Its two linter-only cleanups have SHA256
`2af31cd1c9ae471488614f0f1c1bf8d661e64c9dcaaf7fb1f7d8630f4b390ee1`.
That earlier run stopped at a multiline proof-term layout error in this
specialization. The source hash above includes its parenthesization repair,
which compiled without local warnings in run 45861216253. The complete
[run 45863204593](https://github.com/QwersykBot/barnes-wall-anomaly/actions/runs/45863204593)
subsequently checked this specialization and all other sixteen-module inputs,
with 167 local axiom reports containing only the standard three axioms.
