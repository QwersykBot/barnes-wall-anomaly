# Conditional diagonal-flip construction with E8(2) symmetry

**26 November 2026 — Proposed mathematical proof; internal AI-agent review completed; external expert review pending.**

This package proposes a strongly rational, unitary holomorphic VOA $Y$ of central charge 128 with Virasoro-primary gap four and full automorphism group $E_8(2)$. Its weight-four primary space has dimension $545\,925\,250$. The construction is conditional on the VOA $W_{32}$, its specified elementary abelian subgroup, and the fusion, module and automorphism data of $U$ in Gerald Höhn's [*An extremal vertex operator algebra of central charge c = 64*, version 2, 20 November 2026](https://hexagonmath.org/pdf/2611.00631v2). Those inherited inputs are stated explicitly; this package does not independently verify the entire recent preprint.

The argument constructs the full diagonal extension of $U\otimes U$, then takes the orbifold of its literal flip. The six notes below treat the actual extension and automorphisms, group recognition, unitarity and spectral consequences. The [detailed dependency guide](README.txt) records their assumptions, notation and logical interfaces.

## Read the six notes

| Note | Scope |
| --- | --- |
| [Construction](diagonal-flip-c128-extraspecial-construction-20261126.txt) | The specified extension, character, actual extraspecial subgroup and full involution centralizer. |
| [Permutation preservation](diagonal-flip-permutation-preservation-20261126.txt) | The same extension over a common fixed algebra and an actual three-cycle of its involutions. |
| [Elementary simplicity](extraspecial-centralizer-elementary-simplicity-20261126.txt) | A finite-group simplicity criterion applied to the constructed automorphisms. |
| [Recognition](e8-recognition-from-extraspecial-centralizer-20261126.txt) | The exact Aschbacher ICM theorem and exclusion of its alternatives. |
| [Unitarity](unitarity-three-axis-20261126.txt) | A compatible positive unitary structure on this same extension. |
| [Primaries, conformal designs and the cubic](e8-minimal-primaries-conformal-designs-and-e7-axis-20261126.txt) | Primary representations through weight six, conformal 6-designs and an explicit primary idempotent. |

The [permutation-argument review](diagonal-flip-k-s4-independent-review-20261126.txt) is an internal audit record. The [character-screen guide](e8-minimal-cubic-screen/README.txt) explains the supplied data, exact calculations and their limits.

## Reproduce the finite calculations

Use ordinary **Python 3 with assertions enabled**, without `-O` or `-OO`; leave `PYTHONOPTIMIZE` unset or set it to `0`. Only the standard library is required. From this `diagonal-flip/` directory, run these three commands:

```sh
python3 check_character_low_weights.py
python3 e8-minimal-cubic-screen/analyze_e82.py e8-minimal-cubic-screen/E82cl.g
python3 e8-minimal-cubic-screen/exhaust_degree_splits.py e8-minimal-cubic-screen/E82deg.g e8-minimal-cubic-screen/result.json
```

Compare their JSON output, respectively, with [character-low-weights.json](character-low-weights.json), [result.json](e8-minimal-cubic-screen/result.json) and [degree-splits-result.json](e8-minimal-cubic-screen/degree-splits-result.json). The first calculation uses the character's six initial coefficients and the modular argument in the notes. The other two use Frank Lübeck's supplied class and degree data, with source URLs and acquisition hashes retained alongside them. The scripts read these files as data; they require no network access or GAP execution.

Run `sha256sum -c SHA256SUMS` here to verify the package bytes. The dedicated repository workflow checks these hashes and compares all three outputs with the supplied receipts. These finite checks support displayed numbers; they do not certify the VOA construction, automorphism group or analytic proofs.

## Scope and review status

The mathematical text and code were prepared by coordinated AI agents and received internal mathematical review. There is no claim of independent human or external specialist acceptance, priority, or complete formal verification. The repository's existing Lean development concerns different, explicitly documented ingredients of the Barnes–Wall action; it does not prove this diagonal-flip construction or its $E_8(2)$ recognition.

Equality of the graded character with the dense Barnes–Wall orbifold $T_0$, under that separate project's premises, does **not** identify the vertex products: no isomorphism $Y=T_0$ is used or proved. The package also makes no uniqueness, strong-locality or conformal-net identification claim. The inherited Höhn inputs and the actual extension, product, support and group-recognition arguments remain explicit targets for external review.
