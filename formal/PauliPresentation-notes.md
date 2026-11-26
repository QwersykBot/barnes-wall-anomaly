# The Pauli presentation and its concrete action

`BarnesWall/PauliPresentation.lean` defines `Pauli n` using Mathlib's existing
`PresentedGroup`. `BarnesWall/KRRPauliAction.lean` specializes its universal
property to the actual full-state canonical lifts at all seven numerical
positions. Both files use ordinary group multiplication.

## Exact relations and generator images

The presentation has a central generator c and generators Xᵢ, Zᵢ for
`i : Fin n`. The concrete adapter discharges all eight relation families:

| Presentation field | Relation | Concrete input from `KRRPauliLift` |
|---|---|---|
| `c_sq` | c² = 1 | `theta_sq` |
| `x_sq` | Xᵢ² = 1 | `xLift_sq` |
| `z_sq` | Zᵢ² = 1 | `zLift_sq` |
| `c_comm_x` | c commutes with Xᵢ | `theta_commute_xLift` |
| `c_comm_z` | c commutes with Zᵢ | `theta_commute_zLift` |
| `x_comm_x` | Xᵢ commutes with Xⱼ | `xLift_commute_xLift` |
| `z_comm_z` | Zᵢ commutes with Zⱼ | `zLift_commute_zLift` |
| `x_mul_z` | XᵢZⱼ = (if i = j then c else 1) ZⱼXᵢ | `xLift_mul_zLift`; `xLift_commute_zLift_of_ne` |

`Pauli7` is an abbreviation for `Pauli 7`, not a separate group construction.
The exported homomorphism `KRRPauliAction.action` maps c to the actual upstream
`thetaAut`, and Xᵢ and Zᵢ to the literal `xLift i` and `zLift i`. The generic
theorem `toGroup_injective` requires only a nonidentity central image beyond
the displayed relations; the adapter supplies the proved `theta_ne_one`.

The generic proof establishes that every presentation element has a word
cᵉ times an X-list product times a Z-list product, with each list duplicate-free.
It does not assume this normal form, sort the lists, or assert uniqueness.
Commuting a kernel word against individual generators detects any nonempty
list when the central image is nonidentity; the remaining central factor is
then detected directly. This proves faithfulness without assuming a group
cardinality or a matrix-group identification.

The two quaternion compatibility statements retain literal reversed words:

    action (z 6 * x 6) = KRRQuaternionAction.aLift
    action ((z 5 * x 5) * z 6) = KRRQuaternionAction.bLift.

They correspond to the existing matrix words `a = X₆Z₆` and `b = Z₆(X₅Z₅)`
because canonical lifts reverse matrix multiplication. Source review checked
the eight relation fields, three generator images, injectivity input, and
both Q8 word equalities against the actual imported signatures. It found no
mathematical or API blocker. It does not substitute for compiling the adapter.

## Verification provenance

The latest complete public result is the nineteen-module PASS at commit
`2677b16b8f547fd09eb5a2345ce6a994e59050b7`,
[run 45866546569](https://github.com/QwersykBot/barnes-wall-anomaly/actions/runs/45866546569).
It includes `KRRPauliLift`, all 15 upstream reports, and 187 local type/axiom
reports. It does not certify the two new modules.

The original generic source, SHA256
`665d38524f3fb41ec0024b8db3ae6046950b49980e59de75a0e3de8adaf41fab`,
failed one elaboration in `canonical_relator`: the quotient images of free
generators did not simplify to the named x/z functions in that proof step.
A separate repair makes that target explicit and updates deprecated conditional
simplifier names. Its definitions and theorem statements are unchanged.

The repaired source, SHA256
`e5acb177667c39bd49137db8b8020b4a2d9d24a0ac842e55ae6dd6e6fb982194`,
passed a guarded local compile and a separate importing probe at the pinned
toolchain. The complete repair phase took 4.48 seconds. Source diagnostics were
empty; all nine paired type/axiom reports contained only `propext`,
`Classical.choice` and `Quot.sound`. No dependency rebuild was performed in
that repair phase. The nine declarations are `relations`, `toGroup`, its three
generator-image theorems, `toGroup_unique`, `exists_normalWord`,
`injective_of_central_ne_one`, and `toGroup_injective`.

The integrated `BarnesWall/PauliPresentation.lean` changes only the introductory
status/license comment from the locally checked repair and has SHA256
`91b097232b5272020848cd106854e882eab7df29a5c32177c97edf3a07dbea3f`.
The integrated `BarnesWall/KRRPauliAction.lean` uses the same source-reviewed
proof body with an updated introductory comment and the equivalent
`ite_eq_right` simplifier in place of `if_neg`. Its SHA256 is
`11404478c63d95a6f1f2b12bec03a88a388e3452b76938a5f63fc6ce4831e2c3`.

The pending combined candidate has **21 modules and 204 local reports**:
the previous 187 plus nine generic and eight concrete declarations. The
concrete requests are `relations`, `action`, `action_central`, `action_x`,
`action_z`, `action_injective`, `action_a_word`, and `action_b_word`.
Its complete public compile and axiom result, including the actual VOA adapter,
is still pending. The local generic PASS is not a full 21-module PASS.

## Scope

The new candidate constructs a faithful action of the **presented `Pauli 7`**
on the full lattice VOA, with actual generator images and literal common-Q8
word compatibility. Identification with the prescribed matrix-generated E,
its cardinality and extraspecial plus type remain unformalized. Neither module
asserts global multiplicativity of the canonical section on arbitrary matrix
words. Group cohomology, anomaly detection, unitarity and the orbifold theorem
remain outside this increment. The source and reviews are AI-agent work;
no independent human review is claimed.
