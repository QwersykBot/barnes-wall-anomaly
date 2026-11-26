# The Pauli presentation, matrix subgroup and full-state action

Three small interfaces connect the generic presentation to the prescribed
matrix generators and their canonical lattice-VOA lifts. Ordinary composition
is used throughout. The matrix target has opposite multiplication because
lattice coordinates act on the right.

## Presentation and faithfulness

`BarnesWall/PauliPresentation.lean` uses Mathlib's existing `PresentedGroup`.
For generators `c`, `x i`, and `z i`, the relations say that all generators
square to one, `c` is central, the X and Z families each commute, and

```text
x i * z j = (if i = j then c else 1) * (z j * x i).
```

The universal map `toGroup` is determined by those literal generator images.
The proof constructs a representative of every group element of the form
`c^e * X(xs) * Z(zs)`, with Boolean `e` and duplicate-free lists. It proves
existence from free-group words; normal forms are not assumed. It neither
sorts the lists nor asserts normal-form uniqueness or cardinality.

Commuting a kernel word against individual generators detects each nonempty
list whenever the central image is nonidentity. The remaining central factor
is then detected directly. Thus `toGroup_injective` requires only the stated
relations and a nonidentity central image. It has no hidden finiteness or
positive-rank assumption.

## The actual matrix subgroup

`BarnesWall/KRRPauliMatrix.lean` uses the actual published integral matrix
units: `centralUnit`, `KRRPauli.XUnit`, and `KRRPauli.ZUnit`. It proves their
relations in `(Matˣ)ᵐᵒᵖ` and that the central image has underlying matrix
`-I ≠ I`. These facts give an injective `matrixHom`.

`generated` is the subgroup closure of the literal central, X, and Z images.
The presentation's generation theorem identifies `matrixHom.range` with this
subgroup. `matrixEquiv` is the resulting multiplicative equivalence onto
`generated`; `matrixEquiv_coe` states that its underlying value is `matrixHom`.
The proof uses the existing `map_closure`, `ofInjective`, and `subgroupCongr`
APIs. It introduces no additional quotient or normal-form framework.

The opposite convention preserves the actual quaternion labels:

| Abstract word | Underlying ordinary matrix unit |
|---|---|
| `z 6 * x 6` | `aUnit`, with matrix `X 6 * Z 6` |
| `z 5 * x 5 * z 6` | `bUnit`, with matrix `Z 6 * (X 5 * Z 5)` |

This identification does not prove the subgroup's order or its extraspecial
plus-type classification.

## The full-state action

`BarnesWall/KRRPauliAction.lean` specializes the presentation to `Pauli 7`.
`action` sends `c` to the actual upstream `thetaAut` and sends X and Z to the
literal canonical `xLift` and `zLift`. Every relation and the central
nontriviality premise come from `KRRPauliLift`. The action is faithful and its
two displayed quaternion words have exactly the prescribed `aLift` and `bLift`
as images.

The final transport is

```lean
concreteAction := action.comp KRRPauliMatrix.matrixEquiv.symm.toMonoidHom
```

Its domain is the generated opposite-matrix subgroup. The equivalence and
the already proved faithfulness give `concreteAction_injective`. The equation

```lean
concreteAction (KRRPauliMatrix.matrixEquiv g) = action g
```

transports every generator and quaternion-word image. This construction does
not assert that the canonical section is multiplicative on arbitrary lattice
matrix words; only the established relations and universal property are used.

## Verification status

The complete public check at commit
`9886f589d5b27d11913fce65482f99c2e35ea8c6`,
[run 45868904182](https://github.com/QwersykBot/barnes-wall-anomaly/actions/runs/45868904182),
passed **21 local modules, 204 local declaration reports and 15 upstream
reports**. The local compilation produced no warnings or errors. Source and
probe hashes matched that exact public commit, and the reports used only
`propext`, `Classical.choice`, and `Quot.sound`.

That result includes the presentation's nine requested declarations and the
original action adapter's eight declarations: `relations`, `action`, its
three generator equations, `action_injective`, `action_a_word`, and
`action_b_word`. The generic presentation also passed a separate local check
before publication; the public integrated result is the relevant certificate
for the actual VOA specialization.

The current candidate adds `KRRPauliMatrix` and three transport declarations
in `KRRPauliAction`, yielding **22 modules and 223 local reports**. The added
reports cover sixteen matrix declarations and `concreteAction`,
`concreteAction_injective`, and `concreteAction_matrixEquiv`. Source and
pinned-API reviews found no remaining blocker; the expanded public compile
and axiom result is pending. The prior 21-module run does not certify these
additions.

The exact source snapshot is recorded in the repository manifest. The broad
`krr_full_extraspecial_action_formalized` flag remains false because group order
and plus-type classification are not proved here. Separate receipt flags
describe the matrix identification and concrete action precisely. Cohomology,
anomaly vanishing, twisted-sector energies, orbifold existence, unitarity and
the analytic spectrum statements remain outside this formal development.
