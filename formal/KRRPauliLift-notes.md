# Relations of the concrete Pauli lifts

`BarnesWall/KRRPauliLift.lean` defines `xLift k` and `zLift k` as the literal
canonical lifts of the integral `XUnit k` and `ZUnit k`, for every numerical
bit `k : Fin 7`. It derives their relations from the concrete matrix identities
and the checked small-support composition theorem.

## Derived relations and order

The exports state that each generator squares to one, all X lifts commute
with each other, all Z lifts commute with each other, and X and Z lifts at
distinct positions commute. At the same position the relation is

    xLift k * zLift k = thetaAut * (zLift k * xLift k).

Here `thetaAut` is the actual upstream lattice involution, not a formal sign
symbol. The module proves that it commutes with every generator, squares to
one, is nonidentity, and has order exactly two. Its nontriviality comes from
the already checked quaternion lift and matrix faithfulness.

The order is forced by ordinary function composition: the left side of the
displayed relation is the lift of ZX. The right side is the lift of
`(XZ)(-I)`. The checked equality `ZX = -(XZ)` identifies them. Every step
uses the same half-Gram matrix and global cocycle transport on a common
singleton support. Distinct-index commutation uses a two-position support.

The common quaternion generators retain their literal images:

    aLift = zLift 6 * xLift 6
    bLift = (zLift 5 * xLift 5) * zLift 6.

These correspond to `a = X₆Z₆` and `b = Z₆(X₅Z₅)` with reversed lift order.
They do not identify the unreversed matrix words with those same images.

## Verification status

The source has been independently reviewed against the exact matrix, support,
composition and central-comparison APIs. It has not been compiled locally;
the complete VOA dependency closure is checked by the public workflow.
Its original source had SHA256
`6718119de47b436c9bb8200c08cf6e23519b9fe0e14f35839c25a32f23114dc7`.
The integration copy changes only the initial status/license comment, leaving
imports and proof body identical, and has SHA256
`c58805d25d3180159d73cd024e6276e7faa70ee68ea4ccd8cdd16cc3d32c7206`.

The combined probe requests the two generator definitions and thirteen public
theorems. Compilation, exact type output and the transitive-axiom restriction
remain the acceptance gate; source review alone is not certification.

## Remaining group construction

This adapter supplies concrete relations. It does not yet construct the full
extraspecial-group action, prove a presentation's normal-form theorem, or
identify that presentation with the prescribed matrix group. No global
multiplicativity of the canonical lift on arbitrary words is assumed. A
separate group constructor must consume these proved relations and establish
the complete action and correspondence.
