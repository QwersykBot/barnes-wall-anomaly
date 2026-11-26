# Canonical-lift faithfulness: source-only increment

Date: 2026-11-26.

**Status: source/API inspection complete; Lean elaboration and axiom audit are
pending combined CI. No compiler, download, or dependency build was run for
this increment.** The candidate is `BarnesWall/CanonicalFaithfulness.lean`,
SHA256 `c981d5debbc642d0e2d47b9901d5b8efce076378dfe7fa8444a958e854c0de0e`.
It imports only `BarnesWall.CanonicalLift`; no new upstream import is needed.

## Exact endpoint

For an actual integral coordinate equivalence
`coords : L.carrier ≃ₗ[ℤ] (ι → ℤ)` and any integer matrix `H`, the proposed theorem

```lean
BarnesWall.CanonicalFaithfulness.liftMap_injective
  (coords : L.carrier ≃ₗ[ℤ] (ι → ℤ)) (H : Matrix ι ι ℤ)
```

states `Function.Injective (CanonicalLift.liftMap coords H)`. Thus equality of
the two full complex-linear state maps implies equality of their integral
matrices. No isometry, positivity, invertibility, or block condition is required
for this injectivity statement; those remain necessary elsewhere when the maps
are asserted to be conformal automorphisms with a particular group law.

## Actual charge-state argument

The pinned upstream module defines
`latChargeGen L α = 1 ⊗ eGen L α`, with `eGen L α = Finsupp.single α 1`.
Its `coordEα L α` is the tensor map induced by `Finsupp.lapply α`, followed by
the right-unit equivalence. The proved `coordEα_latStateGen` therefore gives

$$P_\alpha(1\otimes e^\beta)=
\begin{cases}1&\alpha=\beta,\\0&\alpha\ne\beta.\end{cases}$$

Applying this genuine projection to $c e^\alpha=d e^\beta$, with $c\ne0$,
forces $\alpha=\beta$: otherwise it gives $c\cdot1=0$ in the polynomial Fock
space. The code uses the same `smul_eq_zero` instance already used by the
upstream lattice-morphism injectivity proof.

The upstream theorem `latMorphC_latChargeGen` proves
$\Phi_{f,c}(e^x)=c(x)e^{f(x)}$ directly from `TensorProduct.map` and
`Finsupp.linearCombination`. It requires no isometry or positivity hypothesis.
Consequently equality of full maps, with one phase nowhere zero, implies
equality of the lattice linear maps. In the canonical specialization,
`transportedPhase_ne_zero` and `CanonicalLift.phase_ne_zero` supply that
nonvanishing; it is not a new assumption.

Finally `CanonicalLift.coords_rowMap` sends the lattice-map equality to
$vR=vS$ for every integer coordinate vector $v$, using the actual inverse
`coords.symm`. Mathlib's `Matrix.ext_iff_vecMul` then gives $R=S$.

## CI audit targets and pins

All four declarations have prefix `BarnesWall.CanonicalFaithfulness`:

- `charge_eq_of_smul_eq`;
- `latticeMap_eq_of_latMorphC_eq`;
- `rowMap_injective`;
- `liftMap_injective`.

The inspected `CanonicalLift.lean` has SHA256
`8b27dd562b7204d9df1069ba01cd9269f009ca9edda265359b11d46ba7c2768f`;
`CocycleTransport.lean` has SHA256
`69b2e2a51d18937c2915ba1b5c19d99ee798395f9f1a67f69ff6d50347d39324`.
Upstream source pins remain LeanVOA
`faedf8eb9e3fe275d3ac09e645aac694e496e965` and Mathlib
`b63f6e8a68d220e3b3bc4f3792bb53650d375f24`.

The exact inspected APIs are in LeanVOA `Examples/LatticeGenModule.lean`,
`Examples/LatticeGenGrading.lean`, and `Moonshine/LatticeMorph.lean`, plus
Mathlib `Data/Matrix/Mul.lean`. Their implementations were read, including the
Finsupp projection and pure-charge formula. This is a source-level dictionary
check, not a substitute for compiling this new module. No identity-lift,
central-lift, concrete generator, or group-faithfulness theorem was added.
