/-
SPDX-License-Identifier: Apache-2.0
See ../LICENSE-Apache-2.0.txt.
-/
import BarnesWall.CocycleTransport

/-!
# Composition on the full lattice module

For one fixed positive integral lattice, the chosen-basis matrix, orthonormal
frame matrix, and oscillator matrix respect composition. Frame cancellation is
proved using the upstream positive-definite frame invertibility theorem.
`fockMap_comp` and the spanning elementary lattice states then give composition
on the full infinite lattice module, for arbitrary integral linear maps and
scalar phases.

**Right-action convention:** if `f` acts by `R` and `g` acts by `S`, their product
`RS` acts by `g.comp f`. Consequently `Φ_RS = Φ_S ∘ Φ_R`, and its explicit phase
equation is `u_RS(x) = u_R(x) * u_S(f x)`. The last theorem assumes this actual
explicit-phase equation and proves that the single global `τ` preserves it.
No phase equation or frame invertibility is assumed as a conclusion.

This module stops at equality of the full linear maps. Their packaging as
conformal automorphisms is in `CocycleTransport`; no group-action, concrete KRR,
unitarity, or orbifold result is asserted here. The separate local-bridge stage
must check this module; a dependency-only audit does not certify it.
-/

set_option autoImplicit false

noncomputable section

namespace BarnesWall

open VOA VOA.IntegralLattice VOA.LatGen

variable (L : VOA.IntegralLattice)

/-- The real chosen-basis matrix respects ordinary function composition. -/
theorem latMatrix_comp (f g : L.carrier →ₗ[ℤ] L.carrier) :
    latMatrix L L (g.comp f) = latMatrix L L g * latMatrix L L f := by
  ext j i
  change coordR L (g (f (latticeBasis L i))) j =
    (latMatrix L L g * latMatrix L L f) j i
  rw [coordR_map L L g]
  rfl

/-- Cancellation of the middle chosen frame uses positive definiteness. -/
theorem frameMatrix_comp (hPos : L.PosDef) (f g : L.carrier →ₗ[ℤ] L.carrier) :
    frameMatrix L L (g.comp f) = frameMatrix L L g * frameMatrix L L f := by
  simp only [frameMatrix, latMatrix_comp L f g]
  symm
  calc
    (frame L * latMatrix L L g * (frame L)⁻¹) *
        (frame L * latMatrix L L f * (frame L)⁻¹) =
        frame L * latMatrix L L g * ((frame L)⁻¹ * frame L) *
          latMatrix L L f * (frame L)⁻¹ := by
      simp only [Matrix.mul_assoc]
    _ = frame L * (latMatrix L L g * latMatrix L L f) * (frame L)⁻¹ := by
      rw [Matrix.nonsing_inv_mul _ (frame_det_isUnit L hPos), Matrix.mul_one]
      simp only [Matrix.mul_assoc]

/-- Complexification and rank reindexing preserve the proved frame identity. -/
theorem oscMatrix_comp (hPos : L.PosDef) (f g : L.carrier →ₗ[ℤ] L.carrier) :
    oscMatrix L L (g.comp f) = oscMatrix L L g * oscMatrix L L f := by
  simp only [oscMatrix, frameMatrix_comp L hPos f g, Matrix.map_mul,
    Matrix.submatrix_mul_equiv]

/-- Composition holds on every state, not only on the pure lattice charges.
No phase compatibility or isometry assumption is needed for this linear identity. -/
theorem latMorphC_comp (hPos : L.PosDef) (f g : L.carrier →ₗ[ℤ] L.carrier)
    (c d : L.carrier → ℂ) :
    (latMorphC L L g d).comp (latMorphC L L f c) =
      latMorphC L L (g.comp f) (fun x => c x * d (f x)) := by
  refine LinearMap.ext_on_range (latStateGen_span L) fun q => ?_
  obtain ⟨p, α⟩ := q
  simp only [LinearMap.comp_apply, latMorphC_latStateGen, map_smul, smul_smul]
  rw [fockMap_comp, oscMatrix_comp L hPos f g]

/-- The global change of cocycle telescopes when the explicit phases compose.
The displayed equation for `w` is an honest input, not a result of this bridge. -/
theorem transportedPhase_comp
    (H : L.carrier →ₗ[ℤ] L.carrier →ₗ[ℤ] ℤ)
    (f g : L.carrier →ₗ[ℤ] L.carrier) (u v w : L.carrier → ℂ)
    (hcomp : ∀ x, w x = u x * v (f x)) (x : L.carrier) :
    transportedPhase L H (g.comp f) w x =
      transportedPhase L H f u x * transportedPhase L H g v (f x) := by
  simp only [transportedPhase, LinearMap.comp_apply, hcomp]
  field_simp [globalTau_ne_zero L H x, globalTau_ne_zero L H (f x)]

/-- Exact right-action composition after the single global cocycle change:
the lift of `RS` is the lift of `S` after the lift of `R`. -/
theorem transported_latMorphC_comp (hPos : L.PosDef)
    (H : L.carrier →ₗ[ℤ] L.carrier →ₗ[ℤ] ℤ)
    (f g : L.carrier →ₗ[ℤ] L.carrier) (u v w : L.carrier → ℂ)
    (hcomp : ∀ x, w x = u x * v (f x)) :
    latMorphC L L (g.comp f) (transportedPhase L H (g.comp f) w) =
      (latMorphC L L g (transportedPhase L H g v)).comp
        (latMorphC L L f (transportedPhase L H f u)) := by
  calc
    latMorphC L L (g.comp f) (transportedPhase L H (g.comp f) w) =
        latMorphC L L (g.comp f)
          (fun x => transportedPhase L H f u x * transportedPhase L H g v (f x)) :=
      congrArg (latMorphC L L (g.comp f))
        (funext (transportedPhase_comp L H f g u v w hcomp))
    _ = (latMorphC L L g (transportedPhase L H g v)).comp
        (latMorphC L L f (transportedPhase L H f u)) :=
      (latMorphC_comp L hPos f g (transportedPhase L H f u)
        (transportedPhase L H g v)).symm

end BarnesWall
