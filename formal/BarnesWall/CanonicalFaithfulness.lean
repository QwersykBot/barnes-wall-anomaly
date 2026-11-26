/-
SPDX-License-Identifier: Apache-2.0
See ../LICENSE-Apache-2.0.txt.
-/
import BarnesWall.CanonicalLift

/-!
# The full canonical lifts distinguish their integral matrices

The upstream charge projection is the actual `Finsupp.lapply` projection on
the lattice factor, followed by the tensor-product right-unit equivalence.
Its proved value on elementary lattice states distinguishes nonzero multiples
of distinct pure-charge states. The proved `latMorphC_latChargeGen` formula
therefore recovers the lattice linear map from the full state map.

For `CanonicalLift.liftMap`, nonvanishing is supplied by the existing canonical
phase and global cocycle-transport theorems. The actual coordinate equivalence
then recovers every matrix entry. No charge-preservation axiom, isometry,
positive-definiteness assumption, or group law is needed for this injectivity
statement. This source-only increment still requires the combined CI check.
-/

set_option autoImplicit false

noncomputable section

namespace BarnesWall.CanonicalFaithfulness

open Matrix VOA VOA.LatGen
open scoped Matrix

/-- Actual charge-coordinate extraction separates nonzero charged states. -/
theorem charge_eq_of_smul_eq (L : VOA.IntegralLattice)
    {α β : L.carrier} {c d : ℂ} (hc : c ≠ 0)
    (h : c • latChargeGen L α = d • latChargeGen L β) : α = β := by
  classical
  by_contra hne
  have hp := congrArg (coordEα L α) h
  simp only [map_smul, latChargeGen, coordEα_latStateGen,
    ite_eq_right hne, smul_zero, HeisenbergN.vacuumN] at hp
  rcases smul_eq_zero.mp hp with hzero | hone
  · exact hc hzero
  · exact one_ne_zero hone

/-- The full `latMorphC` map determines its lattice map when its phase is nonzero. -/
theorem latticeMap_eq_of_latMorphC_eq (L : VOA.IntegralLattice)
    (f g : L.carrier →ₗ[ℤ] L.carrier) (c d : L.carrier → ℂ)
    (hc : ∀ x, c x ≠ 0)
    (h : latMorphC L L f c = latMorphC L L g d) : f = g := by
  apply LinearMap.ext
  intro x
  have hx := congrArg
    (fun F : LatModuleGen L →ₗ[ℂ] LatModuleGen L => F (latChargeGen L x)) h
  simp only [latMorphC_latChargeGen] at hx
  exact charge_eq_of_smul_eq L (hc x) hx

variable {L : VOA.IntegralLattice} {ι : Type*} [Fintype ι] [LinearOrder ι]
variable (coords : L.carrier ≃ₗ[ℤ] (ι → ℤ))

omit [LinearOrder ι] in
/-- The supplied coordinate equivalence makes the right-matrix action faithful. -/
theorem rowMap_injective : Function.Injective (CanonicalLift.rowMap coords) := by
  intro R S h
  apply Matrix.ext_iff_vecMul.mpr
  intro v
  have hv := congrArg
    (fun f : L.carrier →ₗ[ℤ] L.carrier => coords (f (coords.symm v))) h
  simpa only [CanonicalLift.coords_rowMap, coords.apply_symm_apply] using hv

/-- Equality of the full canonical state maps implies equality of their matrices. -/
theorem liftMap_injective (H : Matrix ι ι ℤ) :
    Function.Injective (CanonicalLift.liftMap coords H) := by
  intro R S h
  apply rowMap_injective coords
  unfold CanonicalLift.liftMap at h
  apply latticeMap_eq_of_latMorphC_eq L _ _ _ _ ?_ h
  exact BarnesWall.transportedPhase_ne_zero L (CanonicalLift.halfForm coords H)
    (CanonicalLift.rowMap coords R) (CanonicalLift.phase coords H R)
    (CanonicalLift.phase_ne_zero coords H R)

end BarnesWall.CanonicalFaithfulness
