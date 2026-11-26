/-
SPDX-License-Identifier: Apache-2.0

The automorphism-wrapper portion is adapted from Fedor K. Popov's
VOA/Moonshine/MoonshineLRLiftLattice.lean:
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see ../LICENSE-Apache-2.0.txt.

This adaptation generalizes the Leech-specific wrapper to an arbitrary positive
even integral lattice and a supplied compatible phase. The global cocycle
transport and the accompanying bridge lemmas are additions in this repository.
-/
import VOA.Moonshine.LatticeMorph

/-!
# A global cocycle change and conformal lattice automorphisms

This is a generic bridge to `Fedor-Popov/Lean_VOA` at
`faedf8eb9e3fe275d3ac09e645aac694e496e965`. It does not construct the Barnes--Wall
lattice, prove a KRR phase formula, or establish a group action or orbifold result.

For an integral bilinear form `H` whose symmetrization is the lattice form, one
global `globalTau` compares the explicit sign cocycle with the library cocycle.
It then transports a supplied compatible phase. A separate wrapper packages an
integral isometry **equivalence** and a compatible nonzero phase as a conformal
automorphism of the full lattice VOA. Equal rank is not used as a substitute for
integral surjectivity.

The automorphism wrapper follows Fedor K. Popov's Leech-specific `latMorphAut` in
`VOA/Moonshine/MoonshineLRLiftLattice.lean` at the above pin (Apache-2.0 source).
Only `LatticeMorph` is imported here. Composition laws are deliberately deferred.

These declarations are checked by the separate local-bridge stage; the dependency
audit alone does not certify them. No unitary/Hermitian structure is asserted by
`VOA.Aut`.
-/

set_option autoImplicit false

noncomputable section

namespace BarnesWall

open VOA VOA.IntegralLattice VOA.LatGen

section Transport

variable (L : VOA.IntegralLattice) (H : L.carrier →ₗ[ℤ] L.carrier →ₗ[ℤ] ℤ)

/-- The sign cocycle in the supplied integral coordinates. -/
def explicitCocycle (x y : L.carrier) : ℂ := (-1 : ℂ) ^ (H x y)

theorem explicitCocycle_ne_zero (x y : L.carrier) :
    explicitCocycle L H x y ≠ 0 :=
  zpow_ne_zero _ (by norm_num)

/-- The sign is library exponent minus explicit exponent. -/
def transportDiscrepancy : L.carrier →ₗ[ℤ] L.carrier →ₗ[ℤ] ℤ := cocForm L - H

theorem transportDiscrepancy_symm_even (hEven : L.Even)
    (hH : ∀ x y, H x y + H y x = L.form x y) (x y : L.carrier) :
    2 ∣ transportDiscrepancy L H x y + transportDiscrepancy L H y x := by
  apply two_dvd_of_neg_one_zpow_eq_one
  have h := neg_one_zpow_cocForm_comm L hEven x y
  simp only [transportDiscrepancy, LinearMap.sub_apply]
  rw [show cocForm L x y - H x y + (cocForm L y x - H y x) =
      (cocForm L x y + cocForm L y x) - (H x y + H y x) by ring,
    zpow_sub₀ (by norm_num), h, hH,
    div_self (zpow_ne_zero _ (by norm_num))]

/-- A single global change of cocycle, independent of an isometry or group word. -/
def globalTau (x : L.carrier) : ℂ :=
  cobSign (latticeBasis L) (transportDiscrepancy L H) x

@[simp] theorem globalTau_zero : globalTau L H 0 = 1 :=
  cobSign_zero (latticeBasis L) (transportDiscrepancy L H)

theorem globalTau_ne_zero (x : L.carrier) : globalTau L H x ≠ 0 :=
  cobSign_ne_zero (latticeBasis L) (transportDiscrepancy L H) x

@[simp] theorem globalTau_neg (x : L.carrier) :
    globalTau L H (-x) = globalTau L H x :=
  cobSign_neg (latticeBasis L) (transportDiscrepancy L H) x

theorem globalTau_add (hEven : L.Even)
    (hH : ∀ x y, H x y + H y x = L.form x y) (x y : L.carrier) :
    globalTau L H (x + y) = globalTau L H x * globalTau L H y *
      (-1 : ℂ) ^ (transportDiscrepancy L H x y) :=
  cobSign_add (latticeBasis L) (transportDiscrepancy L H)
    (transportDiscrepancy_symm_even L H hEven hH) x y

/-- The exact global transport identity; it is proved from `H + Hᵀ = form`. -/
theorem globalTau_cocycle (hEven : L.Even)
    (hH : ∀ x y, H x y + H y x = L.form x y) (x y : L.carrier) :
    latticeCocycle L x y * (globalTau L H x * globalTau L H y) =
      explicitCocycle L H x y * globalTau L H (x + y) := by
  have hsign : explicitCocycle L H x y *
      (-1 : ℂ) ^ (transportDiscrepancy L H x y) = latticeCocycle L x y := by
    rw [explicitCocycle, ← zpow_add₀ (by norm_num), latticeCocycle_eq_zpow]
    congr 1
    change H x y + (cocForm L x y - H x y) = cocForm L x y
    ring
  rw [globalTau_add L H hEven hH, ← hsign]
  ring

/-- The transported phase for an integral linear map, using the same global `τ`. -/
def transportedPhase (ι : L.carrier →ₗ[ℤ] L.carrier) (u : L.carrier → ℂ)
    (x : L.carrier) : ℂ :=
  u x * globalTau L H (ι x) / globalTau L H x

theorem transportedPhase_zero (ι : L.carrier →ₗ[ℤ] L.carrier)
    (u : L.carrier → ℂ) (hu0 : u 0 = 1) : transportedPhase L H ι u 0 = 1 := by
  simp [transportedPhase, hu0]

theorem transportedPhase_ne_zero (ι : L.carrier →ₗ[ℤ] L.carrier)
    (u : L.carrier → ℂ) (hune : ∀ x, u x ≠ 0) (x : L.carrier) :
    transportedPhase L H ι u x ≠ 0 :=
  div_ne_zero (mul_ne_zero (hune x) (globalTau_ne_zero L H (ι x)))
    (globalTau_ne_zero L H x)

theorem transportedPhase_neg (ι : L.carrier →ₗ[ℤ] L.carrier)
    (u : L.carrier → ℂ) (huneg : ∀ x, u (-x) = u x) (x : L.carrier) :
    transportedPhase L H ι u (-x) = transportedPhase L H ι u x := by
  simp only [transportedPhase, map_neg, globalTau_neg, huneg]

/-- Transport an explicit-cocycle phase identity to the library's exact premise.
No isometry, normalization, or nonvanishing of `u` is needed for this identity. -/
theorem transportedPhase_cocycle (hEven : L.Even)
    (hH : ∀ x y, H x y + H y x = L.form x y)
    (ι : L.carrier →ₗ[ℤ] L.carrier) (u : L.carrier → ℂ)
    (hu : ∀ x y, explicitCocycle L H (ι x) (ι y) * (u x * u y) =
      explicitCocycle L H x y * u (x + y)) (x y : L.carrier) :
    latticeCocycle L (ι x) (ι y) *
        (transportedPhase L H ι u x * transportedPhase L H ι u y) =
      latticeCocycle L x y * transportedPhase L H ι u (x + y) := by
  have hx := globalTau_ne_zero L H x
  have hy := globalTau_ne_zero L H y
  have hxy := globalTau_ne_zero L H (x + y)
  have hi : latticeCocycle L (ι x) (ι y) *
      (globalTau L H (ι x) * globalTau L H (ι y)) =
      explicitCocycle L H (ι x) (ι y) * globalTau L H (ι (x + y)) := by
    simpa only [map_add] using globalTau_cocycle L H hEven hH (ι x) (ι y)
  have hbase : explicitCocycle L H x y =
      latticeCocycle L x y * (globalTau L H x * globalTau L H y) /
        globalTau L H (x + y) :=
    (eq_div_iff hxy).2 (globalTau_cocycle L H hEven hH x y).symm
  simp only [transportedPhase]
  calc
    latticeCocycle L (ι x) (ι y) *
        (u x * globalTau L H (ι x) / globalTau L H x *
          (u y * globalTau L H (ι y) / globalTau L H y)) =
        (latticeCocycle L (ι x) (ι y) *
          (globalTau L H (ι x) * globalTau L H (ι y))) * (u x * u y) /
            (globalTau L H x * globalTau L H y) := by
      field_simp [hx, hy] <;> ring
    _ = (explicitCocycle L H (ι x) (ι y) * (u x * u y)) *
        globalTau L H (ι (x + y)) / (globalTau L H x * globalTau L H y) := by
      rw [hi]
      ring
    _ = (explicitCocycle L H x y * u (x + y)) *
        globalTau L H (ι (x + y)) / (globalTau L H x * globalTau L H y) := by
      rw [hu]
    _ = latticeCocycle L x y *
        (u (x + y) * globalTau L H (ι (x + y)) / globalTau L H (x + y)) := by
      rw [hbase]
      field_simp [hx, hy, hxy] <;> ring

end Transport

section Automorphisms

variable (L : VOA.IntegralLattice)

/-- Surjectivity uses the integral equivalence, not merely equality of ranks. -/
theorem latMorphC_surjective (hPos : L.PosDef)
    (e : L.carrier ≃ₗ[ℤ] L.carrier)
    (he : ∀ x y, L.form (e x) (e y) = L.form x y)
    (c : L.carrier → ℂ) (hcne : ∀ x, c x ≠ 0) :
    Function.Surjective (latMorphC L L e.toLinearMap c) := by
  intro x
  have hx : x ∈ LinearMap.range (latMorphC L L e.toLinearMap c) :=
    (mem_range_latMorphC_iff L L e.toLinearMap c hcne hPos he hPos rfl x).mpr
      (fun γ hγ => False.elim (hγ ⟨e.symm γ, e.apply_symm_apply γ⟩))
  exact hx

/-- A genuine conformal automorphism for a normalized nonzero compatible phase.
The VOA is the upstream full infinite lattice VOA, not a weight truncation. -/
def latticeAutOfPhase (hEven : L.Even) (hPos : L.PosDef)
    (e : L.carrier ≃ₗ[ℤ] L.carrier)
    (he : ∀ x y, L.form (e x) (e y) = L.form x y)
    (c : L.carrier → ℂ) (hc0 : c 0 = 1)
    (hcoc : ∀ x y, latticeCocycle L (e x) (e y) * (c x * c y) =
      latticeCocycle L x y * c (x + y))
    (hcne : ∀ x, c x ≠ 0) : Aut (latticeVOAGen L hEven hPos) where
  toLinearEquiv := LinearEquiv.ofBijective (latMorphC L L e.toLinearMap c)
    ⟨latMorphC_injective L L e.toLinearMap c hcne hPos he hPos rfl,
      latMorphC_surjective L hPos e he c hcne⟩
  map_smul' u n v :=
    (latMorphC_isVOAHom L L e.toLinearMap c hc0 hcoc hPos hPos he hEven hEven).map_smul
      u n v
  map_vacuum := latMorphC_vacuum L L e.toLinearMap c hc0
  map_omega := latMorphC_omega L L e.toLinearMap c hc0 hPos hPos he rfl

@[simp] theorem latticeAutOfPhase_apply (hEven : L.Even) (hPos : L.PosDef)
    (e : L.carrier ≃ₗ[ℤ] L.carrier)
    (he : ∀ x y, L.form (e x) (e y) = L.form x y)
    (c : L.carrier → ℂ) (hc0 : c 0 = 1)
    (hcoc : ∀ x y, latticeCocycle L (e x) (e y) * (c x * c y) =
      latticeCocycle L x y * c (x + y))
    (hcne : ∀ x, c x ≠ 0) (v : LatModuleGen L) :
    latticeAutOfPhase L hEven hPos e he c hc0 hcoc hcne v =
      latMorphC L L e.toLinearMap c v := rfl

/-- End-to-end generic construction from an explicit-cocycle phase.
The explicit phase identity remains an honest input; no KRR matrix identity is
assumed to have been established by this bridge. -/
def transportedAut (H : L.carrier →ₗ[ℤ] L.carrier →ₗ[ℤ] ℤ)
    (hEven : L.Even) (hPos : L.PosDef)
    (hH : ∀ x y, H x y + H y x = L.form x y)
    (e : L.carrier ≃ₗ[ℤ] L.carrier)
    (he : ∀ x y, L.form (e x) (e y) = L.form x y)
    (u : L.carrier → ℂ) (hu0 : u 0 = 1)
    (hu : ∀ x y, explicitCocycle L H (e x) (e y) * (u x * u y) =
      explicitCocycle L H x y * u (x + y))
    (hune : ∀ x, u x ≠ 0) : Aut (latticeVOAGen L hEven hPos) :=
  latticeAutOfPhase L hEven hPos e he (transportedPhase L H e.toLinearMap u)
    (transportedPhase_zero L H e.toLinearMap u hu0)
    (transportedPhase_cocycle L H hEven hH e.toLinearMap u hu)
    (transportedPhase_ne_zero L H e.toLinearMap u hune)

end Automorphisms

end BarnesWall
