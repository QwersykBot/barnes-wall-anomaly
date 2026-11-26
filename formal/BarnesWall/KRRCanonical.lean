/-
SPDX-License-Identifier: Apache-2.0
See ../LICENSE-Apache-2.0.txt.
-/
import BarnesWall.CanonicalFaithfulness
import BarnesWall.KRRBlocks

/-!
# Canonical full-state lifts for the concrete ordered KRR128 lattice

The coordinate equivalence is the identity on `Fin 128 → ℤ`. The Gram matrix,
half-Gram matrix, evenness and positivity are the checked concrete definitions
and theorems of `Lattice128`. The fixed block labels are those of `KRRBlocks`.

`lift` accepts an actual integral matrix unit and a proof of preservation of G.
Composition is derived when the two matrices have the proved block-support
premise; its order is reversed because matrices act on coordinates from the
right. Equality of full maps recovers the matrices through the separate
charge-state faithfulness adapter.

This source-only specialization requires combined CI. It introduces no
subgroup, concrete Q16 relation, or agreement claim for a prescribed lift.
-/

set_option autoImplicit false

noncomputable section

namespace BarnesWall.KRRCanonical

open Matrix VOA VOA.LatGen BarnesWall.Lattice128
open scoped Matrix

/-- The actual coordinate equivalence, with no change or permutation of basis. -/
def coordinates : lattice.carrier ≃ₗ[ℤ] Coordinates :=
  LinearEquiv.refl ℤ Coordinates

@[simp] theorem coordinates_apply (x : lattice.carrier) : coordinates x = x := rfl

/-- The exact Gram form of the concrete lattice in these identity coordinates. -/
theorem gram_in_coordinates (x y : lattice.carrier) :
    lattice.form x y = coordinates x ⬝ᵥ (G *ᵥ coordinates y) := by
  change Coordinates at x y
  change Matrix.toBilin' G x y = x ⬝ᵥ (G *ᵥ y)
  exact Matrix.toBilin'_apply' G x y

/-- The cocycle adapter uses the same prescribed ordered half-Gram form. -/
theorem canonicalHalfForm_eq :
    CanonicalLift.halfForm coordinates H = Lattice128.halfForm := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [CanonicalLift.halfForm_apply]
  change Coordinates at x y
  change x ⬝ᵥ (H *ᵥ y) = Matrix.toBilin' H x y
  exact (Matrix.toBilin'_apply' H x y).symm

/-- Support in the sixteen concrete low-four-bit blocks. -/
def BlockSupported (R : Matrix Index Index ℤ) : Prop :=
  ∀ i j, KRRBlocks.block i ≠ KRRBlocks.block j → R i j = 0

/-- The full complex-linear state map with the one global cocycle transport. -/
def liftMap (R : Matrix Index Index ℤ) : LatModuleGen lattice →ₗ[ℂ] LatModuleGen lattice :=
  CanonicalLift.liftMap coordinates H R

/-- An actual integral inverse and Gram preservation give a conformal automorphism. -/
def lift (R : (Matrix Index Index ℤ)ˣ)
    (hR : (R : Matrix Index Index ℤ) * G * (R : Matrix Index Index ℤ)ᵀ = G) :
    VOA.Aut (latticeVOAGen lattice lattice_even lattice_posDef) :=
  CanonicalLift.liftAut coordinates lattice_even lattice_posDef H G R
    gram_in_coordinates H_add_transpose hR

@[simp] theorem lift_apply (R : (Matrix Index Index ℤ)ˣ)
    (hR : (R : Matrix Index Index ℤ) * G * (R : Matrix Index Index ℤ)ᵀ = G)
    (v : LatModuleGen lattice) :
    lift R hR v = liftMap (R : Matrix Index Index ℤ) v := rfl

/-- The proved within-block evenness gives composition on all lattice-VOA states. -/
theorem liftMap_mul (R S : Matrix Index Index ℤ)
    (hRb : BlockSupported R) (hSb : BlockSupported S)
    (hR : R * G * Rᵀ = G) (hS : S * G * Sᵀ = G) :
    liftMap (R * S) = (liftMap S).comp (liftMap R) :=
  CanonicalLift.liftMap_mul coordinates lattice_posDef H G R S
    (block := KRRBlocks.block) H_add_transpose
    (fun _ _ h => KRRBlocks.H_even_of_same_block h) hRb hSb hR hS

/-- The same right-action composition holds for the conformal automorphisms. -/
theorem lift_mul (R S : (Matrix Index Index ℤ)ˣ)
    (hRb : BlockSupported (R : Matrix Index Index ℤ))
    (hSb : BlockSupported (S : Matrix Index Index ℤ))
    (hR : (R : Matrix Index Index ℤ) * G * (R : Matrix Index Index ℤ)ᵀ = G)
    (hS : (S : Matrix Index Index ℤ) * G * (S : Matrix Index Index ℤ)ᵀ = G) :
    lift (R * S)
        (by simpa only [Units.val_mul] using
          CanonicalLift.matrix_isometry_mul G
            (R : Matrix Index Index ℤ) (S : Matrix Index Index ℤ) hR hS) =
      lift S hS * lift R hR :=
  CanonicalLift.liftAut_mul coordinates lattice_even lattice_posDef H G R S
    (block := KRRBlocks.block) gram_in_coordinates H_add_transpose
    (fun _ _ h => KRRBlocks.H_even_of_same_block h) hRb hSb hR hS

/-- Distinct integral matrices have distinct full state maps. -/
theorem liftMap_injective : Function.Injective liftMap :=
  CanonicalFaithfulness.liftMap_injective coordinates H

/-- Equality in the actual conformal automorphism group recovers the matrices. -/
theorem matrix_eq_of_lift_eq (R S : (Matrix Index Index ℤ)ˣ)
    (hR : (R : Matrix Index Index ℤ) * G * (R : Matrix Index Index ℤ)ᵀ = G)
    (hS : (S : Matrix Index Index ℤ) * G * (S : Matrix Index Index ℤ)ᵀ = G)
    (h : lift R hR = lift S hS) :
    (R : Matrix Index Index ℤ) = (S : Matrix Index Index ℤ) := by
  apply liftMap_injective
  apply LinearMap.ext
  intro v
  have hv := congrArg
    (fun F : VOA.Aut (latticeVOAGen lattice lattice_even lattice_posDef) => F v) h
  simpa only [lift_apply] using hv

end BarnesWall.KRRCanonical
