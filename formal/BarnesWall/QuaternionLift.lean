-- SPDX-License-Identifier: MIT
import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# The order-sixteen quaternion presentation

This module maps Mathlib's existing `QuaternionGroup 4` into an arbitrary group
from three explicit relations. The powers descend through `ZMod 8`; the four
normal-form multiplication rules are checked directly. Faithfulness uses the
additional condition that the fourth power of the first generator is nontrivial.
No matrix, lattice, or vertex-operator-algebra claim is assumed here.
-/

set_option autoImplicit false

noncomputable section

namespace BarnesWall.QuaternionLift

universe u

variable {G : Type u} [Group G]

private def cyclicAdd (A : G) (hA8 : A ^ 8 = 1) : ZMod 8 →+ Additive G :=
  ZMod.lift 8 ⟨(zpowersHom G A).toAdditiveRight, by
    change A ^ (8 : ℤ) = 1
    exact (zpow_natCast A 8).trans hA8⟩

private def cyclic (A : G) (hA8 : A ^ 8 = 1) (i : ZMod 8) : G :=
  (cyclicAdd A hA8 i).toMul

private theorem cyclic_zero (A : G) (hA8 : A ^ 8 = 1) :
    cyclic A hA8 0 = 1 :=
  congrArg Additive.toMul (map_zero (cyclicAdd A hA8))

private theorem cyclic_add (A : G) (hA8 : A ^ 8 = 1) (i j : ZMod 8) :
    cyclic A hA8 (i + j) = cyclic A hA8 i * cyclic A hA8 j :=
  congrArg Additive.toMul (map_add (cyclicAdd A hA8) i j)

private theorem cyclic_neg (A : G) (hA8 : A ^ 8 = 1) (i : ZMod 8) :
    cyclic A hA8 (-i) = (cyclic A hA8 i)⁻¹ :=
  congrArg Additive.toMul (map_neg (cyclicAdd A hA8) i)

private theorem cyclic_intCast (A : G) (hA8 : A ^ 8 = 1) (k : ℤ) :
    cyclic A hA8 (k : ZMod 8) = A ^ k := by
  simp only [cyclic, cyclicAdd, ZMod.lift_coe]
  rfl

private theorem cyclic_natCast (A : G) (hA8 : A ^ 8 = 1) (k : ℕ) :
    cyclic A hA8 (k : ZMod 8) = A ^ k := by
  simpa only [Int.cast_natCast, zpow_natCast] using cyclic_intCast A hA8 (k : ℤ)

private theorem cyclic_mul_B (A B : G) (hA8 : A ^ 8 = 1)
    (hconj : A * B = B * A⁻¹) (i : ZMod 8) :
    cyclic A hA8 i * B = B * cyclic A hA8 (-i) := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
  rw [cyclic_neg, cyclic_intCast]
  have h : SemiconjBy B A⁻¹ A := hconj.symm
  have hk := h.zpow_right k
  change B * (A⁻¹) ^ k = A ^ k * B at hk
  simpa only [inv_zpow] using hk.symm

/-- The three stated relations define a homomorphism from Mathlib's `Q16`.
The source generators `a 1` and `xa 0` map to `A` and `B`, respectively. -/
def ofRelations (A B : G) (hA8 : A ^ 8 = 1) (hB2 : B ^ 2 = A ^ 4)
    (hconj : A * B = B * A⁻¹) : QuaternionGroup 4 →* G where
  toFun
    | .a i => cyclic A hA8 i
    | .xa i => B * cyclic A hA8 i
  map_one' := cyclic_zero A hA8
  map_mul' := by
    rintro (i | i) (j | j)
    · exact cyclic_add A hA8 i j
    · change B * cyclic A hA8 (j - i) =
        cyclic A hA8 i * (B * cyclic A hA8 j)
      rw [← mul_assoc, cyclic_mul_B A B hA8 hconj, mul_assoc, ← cyclic_add]
      rw [sub_eq_add_neg, add_comm j (-i)]
    · change B * cyclic A hA8 (i + j) =
        (B * cyclic A hA8 i) * cyclic A hA8 j
      rw [cyclic_add, mul_assoc]
    · change cyclic A hA8 ((4 : ZMod 8) + j - i) =
        (B * cyclic A hA8 i) * (B * cyclic A hA8 j)
      symm
      calc
        (B * cyclic A hA8 i) * (B * cyclic A hA8 j) =
            B * (cyclic A hA8 i * B) * cyclic A hA8 j := by
              simp only [mul_assoc]
        _ = B * (B * cyclic A hA8 (-i)) * cyclic A hA8 j := by
              rw [cyclic_mul_B A B hA8 hconj]
        _ = (B * B) * (cyclic A hA8 (-i) * cyclic A hA8 j) := by
              simp only [mul_assoc]
        _ = cyclic A hA8 4 * cyclic A hA8 (-i + j) := by
              rw [← pow_two, hB2, ← cyclic_natCast A hA8 4, ← cyclic_add]
              rw [Nat.cast_ofNat]
        _ = cyclic A hA8 (4 + (-i + j)) := (cyclic_add A hA8 4 (-i + j)).symm
        _ = cyclic A hA8 (4 + j - i) := by
              congr 1
              rw [sub_eq_add_neg, add_assoc, add_comm (-i) j]

@[simp] theorem ofRelations_a_natCast (A B : G) (hA8 : A ^ 8 = 1)
    (hB2 : B ^ 2 = A ^ 4) (hconj : A * B = B * A⁻¹) (k : ℕ) :
    ofRelations A B hA8 hB2 hconj (.a k) = A ^ k :=
  cyclic_natCast A hA8 k

@[simp] theorem ofRelations_a_one (A B : G) (hA8 : A ^ 8 = 1)
    (hB2 : B ^ 2 = A ^ 4) (hconj : A * B = B * A⁻¹) :
    ofRelations A B hA8 hB2 hconj (.a 1) = A := by
  simpa only [Nat.cast_one, pow_one] using
    ofRelations_a_natCast A B hA8 hB2 hconj 1

@[simp] theorem ofRelations_a_two (A B : G) (hA8 : A ^ 8 = 1)
    (hB2 : B ^ 2 = A ^ 4) (hconj : A * B = B * A⁻¹) :
    ofRelations A B hA8 hB2 hconj (.a 2) = A ^ 2 :=
  ofRelations_a_natCast A B hA8 hB2 hconj 2

@[simp] theorem ofRelations_a_four (A B : G) (hA8 : A ^ 8 = 1)
    (hB2 : B ^ 2 = A ^ 4) (hconj : A * B = B * A⁻¹) :
    ofRelations A B hA8 hB2 hconj (.a 4) = A ^ 4 :=
  ofRelations_a_natCast A B hA8 hB2 hconj 4

@[simp] theorem ofRelations_xa_zero (A B : G) (hA8 : A ^ 8 = 1)
    (hB2 : B ^ 2 = A ^ 4) (hconj : A * B = B * A⁻¹) :
    ofRelations A B hA8 hB2 hconj (.xa 0) = B := by
  change B * cyclic A hA8 0 = B
  rw [cyclic_zero, mul_one]

private theorem cyclic_injective (A : G) (hA8 : A ^ 8 = 1)
    (hA4 : A ^ 4 ≠ 1) : Function.Injective (cyclic A hA8) := by
  have horder : orderOf A = 8 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime_pow (p := 2) (n := 2) hA4 hA8
  have h : Function.Injective (cyclicAdd A hA8) := by
    unfold cyclicAdd
    apply (ZMod.lift_injective 8).mpr
    intro m hm
    change A ^ m = 1 at hm
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd m 8).mpr
    rw [← horder]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hm
  exact fun _ _ hij => h hij

/-- Nontriviality of `A^4` makes the presentation homomorphism faithful.
The cyclic part has exact order eight; an `xa` element cannot lie in the
kernel, because its square maps to `A^4`. -/
theorem ofRelations_injective (A B : G) (hA8 : A ^ 8 = 1)
    (hB2 : B ^ 2 = A ^ 4) (hconj : A * B = B * A⁻¹)
    (hA4 : A ^ 4 ≠ 1) : Function.Injective (ofRelations A B hA8 hB2 hconj) := by
  apply (injective_iff_map_eq_one (ofRelations A B hA8 hB2 hconj)).mpr
  rintro (i | i) hi
  · have hz : i = 0 := cyclic_injective A hA8 hA4
        (hi.trans (cyclic_zero A hA8).symm)
    simp only [hz, QuaternionGroup.a_zero]
  · exfalso
    apply hA4
    calc
      A ^ 4 = ofRelations A B hA8 hB2 hconj (QuaternionGroup.a 4) :=
        (ofRelations_a_four A B hA8 hB2 hconj).symm
      _ = ofRelations A B hA8 hB2 hconj ((QuaternionGroup.xa i) ^ 2) := by
        rw [QuaternionGroup.xa_sq, Nat.cast_ofNat]
      _ = (ofRelations A B hA8 hB2 hconj (QuaternionGroup.xa i)) ^ 2 := map_pow _ _ _
      _ = 1 := by rw [hi, one_pow]

end BarnesWall.QuaternionLift
