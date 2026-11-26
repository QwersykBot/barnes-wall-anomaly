/-
SPDX-License-Identifier: Apache-2.0
See ../LICENSE-Apache-2.0.txt.
-/
import BarnesWall.KRRPauli

/-!
# Blocks obtained by fixing the bits outside a small support

The elements of `s : Finset (Fin 7)` are numerical bit positions, with zero the
least significant bit. Equal block labels force all differing support positions
into `s.image Fin.val`. If `s.card ≤ 3`, the same concrete half-Gram matrix `H`
is divisible by four within each block, and hence even there.

The Pauli support statements hold for every finite `s`; their only premise is
membership of the active bit. This module constructs no lift or group action.
-/

set_option autoImplicit false

noncomputable section

namespace BarnesWall.KRRSupport

open Matrix BarnesWall.Lattice128

/-- Fix all numerical bits outside `s`, in the existing ordered coordinate basis. -/
def block (s : Finset (Fin 7)) (i : Index) : Finset ℕ :=
  support i \ s.image Fin.val

/-- A matrix preserves the blocks obtained by fixing the bits outside `s`. -/
def Supported (s : Finset (Fin 7)) (R : Matrix Index Index ℤ) : Prop :=
  ∀ i j, block s i ≠ block s j → R i j = 0

private theorem support_difference_subset {s : Finset (Fin 7)} {i j : Index}
    (h : block s i = block s j) :
    (support i ∪ support j) \ (support i ∩ support j) ⊆ s.image Fin.val := by
  intro a ha
  by_contra haS
  have hm : a ∈ block s i ↔ a ∈ block s j := by rw [h]
  have he : a ∈ support i ↔ a ∈ support j := by
    simpa [block, haS] using hm
  obtain ⟨hu, hn⟩ := Finset.mem_sdiff.mp ha
  apply hn
  rcases Finset.mem_union.mp hu with hi | hj
  · exact Finset.mem_inter.mpr ⟨hi, he.mp hi⟩
  · exact Finset.mem_inter.mpr ⟨he.mpr hj, hj⟩

private theorem support_union_card_le {s : Finset (Fin 7)} (hs : s.card ≤ 3)
    {i j : Index} (h : block s i = block s j) :
    (support i ∪ support j).card ≤ (support i ∩ support j).card + 3 := by
  have hd := Finset.card_le_card (support_difference_subset h)
  have himage : (s.image Fin.val).card ≤ s.card := by
    apply Finset.card_image_le
  have hsub : support i ∩ support j ⊆ support i ∪ support j :=
    Finset.inter_subset_left.trans Finset.subset_union_left
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  omega

private theorem gramPower_ge_six_of_same_block {s : Finset (Fin 7)}
    (hs : s.card ≤ 3) {i j : Index} (h : block s i = block s j) :
    6 ≤ gramPower i j := by
  have hi := halfPower_identity i
  have hj := halfPower_identity j
  have hu := support_union_card_le hs h
  have hc := Finset.card_union_add_card_inter (support i) (support j)
  unfold gramPower
  omega

private theorem four_dvd_G_of_same_block {s : Finset (Fin 7)}
    (hs : s.card ≤ 3) {i j : Index} (h : block s i = block s j) :
    (4 : ℤ) ∣ G i j := by
  have hg := gramPower_ge_six_of_same_block hs h
  have he : gramPower i j - 4 = 2 + (gramPower i j - 6) := by omega
  refine ⟨(2 : ℤ) ^ (gramPower i j - 6), ?_⟩
  unfold G
  rw [he, pow_add]
  norm_num

private theorem four_dvd_H_of_same_block {s : Finset (Fin 7)}
    (hs : s.card ≤ 3) {i j : Index} (h : block s i = block s j) :
    (4 : ℤ) ∣ H i j := by
  by_cases hlt : j < i
  · simpa [H, hlt] using four_dvd_G_of_same_block hs h
  by_cases heq : i = j
  · refine ⟨(2 : ℤ) ^ parity i, ?_⟩
    simp [H, heq, pow_add]
  · simp [H, hlt, heq]

/-- The unchanged prescribed half-Gram matrix is even on every small-support block. -/
theorem H_even_of_same_block {s : Finset (Fin 7)} (hs : s.card ≤ 3)
    {i j : Index} (h : block s i = block s j) : Even (H i j) := by
  exact even_iff_two_dvd.mpr
    ((show (2 : ℤ) ∣ 4 from ⟨2, rfl⟩).trans (four_dvd_H_of_same_block hs h))

private theorem block_toggle (s : Finset (Fin 7)) (k : Fin 7) (hk : k ∈ s)
    (i : Index) : block s (KRRPauli.toggle k i) = block s i := by
  apply Finset.ext
  intro a
  by_cases ha : a = k.val
  · subst a
    have hkimage : k.val ∈ s.image Fin.val := Finset.mem_image.mpr ⟨k, hk, rfl⟩
    simp [block, hkimage]
  · simp only [block, Finset.mem_sdiff, KRRPauli.mem_support_toggle_of_ne k i ha]

/-- The literal integral X rows preserve the block of every set containing their bit. -/
theorem X_supported (s : Finset (Fin 7)) (k : Fin 7) (hk : k ∈ s) :
    Supported s (KRRPauli.X k) := by
  intro i j h
  have hij : i ≠ j := fun heq => h (congrArg (block s) heq)
  have hfij : KRRPauli.toggle k i ≠ j := by
    intro heq
    exact h ((block_toggle s k hk i).symm.trans (congrArg (block s) heq))
  by_cases hi : k.val ∈ support i <;> simp [KRRPauli.X, hi, hij, hfij, eq_comm]

/-- The literal integral Z rows preserve the block of every set containing their bit. -/
theorem Z_supported (s : Finset (Fin 7)) (k : Fin 7) (hk : k ∈ s) :
    Supported s (KRRPauli.Z k) := by
  intro i j h
  have hij : i ≠ j := fun heq => h (congrArg (block s) heq)
  have hfij : KRRPauli.toggle k i ≠ j := by
    intro heq
    exact h ((block_toggle s k hk i).symm.trans (congrArg (block s) heq))
  by_cases hi : k.val ∈ support i <;> simp [KRRPauli.Z, hi, hij, hfij, eq_comm]

end BarnesWall.KRRSupport
