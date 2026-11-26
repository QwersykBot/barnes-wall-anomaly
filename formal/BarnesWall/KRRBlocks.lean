/-
SPDX-License-Identifier: Apache-2.0

The block labels retain the four low numerical bits in the ordered KRR basis.
-/
import BarnesWall.Lattice128

set_option autoImplicit false

noncomputable section

namespace BarnesWall.KRRBlocks

open BarnesWall.Lattice128

/-- Tensor positions 1--3 may vary; positions 4--7 give the block label. -/
def block (i : Index) : Fin 16 := ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩

theorem block_val (i : Index) : (block i).val = i.val % 16 := rfl

theorem block_eq_iff (i j : Index) :
    block i = block j ↔ i.val % 16 = j.val % 16 := by
  constructor
  · exact congrArg Fin.val
  · intro h
    apply Fin.ext
    exact h

theorem block_surjective : Function.Surjective block := by
  intro b
  let i : Index := ⟨b.val, by have hb := b.isLt; omega⟩
  refine ⟨i, ?_⟩
  apply Fin.ext
  exact Nat.mod_eq_of_lt b.isLt

/-- Equal block labels give equal bits at each of the four fixed positions. -/
theorem low_testBit_eq {i j : Index} (h : block i = block j)
    {a : ℕ} (ha : a < 4) : i.val.testBit a = j.val.testBit a := by
  have hm : i.val % 16 = j.val % 16 := (block_eq_iff i j).mp h
  have hi : (i.val % 16).testBit a = i.val.testBit a := by
    simpa [ha] using Nat.testBit_mod_two_pow i.val 4 a
  have hj : (j.val % 16).testBit a = j.val.testBit a := by
    simpa [ha] using Nat.testBit_mod_two_pow j.val 4 a
  rw [← hi, ← hj, hm]

theorem mem_support_low_iff {i j : Index} (h : block i = block j)
    {a : ℕ} (ha : a < 4) : a ∈ support i ↔ a ∈ support j := by
  simp only [support, List.mem_toFinset, Nat.mem_bitIndices]
  rw [low_testBit_eq h ha]

/-- The differing bit positions lie among 4, 5, 6; there is no pair enumeration. -/
theorem support_difference_subset {i j : Index} (h : block i = block j) :
    (support i ∪ support j) \ (support i ∩ support j) ⊆
      Finset.range 7 \ Finset.range 4 := by
  intro a ha
  obtain ⟨hu, hn⟩ := Finset.mem_sdiff.mp ha
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · rcases Finset.mem_union.mp hu with hi | hj
    · exact support_subset_range i hi
    · exact support_subset_range j hj
  · intro hl
    have he := mem_support_low_iff h (Finset.mem_range.mp hl)
    apply hn
    rcases Finset.mem_union.mp hu with hi | hj
    · exact Finset.mem_inter.mpr ⟨hi, he.mp hi⟩
    · exact Finset.mem_inter.mpr ⟨he.mpr hj, hj⟩

theorem support_union_card_le {i j : Index} (h : block i = block j) :
    (support i ∪ support j).card ≤ (support i ∩ support j).card + 3 := by
  have hd := Finset.card_le_card (support_difference_subset h)
  have hr : (Finset.range 7 \ Finset.range 4).card = 3 := by
    rw [Finset.card_sdiff_of_subset (Finset.range_mono (by decide : 4 ≤ 7))]
    rfl
  rw [hr] at hd
  have hs : support i ∩ support j ⊆ support i ∪ support j :=
    Finset.inter_subset_left.trans Finset.subset_union_left
  have hc := Finset.card_sdiff_add_card_eq_card hs
  omega

/-- Three varying bits force the numerator Gram exponent to be at least six. -/
theorem gramPower_ge_six_of_same_block {i j : Index} (h : block i = block j) :
    6 ≤ gramPower i j := by
  have hi := halfPower_identity i
  have hj := halfPower_identity j
  have hu := support_union_card_le h
  have hc := Finset.card_union_add_card_inter (support i) (support j)
  unfold gramPower
  omega

theorem four_dvd_G_of_same_block {i j : Index} (h : block i = block j) :
    (4 : ℤ) ∣ G i j := by
  have hg := gramPower_ge_six_of_same_block h
  have he : gramPower i j - 4 = 2 + (gramPower i j - 6) := by omega
  refine ⟨(2 : ℤ) ^ (gramPower i j - 6), ?_⟩
  unfold G
  rw [he, pow_add]
  norm_num

/-- The prescribed half-Gram matrix is in fact divisible by four in each block. -/
theorem four_dvd_H_of_same_block {i j : Index} (h : block i = block j) :
    (4 : ℤ) ∣ H i j := by
  by_cases hlt : j < i
  · simpa [H, hlt] using four_dvd_G_of_same_block h
  by_cases heq : i = j
  · refine ⟨(2 : ℤ) ^ parity i, ?_⟩
    simp [H, heq, pow_add]
  · simp [H, hlt, heq]

theorem H_even_of_same_block {i j : Index} (h : block i = block j) :
    Even (H i j) := by
  exact even_iff_two_dvd.mpr
    ((by decide : (2 : ℤ) ∣ 4).trans (four_dvd_H_of_same_block h))

end BarnesWall.KRRBlocks
