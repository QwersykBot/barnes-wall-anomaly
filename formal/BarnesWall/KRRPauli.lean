/-
SPDX-License-Identifier: Apache-2.0

The integral rows are Keller--Roberts--Roberts, arXiv:2411.13646v2,
Appendix A.2, equations (A.2.5)--(A.2.6). Numerical bit k is tensor
position 7-k. The Cartesian comparison uses the exact ordered basis B/4.
-/
import BarnesWall.KRRBlocks

set_option autoImplicit false

noncomputable section

namespace BarnesWall.KRRPauli

open Matrix BarnesWall.Lattice128
open scoped Matrix BigOperators

/-- Reconstruct an actual numerical index from its bounded binary support. -/
def indexOfSupport (s : Finset ℕ) (hs : s ⊆ Finset.range 7) : Index :=
  ⟨∑ a ∈ s, 2 ^ a, by
    have hle := Finset.sum_le_sum_of_subset (f := fun a : ℕ => 2 ^ a) hs
    have hsum : ∑ a ∈ Finset.range 7, (2 : ℕ) ^ a = 127 := by decide
    rw [hsum] at hle
    omega⟩

@[simp] theorem support_indexOfSupport (s : Finset ℕ) (hs : s ⊆ Finset.range 7) :
    support (indexOfSupport s hs) = s :=
  Finset.toFinset_bitIndices_sum_two_pow s

def toggleSupport (k : Fin 7) (s : Finset ℕ) : Finset ℕ :=
  if k.val ∈ s then s.erase k.val else insert k.val s

theorem toggleSupport_subset (k : Fin 7) (i : Index) :
    toggleSupport k (support i) ⊆ Finset.range 7 := by
  by_cases h : k.val ∈ support i
  · simpa only [toggleSupport, ite_eq_left h] using
      (Finset.erase_subset k.val (support i)).trans (support_subset_range i)
  · simp only [toggleSupport, ite_eq_right h, Finset.insert_subset_iff]
    exact ⟨Finset.mem_range.mpr k.isLt, support_subset_range i⟩

/-- Toggle numerical bit k, without changing the numerical order of the basis. -/
def toggle (k : Fin 7) (i : Index) : Index :=
  indexOfSupport (toggleSupport k (support i)) (toggleSupport_subset k i)

theorem support_toggle (k : Fin 7) (i : Index) :
    support (toggle k i) =
      if k.val ∈ support i then (support i).erase k.val else insert k.val (support i) := by
  simp only [toggle, support_indexOfSupport, toggleSupport]

@[simp] theorem mem_support_toggle_self (k : Fin 7) (i : Index) :
    k.val ∈ support (toggle k i) ↔ k.val ∉ support i := by
  by_cases h : k.val ∈ support i <;> simp [support_toggle, h]

theorem mem_support_toggle_of_ne (k : Fin 7) (i : Index) {a : ℕ} (h : a ≠ k.val) :
    a ∈ support (toggle k i) ↔ a ∈ support i := by
  by_cases hk : k.val ∈ support i <;> simp [support_toggle, hk, h]

@[simp] theorem toggle_toggle (k : Fin 7) (i : Index) : toggle k (toggle k i) = i := by
  apply support_injective
  apply Finset.ext
  intro a
  by_cases h : a = k.val
  · subst a
    simp only [mem_support_toggle_self, not_not]
  · rw [mem_support_toggle_of_ne k (toggle k i) h, mem_support_toggle_of_ne k i h]

theorem toggle_injective (k : Fin 7) : Function.Injective (toggle k) := by
  intro i j h
  have hh := congrArg (toggle k) h
  simpa only [toggle_toggle] using hh

theorem toggle_eq_iff (k : Fin 7) (i j : Index) :
    i = toggle k j ↔ j = toggle k i := by
  constructor <;> intro h
  · have hh := congrArg (toggle k) h
    simpa only [toggle_toggle] using hh.symm
  · have hh := congrArg (toggle k) h
    simpa only [toggle_toggle] using hh.symm

theorem card_support_toggle_of_mem (k : Fin 7) (i : Index) (h : k.val ∈ support i) :
    (support (toggle k i)).card + 1 = (support i).card := by
  rw [support_toggle, ite_eq_left h, Finset.card_erase_of_mem h]
  have hp : 0 < (support i).card := Finset.card_pos.mpr ⟨k.val, h⟩
  omega

theorem card_support_toggle_of_notMem (k : Fin 7) (i : Index) (h : k.val ∉ support i) :
    (support (toggle k i)).card = (support i).card + 1 := by
  rw [support_toggle, ite_eq_right h, Finset.card_insert_of_notMem h]

theorem parity_toggle (k : Fin 7) (i : Index) :
    parity i + parity (toggle k i) = 1 := by
  have hi := support_card_le i
  have hf := support_card_le (toggle k i)
  by_cases h : k.val ∈ support i
  · have hc := card_support_toggle_of_mem k i h
    dsimp [parity, zeros]
    omega
  · have hc := card_support_toggle_of_notMem k i h
    dsimp [parity, zeros]
    omega

theorem coefficient_halfPower (k : Fin 7) (i : Index) :
    (2 : ℤ) ^ parity i * 2 ^ halfPower (toggle k i) =
      if k.val ∈ support i then 2 * 2 ^ halfPower i else 2 ^ halfPower i := by
  have hi := halfPower_identity i
  have hf := halfPower_identity (toggle k i)
  have hp := parity_toggle k i
  by_cases h : k.val ∈ support i
  · have hc := card_support_toggle_of_mem k i h
    have he : parity i + halfPower (toggle k i) = halfPower i + 1 := by omega
    rw [ite_eq_left h, ← pow_add, he, pow_succ, mul_comm]
  · have hc := card_support_toggle_of_notMem k i h
    have he : parity i + halfPower (toggle k i) = halfPower i := by omega
    rw [ite_eq_right h, ← pow_add, he]

/-- The active numerical bits 4,5,6 leave KRR's low-four-bit label unchanged. -/
theorem block_toggle (k : Fin 7) (hk : 4 ≤ k.val) (i : Index) :
    KRRBlocks.block (toggle k i) = KRRBlocks.block i := by
  apply (KRRBlocks.block_eq_iff _ _).mpr
  apply Nat.eq_of_testBit_eq
  intro a
  change ((toggle k i).val % 2 ^ 4).testBit a = (i.val % 2 ^ 4).testBit a
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases ha : a < 4
  · have hne : a ≠ k.val := by omega
    have hm := mem_support_toggle_of_ne k i hne
    simp only [support, List.mem_toFinset, Nat.mem_bitIndices] at hm
    have hb : (toggle k i).val.testBit a = i.val.testBit a := by
      cases hleft : (toggle k i).val.testBit a <;>
        cases hright : i.val.testBit a <;> simp_all
    simp [ha, hb]
  · simp [ha]

/-- KRR's integral X row at numerical bit k. -/
def X (k : Fin 7) : Matrix Index Index ℤ := fun i =>
  if k.val ∈ support i then Pi.single i 1
  else -Pi.single i 1 + (2 : ℤ) ^ parity i • Pi.single (toggle k i) 1

/-- KRR's integral Z row at numerical bit k. -/
def Z (k : Fin 7) : Matrix Index Index ℤ := fun i =>
  if k.val ∈ support i then -Pi.single i 1 + (2 : ℤ) ^ parity i • Pi.single (toggle k i) 1
  else Pi.single i 1

/-- Cartesian bit-toggle permutation, acting on row vectors from the right. -/
def cartX (k : Fin 7) : Matrix Index Index ℤ := fun i j =>
  if i = toggle k j then 1 else 0

def cartSign (k : Fin 7) (i : Index) : ℤ := if k.val ∈ support i then -1 else 1

/-- Cartesian sign matrix. -/
def cartZ (k : Fin 7) : Matrix Index Index ℤ := Matrix.diagonal (cartSign k)

theorem X_mul_apply (k : Fin 7) (M : Matrix Index Index ℤ) (i j : Index) :
    (X k * M) i j = if k.val ∈ support i then M i j
      else -M i j + (2 : ℤ) ^ parity i * M (toggle k i) j := by
  have hrow : (X k * M).row i = if k.val ∈ support i then M.row i
      else -M.row i + (2 : ℤ) ^ parity i • M.row (toggle k i) := by
    change X k i ᵥ* M = _
    by_cases h : k.val ∈ support i
    · simp only [X, ite_eq_left h, Matrix.single_vecMul, one_smul]
    · simp only [X, ite_eq_right h, Matrix.add_vecMul, Matrix.neg_vecMul,
        Matrix.smul_vecMul, Matrix.single_vecMul, one_smul]
  have h := congrFun hrow j
  by_cases hi : k.val ∈ support i <;> simpa [hi] using h

theorem Z_mul_apply (k : Fin 7) (M : Matrix Index Index ℤ) (i j : Index) :
    (Z k * M) i j = if k.val ∈ support i
      then -M i j + (2 : ℤ) ^ parity i * M (toggle k i) j else M i j := by
  have hrow : (Z k * M).row i = if k.val ∈ support i
      then -M.row i + (2 : ℤ) ^ parity i • M.row (toggle k i) else M.row i := by
    change Z k i ᵥ* M = _
    by_cases h : k.val ∈ support i
    · simp only [Z, ite_eq_left h, Matrix.add_vecMul, Matrix.neg_vecMul,
        Matrix.smul_vecMul, Matrix.single_vecMul, one_smul]
    · simp only [Z, ite_eq_right h, Matrix.single_vecMul, one_smul]
  have h := congrFun hrow j
  by_cases hi : k.val ∈ support i <;> simpa [hi] using h

theorem mul_cartX_apply (k : Fin 7) (M : Matrix Index Index ℤ) (i j : Index) :
    (M * cartX k) i j = M i (toggle k j) := by
  simp [Matrix.mul_apply, cartX]

theorem mul_cartZ_apply (k : Fin 7) (M : Matrix Index Index ℤ) (i j : Index) :
    (M * cartZ k) i j = M i j * cartSign k j :=
  Matrix.mul_diagonal (cartSign k) M i j

private theorem subset_insert_iff_erase_subset (s t : Finset ℕ) (a : ℕ) :
    s ⊆ insert a t ↔ s.erase a ⊆ t := by
  constructor
  · intro h b hb
    obtain ⟨hne, hs⟩ := Finset.mem_erase.mp hb
    rcases Finset.mem_insert.mp (h hs) with heq | ht
    · exact (hne heq).elim
    · exact ht
  · intro h b hb
    by_cases heq : b = a
    · exact Finset.mem_insert.mpr (Or.inl heq)
    · exact Finset.mem_insert.mpr (Or.inr (h (Finset.mem_erase.mpr ⟨heq, hb⟩)))

private theorem subset_erase_iff_of_notMem (s t : Finset ℕ) (a : ℕ) (h : a ∉ s) :
    s ⊆ t.erase a ↔ s ⊆ t := by
  constructor
  · exact fun hs => hs.trans (Finset.erase_subset a t)
  · intro hs b hb
    refine Finset.mem_erase.mpr ⟨?_, hs hb⟩
    intro heq
    exact h (heq ▸ hb)

theorem toggle_subset_iff_of_mem (k : Fin 7) (i j : Index) (hi : k.val ∈ support i) :
    support (toggle k j) ⊆ support i ↔ support j ⊆ support i := by
  constructor
  · intro h a ha
    by_cases heq : a = k.val
    · simpa only [heq] using hi
    · exact h ((mem_support_toggle_of_ne k j heq).mpr ha)
  · intro h a ha
    by_cases heq : a = k.val
    · simpa only [heq] using hi
    · exact h ((mem_support_toggle_of_ne k j heq).mp ha)

theorem scaled_B_toggle_of_notMem (k : Fin 7) (i j : Index)
    (hi : k.val ∉ support i) :
    (2 : ℤ) ^ parity i * B (toggle k i) j =
      if (support j).erase k.val ⊆ support i then 2 ^ halfPower i else 0 := by
  have hw := coefficient_halfPower k i
  rw [ite_eq_right hi] at hw
  have hs := subset_insert_iff_erase_subset (support j) (support i) k.val
  by_cases h : (support j).erase k.val ⊆ support i
  · have hsub : support j ⊆ insert k.val (support i) := hs.mpr h
    simpa [B, support_toggle, hi, h, hsub] using hw
  · have hsub : ¬support j ⊆ insert k.val (support i) := fun hh => h (hs.mp hh)
    simp [B, support_toggle, hi, h, hsub]

/-- Exact change of basis for the source X rows, proved by sparse support identities. -/
theorem X_mul_B (k : Fin 7) : X k * B = B * cartX k := by
  funext i j
  rw [X_mul_apply, mul_cartX_apply]
  by_cases hi : k.val ∈ support i
  · rw [ite_eq_left hi]
    simp only [B, toggle_subset_iff_of_mem k i j hi]
  · rw [ite_eq_right hi, scaled_B_toggle_of_notMem k i j hi]
    by_cases hj : k.val ∈ support j
    · have hsub : ¬support j ⊆ support i := fun h => hi (h hj)
      simp [B, support_toggle, hj, hsub]
    · have hsub : ¬insert k.val (support j) ⊆ support i := by
        intro h
        exact hi (h (Finset.mem_insert_self _ _))
      simp [B, support_toggle, hj, hsub]

/-- Exact change of basis for the source Z rows. -/
theorem Z_mul_B (k : Fin 7) : Z k * B = B * cartZ k := by
  funext i j
  rw [Z_mul_apply, mul_cartZ_apply]
  by_cases hi : k.val ∈ support i
  · rw [ite_eq_left hi]
    have hw := coefficient_halfPower k i
    rw [ite_eq_left hi] at hw
    by_cases hj : k.val ∈ support j
    · have hsub : ¬support j ⊆ (support i).erase k.val := by
        intro h
        exact Finset.notMem_erase k.val (support i) (h hj)
      simp [B, support_toggle, hi, hsub, cartSign, hj]
    · have hs := subset_erase_iff_of_notMem (support j) (support i) k.val hj
      by_cases hsub : support j ⊆ support i
      · have herase := hs.mpr hsub
        simp only [B, support_toggle, ite_eq_left hi, ite_eq_left hsub, ite_eq_left herase,
          cartSign, ite_eq_right hj, mul_one]
        rw [hw]
        ring
      · have herase : ¬support j ⊆ (support i).erase k.val :=
          fun h => hsub (hs.mp h)
        simp [B, support_toggle, hi, hsub, herase, cartSign, hj]
  · rw [ite_eq_right hi]
    by_cases hj : k.val ∈ support j
    · have hsub : ¬support j ⊆ support i := fun h => hi (h hj)
      simp [B, hsub, cartSign, hj]
    · simp [cartSign, hj]

theorem cartX_transpose (k : Fin 7) : (cartX k)ᵀ = cartX k := by
  funext i j
  simp only [cartX, Matrix.transpose_apply, toggle_eq_iff k j i]

theorem cartX_sq (k : Fin 7) : cartX k * cartX k = 1 := by
  funext i j
  rw [mul_cartX_apply]
  simp [cartX, toggle_toggle, Matrix.one_apply]

theorem cartZ_transpose (k : Fin 7) : (cartZ k)ᵀ = cartZ k := by
  funext i j
  by_cases h : i = j
  · subst j
    rfl
  · simp [cartZ, Matrix.diagonal, h, Ne.symm h]

theorem cartZ_sq (k : Fin 7) : cartZ k * cartZ k = 1 := by
  rw [cartZ, Matrix.diagonal_mul_diagonal]
  have h : (fun i => cartSign k i * cartSign k i) = (fun _ => (1 : ℤ)) := by
    funext i
    by_cases hi : k.val ∈ support i <;> simp [cartSign, hi]
  rw [h, Matrix.diagonal_one]

/-- The integral numerator Gram identity transports a full Cartesian isometry. -/
theorem isometry_of_intertwining (R C : Matrix Index Index ℤ)
    (h : R * B = B * C) (hC : C * Cᵀ = 1) : R * G * Rᵀ = G := by
  have hscaled : (16 : ℤ) • (R * G * Rᵀ) = (16 : ℤ) • G := by
    calc
      (16 : ℤ) • (R * G * Rᵀ) = R * ((16 : ℤ) • G) * Rᵀ := by
        simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = (R * B) * (R * B)ᵀ := by
        rw [← B_mul_transpose]
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (B * C) * (B * C)ᵀ := by rw [h]
      _ = B * Bᵀ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc C Cᵀ Bᵀ, hC, Matrix.one_mul]
      _ = (16 : ℤ) • G := B_mul_transpose
  funext i j
  have he := congrFun (congrFun hscaled i) j
  change (16 : ℤ) * (R * G * Rᵀ) i j = 16 * G i j at he
  exact mul_left_cancel₀ (by decide : (16 : ℤ) ≠ 0) he

theorem X_isometry (k : Fin 7) : X k * G * (X k)ᵀ = G :=
  isometry_of_intertwining (X k) (cartX k) (X_mul_B k)
    (by rw [cartX_transpose, cartX_sq])

theorem Z_isometry (k : Fin 7) : Z k * G * (Z k)ᵀ = G :=
  isometry_of_intertwining (Z k) (cartZ k) (Z_mul_B k)
    (by rw [cartZ_transpose, cartZ_sq])

theorem mul_B_injective : Function.Injective (fun R : Matrix Index Index ℤ => R * B) := by
  intro R S h
  funext i
  have hrow : R i ᵥ* B = S i ᵥ* B := congrFun h i
  have hz : (R i - S i) ᵥ* B = 0 := by rw [Matrix.sub_vecMul, hrow, sub_self]
  exact sub_eq_zero.mp (Matrix.eq_zero_of_vecMul_eq_zero B_det_ne_zero hz)

theorem involution_of_intertwining (R C : Matrix Index Index ℤ)
    (h : R * B = B * C) (hC : C * C = 1) : R * R = 1 := by
  apply mul_B_injective
  calc
    (R * R) * B = R * (R * B) := Matrix.mul_assoc _ _ _
    _ = R * (B * C) := by rw [h]
    _ = (R * B) * C := (Matrix.mul_assoc _ _ _).symm
    _ = (B * C) * C := by rw [h]
    _ = B * (C * C) := Matrix.mul_assoc _ _ _
    _ = 1 * B := by rw [hC, Matrix.mul_one, Matrix.one_mul]

theorem X_sq (k : Fin 7) : X k * X k = 1 :=
  involution_of_intertwining (X k) (cartX k) (X_mul_B k) (cartX_sq k)

theorem Z_sq (k : Fin 7) : Z k * Z k = 1 :=
  involution_of_intertwining (Z k) (cartZ k) (Z_mul_B k) (cartZ_sq k)

/-- Both inverse equations hold over the integers. -/
def XUnit (k : Fin 7) : (Matrix Index Index ℤ)ˣ where
  val := X k
  inv := X k
  val_inv := X_sq k
  inv_val := X_sq k

def ZUnit (k : Fin 7) : (Matrix Index Index ℤ)ˣ where
  val := Z k
  inv := Z k
  val_inv := Z_sq k
  inv_val := Z_sq k

@[simp] theorem XUnit_val (k : Fin 7) : (XUnit k : Matrix Index Index ℤ) = X k := rfl
@[simp] theorem ZUnit_val (k : Fin 7) : (ZUnit k : Matrix Index Index ℤ) = Z k := rfl

theorem X_block_support (k : Fin 7) (hk : 4 ≤ k.val) (i j : Index)
    (h : KRRBlocks.block i ≠ KRRBlocks.block j) : X k i j = 0 := by
  have hij : i ≠ j := fun heq => h (congrArg KRRBlocks.block heq)
  have hfij : toggle k i ≠ j := by
    intro heq
    exact h ((block_toggle k hk i).symm.trans (congrArg KRRBlocks.block heq))
  by_cases hi : k.val ∈ support i <;> simp [X, hi, hij, hfij, eq_comm]

theorem Z_block_support (k : Fin 7) (hk : 4 ≤ k.val) (i j : Index)
    (h : KRRBlocks.block i ≠ KRRBlocks.block j) : Z k i j = 0 := by
  have hij : i ≠ j := fun heq => h (congrArg KRRBlocks.block heq)
  have hfij : toggle k i ≠ j := by
    intro heq
    exact h ((block_toggle k hk i).symm.trans (congrArg KRRBlocks.block heq))
  by_cases hi : k.val ∈ support i <;> simp [Z, hi, hij, hfij, eq_comm]

end BarnesWall.KRRPauli
