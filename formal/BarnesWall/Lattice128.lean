/-
SPDX-License-Identifier: Apache-2.0

The definitions specialize the ordered Barnes--Wall basis in Keller--Roberts--
Roberts, arXiv:2411.13646v2, Appendix A.1, to m = 7. The binary-support and
powerset arguments use Mathlib; the integral-lattice interface is due to
Fedor K. Popov and the LeanVOA contributors.
-/
import VOA.Foundations.Lattices
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Powerset
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Tactic.Ring.Basic
import Lean.Elab.Tactic.Omega

/-!
# The concrete ordered KRR lattice in dimension 128

The carrier is literally `Fin 128 → ℤ`, in its standard ordered basis.
`support i` consists of the numerical one-bit positions of `i`; numerical bit
`7-a` is tensor position `a` in KRR's order (positions numbered 1 through 7).

If `z = 7 - |support i|`, `p = z % 2`, and `t = (z+1)/2`, the nonzero entries
of the source's Cartesian basis row are `2^t / 4`. They occur exactly at the
subsets of `support i`. Thus `basisMatrix` is the exact rational matrix `B/4`.
The equality of its Gram matrix with the integral matrix `G` is proved below.

The proof of `B * Bᵀ = 16 • G` counts subsets of an intersection. There is no
flat enumeration of matrix coefficients. Lower triangularity and the nonzero
diagonal prove injectivity; a sum of squares then proves positive definiteness.
`H + Hᵀ = G` proves evenness and fixes the half-Gram form for later cocycle work.

This file makes no claims about unimodularity, minimum norm, isometries,
canonical phases, a quaternion subgroup, or an orbifold.
-/

set_option autoImplicit false

noncomputable section

namespace BarnesWall.Lattice128

open Matrix
open scoped Matrix BigOperators

abbrev Index := Fin 128
abbrev Coordinates := Index → ℤ

/-- The actual ordered integral coordinate basis, not LeanVOA's chosen basis. -/
def orderedBasis : Module.Basis Index ℤ Coordinates := Pi.basisFun ℤ Index

/-- Numerical bit positions, with position zero the least significant bit. -/
def support (i : Index) : Finset ℕ := i.val.bitIndices.toFinset

theorem support_sum (i : Index) : ∑ a ∈ support i, 2 ^ a = i.val :=
  Finset.sum_toFinset_bitIndices_two_pow i.val

theorem support_injective : Function.Injective support := by
  intro i j h
  apply Fin.ext
  exact Finset.equivBitIndices.injective h

theorem support_subset_range (i : Index) : support i ⊆ Finset.range 7 := by
  intro a ha
  have hp : 2 ^ a ≤ i.val :=
    Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp ha)
  apply Finset.mem_range.mpr
  by_contra hn
  have hseven : 7 ≤ a := Nat.le_of_not_gt hn
  have hpow : (2 : ℕ) ^ 7 ≤ 2 ^ a :=
    pow_le_pow_right₀ (by decide) hseven
  have hi : i.val < 128 := i.isLt
  norm_num at hpow
  omega

theorem support_card_le (i : Index) : (support i).card ≤ 7 := by
  simpa only [Finset.card_range] using Finset.card_le_card (support_subset_range i)

theorem index_le_of_support_subset {i j : Index} (h : support i ⊆ support j) :
    i ≤ j := by
  change i.val ≤ j.val
  calc
    i.val = ∑ a ∈ support i, 2 ^ a := (support_sum i).symm
    _ ≤ ∑ a ∈ support j, 2 ^ a := Finset.sum_le_sum_of_subset h
    _ = j.val := support_sum j

/-- The only closed finite arithmetic check in the combinatorial construction. -/
private theorem range_seven_sum : ∑ a ∈ Finset.range 7, (2 : ℕ) ^ a = 127 := by
  decide

/-- Restrict binary support to a powerset; this is a genuine bijective count. -/
theorem card_support_subsets (s : Finset ℕ) (hs : s ⊆ Finset.range 7) :
    (Finset.univ.filter fun i : Index => support i ⊆ s).card = 2 ^ s.card := by
  classical
  rw [← Finset.card_powerset]
  apply Finset.card_bij (fun i _ => support i)
  · intro i hi
    exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hi).2
  · intro i _ j _ hij
    exact support_injective hij
  · intro t ht
    have hts : t ⊆ s := Finset.mem_powerset.mp ht
    let n : ℕ := ∑ a ∈ t, 2 ^ a
    have hn : n < 128 := by
      have hle : n ≤ ∑ a ∈ Finset.range 7, 2 ^ a :=
        Finset.sum_le_sum_of_subset (hts.trans hs)
      rw [range_seven_sum] at hle
      omega
    have hsupport : support ⟨n, hn⟩ = t :=
      Finset.toFinset_bitIndices_sum_two_pow t
    refine ⟨⟨n, hn⟩, ?_, hsupport⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [hsupport] using hts

def zeros (i : Index) : ℕ := 7 - (support i).card
def parity (i : Index) : ℕ := zeros i % 2
def halfPower (i : Index) : ℕ := (zeros i + 1) / 2

theorem parity_lt_two (i : Index) : parity i < 2 := Nat.mod_lt _ (by decide)

theorem halfPower_identity (i : Index) :
    2 * halfPower i + (support i).card = 7 + parity i := by
  have hc := support_card_le i
  dsimp [halfPower, parity, zeros]
  omega

/-- The integer numerator of the ordered Cartesian basis matrix. -/
def B : Matrix Index Index ℤ := fun i j =>
  if support j ⊆ support i then (2 : ℤ) ^ halfPower i else 0

/-- The exact Cartesian basis is `B/4`, with no irrational coefficients for m=7. -/
def basisMatrix : Matrix Index Index ℚ := fun i j => (B i j : ℚ) / 4

/-- The exponent before removal of the factor 16 in the numerator Gram matrix. -/
def gramPower (i j : Index) : ℕ :=
  halfPower i + halfPower j + (support i ∩ support j).card

theorem gramPower_ge_four (i j : Index) : 4 ≤ gramPower i j := by
  have hi := halfPower_identity i
  have hj := halfPower_identity j
  have hu : (support i ∪ support j).card ≤ 7 := by
    have hs : support i ∪ support j ⊆ Finset.range 7 :=
      Finset.union_subset (support_subset_range i) (support_subset_range j)
    simpa only [Finset.card_range] using Finset.card_le_card hs
  have hc := Finset.card_union_add_card_inter (support i) (support j)
  dsimp [gramPower]
  omega

/-- The integral Gram matrix of the KRR basis. The exponent is nonnegative. -/
def G : Matrix Index Index ℤ := fun i j => (2 : ℤ) ^ (gramPower i j - 4)

theorem G_symm (i j : Index) : G i j = G j i := by
  unfold G gramPower
  rw [Finset.inter_comm (support i) (support j), add_comm (halfPower i) (halfPower j)]

theorem G_transpose : Gᵀ = G := by
  funext i j
  exact G_symm j i

theorem G_diagonal (i : Index) : G i i = (2 : ℤ) ^ (3 + parity i) := by
  have hi := halfPower_identity i
  unfold G gramPower
  rw [Finset.inter_self]
  congr 1
  omega

theorem B_diagonal (i : Index) : B i i = (2 : ℤ) ^ halfPower i := by
  simp [B]

theorem B_lower_triangular : B.IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  change (if support j ⊆ support i then (2 : ℤ) ^ halfPower i else 0) = 0
  exact ite_eq_right (fun h => (not_le_of_gt hij) (index_le_of_support_subset h))

theorem B_det_ne_zero : B.det ≠ 0 := by
  rw [Matrix.det_of_isLowerTriangular B B_lower_triangular]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rw [B_diagonal]
  exact pow_ne_zero _ (by decide)

/-- The numerator Gram identity follows from a powerset count, not enumeration. -/
theorem B_mul_transpose : B * Bᵀ = (16 : ℤ) • G := by
  classical
  funext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  have hcount :
      (Finset.univ.filter fun k : Index => support k ⊆ support i ∩ support j).card =
        2 ^ (support i ∩ support j).card :=
    card_support_subsets _ (Finset.inter_subset_left.trans (support_subset_range i))
  have hterm (k : Index) : B i k * B j k =
      if support k ⊆ support i ∩ support j
      then (2 : ℤ) ^ halfPower i * 2 ^ halfPower j else 0 := by
    by_cases hi : support k ⊆ support i <;>
      by_cases hj : support k ⊆ support j <;>
      simp [B, Finset.subset_inter_iff, hi, hj]
  calc
    (∑ k : Index, B i k * B j k) =
        ∑ k : Index, if support k ⊆ support i ∩ support j
          then (2 : ℤ) ^ halfPower i * 2 ^ halfPower j else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      exact hterm k
    _ = ((Finset.univ.filter fun k : Index => support k ⊆ support i ∩ support j).card : ℤ) *
        ((2 : ℤ) ^ halfPower i * 2 ^ halfPower j) := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = (2 : ℤ) ^ (support i ∩ support j).card *
        (2 ^ halfPower i * 2 ^ halfPower j) := by
      rw [hcount]
      norm_cast
    _ = (2 : ℤ) ^ gramPower i j := by
      simp only [gramPower, pow_add]
      ring
    _ = 16 * G i j := by
      unfold G
      have he : 4 + (gramPower i j - 4) = gramPower i j := by
        have h := gramPower_ge_four i j
        omega
      rw [show (16 : ℤ) = 2 ^ 4 by norm_num, ← pow_add, he]

/-- This identifies the rational row matrix `B/4` with the stated integral form. -/
theorem basisMatrix_gram (i j : Index) :
    (∑ k : Index, basisMatrix i k * basisMatrix j k) = (G i j : ℚ) := by
  have hz : (∑ k : Index, B i k * B j k) = 16 * G i j := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
      using congrFun (congrFun B_mul_transpose i) j
  have hq : (∑ k : Index, (B i k : ℚ) * (B j k : ℚ)) = 16 * (G i j : ℚ) := by
    exact_mod_cast hz
  calc
    (∑ k : Index, basisMatrix i k * basisMatrix j k) =
        ∑ k : Index, (1 / 16 : ℚ) * ((B i k : ℚ) * (B j k : ℚ)) := by
      apply Finset.sum_congr rfl
      intro k _
      dsimp [basisMatrix]
      ring
    _ = (1 / 16 : ℚ) * (∑ k : Index, (B i k : ℚ) * (B j k : ℚ)) :=
      (Finset.mul_sum _ _ _).symm
    _ = (G i j : ℚ) := by rw [hq]; ring

/-- The prescribed integral half-Gram matrix: lower triangle and half diagonal. -/
def H : Matrix Index Index ℤ := fun i j =>
  if j < i then G i j else if i = j then (2 : ℤ) ^ (2 + parity i) else 0

theorem H_add_transpose : H + Hᵀ = G := by
  funext i j
  change H i j + H j i = G i j
  rcases lt_trichotomy i j with hij | hij | hji
  · simp only [H, ite_eq_right (not_lt_of_ge (le_of_lt hij)), ite_eq_right (ne_of_lt hij),
      ite_eq_left hij, zero_add]
    exact G_symm j i
  · subst j
    simp only [H, lt_self_iff_false, ite_false, ite_true]
    rw [G_diagonal]
    have he : 3 + parity i = (2 + parity i) + 1 := by omega
    rw [he, pow_succ]
    ring
  · simp only [H, ite_eq_left hji, ite_eq_right (not_lt_of_ge (le_of_lt hji)),
      ite_eq_right (ne_of_lt hji), add_zero]

/-- The bundled lattice uses exactly the concrete coordinate form. -/
def lattice : VOA.IntegralLattice where
  carrier := Coordinates
  form := Matrix.toBilin' G
  isSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr G_transpose

theorem lattice_rank : Module.finrank ℤ lattice.carrier = 128 := by
  change Module.finrank ℤ (Index → ℤ) = 128
  rw [Module.finrank_pi]
  rfl

theorem form_orderedBasis (i j : Index) :
    lattice.form (orderedBasis i) (orderedBasis j) = G i j := by
  change Matrix.toBilin' G (orderedBasis i) (orderedBasis j) = G i j
  simpa only [orderedBasis, Pi.basisFun_apply] using Matrix.toBilin'_single G i j

def halfForm : LinearMap.BilinForm ℤ lattice.carrier := Matrix.toBilin' H

theorem halfForm_orderedBasis (i j : Index) :
    halfForm (orderedBasis i) (orderedBasis j) = H i j := by
  change Matrix.toBilin' H (orderedBasis i) (orderedBasis j) = H i j
  simpa only [orderedBasis, Pi.basisFun_apply] using Matrix.toBilin'_single H i j

theorem halfForm_symmetrization (v w : lattice.carrier) :
    halfForm v w + halfForm w v = lattice.form v w := by
  change Coordinates at v w
  change Matrix.toBilin' H v w + Matrix.toBilin' H w v = Matrix.toBilin' G v w
  rw [← H_add_transpose]
  simp only [Matrix.toBilin'_apply', Matrix.add_mulVec, dotProduct_add,
    Matrix.dotProduct_transpose_mulVec]

theorem lattice_even : lattice.Even := by
  intro v
  refine ⟨halfForm v v, ?_⟩
  rw [← halfForm_symmetrization v v]
  ring

/-- Row multiplication by the integer basis numerator preserves the form up to 16. -/
theorem scaled_form (v w : lattice.carrier) :
    16 * lattice.form v w = (v ᵥ* B) ⬝ᵥ (w ᵥ* B) := by
  change Coordinates at v w
  change 16 * Matrix.toBilin' G v w = _
  rw [Matrix.toBilin'_apply']
  calc
    16 * (v ⬝ᵥ (G *ᵥ w)) = v ⬝ᵥ (((16 : ℤ) • G) *ᵥ w) := by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    _ = v ⬝ᵥ ((B * Bᵀ) *ᵥ w) := by rw [B_mul_transpose]
    _ = (v ᵥ* B) ⬝ᵥ (w ᵥ* B) := by
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

theorem lattice_posDef : lattice.PosDef := by
  intro v hv
  have hvB : v ᵥ* B ≠ 0 := by
    intro hz
    exact hv (Matrix.eq_zero_of_vecMul_eq_zero B_det_ne_zero hz)
  have hp : 0 < (v ᵥ* B) ⬝ᵥ (v ᵥ* B) := by
    change 0 < ∑ i : Index, (v ᵥ* B) i * (v ᵥ* B) i
    refine Finset.sum_pos' (fun i _ => mul_self_nonneg ((v ᵥ* B) i)) ?_
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hvB
    exact ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩
  rw [← scaled_form v v] at hp
  exact (mul_pos_iff_of_pos_left (by decide : (0 : ℤ) < 16)).mp hp

end BarnesWall.Lattice128
