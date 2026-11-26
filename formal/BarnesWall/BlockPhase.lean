import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic

/-!
# Canonical phases for block-preserving matrices

All vectors are row vectors. The canonical phase uses the strict lower triangle
of `H - R * H * Rᵀ`. The composition theorem assumes that `R` and `S` preserve
`H + Hᵀ`, preserve each block, and that `H` vanishes within every block.

The zero-diagonal statements are proved explicitly: symmetry alone would not
make a quadratic expression vanish in characteristic two. No invertibility or
particular Barnes–Wall lattice is assumed in this matrix lemma.
-/

set_option autoImplicit false

namespace BarnesWall.BlockPhase

open Matrix
open scoped Matrix BigOperators

variable {ι κ : Type*}

/-- Entries outside a block are zero. -/
def PreservesBlocks (block : ι → κ) (R : Matrix ι ι (ZMod 2)) : Prop :=
  ∀ i j, block i ≠ block j → R i j = 0

/-- Entries whose two indices belong to the same block are zero. -/
def VanishesWithinBlocks (block : ι → κ) (H : Matrix ι ι (ZMod 2)) : Prop :=
  ∀ i j, block i = block j → H i j = 0

/-- The strict lower triangle, in the specified order on the basis. -/
def strictLower [LinearOrder ι] (M : Matrix ι ι (ZMod 2)) : Matrix ι ι (ZMod 2) :=
  Matrix.of fun i j => if j < i then M i j else 0

/-- The defect of the half-Gram matrix under a right row action. -/
def liftDefect [Fintype ι] (H R : Matrix ι ι (ZMod 2)) : Matrix ι ι (ZMod 2) :=
  H - R * H * Rᵀ

/-- Matrix of the canonical quadratic phase. -/
def canonicalMatrix [Fintype ι] [LinearOrder ι]
    (H R : Matrix ι ι (ZMod 2)) : Matrix ι ι (ZMod 2) :=
  strictLower (liftDefect H R)

/-- The canonical phase exponent, valued in `ZMod 2`. -/
def canonicalPhase [Fintype ι] [LinearOrder ι]
    (H R : Matrix ι ι (ZMod 2)) (v : ι → ZMod 2) : ZMod 2 :=
  v ⬝ᵥ (canonicalMatrix H R *ᵥ v)

private theorem matrix_add_self (M : Matrix ι ι (ZMod 2)) : M + M = 0 := by
  funext i j
  exact CharTwo.add_self_eq_zero (M i j)

theorem liftDefect_eq_add [Fintype ι] (H R : Matrix ι ι (ZMod 2)) :
    liftDefect H R = H + R * H * Rᵀ := by
  funext i j
  exact CharTwo.sub_eq_add (H i j) ((R * H * Rᵀ) i j)

@[simp] theorem strictLower_diagonal [LinearOrder ι] (M : Matrix ι ι (ZMod 2)) (i : ι) :
    strictLower M i i = 0 := by
  simp [strictLower]

@[simp] theorem canonicalMatrix_diagonal [Fintype ι] [LinearOrder ι]
    (H R : Matrix ι ι (ZMod 2)) (i : ι) :
    canonicalMatrix H R i i = 0 :=
  strictLower_diagonal _ _

theorem preservesBlocks_mul [Fintype ι] {block : ι → κ} {R S : Matrix ι ι (ZMod 2)}
    (hR : PreservesBlocks block R) (hS : PreservesBlocks block S) :
    PreservesBlocks block (R * S) := by
  classical
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : block i = block k
  · have hkj : block k ≠ block j := fun h => hij (hik.trans h)
    rw [hS k j hkj, mul_zero]
  · rw [hR i k hik, zero_mul]

theorem vanishesWithinBlocks_conjugate [Fintype ι] {block : ι → κ}
    {R M : Matrix ι ι (ZMod 2)}
    (hR : PreservesBlocks block R) (hM : VanishesWithinBlocks block M) :
    VanishesWithinBlocks block (R * M * Rᵀ) := by
  classical
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro a _
  change (R i a * M a b) * R j b = 0
  by_cases hia : block i = block a
  · by_cases hbj : block b = block j
    · have hab : block a = block b := hia.symm.trans (hij.trans hbj.symm)
      rw [hM a b hab, mul_zero, zero_mul]
    · rw [hR j b (Ne.symm hbj), mul_zero]
  · rw [hR i a hia, zero_mul, zero_mul]

theorem liftDefect_vanishesWithinBlocks [Fintype ι] {block : ι → κ}
    {H R : Matrix ι ι (ZMod 2)}
    (hH : VanishesWithinBlocks block H) (hR : PreservesBlocks block R) :
    VanishesWithinBlocks block (liftDefect H R) := by
  intro i j hij
  change H i j - (R * H * Rᵀ) i j = 0
  rw [hH i j hij, vanishesWithinBlocks_conjugate hR hH i j hij, sub_self]

theorem liftDefect_diagonal [Fintype ι] {block : ι → κ} {H R : Matrix ι ι (ZMod 2)}
    (hH : VanishesWithinBlocks block H) (hR : PreservesBlocks block R) (i : ι) :
    liftDefect H R i i = 0 :=
  liftDefect_vanishesWithinBlocks hH hR i i rfl

theorem canonicalMatrix_vanishesWithinBlocks [Fintype ι] [LinearOrder ι] {block : ι → κ}
    {H R : Matrix ι ι (ZMod 2)}
    (hH : VanishesWithinBlocks block H) (hR : PreservesBlocks block R) :
    VanishesWithinBlocks block (canonicalMatrix H R) := by
  intro i j hij
  simp [canonicalMatrix, strictLower, liftDefect_vanishesWithinBlocks hH hR i j hij]

theorem liftDefect_add_transpose [Fintype ι] (H R : Matrix ι ι (ZMod 2))
    (hR : R * (H + Hᵀ) * Rᵀ = H + Hᵀ) :
    liftDefect H R + (liftDefect H R)ᵀ = 0 := by
  calc
    liftDefect H R + (liftDefect H R)ᵀ =
        (H + Hᵀ) + (R * H * Rᵀ + R * Hᵀ * Rᵀ) := by
      simp only [liftDefect_eq_add, Matrix.transpose_add, Matrix.transpose_mul,
        Matrix.transpose_transpose, Matrix.mul_assoc]
      ac_rfl
    _ = (H + Hᵀ) + (H + Hᵀ) := by
      rw [← Matrix.add_mul, ← Matrix.mul_add, hR]
    _ = 0 := matrix_add_self _

private theorem transpose_eq_self_of_add_transpose_eq_zero
    (M : Matrix ι ι (ZMod 2)) (hM : M + Mᵀ = 0) : Mᵀ = M := by
  funext i j
  have h : M i j + M j i = 0 := congrFun (congrFun hM i) j
  exact (CharTwo.add_eq_zero.mp h).symm

theorem liftDefect_transpose [Fintype ι] (H R : Matrix ι ι (ZMod 2))
    (hR : R * (H + Hᵀ) * Rᵀ = H + Hᵀ) :
    (liftDefect H R)ᵀ = liftDefect H R :=
  transpose_eq_self_of_add_transpose_eq_zero _ (liftDefect_add_transpose H R hR)

/-- A symmetric zero-diagonal matrix is its strict lower triangle plus its transpose. -/
theorem strictLower_add_transpose [LinearOrder ι] (M : Matrix ι ι (ZMod 2))
    (hM : Mᵀ = M) (hdiag : ∀ i, M i i = 0) :
    strictLower M + (strictLower M)ᵀ = M := by
  funext i j
  change (if j < i then M i j else 0) + (if i < j then M j i else 0) = M i j
  rcases lt_trichotomy i j with hij | hij | hji
  · rw [ite_eq_right (not_lt_of_ge (le_of_lt hij)), ite_eq_left hij, zero_add]
    exact congrFun (congrFun hM i) j
  · subst j
    simp [hdiag]
  · rw [ite_eq_left hji, ite_eq_right (not_lt_of_ge (le_of_lt hji)), add_zero]

theorem canonicalMatrix_add_transpose [Fintype ι] [LinearOrder ι] {block : ι → κ}
    {H R : Matrix ι ι (ZMod 2)}
    (hH : VanishesWithinBlocks block H) (hblock : PreservesBlocks block R)
    (hR : R * (H + Hᵀ) * Rᵀ = H + Hᵀ) :
    canonicalMatrix H R + (canonicalMatrix H R)ᵀ = liftDefect H R :=
  strictLower_add_transpose _ (liftDefect_transpose H R hR)
    (liftDefect_diagonal hH hblock)

theorem isometry_mul [Fintype ι] {G R S : Matrix ι ι (ZMod 2)}
    (hR : R * G * Rᵀ = G) (hS : S * G * Sᵀ = G) :
    (R * S) * G * (R * S)ᵀ = G := by
  calc
    (R * S) * G * (R * S)ᵀ = R * (S * G * Sᵀ) * Rᵀ := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = R * G * Rᵀ := by rw [hS]
    _ = G := hR

theorem liftDefect_composition_cancel [Fintype ι] (H R S : Matrix ι ι (ZMod 2)) :
    liftDefect H R + R * liftDefect H S * Rᵀ + liftDefect H (R * S) = 0 := by
  calc
    liftDefect H R + R * liftDefect H S * Rᵀ + liftDefect H (R * S) =
        (H + H) + (R * H * Rᵀ + R * H * Rᵀ) +
          ((R * S) * H * (R * S)ᵀ + (R * S) * H * (R * S)ᵀ) := by
      simp only [liftDefect_eq_add, Matrix.transpose_mul, Matrix.mul_add,
        Matrix.add_mul, Matrix.mul_assoc]
      ac_rfl
    _ = 0 := by simp only [matrix_add_self, add_zero]

/-- The matrix whose quadratic expression is the failure of phase composition. -/
def compositionDefect [Fintype ι] [LinearOrder ι]
    (H R S : Matrix ι ι (ZMod 2)) : Matrix ι ι (ZMod 2) :=
  canonicalMatrix H R + R * canonicalMatrix H S * Rᵀ + canonicalMatrix H (R * S)

/-- The middle term's diagonal vanishes by block support, not just by symmetry. -/
theorem compositionDefect_diagonal [Fintype ι] [LinearOrder ι]
    {block : ι → κ} {H R S : Matrix ι ι (ZMod 2)}
    (hH : VanishesWithinBlocks block H)
    (hR : PreservesBlocks block R) (hS : PreservesBlocks block S) (i : ι) :
    compositionDefect H R S i i = 0 := by
  change canonicalMatrix H R i i + (R * canonicalMatrix H S * Rᵀ) i i +
    canonicalMatrix H (R * S) i i = 0
  rw [canonicalMatrix_diagonal, canonicalMatrix_diagonal,
    vanishesWithinBlocks_conjugate hR (canonicalMatrix_vanishesWithinBlocks hH hS) i i rfl]
  rfl

theorem compositionDefect_add_transpose [Fintype ι] [LinearOrder ι] {block : ι → κ}
    {H R S : Matrix ι ι (ZMod 2)}
    (hH : VanishesWithinBlocks block H)
    (hRb : PreservesBlocks block R) (hSb : PreservesBlocks block S)
    (hR : R * (H + Hᵀ) * Rᵀ = H + Hᵀ)
    (hS : S * (H + Hᵀ) * Sᵀ = H + Hᵀ) :
    compositionDefect H R S + (compositionDefect H R S)ᵀ = 0 := by
  calc
    compositionDefect H R S + (compositionDefect H R S)ᵀ =
        (canonicalMatrix H R + (canonicalMatrix H R)ᵀ) +
          R * (canonicalMatrix H S + (canonicalMatrix H S)ᵀ) * Rᵀ +
          (canonicalMatrix H (R * S) + (canonicalMatrix H (R * S))ᵀ) := by
      simp only [compositionDefect, Matrix.transpose_add, Matrix.transpose_mul,
        Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      ac_rfl
    _ = liftDefect H R + R * liftDefect H S * Rᵀ + liftDefect H (R * S) := by
      rw [canonicalMatrix_add_transpose hH hRb hR,
        canonicalMatrix_add_transpose hH hSb hS,
        canonicalMatrix_add_transpose hH (preservesBlocks_mul hRb hSb) (isometry_mul hR hS)]
    _ = 0 := liftDefect_composition_cancel H R S

/-- In characteristic two the quadratic expression of a symmetric zero-diagonal matrix is zero. -/
theorem quadratic_zero_of_symmetric_zero_diagonal [Fintype ι] [LinearOrder ι]
    (M : Matrix ι ι (ZMod 2))
    (hM : Mᵀ = M) (hdiag : ∀ i, M i i = 0) (v : ι → ZMod 2) :
    v ⬝ᵥ (M *ᵥ v) = 0 := by
  rw [← strictLower_add_transpose M hM hdiag, Matrix.add_mulVec, dotProduct_add,
    Matrix.dotProduct_transpose_mulVec]
  exact CharTwo.add_self_eq_zero _

theorem quadratic_conjugate [Fintype ι]
    (R B : Matrix ι ι (ZMod 2)) (v : ι → ZMod 2) :
    v ⬝ᵥ ((R * B * Rᵀ) *ᵥ v) = (v ᵥ* R) ⬝ᵥ (B *ᵥ (v ᵥ* R)) := by
  calc
    v ⬝ᵥ ((R * B * Rᵀ) *ᵥ v) = v ⬝ᵥ (R *ᵥ (B *ᵥ (Rᵀ *ᵥ v))) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = (v ᵥ* R) ⬝ᵥ (B *ᵥ (v ᵥ* R)) := by
      rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

/-- Canonical phases compose on the block-preserving isometries of `H + Hᵀ`.
The vector in the second phase is `v ᵥ* R`, expressing right row action. -/
theorem canonicalPhase_mul [Fintype ι] [LinearOrder ι]
    {block : ι → κ} {H R S : Matrix ι ι (ZMod 2)}
    (hH : VanishesWithinBlocks block H)
    (hRb : PreservesBlocks block R) (hSb : PreservesBlocks block S)
    (hR : R * (H + Hᵀ) * Rᵀ = H + Hᵀ)
    (hS : S * (H + Hᵀ) * Sᵀ = H + Hᵀ) (v : ι → ZMod 2) :
    canonicalPhase H (R * S) v = canonicalPhase H R v + canonicalPhase H S (v ᵥ* R) := by
  have hsym : (compositionDefect H R S)ᵀ = compositionDefect H R S :=
    transpose_eq_self_of_add_transpose_eq_zero _
      (compositionDefect_add_transpose hH hRb hSb hR hS)
  have hz := quadratic_zero_of_symmetric_zero_diagonal (compositionDefect H R S)
    hsym (compositionDefect_diagonal hH hRb hSb) v
  have hphase : canonicalPhase H R v + canonicalPhase H S (v ᵥ* R) +
      canonicalPhase H (R * S) v = 0 := by
    simpa only [compositionDefect, Matrix.add_mulVec, dotProduct_add, quadratic_conjugate,
      canonicalPhase] using hz
  exact (CharTwo.add_eq_zero.mp hphase).symm

end BarnesWall.BlockPhase
