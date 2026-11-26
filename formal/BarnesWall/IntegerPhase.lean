import BarnesWall.BlockPhase
import Mathlib.Algebra.Field.Defs

/-!
# Integral canonical phases and their signs

The exponent is computed over the integers, using the strict lower triangle of
`H - R * H * Rᵀ`. Reduction modulo two connects it to `BlockPhase`.
The sign itself is the integer power of `-1` in a field, so specialization to
the complex numbers needs no ring homomorphism from `ZMod 2`.
-/

set_option autoImplicit false

namespace BarnesWall.IntegerPhase

open Matrix
open scoped Matrix BigOperators

variable {ι κ : Type*}

def reduceMatrix (M : Matrix ι ι ℤ) : Matrix ι ι (ZMod 2) :=
  M.map (Int.castRingHom (ZMod 2))

def reduceVector (v : ι → ℤ) : ι → ZMod 2 :=
  (Int.castRingHom (ZMod 2)) ∘ v

def strictLower [LinearOrder ι] (M : Matrix ι ι ℤ) : Matrix ι ι ℤ :=
  Matrix.of fun i j => if j < i then M i j else 0

def liftDefect [Fintype ι] (H R : Matrix ι ι ℤ) : Matrix ι ι ℤ :=
  H - R * H * Rᵀ

def canonicalMatrix [Fintype ι] [LinearOrder ι] (H R : Matrix ι ι ℤ) : Matrix ι ι ℤ :=
  strictLower (liftDefect H R)

def exponent [Fintype ι] [LinearOrder ι] (H R : Matrix ι ι ℤ) (v : ι → ℤ) : ℤ :=
  v ⬝ᵥ (canonicalMatrix H R *ᵥ v)

/-- The actual sign, with an integer exponent; `K` can later be instantiated to `ℂ`. -/
def phase (K : Type*) [Field K] [Fintype ι] [LinearOrder ι]
    (H R : Matrix ι ι ℤ) (v : ι → ℤ) : K :=
  (-1 : K) ^ exponent H R v

def explicitCocycle (K : Type*) [Field K] [Fintype ι]
    (H : Matrix ι ι ℤ) (v w : ι → ℤ) : K :=
  (-1 : K) ^ (v ⬝ᵥ (H *ᵥ w))

theorem reduceMatrix_add (M N : Matrix ι ι ℤ) :
    reduceMatrix (M + N) = reduceMatrix M + reduceMatrix N := by
  funext i j
  exact Int.cast_add (M i j) (N i j)

theorem reduceMatrix_sub (M N : Matrix ι ι ℤ) :
    reduceMatrix (M - N) = reduceMatrix M - reduceMatrix N := by
  funext i j
  exact Int.cast_sub (M i j) (N i j)

theorem reduceMatrix_transpose (M : Matrix ι ι ℤ) :
    reduceMatrix Mᵀ = (reduceMatrix M)ᵀ := rfl

theorem reduceMatrix_mul [Fintype ι] (M N : Matrix ι ι ℤ) :
    reduceMatrix (M * N) = reduceMatrix M * reduceMatrix N :=
  Matrix.map_mul

theorem reduceVector_add (v w : ι → ℤ) :
    reduceVector (v + w) = reduceVector v + reduceVector w := by
  funext i
  exact Int.cast_add (v i) (w i)

theorem reduceVector_vecMul [Fintype ι] (v : ι → ℤ) (R : Matrix ι ι ℤ) :
    reduceVector (v ᵥ* R) = reduceVector v ᵥ* reduceMatrix R := by
  funext i
  exact (Int.castRingHom (ZMod 2)).map_vecMul R v i

theorem reduceVector_mulVec [Fintype ι] (H : Matrix ι ι ℤ) (v : ι → ℤ) :
    reduceVector (H *ᵥ v) = reduceMatrix H *ᵥ reduceVector v := by
  funext i
  exact (Int.castRingHom (ZMod 2)).map_mulVec H v i

theorem reduce_bilinear [Fintype ι] (H : Matrix ι ι ℤ) (v w : ι → ℤ) :
    ((v ⬝ᵥ (H *ᵥ w) : ℤ) : ZMod 2) =
      reduceVector v ⬝ᵥ (reduceMatrix H *ᵥ reduceVector w) := by
  change (Int.castRingHom (ZMod 2)) (v ⬝ᵥ (H *ᵥ w)) = _
  rw [RingHom.map_dotProduct]
  change reduceVector v ⬝ᵥ reduceVector (H *ᵥ w) = _
  rw [reduceVector_mulVec]

theorem reduce_strictLower [LinearOrder ι] (M : Matrix ι ι ℤ) :
    reduceMatrix (strictLower M) = BlockPhase.strictLower (reduceMatrix M) := by
  funext i j
  by_cases h : j < i <;> simp [strictLower, BlockPhase.strictLower, reduceMatrix, h]

theorem reduce_liftDefect [Fintype ι] (H R : Matrix ι ι ℤ) :
    reduceMatrix (liftDefect H R) = BlockPhase.liftDefect (reduceMatrix H) (reduceMatrix R) := by
  simp only [liftDefect, BlockPhase.liftDefect, reduceMatrix_sub, reduceMatrix_mul,
    reduceMatrix_transpose]

theorem reduce_canonicalMatrix [Fintype ι] [LinearOrder ι] (H R : Matrix ι ι ℤ) :
    reduceMatrix (canonicalMatrix H R) =
      BlockPhase.canonicalMatrix (reduceMatrix H) (reduceMatrix R) := by
  unfold canonicalMatrix BlockPhase.canonicalMatrix
  rw [reduce_strictLower, reduce_liftDefect]

theorem reduce_exponent [Fintype ι] [LinearOrder ι] (H R : Matrix ι ι ℤ) (v : ι → ℤ) :
    (exponent H R v : ZMod 2) =
      BlockPhase.canonicalPhase (reduceMatrix H) (reduceMatrix R) (reduceVector v) := by
  unfold exponent BlockPhase.canonicalPhase
  rw [reduce_bilinear, reduce_canonicalMatrix]

theorem reduce_isometry [Fintype ι] {G R : Matrix ι ι ℤ}
    (hR : R * G * Rᵀ = G) :
    reduceMatrix R * reduceMatrix G * (reduceMatrix R)ᵀ = reduceMatrix G := by
  have h := congrArg reduceMatrix hR
  simpa only [reduceMatrix_mul, reduceMatrix_transpose] using h

/-- Integral skew-symmetry follows from the isometry of the symmetrization. -/
theorem liftDefect_add_transpose [Fintype ι] (H R : Matrix ι ι ℤ)
    (hR : R * (H + Hᵀ) * Rᵀ = H + Hᵀ) :
    liftDefect H R + (liftDefect H R)ᵀ = 0 := by
  calc
    liftDefect H R + (liftDefect H R)ᵀ =
        (H + Hᵀ) - (R * H * Rᵀ + R * Hᵀ * Rᵀ) := by
      simp only [liftDefect, Matrix.transpose_sub, Matrix.transpose_mul,
        Matrix.transpose_transpose, Matrix.mul_assoc]
      simp only [sub_eq_add_neg, neg_add]
      ac_rfl
    _ = 0 := by
      rw [← Matrix.add_mul, ← Matrix.mul_add, hR, sub_self]

/-- Over the integers, the skew defect has zero diagonal before reduction. -/
theorem liftDefect_diagonal [Fintype ι] (H R : Matrix ι ι ℤ)
    (hR : R * (H + Hᵀ) * Rᵀ = H + Hᵀ) (i : ι) :
    liftDefect H R i i = 0 := by
  have h : liftDefect H R i i + liftDefect H R i i = 0 :=
    congrFun (congrFun (liftDefect_add_transpose H R hR) i) i
  have htwo : (2 : ℤ) * liftDefect H R i i = 0 := by
    simpa only [two_mul] using h
  exact (mul_eq_zero.mp htwo).resolve_left (by decide)

theorem reduced_canonicalMatrix_add_transpose [Fintype ι] [LinearOrder ι]
    (H R : Matrix ι ι ℤ) (hR : R * (H + Hᵀ) * Rᵀ = H + Hᵀ) :
    BlockPhase.canonicalMatrix (reduceMatrix H) (reduceMatrix R) +
        (BlockPhase.canonicalMatrix (reduceMatrix H) (reduceMatrix R))ᵀ =
      BlockPhase.liftDefect (reduceMatrix H) (reduceMatrix R) := by
  have hR₂ : reduceMatrix R * (reduceMatrix H + (reduceMatrix H)ᵀ) *
      (reduceMatrix R)ᵀ = reduceMatrix H + (reduceMatrix H)ᵀ := by
    simpa only [reduceMatrix_add, reduceMatrix_transpose] using reduce_isometry hR
  have hdiag : ∀ i, BlockPhase.liftDefect (reduceMatrix H) (reduceMatrix R) i i = 0 := by
    intro i
    rw [← reduce_liftDefect]
    change ((liftDefect H R i i : ℤ) : ZMod 2) = 0
    rw [liftDefect_diagonal H R hR i, Int.cast_zero]
  exact BlockPhase.strictLower_add_transpose _
    (BlockPhase.liftDefect_transpose _ _ hR₂) hdiag

private theorem quadratic_add [Fintype ι] (B : Matrix ι ι (ZMod 2))
    (v w : ι → ZMod 2) :
    (v + w) ⬝ᵥ (B *ᵥ (v + w)) =
      v ⬝ᵥ (B *ᵥ v) + w ⬝ᵥ (B *ᵥ w) + v ⬝ᵥ ((B + Bᵀ) *ᵥ w) := by
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, Matrix.add_mulVec,
    Matrix.dotProduct_transpose_mulVec]
  simp only [add_assoc, add_comm, add_left_comm]

private theorem bilinear_conjugate [Fintype ι] (R H : Matrix ι ι (ZMod 2))
    (v w : ι → ZMod 2) :
    v ⬝ᵥ ((R * H * Rᵀ) *ᵥ w) = (v ᵥ* R) ⬝ᵥ (H *ᵥ (w ᵥ* R)) := by
  calc
    v ⬝ᵥ ((R * H * Rᵀ) *ᵥ w) = v ⬝ᵥ (R *ᵥ (H *ᵥ (Rᵀ *ᵥ w))) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = (v ᵥ* R) ⬝ᵥ (H *ᵥ (w ᵥ* R)) := by
      rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

theorem reduced_phase_polar [Fintype ι] [LinearOrder ι] (H R : Matrix ι ι ℤ)
    (hR : R * (H + Hᵀ) * Rᵀ = H + Hᵀ) (v w : ι → ZMod 2) :
    BlockPhase.canonicalPhase (reduceMatrix H) (reduceMatrix R) (v + w) =
      BlockPhase.canonicalPhase (reduceMatrix H) (reduceMatrix R) v +
        BlockPhase.canonicalPhase (reduceMatrix H) (reduceMatrix R) w +
        (v ⬝ᵥ (reduceMatrix H *ᵥ w) +
          (v ᵥ* reduceMatrix R) ⬝ᵥ (reduceMatrix H *ᵥ (w ᵥ* reduceMatrix R))) := by
  unfold BlockPhase.canonicalPhase
  rw [quadratic_add, reduced_canonicalMatrix_add_transpose H R hR,
    BlockPhase.liftDefect_eq_add, Matrix.add_mulVec, dotProduct_add, bilinear_conjugate]

private theorem charTwo_cocycle_rearrange (a b c d : ZMod 2) :
    b + (c + d) = a + (c + d + (a + b)) := by
  calc
    b + (c + d) = (a + a) + (b + (c + d)) := by
      rw [CharTwo.add_self_eq_zero, zero_add]
    _ = a + (c + d + (a + b)) := by ac_rfl

/-- The exponent equality needed for the explicit-cocycle identity, modulo two. -/
theorem exponent_cocycle_mod_two [Fintype ι] [LinearOrder ι] (H R : Matrix ι ι ℤ)
    (hR : R * (H + Hᵀ) * Rᵀ = H + Hᵀ) (v w : ι → ℤ) :
    (((v ᵥ* R) ⬝ᵥ (H *ᵥ (w ᵥ* R)) + (exponent H R v + exponent H R w) : ℤ) : ZMod 2) =
      ((v ⬝ᵥ (H *ᵥ w) + exponent H R (v + w) : ℤ) : ZMod 2) := by
  simp only [Int.cast_add, reduce_bilinear, reduce_exponent, reduceVector_vecMul, reduceVector_add]
  rw [reduced_phase_polar H R hR]
  exact charTwo_cocycle_rearrange _ _ _ _

/-- Equality of integer residues implies equality of the actual integer powers of `-1`. -/
theorem neg_one_zpow_eq_of_mod_two {K : Type*} [Field K] {a b : ℤ}
    (h : (a : ZMod 2) = (b : ZMod 2)) : (-1 : K) ^ a = (-1 : K) ^ b := by
  have heven : Even a ↔ Even b := by
    rw [← ZMod.intCast_eq_zero_iff_even, ← ZMod.intCast_eq_zero_iff_even, h]
  simp only [neg_one_zpow_eq_ite, heven]

@[simp] theorem exponent_zero [Fintype ι] [LinearOrder ι] (H R : Matrix ι ι ℤ) :
    exponent H R 0 = 0 := by
  simp [exponent]

theorem exponent_neg [Fintype ι] [LinearOrder ι] (H R : Matrix ι ι ℤ) (v : ι → ℤ) :
    exponent H R (-v) = exponent H R v := by
  simp only [exponent, Matrix.mulVec_neg, neg_dotProduct_neg]

@[simp] theorem phase_zero (K : Type*) [Field K] [Fintype ι] [LinearOrder ι]
    (H R : Matrix ι ι ℤ) : phase K H R 0 = 1 := by
  simp [phase]

theorem phase_ne_zero (K : Type*) [Field K] [Fintype ι] [LinearOrder ι]
    (H R : Matrix ι ι ℤ) (v : ι → ℤ) : phase K H R v ≠ 0 :=
  zpow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

theorem phase_neg (K : Type*) [Field K] [Fintype ι] [LinearOrder ι]
    (H R : Matrix ι ι ℤ) (v : ι → ℤ) : phase K H R (-v) = phase K H R v := by
  unfold phase
  rw [exponent_neg]

theorem phase_eq_one_of_even (K : Type*) [Field K] [Fintype ι] [LinearOrder ι]
    (H R : Matrix ι ι ℤ) (v : ι → ℤ) (h : Even (exponent H R v)) :
    phase K H R v = 1 :=
  h.neg_one_zpow

/-- The precise explicit-cocycle compatibility required by the lattice-VOA lift. -/
theorem phase_cocycle (K : Type*) [Field K] [Fintype ι] [LinearOrder ι]
    (H R : Matrix ι ι ℤ) (hR : R * (H + Hᵀ) * Rᵀ = H + Hᵀ) (v w : ι → ℤ) :
    explicitCocycle K H (v ᵥ* R) (w ᵥ* R) * (phase K H R v * phase K H R w) =
      explicitCocycle K H v w * phase K H R (v + w) := by
  have hn : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  unfold explicitCocycle phase
  rw [← zpow_add₀ hn, ← zpow_add₀ hn, ← zpow_add₀ hn]
  exact neg_one_zpow_eq_of_mod_two (exponent_cocycle_mod_two H R hR v w)

theorem phase_cocycle_of_form (K : Type*) [Field K] [Fintype ι] [LinearOrder ι]
    (H G R : Matrix ι ι ℤ) (hform : H + Hᵀ = G) (hR : R * G * Rᵀ = G)
    (v w : ι → ℤ) :
    explicitCocycle K H (v ᵥ* R) (w ᵥ* R) * (phase K H R v * phase K H R w) =
      explicitCocycle K H v w * phase K H R (v + w) := by
  apply phase_cocycle K H R _ v w
  simpa only [hform] using hR

/-- Integral block preservation implies block preservation after reduction. -/
theorem reduce_preservesBlocks {block : ι → κ} {R : Matrix ι ι ℤ}
    (hR : ∀ i j, block i ≠ block j → R i j = 0) :
    BlockPhase.PreservesBlocks block (reduceMatrix R) := by
  intro i j hij
  change ((R i j : ℤ) : ZMod 2) = 0
  rw [hR i j hij, Int.cast_zero]

/-- Even within-block entries, rather than zero integral entries, are sufficient. -/
theorem reduce_vanishesWithinBlocks {block : ι → κ} {H : Matrix ι ι ℤ}
    (hH : ∀ i j, block i = block j → Even (H i j)) :
    BlockPhase.VanishesWithinBlocks block (reduceMatrix H) := by
  intro i j hij
  exact (ZMod.intCast_eq_zero_iff_even).mpr (hH i j hij)

theorem exponent_mul_mod_two [Fintype ι] [LinearOrder ι]
    {block : ι → κ} {H R S : Matrix ι ι ℤ}
    (hH : ∀ i j, block i = block j → Even (H i j))
    (hRb : ∀ i j, block i ≠ block j → R i j = 0)
    (hSb : ∀ i j, block i ≠ block j → S i j = 0)
    (hR : R * (H + Hᵀ) * Rᵀ = H + Hᵀ)
    (hS : S * (H + Hᵀ) * Sᵀ = H + Hᵀ) (v : ι → ℤ) :
    (exponent H (R * S) v : ZMod 2) =
      ((exponent H R v + exponent H S (v ᵥ* R) : ℤ) : ZMod 2) := by
  have hR₂ : reduceMatrix R * (reduceMatrix H + (reduceMatrix H)ᵀ) *
      (reduceMatrix R)ᵀ = reduceMatrix H + (reduceMatrix H)ᵀ := by
    simpa only [reduceMatrix_add, reduceMatrix_transpose] using reduce_isometry hR
  have hS₂ : reduceMatrix S * (reduceMatrix H + (reduceMatrix H)ᵀ) *
      (reduceMatrix S)ᵀ = reduceMatrix H + (reduceMatrix H)ᵀ := by
    simpa only [reduceMatrix_add, reduceMatrix_transpose] using reduce_isometry hS
  simp only [Int.cast_add, reduce_exponent, reduceMatrix_mul, reduceVector_vecMul]
  exact BlockPhase.canonicalPhase_mul (reduce_vanishesWithinBlocks hH)
    (reduce_preservesBlocks hRb) (reduce_preservesBlocks hSb) hR₂ hS₂ (reduceVector v)

/-- Canonical integer signs compose under the integral isometry and block hypotheses. -/
theorem phase_mul (K : Type*) [Field K] [Fintype ι] [LinearOrder ι]
    {block : ι → κ} {H R S : Matrix ι ι ℤ}
    (hH : ∀ i j, block i = block j → Even (H i j))
    (hRb : ∀ i j, block i ≠ block j → R i j = 0)
    (hSb : ∀ i j, block i ≠ block j → S i j = 0)
    (hR : R * (H + Hᵀ) * Rᵀ = H + Hᵀ)
    (hS : S * (H + Hᵀ) * Sᵀ = H + Hᵀ) (v : ι → ℤ) :
    phase K H (R * S) v = phase K H R v * phase K H S (v ᵥ* R) := by
  unfold phase
  rw [← zpow_add₀ (neg_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0))]
  exact neg_one_zpow_eq_of_mod_two (exponent_mul_mod_two hH hRb hSb hR hS v)

end BarnesWall.IntegerPhase
