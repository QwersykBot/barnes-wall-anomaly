/-
SPDX-License-Identifier: Apache-2.0
See ../LICENSE-Apache-2.0.txt.
-/
import BarnesWall.IntegerPhase
import BarnesWall.LatticeComposition

/-!
# Canonical matrix phases as conformal lattice automorphisms

`coords` is an actual integral coordinate equivalence. The half-Gram matrix is
pulled back along it, while matrices act on its coordinate vectors on the right.
For an integral matrix unit preserving the Gram matrix, the canonical integer
sign from `IntegerPhase` therefore supplies all the explicit-phase hypotheses
of `transportedAut`. A matrix unit contains an integral inverse and both inverse
identities; a nonzero rational determinant is not a substitute for this input.

Under the even-within-block and block-support hypotheses, phase composition is
proved by `IntegerPhase.phase_mul`, then transported by the one global `tau` and
the full-state composition theorem. The order is visibly reversed:
`lift (R * S) = lift S * lift R`, since `VOA.Aut` uses function composition.

These are generic coordinate results. No concrete Barnes--Wall generator,
quaternion relation, faithfulness, unitary structure, or orbifold is asserted.
The separate local-bridge stage must check these declarations; the upstream
dependency audit does not certify them.
-/

set_option autoImplicit false

noncomputable section

namespace BarnesWall.CanonicalLift

open Matrix VOA VOA.LatGen
open scoped Matrix BigOperators

variable {L : VOA.IntegralLattice} {ι κ : Type*} [Fintype ι] [LinearOrder ι]
variable (coords : L.carrier ≃ₗ[ℤ] (ι → ℤ))

/-- The bilinear half-Gram form in the supplied integral coordinates. -/
def halfForm (H : Matrix ι ι ℤ) : L.carrier →ₗ[ℤ] L.carrier →ₗ[ℤ] ℤ :=
  (Matrix.toBilin' H).compl₁₂ coords.toLinearMap coords.toLinearMap

@[simp] theorem halfForm_apply (H : Matrix ι ι ℤ) (x y : L.carrier) :
    halfForm coords H x y = coords x ⬝ᵥ (H *ᵥ coords y) :=
  Matrix.toBilin'_apply' H (coords x) (coords y)

theorem halfForm_symmetrization (H G : Matrix ι ι ℤ)
    (hGram : ∀ x y, L.form x y = coords x ⬝ᵥ (G *ᵥ coords y))
    (hHG : H + Hᵀ = G) (x y : L.carrier) :
    halfForm coords H x y + halfForm coords H y x = L.form x y := by
  rw [halfForm_apply, halfForm_apply]
  calc
    coords x ⬝ᵥ (H *ᵥ coords y) + coords y ⬝ᵥ (H *ᵥ coords x) =
        coords x ⬝ᵥ ((H + Hᵀ) *ᵥ coords y) := by
      rw [Matrix.add_mulVec, dotProduct_add, Matrix.dotProduct_transpose_mulVec]
    _ = L.form x y := by rw [hHG, ← hGram]

/-- Integral half-Gram coordinates also imply evenness of the lattice. -/
theorem even_of_halfForm (H G : Matrix ι ι ℤ)
    (hGram : ∀ x y, L.form x y = coords x ⬝ᵥ (G *ᵥ coords y))
    (hHG : H + Hᵀ = G) : L.Even := by
  intro x
  refine ⟨halfForm coords H x x, ?_⟩
  simpa only [two_mul] using
    (halfForm_symmetrization coords H G hGram hHG x x).symm

/-- Right multiplication on coordinates, transported to the lattice itself. -/
def rowMap (R : Matrix ι ι ℤ) : L.carrier →ₗ[ℤ] L.carrier :=
  coords.symm.toLinearMap.comp (R.vecMulLinear.comp coords.toLinearMap)

@[simp] theorem coords_rowMap (R : Matrix ι ι ℤ) (x : L.carrier) :
    coords (rowMap coords R x) = coords x ᵥ* R :=
  coords.apply_symm_apply _

/-- Matrix multiplication is proved to be the corresponding right action. -/
theorem rowMap_mul (R S : Matrix ι ι ℤ) :
    rowMap coords (R * S) = (rowMap coords S).comp (rowMap coords R) := by
  apply LinearMap.ext
  intro x
  apply coords.injective
  simp only [LinearMap.comp_apply, coords_rowMap, Matrix.vecMul_vecMul]

/-- A matrix unit supplies an actual integral inverse, on both sides. -/
def rowEquiv (R : (Matrix ι ι ℤ)ˣ) : L.carrier ≃ₗ[ℤ] L.carrier where
  toLinearMap := rowMap coords (R : Matrix ι ι ℤ)
  invFun := rowMap coords (↑R⁻¹ : Matrix ι ι ℤ)
  left_inv x := by
    apply coords.injective
    simp only [coords_rowMap, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
  right_inv x := by
    apply coords.injective
    simp only [coords_rowMap, Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one]

@[simp] theorem rowEquiv_toLinearMap (R : (Matrix ι ι ℤ)ˣ) :
    (rowEquiv coords R).toLinearMap = rowMap coords (R : Matrix ι ι ℤ) := rfl

private theorem bilinear_conjugate (R G : Matrix ι ι ℤ) (v w : ι → ℤ) :
    v ⬝ᵥ ((R * G * Rᵀ) *ᵥ w) = (v ᵥ* R) ⬝ᵥ (G *ᵥ (w ᵥ* R)) := by
  calc
    v ⬝ᵥ ((R * G * Rᵀ) *ᵥ w) = v ⬝ᵥ (R *ᵥ (G *ᵥ (Rᵀ *ᵥ w))) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = (v ᵥ* R) ⬝ᵥ (G *ᵥ (w ᵥ* R)) := by
      rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

theorem rowMap_isometry (G R : Matrix ι ι ℤ)
    (hGram : ∀ x y, L.form x y = coords x ⬝ᵥ (G *ᵥ coords y))
    (hR : R * G * Rᵀ = G) (x y : L.carrier) :
    L.form (rowMap coords R x) (rowMap coords R y) = L.form x y := by
  rw [hGram, hGram, coords_rowMap, coords_rowMap, ← bilinear_conjugate, hR]

/-- The actual complex sign, with the checked integer exponent. -/
def phase (H R : Matrix ι ι ℤ) (x : L.carrier) : ℂ :=
  IntegerPhase.phase ℂ H R (coords x)

@[simp] theorem phase_zero (H R : Matrix ι ι ℤ) : phase coords H R 0 = 1 := by
  simp only [phase, map_zero, IntegerPhase.phase_zero]

theorem phase_ne_zero (H R : Matrix ι ι ℤ) (x : L.carrier) :
    phase coords H R x ≠ 0 := IntegerPhase.phase_ne_zero ℂ H R (coords x)

theorem phase_neg (H R : Matrix ι ι ℤ) (x : L.carrier) :
    phase coords H R (-x) = phase coords H R x := by
  simp only [phase, map_neg, IntegerPhase.phase_neg]

/-- The explicit cocycle identity is derived from the matrix isometry. -/
theorem phase_cocycle (H G R : Matrix ι ι ℤ)
    (hHG : H + Hᵀ = G) (hR : R * G * Rᵀ = G) (x y : L.carrier) :
    BarnesWall.explicitCocycle L (halfForm coords H)
        (rowMap coords R x) (rowMap coords R y) *
        (phase coords H R x * phase coords H R y) =
      BarnesWall.explicitCocycle L (halfForm coords H) x y * phase coords H R (x + y) := by
  simpa only [BarnesWall.explicitCocycle, halfForm_apply, phase, coords_rowMap,
    map_add, IntegerPhase.explicitCocycle] using
    IntegerPhase.phase_cocycle_of_form ℂ H G R hHG hR (coords x) (coords y)

/-- This is the full linear state map with the one global cocycle transport. -/
def liftMap (H R : Matrix ι ι ℤ) : LatModuleGen L →ₗ[ℂ] LatModuleGen L :=
  latMorphC L L (rowMap coords R)
    (BarnesWall.transportedPhase L (halfForm coords H) (rowMap coords R) (phase coords H R))

/-- The derived sign produces a genuine conformal automorphism of the infinite VOA. -/
def liftAut (hEven : L.Even) (hPos : L.PosDef) (H G : Matrix ι ι ℤ)
    (R : (Matrix ι ι ℤ)ˣ)
    (hGram : ∀ x y, L.form x y = coords x ⬝ᵥ (G *ᵥ coords y))
    (hHG : H + Hᵀ = G) (hR : (R : Matrix ι ι ℤ) * G * (R : Matrix ι ι ℤ)ᵀ = G) :
    Aut (latticeVOAGen L hEven hPos) :=
  BarnesWall.transportedAut L (halfForm coords H) hEven hPos
    (halfForm_symmetrization coords H G hGram hHG) (rowEquiv coords R)
    (rowMap_isometry coords G R hGram hR) (phase coords H R)
    (phase_zero coords H R) (phase_cocycle coords H G R hHG hR)
    (phase_ne_zero coords H R)

@[simp] theorem liftAut_apply (hEven : L.Even) (hPos : L.PosDef) (H G : Matrix ι ι ℤ)
    (R : (Matrix ι ι ℤ)ˣ)
    (hGram : ∀ x y, L.form x y = coords x ⬝ᵥ (G *ᵥ coords y))
    (hHG : H + Hᵀ = G) (hR : (R : Matrix ι ι ℤ) * G * (R : Matrix ι ι ℤ)ᵀ = G)
    (v : LatModuleGen L) :
    liftAut coords hEven hPos H G R hGram hHG hR v =
      liftMap coords H (R : Matrix ι ι ℤ) v := rfl

/-- The block theorem proves the actual phase composition; it is not an input. -/
theorem phase_mul (H G R S : Matrix ι ι ℤ) {block : ι → κ}
    (hHG : H + Hᵀ = G)
    (hH : ∀ i j, block i = block j → Even (H i j))
    (hRb : ∀ i j, block i ≠ block j → R i j = 0)
    (hSb : ∀ i j, block i ≠ block j → S i j = 0)
    (hR : R * G * Rᵀ = G) (hS : S * G * Sᵀ = G) (x : L.carrier) :
    phase coords H (R * S) x = phase coords H R x * phase coords H S (rowMap coords R x) := by
  have hRH : R * (H + Hᵀ) * Rᵀ = H + Hᵀ := by simpa only [hHG] using hR
  have hSH : S * (H + Hᵀ) * Sᵀ = H + Hᵀ := by simpa only [hHG] using hS
  simpa only [phase, coords_rowMap] using
    IntegerPhase.phase_mul ℂ hH hRb hSb hRH hSH (coords x)

/-- Exact right-action composition on all states, including oscillators. -/
theorem liftMap_mul (hPos : L.PosDef) (H G R S : Matrix ι ι ℤ) {block : ι → κ}
    (hHG : H + Hᵀ = G)
    (hH : ∀ i j, block i = block j → Even (H i j))
    (hRb : ∀ i j, block i ≠ block j → R i j = 0)
    (hSb : ∀ i j, block i ≠ block j → S i j = 0)
    (hR : R * G * Rᵀ = G) (hS : S * G * Sᵀ = G) :
    liftMap coords H (R * S) = (liftMap coords H S).comp (liftMap coords H R) := by
  unfold liftMap
  rw [rowMap_mul coords R S]
  exact BarnesWall.transported_latMorphC_comp L hPos (halfForm coords H)
    (rowMap coords R) (rowMap coords S) (phase coords H R) (phase coords H S)
    (phase coords H (R * S)) (phase_mul coords H G R S hHG hH hRb hSb hR hS)

theorem matrix_isometry_mul (G R S : Matrix ι ι ℤ)
    (hR : R * G * Rᵀ = G) (hS : S * G * Sᵀ = G) :
    (R * S) * G * (R * S)ᵀ = G := by
  calc
    (R * S) * G * (R * S)ᵀ = R * (S * G * Sᵀ) * Rᵀ := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = G := by rw [hS, hR]

/-- For matrix units, the full-state equality is also equality in conformal `Aut`.
The product on the right applies the lift of `R` first. -/
theorem liftAut_mul (hEven : L.Even) (hPos : L.PosDef) (H G : Matrix ι ι ℤ)
    (R S : (Matrix ι ι ℤ)ˣ) {block : ι → κ}
    (hGram : ∀ x y, L.form x y = coords x ⬝ᵥ (G *ᵥ coords y))
    (hHG : H + Hᵀ = G)
    (hH : ∀ i j, block i = block j → Even (H i j))
    (hRb : ∀ i j, block i ≠ block j → (R : Matrix ι ι ℤ) i j = 0)
    (hSb : ∀ i j, block i ≠ block j → (S : Matrix ι ι ℤ) i j = 0)
    (hR : (R : Matrix ι ι ℤ) * G * (R : Matrix ι ι ℤ)ᵀ = G)
    (hS : (S : Matrix ι ι ℤ) * G * (S : Matrix ι ι ℤ)ᵀ = G) :
    liftAut coords hEven hPos H G (R * S) hGram hHG
        (by simpa only [Units.val_mul] using matrix_isometry_mul G R S hR hS) =
      liftAut coords hEven hPos H G S hGram hHG hS *
        liftAut coords hEven hPos H G R hGram hHG hR := by
  apply VOA.Aut.ext
  apply LinearEquiv.ext
  intro v
  simp only [VOA.Aut.coe_toLinearEquiv, VOA.Aut.mul_apply, liftAut_apply, Units.val_mul]
  exact congrArg (fun f : LatModuleGen L →ₗ[ℂ] LatModuleGen L => f v)
    (liftMap_mul coords hPos H G R S hHG hH hRb hSb hR hS)

end BarnesWall.CanonicalLift
