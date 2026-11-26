/-
SPDX-License-Identifier: Apache-2.0
See ../LICENSE-Apache-2.0.txt.
-/
import BarnesWall.CanonicalLift

/-!
# The canonical central lift is the prescribed lattice involution

For the matrix `-1`, the chosen integer exponent is zero and the single global
cocycle transport has ratio one. The oscillator map negates each polynomial
generator, exactly as upstream `sigmaN` does. Spanning elementary lattice states
then identify the full linear map with upstream `thetaLat`.

The linear-map theorem requires positive definiteness for the upstream frame
cancellation, but no Gram, evenness, block-support, or anomaly hypothesis.
-/

set_option autoImplicit false

noncomputable section

namespace BarnesWall.CanonicalLift

open Matrix VOA VOA.IntegralLattice VOA.LatGen
open HeisenbergN MvPolynomial
open scoped Matrix BigOperators

variable {L : VOA.IntegralLattice} {ι : Type*} [Fintype ι] [LinearOrder ι]
variable (coords : L.carrier ≃ₗ[ℤ] (ι → ℤ))

private theorem rowMap_neg_one :
    rowMap coords (-1 : Matrix ι ι ℤ) = -(LinearMap.id : L.carrier →ₗ[ℤ] L.carrier) := by
  apply LinearMap.ext
  intro x
  apply coords.injective
  simp only [coords_rowMap, LinearMap.neg_apply, LinearMap.id_apply, map_neg,
    Matrix.vecMul_neg, Matrix.vecMul_one]

private theorem phase_neg_one (H : Matrix ι ι ℤ) (x : L.carrier) :
    phase coords H (-1) x = 1 := by
  simp [phase, IntegerPhase.phase, IntegerPhase.exponent,
    IntegerPhase.canonicalMatrix, IntegerPhase.liftDefect,
    IntegerPhase.strictLower, Matrix.mulVec, dotProduct]

private theorem transportedPhase_neg_one (H : Matrix ι ι ℤ) (x : L.carrier) :
    BarnesWall.transportedPhase L (halfForm coords H) (rowMap coords (-1))
      (phase coords H (-1)) x = 1 := by
  rw [BarnesWall.transportedPhase, phase_neg_one, rowMap_neg_one]
  simp only [LinearMap.neg_apply, LinearMap.id_apply, BarnesWall.globalTau_neg, one_mul]
  exact div_self (BarnesWall.globalTau_ne_zero L (halfForm coords H) x)

private theorem latMatrix_neg (f : L.carrier →ₗ[ℤ] L.carrier) :
    latMatrix L L (-f) = -latMatrix L L f := by
  ext j i
  simp [latMatrix, coordR, coord]

private theorem oscMatrix_neg (f : L.carrier →ₗ[ℤ] L.carrier) :
    oscMatrix L L (-f) = -oscMatrix L L f := by
  have hframe : frameMatrix L L (-f) = -frameMatrix L L f := by
    simp only [frameMatrix, latMatrix_neg, mul_neg, neg_mul]
  ext a b
  change (frameMatrix L L (-f) (rankEquiv L a) (rankEquiv L b) : ℂ) =
    -(frameMatrix L L f (rankEquiv L a) (rankEquiv L b) : ℂ)
  rw [hframe]
  simp

private theorem fockMap_neg_one {r : ℕ} (p : FockN r) :
    fockMap (-1 : Matrix (Fin r) (Fin r) ℂ) p = sigmaN r p := by
  have h : fockMap (-1 : Matrix (Fin r) (Fin r) ℂ) = sigmaAlg r := by
    refine MvPolynomial.algHom_ext fun v => ?_
    obtain ⟨k, a⟩ := v
    rw [fockMap_X, sigmaAlg_X, Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Matrix.one_apply, hb]
    · intro ha
      exact False.elim (ha (Finset.mem_univ a))
  rw [sigmaN_apply, h]

/-- The chosen central lift agrees with the prescribed involution on every state. -/
theorem liftMap_neg_one (hPos : L.PosDef) (H : Matrix ι ι ℤ) :
    liftMap coords H (-1) = (thetaLat L).toLinearMap := by
  refine LinearMap.ext_on_range (latStateGen_span L) fun q => ?_
  obtain ⟨p, α⟩ := q
  change liftMap coords H (-1) (latStateGen L p α) =
    thetaLat L (latStateGen L p α)
  rw [liftMap, latMorphC_latStateGen, transportedPhase_neg_one,
    rowMap_neg_one, oscMatrix_neg, oscMatrix_id L hPos,
    fockMap_neg_one, thetaLat_latStateGen]
  simp only [one_smul, LinearMap.neg_apply, LinearMap.id_apply]

/-- Any matrix unit with underlying matrix `-1` gives exactly upstream `thetaAut`. -/
theorem liftAut_eq_thetaAut_of_val_neg_one
    (hEven : L.Even) (hPos : L.PosDef) (H G : Matrix ι ι ℤ)
    (R : (Matrix ι ι ℤ)ˣ)
    (hGram : ∀ x y, L.form x y = coords x ⬝ᵥ (G *ᵥ coords y))
    (hHG : H + Hᵀ = G)
    (hR : (R : Matrix ι ι ℤ) * G * (R : Matrix ι ι ℤ)ᵀ = G)
    (hNeg : (R : Matrix ι ι ℤ) = -1) :
    liftAut coords hEven hPos H G R hGram hHG hR = thetaAut L hEven hPos := by
  apply VOA.Aut.ext
  apply LinearEquiv.ext
  intro v
  simp only [liftAut_apply, hNeg, thetaAut_apply]
  exact LinearMap.congr_fun (liftMap_neg_one coords hPos H) v

end BarnesWall.CanonicalLift
