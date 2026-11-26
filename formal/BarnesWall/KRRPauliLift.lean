/-
SPDX-License-Identifier: Apache-2.0
See ../LICENSE-Apache-2.0.txt.
-/
import BarnesWall.KRRSupportedLift
import BarnesWall.KRRCentralLift

/-!
# The actual full-state Pauli lifts satisfy the extraspecial relations

The generators below are literally the canonical lifts of `XUnit k` and
`ZUnit k`. Every composition used here has a common support of one or two
numerical bit positions. The fixed ordered half-Gram matrix and the one global
cocycle transport are unchanged.

Canonical lifts reverse matrix products. Thus `xLift k * zLift k` lifts `ZX`,
whereas `thetaAut * (zLift k * xLift k)` lifts `(XZ)(-I)`. The checked matrix
identity `ZX = -(XZ)` proves the displayed ordinary-Aut anticommutation law.
This is a relation adapter, not a constructed action of a presented group.
-/

set_option autoImplicit false

noncomputable section

namespace BarnesWall.KRRPauliLift

open Matrix VOA VOA.LatGen BarnesWall.Lattice128
open scoped Matrix

abbrev Mat := Matrix Index Index ℤ
abbrev Aut128 := KRRQuaternionAction.Aut128

/-- The literal canonical lift of the integral X involution at numerical bit k. -/
def xLift (k : Fin 7) : Aut128 :=
  KRRCanonical.lift (KRRPauli.XUnit k) (KRRPauli.X_isometry k)

/-- The literal canonical lift of the integral Z involution at numerical bit k. -/
def zLift (k : Fin 7) : Aut128 :=
  KRRCanonical.lift (KRRPauli.ZUnit k) (KRRPauli.Z_isometry k)

private theorem mul_isometry (R T : Matˣ)
    (hR : (R : Mat) * G * (R : Mat)ᵀ = G)
    (hT : (T : Mat) * G * (T : Mat)ᵀ = G) :
    (↑(R * T) : Mat) * G * (↑(R * T) : Mat)ᵀ = G := by
  simpa only [Units.val_mul] using
    (CanonicalLift.matrix_isometry_mul G (R : Mat) (T : Mat) hR hT)

private theorem lift_eq_of_val_eq (R T : Matˣ)
    (hR : (R : Mat) * G * (R : Mat)ᵀ = G)
    (hT : (T : Mat) * G * (T : Mat)ᵀ = G) (h : (R : Mat) = (T : Mat)) :
    KRRCanonical.lift R hR = KRRCanonical.lift T hT := by
  have hu : R = T := Units.ext h
  cases hu
  rfl

private theorem lift_mul_eq (s : Finset (Fin 7)) (hs : s.card ≤ 3)
    (R T U : Matˣ)
    (hRs : KRRSupport.Supported s (R : Mat))
    (hTs : KRRSupport.Supported s (T : Mat))
    (hR : (R : Mat) * G * (R : Mat)ᵀ = G)
    (hT : (T : Mat) * G * (T : Mat)ᵀ = G)
    (hU : (U : Mat) * G * (U : Mat)ᵀ = G)
    (h : (T : Mat) * (R : Mat) = (U : Mat)) :
    KRRCanonical.lift R hR * KRRCanonical.lift T hT = KRRCanonical.lift U hU := by
  calc
    KRRCanonical.lift R hR * KRRCanonical.lift T hT =
        KRRCanonical.lift (T * R) (mul_isometry T R hT hR) :=
      (KRRCanonical.lift_mul_of_small_support s hs T R hTs hRs hT hR).symm
    _ = KRRCanonical.lift U hU :=
      lift_eq_of_val_eq (T * R) U (mul_isometry T R hT hR) hU
        (by simpa only [Units.val_mul] using h)

private theorem lift_commute (s : Finset (Fin 7)) (hs : s.card ≤ 3)
    (R T : Matˣ)
    (hRs : KRRSupport.Supported s (R : Mat))
    (hTs : KRRSupport.Supported s (T : Mat))
    (hR : (R : Mat) * G * (R : Mat)ᵀ = G)
    (hT : (T : Mat) * G * (T : Mat)ᵀ = G)
    (hRT : Commute (R : Mat) (T : Mat)) :
    Commute (KRRCanonical.lift R hR) (KRRCanonical.lift T hT) := by
  change KRRCanonical.lift R hR * KRRCanonical.lift T hT =
    KRRCanonical.lift T hT * KRRCanonical.lift R hR
  exact
    (lift_mul_eq s hs R T (R * T) hRs hTs hR hT (mul_isometry R T hR hT)
      (by simpa only [Units.val_mul] using hRT.eq.symm)).trans
    (KRRCanonical.lift_mul_of_small_support s hs R T hRs hTs hR hT)

private theorem supported_mul (s : Finset (Fin 7)) (R T : Mat)
    (hR : KRRSupport.Supported s R) (hT : KRRSupport.Supported s T) :
    KRRSupport.Supported s (R * T) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : KRRSupport.block s i = KRRSupport.block s k
  · rw [hT k j (fun hkj => hij (hik.trans hkj)), mul_zero]
  · rw [hR i k hik, zero_mul]

private theorem central_supported (s : Finset (Fin 7)) :
    KRRSupport.Supported s (KRRQuaternionAction.centralUnit : Mat) := by
  intro i j h
  have hij : i ≠ j := fun he => h (congrArg (KRRSupport.block s) he)
  rw [KRRQuaternionAction.centralUnit_val]
  simp [hij]

private theorem pair_card_le_three (k l : Fin 7) :
    ({k, l} : Finset (Fin 7)).card ≤ 3 :=
  (show ({k, l} : Finset (Fin 7)).card ≤ 2 from Finset.card_le_two).trans (by decide)

theorem xLift_sq (k : Fin 7) : xLift k ^ 2 = 1 := by
  rw [pow_two]
  exact
    (lift_mul_eq {k} (by simp) (KRRPauli.XUnit k) (KRRPauli.XUnit k) (1 : Matˣ)
      (KRRSupport.X_supported {k} k (by simp))
      (KRRSupport.X_supported {k} k (by simp))
      (KRRPauli.X_isometry k) (KRRPauli.X_isometry k) KRRQuaternionAction.one_isometry
      (KRRPauli.X_sq k)).trans KRRQuaternionAction.lift_one

theorem zLift_sq (k : Fin 7) : zLift k ^ 2 = 1 := by
  rw [pow_two]
  exact
    (lift_mul_eq {k} (by simp) (KRRPauli.ZUnit k) (KRRPauli.ZUnit k) (1 : Matˣ)
      (KRRSupport.Z_supported {k} k (by simp))
      (KRRSupport.Z_supported {k} k (by simp))
      (KRRPauli.Z_isometry k) (KRRPauli.Z_isometry k) KRRQuaternionAction.one_isometry
      (KRRPauli.Z_sq k)).trans KRRQuaternionAction.lift_one

theorem xLift_commute_xLift (k l : Fin 7) : Commute (xLift k) (xLift l) :=
  lift_commute {k, l} (pair_card_le_three k l) (KRRPauli.XUnit k) (KRRPauli.XUnit l)
    (KRRSupport.X_supported {k, l} k (by simp))
    (KRRSupport.X_supported {k, l} l (by simp))
    (KRRPauli.X_isometry k) (KRRPauli.X_isometry l) (KRRQ16.X_commute_X k l)

theorem zLift_commute_zLift (k l : Fin 7) : Commute (zLift k) (zLift l) :=
  lift_commute {k, l} (pair_card_le_three k l) (KRRPauli.ZUnit k) (KRRPauli.ZUnit l)
    (KRRSupport.Z_supported {k, l} k (by simp))
    (KRRSupport.Z_supported {k, l} l (by simp))
    (KRRPauli.Z_isometry k) (KRRPauli.Z_isometry l) (KRRQ16.Z_commute_Z k l)

theorem xLift_commute_zLift_of_ne (k l : Fin 7) (h : k ≠ l) :
    Commute (xLift k) (zLift l) :=
  lift_commute {k, l} (pair_card_le_three k l) (KRRPauli.XUnit k) (KRRPauli.ZUnit l)
    (KRRSupport.X_supported {k, l} k (by simp))
    (KRRSupport.Z_supported {k, l} l (by simp))
    (KRRPauli.X_isometry k) (KRRPauli.Z_isometry l) (KRRQ16.X_commute_Z k l h)

theorem theta_commute_xLift (k : Fin 7) :
    Commute (thetaAut lattice lattice_even lattice_posDef) (xLift k) := by
  rw [← KRRCentralLift.centralLift_eq_thetaAut]
  refine lift_commute {k} (by simp) KRRQuaternionAction.centralUnit (KRRPauli.XUnit k)
    (central_supported {k}) (KRRSupport.X_supported {k} k (by simp))
    KRRQuaternionAction.centralUnit_isometry (KRRPauli.X_isometry k) ?_
  change (KRRQuaternionAction.centralUnit : Mat) * KRRPauli.X k =
    KRRPauli.X k * (KRRQuaternionAction.centralUnit : Mat)
  rw [KRRQuaternionAction.centralUnit_val]
  simp only [Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one]

theorem theta_commute_zLift (k : Fin 7) :
    Commute (thetaAut lattice lattice_even lattice_posDef) (zLift k) := by
  rw [← KRRCentralLift.centralLift_eq_thetaAut]
  refine lift_commute {k} (by simp) KRRQuaternionAction.centralUnit (KRRPauli.ZUnit k)
    (central_supported {k}) (KRRSupport.Z_supported {k} k (by simp))
    KRRQuaternionAction.centralUnit_isometry (KRRPauli.Z_isometry k) ?_
  change (KRRQuaternionAction.centralUnit : Mat) * KRRPauli.Z k =
    KRRPauli.Z k * (KRRQuaternionAction.centralUnit : Mat)
  rw [KRRQuaternionAction.centralUnit_val]
  simp only [Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg, Matrix.mul_one]

/-- The sign is the actual upstream lattice involution, in ordinary Aut order. -/
theorem xLift_mul_zLift (k : Fin 7) :
    xLift k * zLift k =
      thetaAut lattice lattice_even lattice_posDef * (zLift k * xLift k) := by
  let U : Matˣ := KRRPauli.XUnit k * KRRPauli.ZUnit k
  let V : Matˣ := KRRPauli.ZUnit k * KRRPauli.XUnit k
  have hU : (U : Mat) * G * (U : Mat)ᵀ = G :=
    mul_isometry (KRRPauli.XUnit k) (KRRPauli.ZUnit k)
      (KRRPauli.X_isometry k) (KRRPauli.Z_isometry k)
  have hV : (V : Mat) * G * (V : Mat)ᵀ = G :=
    mul_isometry (KRRPauli.ZUnit k) (KRRPauli.XUnit k)
      (KRRPauli.Z_isometry k) (KRRPauli.X_isometry k)
  have hUs : KRRSupport.Supported {k} (U : Mat) :=
    supported_mul {k} (KRRPauli.X k) (KRRPauli.Z k)
      (KRRSupport.X_supported {k} k (by simp))
      (KRRSupport.Z_supported {k} k (by simp))
  have hUL : KRRCanonical.lift U hU = zLift k * xLift k :=
    KRRCanonical.lift_mul_of_small_support {k} (by simp)
      (KRRPauli.XUnit k) (KRRPauli.ZUnit k)
      (KRRSupport.X_supported {k} k (by simp))
      (KRRSupport.Z_supported {k} k (by simp))
      (KRRPauli.X_isometry k) (KRRPauli.Z_isometry k)
  have hVL : KRRCanonical.lift V hV = xLift k * zLift k :=
    KRRCanonical.lift_mul_of_small_support {k} (by simp)
      (KRRPauli.ZUnit k) (KRRPauli.XUnit k)
      (KRRSupport.Z_supported {k} k (by simp))
      (KRRSupport.X_supported {k} k (by simp))
      (KRRPauli.Z_isometry k) (KRRPauli.X_isometry k)
  have hneg : (U : Mat) * (KRRQuaternionAction.centralUnit : Mat) = (V : Mat) := by
    change (KRRPauli.X k * KRRPauli.Z k) * (KRRQuaternionAction.centralUnit : Mat) =
      KRRPauli.Z k * KRRPauli.X k
    rw [KRRQuaternionAction.centralUnit_val, Matrix.mul_neg, Matrix.mul_one]
    exact (KRRQ16.Z_mul_X k).symm
  have hc : KRRQuaternionAction.centralLift * KRRCanonical.lift U hU =
      KRRCanonical.lift V hV :=
    lift_mul_eq {k} (by simp) KRRQuaternionAction.centralUnit U V
      (central_supported {k}) hUs KRRQuaternionAction.centralUnit_isometry hU hV hneg
  calc
    xLift k * zLift k = KRRCanonical.lift V hV := hVL.symm
    _ = KRRQuaternionAction.centralLift * KRRCanonical.lift U hU := hc.symm
    _ = thetaAut lattice lattice_even lattice_posDef * (zLift k * xLift k) := by
      rw [hUL, KRRCentralLift.centralLift_eq_thetaAut]

theorem theta_sq : (thetaAut lattice lattice_even lattice_posDef) ^ 2 = 1 := by
  simpa only [pow_two] using (VOA.LatGen.thetaAut_sq lattice lattice_even lattice_posDef)

theorem theta_ne_one : thetaAut lattice lattice_even lattice_posDef ≠ 1 := by
  intro h
  exact KRRQuaternionAction.gLift_four_ne_one
    (KRRQuaternionAction.gLift_four.trans (KRRCentralLift.centralLift_eq_thetaAut.trans h))

theorem theta_orderOf : orderOf (thetaAut lattice lattice_even lattice_posDef) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime theta_sq theta_ne_one

/-- The first prescribed Q8 generator keeps the exact reversed X/Z word. -/
theorem aLift_eq_zLift_mul_xLift : KRRQuaternionAction.aLift = zLift 6 * xLift 6 := by
  symm
  exact lift_mul_eq {6} (by simp) (KRRPauli.ZUnit 6) (KRRPauli.XUnit 6)
    KRRQuaternionAction.aUnit
    (KRRSupport.Z_supported {6} 6 (by simp))
    (KRRSupport.X_supported {6} 6 (by simp))
    (KRRPauli.Z_isometry 6) (KRRPauli.X_isometry 6) KRRQuaternionAction.aUnit_isometry
    KRRQuaternionAction.aUnit_val.symm

/-- The second prescribed Q8 generator is the literal reversed three-factor word. -/
theorem bLift_eq_zLift_mul_xLift_mul_zLift :
    KRRQuaternionAction.bLift = (zLift 5 * xLift 5) * zLift 6 := by
  let U : Matˣ := KRRPauli.XUnit 5 * KRRPauli.ZUnit 5
  have hU : (U : Mat) * G * (U : Mat)ᵀ = G :=
    mul_isometry (KRRPauli.XUnit 5) (KRRPauli.ZUnit 5)
      (KRRPauli.X_isometry 5) (KRRPauli.Z_isometry 5)
  have hUs : KRRSupport.Supported {5, 6} (U : Mat) :=
    supported_mul {5, 6} (KRRPauli.X 5) (KRRPauli.Z 5)
      (KRRSupport.X_supported {5, 6} 5 (by simp))
      (KRRSupport.Z_supported {5, 6} 5 (by simp))
  have hUL : KRRCanonical.lift U hU = zLift 5 * xLift 5 :=
    KRRCanonical.lift_mul_of_small_support {5} (by simp)
      (KRRPauli.XUnit 5) (KRRPauli.ZUnit 5)
      (KRRSupport.X_supported {5} 5 (by simp))
      (KRRSupport.Z_supported {5} 5 (by simp))
      (KRRPauli.X_isometry 5) (KRRPauli.Z_isometry 5)
  have hb : KRRCanonical.lift U hU * zLift 6 = KRRQuaternionAction.bLift :=
    lift_mul_eq {5, 6} (pair_card_le_three 5 6) U (KRRPauli.ZUnit 6) KRRQ16.bUnit
      hUs (KRRSupport.Z_supported {5, 6} 6 (by simp))
      hU (KRRPauli.Z_isometry 6) KRRQ16.b_isometry rfl
  calc
    KRRQuaternionAction.bLift = KRRCanonical.lift U hU * zLift 6 := hb.symm
    _ = (zLift 5 * xLift 5) * zLift 6 :=
      congrArg (fun F : Aut128 => F * zLift 6) hUL

end BarnesWall.KRRPauliLift
