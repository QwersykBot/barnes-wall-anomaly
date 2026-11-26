/-
SPDX-License-Identifier: Apache-2.0
See ../LICENSE-Apache-2.0.txt.
-/
import BarnesWall.KRRCanonical
import BarnesWall.KRRQ16
import BarnesWall.QuaternionLift

/-!
# An ordinary faithful quaternion action with the prescribed generator lifts

The concrete canonical map is anti-multiplicative: `lift (R * S) = lift S * lift R`.
Nevertheless, the actual lifts of `g` and `b` satisfy the defining relations of
`QuaternionGroup 4`, with neither generator replaced by its inverse. The checked
matrix relation `b * g * b * g = b * b` first cancels to `g * b * g = b`.
Two applications of canonical anti-composition then give `gLift * bLift * gLift = bLift`.

The resulting ordinary homomorphism preserves the named generators, including
the common quaternion-subgroup generators `a = g^2` and `b`. Its normal form
`xa i` acts as `bLift * gLift^i`, hence corresponds to the matrix word `g^i * b`.
It is NOT the raw map sending every standard matrix label `b * g^i` to its lift.
That matrix-labelled action has the opposite group as its ordinary domain.

This is a source-only candidate pending combined CI. No quaternion relation or
faithfulness premise is assumed: both are derived from the checked matrix and
full-state lift theorems. Agreement with an additional prescribed central lift
is a separate interface and is not claimed here.
-/

set_option autoImplicit false

noncomputable section

namespace BarnesWall.KRRQuaternionAction

open Matrix VOA VOA.LatGen BarnesWall.Lattice128
open scoped Matrix

abbrev Mat := Matrix Index Index ℤ
abbrev Aut128 := VOA.Aut (latticeVOAGen lattice lattice_even lattice_posDef)

theorem one_isometry : (1 : Mat) * G * (1 : Mat)ᵀ = G := by
  simp

private theorem one_supported : KRRCanonical.BlockSupported (1 : Mat) := by
  intro i j h
  have hij : i ≠ j := fun he => h (congrArg KRRBlocks.block he)
  simp [hij]

/-- Identity is forced by the proved composition theorem and cancellation in `Aut`. -/
theorem lift_one : KRRCanonical.lift (1 : Matˣ) one_isometry = 1 := by
  let e : Aut128 := KRRCanonical.lift (1 : Matˣ) one_isometry
  have he : e = e * e := by
    simpa only [one_mul] using
      (KRRCanonical.lift_mul (1 : Matˣ) (1 : Matˣ)
        one_supported one_supported one_isometry one_isometry)
  have he' : e * e = e * 1 := he.symm.trans (mul_one e).symm
  exact mul_left_cancel he'

theorem pow_isometry (R : Matˣ)
    (hR : (R : Mat) * G * (R : Mat)ᵀ = G) (n : ℕ) :
    (↑(R ^ n) : Mat) * G * (↑(R ^ n) : Mat)ᵀ = G := by
  induction n with
  | zero =>
      change (1 : Mat) * G * (1 : Mat)ᵀ = G
      exact one_isometry
  | succ n ih =>
      simpa only [pow_succ, Units.val_mul] using
        KRRQ16.isometry_mul (↑(R ^ n) : Mat) (R : Mat) ih hR

private theorem pow_supported (R : Matˣ)
    (hR : KRRCanonical.BlockSupported (R : Mat)) (n : ℕ) :
    KRRCanonical.BlockSupported (↑(R ^ n) : Mat) := by
  induction n with
  | zero =>
      change KRRCanonical.BlockSupported (1 : Mat)
      exact one_supported
  | succ n ih =>
      unfold KRRCanonical.BlockSupported
      simpa only [pow_succ, Units.val_mul] using
        KRRQ16.block_support_mul (↑(R ^ n) : Mat) (R : Mat) ih hR

/-- Anti-composition agrees with ordinary powers of one supported isometry. -/
theorem lift_pow (R : Matˣ) (hRb : KRRCanonical.BlockSupported (R : Mat))
    (hR : (R : Mat) * G * (R : Mat)ᵀ = G) (n : ℕ) :
    KRRCanonical.lift (R ^ n) (pow_isometry R hR n) =
      (KRRCanonical.lift R hR) ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using lift_one
  | succ n ih =>
      calc
        KRRCanonical.lift (R ^ (n + 1)) (pow_isometry R hR (n + 1)) =
            KRRCanonical.lift R hR *
              KRRCanonical.lift (R ^ n) (pow_isometry R hR n) := by
          simpa only [pow_succ] using
            (KRRCanonical.lift_mul (R ^ n) R (pow_supported R hRb n) hRb
              (pow_isometry R hR n) hR)
        _ = KRRCanonical.lift R hR * (KRRCanonical.lift R hR) ^ n := by rw [ih]
        _ = (KRRCanonical.lift R hR) ^ (n + 1) := (pow_succ' _ _).symm

private theorem lift_eq_of_unit_eq (R S : Matˣ)
    (hR : (R : Mat) * G * (R : Mat)ᵀ = G)
    (hS : (S : Mat) * G * (S : Mat)ᵀ = G) (h : R = S) :
    KRRCanonical.lift R hR = KRRCanonical.lift S hS := by
  cases h
  rfl

/-- The exact canonical lift of the checked integral order-eight matrix unit. -/
def gLift : Aut128 := KRRCanonical.lift KRRQ16.gUnit KRRQ16.g_isometry

/-- The exact canonical lift of the prescribed second quaternion generator. -/
def bLift : Aut128 := KRRCanonical.lift KRRQ16.bUnit KRRQ16.b_isometry

/-- The unit whose underlying matrix is the prescribed `a = g^2`. -/
def aUnit : Matˣ := KRRQ16.gUnit ^ 2

@[simp] theorem aUnit_val : (aUnit : Mat) = KRRQ16.a := by
  change KRRQ16.g ^ 2 = KRRQ16.a
  simpa only [pow_two] using KRRQ16.g_sq

theorem aUnit_isometry : (aUnit : Mat) * G * (aUnit : Mat)ᵀ = G :=
  pow_isometry KRRQ16.gUnit KRRQ16.g_isometry 2

def aLift : Aut128 := KRRCanonical.lift aUnit aUnit_isometry

/-- This actual unit has underlying matrix `-I`; no central-lift identification is assumed. -/
def centralUnit : Matˣ := KRRQ16.gUnit ^ 4

@[simp] theorem centralUnit_val : (centralUnit : Mat) = -1 := by
  change KRRQ16.g ^ 4 = -1
  exact KRRQ16.g_four

theorem centralUnit_isometry : (centralUnit : Mat) * G * (centralUnit : Mat)ᵀ = G :=
  pow_isometry KRRQ16.gUnit KRRQ16.g_isometry 4

def centralLift : Aut128 := KRRCanonical.lift centralUnit centralUnit_isometry

theorem gLift_sq : gLift ^ 2 = aLift :=
  (lift_pow KRRQ16.gUnit KRRQ16.g_block_support KRRQ16.g_isometry 2).symm

theorem gLift_four : gLift ^ 4 = centralLift :=
  (lift_pow KRRQ16.gUnit KRRQ16.g_block_support KRRQ16.g_isometry 4).symm

private theorem gUnit_eight : KRRQ16.gUnit ^ 8 = 1 := by
  apply Units.ext
  change KRRQ16.g ^ 8 = 1
  exact KRRQ16.g_eight

private theorem bUnit_sq : KRRQ16.bUnit ^ 2 = KRRQ16.gUnit ^ 4 := by
  apply Units.ext
  change KRRQ16.b ^ 2 = KRRQ16.g ^ 4
  rw [pow_two, KRRQ16.b_sq, KRRQ16.g_four]

private theorem gUnit_bUnit_gUnit :
    KRRQ16.gUnit * KRRQ16.bUnit * KRRQ16.gUnit = KRRQ16.bUnit := by
  apply mul_left_cancel (a := KRRQ16.bUnit)
  apply Units.ext
  change KRRQ16.b * (KRRQ16.g * KRRQ16.b * KRRQ16.g) = KRRQ16.b * KRRQ16.b
  simpa only [mul_assoc] using KRRQ16.b_g_b_g.trans KRRQ16.b_sq.symm

/-- The reversed defining matrix word follows by cancellation, not by assumption. -/
theorem reversed_unit_word :
    KRRQ16.gUnit * KRRQ16.bUnit * KRRQ16.gUnit * KRRQ16.bUnit =
      KRRQ16.bUnit ^ 2 := by
  rw [gUnit_bUnit_gUnit, pow_two]

theorem gLift_eight : gLift ^ 8 = 1 := by
  calc
    gLift ^ 8 = KRRCanonical.lift (KRRQ16.gUnit ^ 8)
        (pow_isometry KRRQ16.gUnit KRRQ16.g_isometry 8) :=
      (lift_pow KRRQ16.gUnit KRRQ16.g_block_support KRRQ16.g_isometry 8).symm
    _ = KRRCanonical.lift (1 : Matˣ) one_isometry :=
      lift_eq_of_unit_eq _ _ _ _ gUnit_eight
    _ = 1 := lift_one

theorem bLift_sq : bLift ^ 2 = gLift ^ 4 := by
  calc
    bLift ^ 2 = KRRCanonical.lift (KRRQ16.bUnit ^ 2)
        (pow_isometry KRRQ16.bUnit KRRQ16.b_isometry 2) :=
      (lift_pow KRRQ16.bUnit KRRQ16.b_block_support KRRQ16.b_isometry 2).symm
    _ = KRRCanonical.lift (KRRQ16.gUnit ^ 4)
        (pow_isometry KRRQ16.gUnit KRRQ16.g_isometry 4) :=
      lift_eq_of_unit_eq _ _ _ _ bUnit_sq
    _ = gLift ^ 4 :=
      lift_pow KRRQ16.gUnit KRRQ16.g_block_support KRRQ16.g_isometry 4

private theorem mul_eq_mul_inv_of_products {Γ : Type*} [Group Γ]
    (a b c : Γ) (hcb : c = b * a) (hac : a * c = b) :
    a * b = b * a⁻¹ := by
  apply (_root_.eq_mul_inv_iff_mul_eq (a := a * b) (b := b) (c := a)).mpr
  exact (_root_.mul_assoc a b a).trans
    ((congrArg (fun x : Γ => a * x) hcb.symm).trans hac)

/-- Two full-state anti-compositions transport the actual palindrome `g b g = b`. -/
theorem gLift_mul_bLift : gLift * bLift = bLift * gLift⁻¹ := by
  let U : Matˣ := KRRQ16.gUnit * KRRQ16.bUnit
  have hUb : KRRCanonical.BlockSupported (U : Mat) :=
    KRRQ16.block_support_mul KRRQ16.g KRRQ16.b
      KRRQ16.g_block_support KRRQ16.b_block_support
  have hU : (U : Mat) * G * (U : Mat)ᵀ = G :=
    KRRQ16.isometry_mul KRRQ16.g KRRQ16.b KRRQ16.g_isometry KRRQ16.b_isometry
  have hUg : (↑(U * KRRQ16.gUnit) : Mat) * G *
      (↑(U * KRRQ16.gUnit) : Mat)ᵀ = G :=
    KRRQ16.isometry_mul (U : Mat) KRRQ16.g hU KRRQ16.g_isometry
  have hfirst : KRRCanonical.lift U hU = bLift * gLift :=
    KRRCanonical.lift_mul KRRQ16.gUnit KRRQ16.bUnit
      KRRQ16.g_block_support KRRQ16.b_block_support
      KRRQ16.g_isometry KRRQ16.b_isometry
  have hsecond : KRRCanonical.lift (U * KRRQ16.gUnit) hUg =
      gLift * KRRCanonical.lift U hU :=
    KRRCanonical.lift_mul U KRRQ16.gUnit hUb KRRQ16.g_block_support hU KRRQ16.g_isometry
  have heq : KRRCanonical.lift (U * KRRQ16.gUnit) hUg = bLift :=
    lift_eq_of_unit_eq (U * KRRQ16.gUnit) KRRQ16.bUnit
      hUg KRRQ16.b_isometry gUnit_bUnit_gUnit
  exact mul_eq_mul_inv_of_products (Γ := Aut128) gLift bLift
    (KRRCanonical.lift U hU) hfirst (hsecond.symm.trans heq)

/-- The center cannot collapse: equality of full lifts would force `-I = I`. -/
theorem gLift_four_ne_one : gLift ^ 4 ≠ 1 := by
  intro h
  have he : centralLift = KRRCanonical.lift (1 : Matˣ) one_isometry :=
    (gLift_four.symm.trans h).trans lift_one.symm
  have hm := KRRCanonical.matrix_eq_of_lift_eq centralUnit (1 : Matˣ)
    centralUnit_isometry one_isometry he
  change (centralUnit : Mat) = (1 : Mat) at hm
  exact KRRQ16.neg_one_ne_one (centralUnit_val.symm.trans hm)

/-- Ordinary action with `a 1 ↦ lift(g)` and `xa 0 ↦ lift(b)`. -/
def action : QuaternionGroup 4 →* Aut128 :=
  QuaternionLift.ofRelations gLift bLift gLift_eight bLift_sq gLift_mul_bLift

@[simp] theorem action_a_one : action (QuaternionGroup.a 1) = gLift :=
  QuaternionLift.ofRelations_a_one gLift bLift gLift_eight bLift_sq gLift_mul_bLift

@[simp] theorem action_xa_zero : action (QuaternionGroup.xa 0) = bLift :=
  QuaternionLift.ofRelations_xa_zero gLift bLift gLift_eight bLift_sq gLift_mul_bLift

/-- Literal image of the first common `Q8` generator, whose matrix is `a = g^2`. -/
@[simp] theorem action_a_two : action (QuaternionGroup.a 2) = aLift :=
  (QuaternionLift.ofRelations_a_two gLift bLift gLift_eight bLift_sq gLift_mul_bLift).trans
    gLift_sq

/-- The central element maps to the canonical lift of the actual matrix `-I`. -/
@[simp] theorem action_a_four : action (QuaternionGroup.a 4) = centralLift :=
  (QuaternionLift.ofRelations_a_four gLift bLift gLift_eight bLift_sq gLift_mul_bLift).trans
    gLift_four

/-- This order is explicit: `xa k` acts by `bLift * gLift^k`. -/
theorem action_xa_nat (k : ℕ) :
    action (QuaternionGroup.xa (k : ZMod 8)) = bLift * gLift ^ k := by
  have hn : (QuaternionGroup.xa (k : ZMod 8) : QuaternionGroup 4) =
      QuaternionGroup.xa 0 * (QuaternionGroup.a 1) ^ k := by
    rw [QuaternionGroup.a_one_pow, QuaternionGroup.xa_mul_a, zero_add]
  rw [hn, map_mul, map_pow, action_xa_zero, action_a_one]

/-- Faithfulness uses the actual nontrivial central lift, not a matrix-only action. -/
theorem action_injective : Function.Injective action :=
  QuaternionLift.ofRelations_injective gLift bLift gLift_eight bLift_sq gLift_mul_bLift
    gLift_four_ne_one

end BarnesWall.KRRQuaternionAction
