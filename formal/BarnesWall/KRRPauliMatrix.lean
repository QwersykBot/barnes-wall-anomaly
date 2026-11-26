/-
SPDX-License-Identifier: Apache-2.0
See ../LICENSE-Apache-2.0.txt.
-/
import BarnesWall.PauliPresentation
import BarnesWall.KRRQuaternionAction
import Mathlib.Algebra.Group.Opposite

/-!
# The Pauli presentation as the generated opposite KRR matrix group

The target consists of the actual published integral matrix units, with
opposite multiplication. This convention sends the ordinary abstract words
`z 6 * x 6` and `z 5 * x 5 * z 6` to the prescribed matrix units `a` and `b`.
It therefore retains the future VOA labels `aLift = alpha (z 6 * x 6)` and
`bLift = alpha (z 5 * x 5 * z 6)`.

The subgroup below is the closure of the actual central, X, and Z images.
Faithfulness and generation give an equivalence onto this subgroup. No group
cardinality, unique sorted normal form, or global multiplicativity of a
canonical lattice lift is used or asserted. No VOA action is defined here.
-/

set_option autoImplicit false

noncomputable section

namespace BarnesWall.KRRPauliMatrix

open BarnesWall.Lattice128 PauliPresentation

abbrev Mat := Matrix Index Index ℤ
abbrev OppositeMatrixGroup := (Matˣ)ᵐᵒᵖ

def centralImage : OppositeMatrixGroup :=
  MulOpposite.op KRRQuaternionAction.centralUnit

def xImage (i : Fin 7) : OppositeMatrixGroup :=
  MulOpposite.op (KRRPauli.XUnit i)

def zImage (i : Fin 7) : OppositeMatrixGroup :=
  MulOpposite.op (KRRPauli.ZUnit i)

@[simp] theorem centralImage_val :
    ((MulOpposite.unop centralImage : Matˣ) : Mat) = -1 :=
  KRRQuaternionAction.centralUnit_val

@[simp] theorem xImage_val (i : Fin 7) :
    ((MulOpposite.unop (xImage i) : Matˣ) : Mat) = KRRPauli.X i := rfl

@[simp] theorem zImage_val (i : Fin 7) :
    ((MulOpposite.unop (zImage i) : Matˣ) : Mat) = KRRPauli.Z i := rfl

theorem matrixRelations : Relations centralImage xImage zImage := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply MulOpposite.unop_injective
    apply Units.ext
    change (KRRQuaternionAction.centralUnit : Mat) *
      (KRRQuaternionAction.centralUnit : Mat) = 1
    simp only [KRRQuaternionAction.centralUnit_val, neg_mul_neg, one_mul]
  · intro i
    apply MulOpposite.unop_injective
    apply Units.ext
    change KRRPauli.X i * KRRPauli.X i = 1
    exact KRRPauli.X_sq i
  · intro i
    apply MulOpposite.unop_injective
    apply Units.ext
    change KRRPauli.Z i * KRRPauli.Z i = 1
    exact KRRPauli.Z_sq i
  · intro i
    change centralImage * xImage i = xImage i * centralImage
    apply MulOpposite.unop_injective
    apply Units.ext
    change KRRPauli.X i * (KRRQuaternionAction.centralUnit : Mat) =
      (KRRQuaternionAction.centralUnit : Mat) * KRRPauli.X i
    simp only [KRRQuaternionAction.centralUnit_val, mul_neg, neg_mul,
      mul_one, one_mul]
  · intro i
    change centralImage * zImage i = zImage i * centralImage
    apply MulOpposite.unop_injective
    apply Units.ext
    change KRRPauli.Z i * (KRRQuaternionAction.centralUnit : Mat) =
      (KRRQuaternionAction.centralUnit : Mat) * KRRPauli.Z i
    simp only [KRRQuaternionAction.centralUnit_val, mul_neg, neg_mul,
      mul_one, one_mul]
  · intro i j
    change xImage i * xImage j = xImage j * xImage i
    apply MulOpposite.unop_injective
    apply Units.ext
    change KRRPauli.X j * KRRPauli.X i = KRRPauli.X i * KRRPauli.X j
    exact (KRRQ16.X_commute_X i j).eq.symm
  · intro i j
    change zImage i * zImage j = zImage j * zImage i
    apply MulOpposite.unop_injective
    apply Units.ext
    change KRRPauli.Z j * KRRPauli.Z i = KRRPauli.Z i * KRRPauli.Z j
    exact (KRRQ16.Z_commute_Z i j).eq.symm
  · intro i j
    by_cases hij : i = j
    · subst j
      simp only
      apply MulOpposite.unop_injective
      apply Units.ext
      change KRRPauli.Z i * KRRPauli.X i =
        (KRRPauli.X i * KRRPauli.Z i) *
          (KRRQuaternionAction.centralUnit : Mat)
      simpa only [KRRQuaternionAction.centralUnit_val, mul_neg, mul_one] using
        KRRQ16.Z_mul_X i
    · simp only [ite_eq_right hij, one_mul]
      apply MulOpposite.unop_injective
      apply Units.ext
      change KRRPauli.Z j * KRRPauli.X i = KRRPauli.X i * KRRPauli.Z j
      exact (KRRQ16.X_commute_Z i j hij).eq.symm

theorem centralImage_ne_one : centralImage ≠ 1 := by
  intro h
  have hm := congrArg
    (fun u : OppositeMatrixGroup => ((MulOpposite.unop u : Matˣ) : Mat)) h
  change (KRRQuaternionAction.centralUnit : Mat) = 1 at hm
  rw [KRRQuaternionAction.centralUnit_val] at hm
  exact KRRQ16.neg_one_ne_one hm

/-- The ordinary homomorphism into the opposite group of the actual matrix units. -/
def matrixHom : Pauli 7 →* OppositeMatrixGroup := toGroup matrixRelations

@[simp] theorem matrixHom_central : matrixHom (central 7) = centralImage :=
  toGroup_central matrixRelations

@[simp] theorem matrixHom_x (i : Fin 7) : matrixHom (x i) = xImage i :=
  toGroup_x matrixRelations i

@[simp] theorem matrixHom_z (i : Fin 7) : matrixHom (z i) = zImage i :=
  toGroup_z matrixRelations i

theorem matrixHom_injective : Function.Injective matrixHom :=
  toGroup_injective matrixRelations centralImage_ne_one

/-- The first prescribed quaternion word has exactly the published `a` unit as image. -/
@[simp] theorem matrixHom_aWord :
    matrixHom (z 6 * x 6) = MulOpposite.op KRRQuaternionAction.aUnit := by
  simp only [map_mul, matrixHom_z, matrixHom_x]
  apply MulOpposite.unop_injective
  apply Units.ext
  change KRRPauli.X 6 * KRRPauli.Z 6 = (KRRQuaternionAction.aUnit : Mat)
  rw [KRRQuaternionAction.aUnit_val]
  rfl

/-- The second prescribed quaternion word has exactly the published `b` unit as image. -/
@[simp] theorem matrixHom_bWord :
    matrixHom (z 5 * x 5 * z 6) = MulOpposite.op KRRQ16.bUnit := by
  simp only [map_mul, matrixHom_z, matrixHom_x]
  apply MulOpposite.unop_injective
  apply Units.ext
  change KRRPauli.Z 6 * (KRRPauli.X 5 * KRRPauli.Z 5) = (KRRQ16.bUnit : Mat)
  rw [KRRQ16.bUnit_val]
  rfl

/-- The subgroup generated by the literal central, X, and Z opposite matrix units. -/
def generated : Subgroup OppositeMatrixGroup :=
  Subgroup.closure (Set.range (generatorImage centralImage xImage zImage))

theorem matrixHom_range : matrixHom.range = generated := by
  have hgen :
      matrixHom ∘ (PresentedGroup.of : Generator 7 → Pauli 7) =
        generatorImage centralImage xImage zImage := by
    funext g
    cases g with
    | central => exact matrixHom_central
    | x i => exact matrixHom_x i
    | z i => exact matrixHom_z i
  have h := MonoidHom.map_closure matrixHom
    (Set.range (PresentedGroup.of : Generator 7 → Pauli 7))
  rw [PresentedGroup.closure_range_of, Subgroup.map_top,
    ← Set.range_comp, hgen] at h
  exact h

/-- Faithfulness and generation identify the presentation with its actual matrix subgroup. -/
noncomputable def matrixEquiv : Pauli 7 ≃* generated :=
  (MonoidHom.ofInjective (f := matrixHom) matrixHom_injective).trans
    (MulEquiv.subgroupCongr matrixHom_range)

@[simp] theorem matrixEquiv_coe (g : Pauli 7) :
    (matrixEquiv g : OppositeMatrixGroup) = matrixHom g := rfl

end BarnesWall.KRRPauliMatrix
