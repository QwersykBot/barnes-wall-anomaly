/-
SPDX-License-Identifier: Apache-2.0

The additional generator is defined by integral rows in the exact ordered KRR
basis. Tensor positions 1,2,3 are numerical bits 6,5,4. All matrix and block
identities below are derived; no group or canonical-phase relation is assumed.
-/
import BarnesWall.KRRPauli

set_option autoImplicit false

noncomputable section

namespace BarnesWall.KRRQ16

open Matrix BarnesWall.Lattice128 BarnesWall.KRRPauli
open scoped Matrix BigOperators

abbrev Mat := Matrix Index Index ℤ

theorem toggle_commute (k l : Fin 7) (i : Index) :
    toggle k (toggle l i) = toggle l (toggle k i) := by
  by_cases h : k = l
  · subst l
    rfl
  have hkl : k.val ≠ l.val := fun heq => h (Fin.ext heq)
  apply support_injective
  apply Finset.ext
  intro a
  by_cases hak : a = k.val
  · subst a
    simp only [mem_support_toggle_self, mem_support_toggle_of_ne l i hkl,
      mem_support_toggle_of_ne l (toggle k i) hkl]
  by_cases hal : a = l.val
  · subst a
    simp only [mem_support_toggle_self, mem_support_toggle_of_ne k i (Ne.symm hkl),
      mem_support_toggle_of_ne k (toggle l i) (Ne.symm hkl)]
  · simp only [mem_support_toggle_of_ne k (toggle l i) hak,
      mem_support_toggle_of_ne l i hal, mem_support_toggle_of_ne l (toggle k i) hal,
      mem_support_toggle_of_ne k i hak]

theorem cartSign_toggle (k : Fin 7) (i : Index) :
    cartSign k (toggle k i) = -cartSign k i := by
  by_cases hi : k.val ∈ support i <;> simp [cartSign, hi]

theorem cartSign_toggle_of_ne (k l : Fin 7) (h : k ≠ l) (i : Index) :
    cartSign k (toggle l i) = cartSign k i := by
  have hv : k.val ≠ l.val := fun heq => h (Fin.ext heq)
  simp only [cartSign, mem_support_toggle_of_ne l i hv]

theorem cartX_commute (k l : Fin 7) : Commute (cartX k) (cartX l) := by
  change cartX k * cartX l = cartX l * cartX k
  funext i j
  rw [mul_cartX_apply, mul_cartX_apply]
  simp only [cartX, toggle_commute k l j]

theorem cartZ_commute (k l : Fin 7) : Commute (cartZ k) (cartZ l) := by
  change Matrix.diagonal (cartSign k) * Matrix.diagonal (cartSign l) =
    Matrix.diagonal (cartSign l) * Matrix.diagonal (cartSign k)
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem cartX_cartZ_commute (k l : Fin 7) (h : k ≠ l) :
    Commute (cartX k) (cartZ l) := by
  change cartX k * cartZ l = cartZ l * cartX k
  funext i j
  rw [mul_cartZ_apply, mul_cartX_apply]
  by_cases hij : i = toggle k j
  · subst i
    simp [cartX, cartZ, Matrix.diagonal, cartSign_toggle_of_ne l k (Ne.symm h)]
  · simp [cartX, cartZ, Matrix.diagonal, hij]

theorem cartZ_mul_cartX (k : Fin 7) :
    cartZ k * cartX k = -(cartX k * cartZ k) := by
  funext i j
  change (cartZ k * cartX k) i j = -(cartX k * cartZ k) i j
  rw [mul_cartX_apply, mul_cartZ_apply]
  by_cases hij : i = toggle k j
  · subst i
    simp [cartX, cartZ, Matrix.diagonal, cartSign_toggle]
  · simp [cartX, cartZ, Matrix.diagonal, hij]

theorem product_intertwining (R S C D : Mat)
    (hR : R * B = B * C) (hS : S * B = B * D) :
    (R * S) * B = B * (C * D) := by
  calc
    (R * S) * B = R * (S * B) := Matrix.mul_assoc _ _ _
    _ = R * (B * D) := by rw [hS]
    _ = (R * B) * D := (Matrix.mul_assoc _ _ _).symm
    _ = B * (C * D) := by rw [hR, Matrix.mul_assoc]

theorem commute_of_intertwining (R S C D : Mat)
    (hR : R * B = B * C) (hS : S * B = B * D) (hCD : Commute C D) :
    Commute R S := by
  change R * S = S * R
  apply mul_B_injective
  change (R * S) * B = (S * R) * B
  rw [product_intertwining R S C D hR hS, product_intertwining S R D C hS hR, hCD.eq]

theorem X_commute_X (k l : Fin 7) : Commute (X k) (X l) :=
  commute_of_intertwining _ _ _ _ (X_mul_B k) (X_mul_B l) (cartX_commute k l)

theorem Z_commute_Z (k l : Fin 7) : Commute (Z k) (Z l) :=
  commute_of_intertwining _ _ _ _ (Z_mul_B k) (Z_mul_B l) (cartZ_commute k l)

theorem X_commute_Z (k l : Fin 7) (h : k ≠ l) : Commute (X k) (Z l) :=
  commute_of_intertwining _ _ _ _ (X_mul_B k) (Z_mul_B l) (cartX_cartZ_commute k l h)

theorem Z_commute_X (k l : Fin 7) (h : k ≠ l) : Commute (Z k) (X l) :=
  (X_commute_Z l k (Ne.symm h)).symm

theorem Z_mul_X (k : Fin 7) : Z k * X k = -(X k * Z k) := by
  apply mul_B_injective
  change (Z k * X k) * B = (-(X k * Z k)) * B
  rw [product_intertwining _ _ _ _ (Z_mul_B k) (X_mul_B k),
    Matrix.neg_mul, product_intertwining _ _ _ _ (X_mul_B k) (Z_mul_B k),
    cartZ_mul_cartX, Matrix.mul_neg]

def Y (k : Fin 7) : Mat := X k * Z k
def T (k : Fin 7) : Mat := X k + Z k

private theorem product_square (P Q : Mat) (hP : P * P = 1) (hQ : Q * Q = 1)
    (hQP : Q * P = -(P * Q)) : (P * Q) * (P * Q) = -1 := by
  calc
    (P * Q) * (P * Q) = P * (Q * P) * Q := by simp only [Matrix.mul_assoc]
    _ = P * (-(P * Q)) * Q := by rw [hQP]
    _ = -((P * P) * (Q * Q)) := by simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -1 := by rw [hP, hQ, Matrix.one_mul]

private theorem sum_square (P Q : Mat) (hP : P * P = 1) (hQ : Q * Q = 1)
    (hQP : Q * P = -(P * Q)) : (P + Q) * (P + Q) = (2 : ℤ) • (1 : Mat) := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hP, hQ, hQP]
  funext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem Y_sq (k : Fin 7) : Y k * Y k = -1 :=
  product_square _ _ (X_sq k) (Z_sq k) (Z_mul_X k)

theorem T_sq (k : Fin 7) : T k * T k = (2 : ℤ) • (1 : Mat) :=
  sum_square _ _ (X_sq k) (Z_sq k) (Z_mul_X k)

theorem Y_commute_X (k l : Fin 7) (h : k ≠ l) : Commute (Y k) (X l) :=
  (X_commute_X k l).mul_left (Z_commute_X k l h)

theorem Y_commute_Z (k l : Fin 7) (h : k ≠ l) : Commute (Y k) (Z l) :=
  (X_commute_Z k l h).mul_left (Z_commute_Z k l)

theorem Y_commute_Y (k l : Fin 7) (h : k ≠ l) : Commute (Y k) (Y l) :=
  (Y_commute_X k l h).mul_right (Y_commute_Z k l h)

theorem Y_commute_T (k l : Fin 7) (h : k ≠ l) : Commute (Y k) (T l) :=
  (Y_commute_X k l h).add_right (Y_commute_Z k l h)

theorem Z_commute_T (k l : Fin 7) (h : k ≠ l) : Commute (Z k) (T l) :=
  (Z_commute_X k l h).add_right (Z_commute_Z k l)

theorem coefficient_pair (k : Fin 7) (i : Index) :
    (2 : ℤ) ^ parity i * 2 ^ parity (toggle k i) = 2 := by
  rw [← pow_add, parity_toggle, pow_one]

theorem Y_mul_apply (k : Fin 7) (M : Mat) (i j : Index) :
    (Y k * M) i j = if k.val ∈ support i
      then -M i j + (2 : ℤ) ^ parity i * M (toggle k i) j
      else M i j - (2 : ℤ) ^ parity i * M (toggle k i) j := by
  rw [Y, Matrix.mul_assoc, X_mul_apply]
  by_cases hi : k.val ∈ support i
  · simp only [ite_eq_left hi]
    rw [Z_mul_apply, ite_eq_left hi]
  · simp only [ite_eq_right hi]
    rw [Z_mul_apply, ite_eq_right hi, Z_mul_apply]
    have hf : k.val ∈ support (toggle k i) := (mem_support_toggle_self k i).mpr hi
    rw [ite_eq_left hf, toggle_toggle]
    calc
      -M i j + 2 ^ parity i *
          (-M (toggle k i) j + 2 ^ parity (toggle k i) * M i j) =
        ((2 : ℤ) ^ parity i * 2 ^ parity (toggle k i) - 1) * M i j -
          2 ^ parity i * M (toggle k i) j := by ring
      _ = M i j - 2 ^ parity i * M (toggle k i) j := by
        rw [coefficient_pair]
        ring

theorem T_mul_apply (k : Fin 7) (M : Mat) (i j : Index) :
    (T k * M) i j = (2 : ℤ) ^ parity i * M (toggle k i) j := by
  rw [T, Matrix.add_mul]
  change (X k * M) i j + (Z k * M) i j = _
  rw [X_mul_apply, Z_mul_apply]
  by_cases hi : k.val ∈ support i
  · simp only [ite_eq_left hi]
    ring
  · simp only [ite_eq_right hi]
    ring

theorem T_apply (k : Fin 7) (i j : Index) :
    T k i j = (2 : ℤ) ^ parity i * (1 : Mat) (toggle k i) j := by
  simpa only [Matrix.mul_one] using T_mul_apply k (1 : Mat) i j

abbrev a : Mat := Y 6
abbrev b : Mat := Z 6 * Y 5
abbrev S : Mat := T 4

/-- Direct integral rows of the additional generator. No division is used. -/
def g : Mat := fun i j =>
  if (6 : ℕ) ∈ support i then (1 : Mat) (toggle 4 (toggle 6 i)) j
  else (2 : ℤ) ^ parity i * (1 : Mat) (toggle 4 i) j -
    (1 : Mat) (toggle 4 (toggle 6 i)) j

theorem two_g : (2 : ℤ) • g = (1 + a) * S := by
  funext i j
  change 2 * g i j = ((1 + a) * S) i j
  rw [Matrix.add_mul, Matrix.one_mul]
  change 2 * g i j = S i j + (Y 6 * S) i j
  simp only [Y_mul_apply, T_apply]
  by_cases hi : (6 : ℕ) ∈ support i
  · have hif : (6 : Fin 7).val ∈ support i := hi
    simp only [g, ite_eq_left hi, ite_eq_left hif]
    calc
      2 * (1 : Mat) (toggle 4 (toggle 6 i)) j =
          ((2 : ℤ) ^ parity i * 2 ^ parity (toggle 6 i)) *
            (1 : Mat) (toggle 4 (toggle 6 i)) j := by rw [coefficient_pair]
      _ = _ := by ring
  · have hif : (6 : Fin 7).val ∉ support i := hi
    simp only [g, ite_eq_right hi, ite_eq_right hif]
    calc
      2 * (2 ^ parity i * (1 : Mat) (toggle 4 i) j -
          (1 : Mat) (toggle 4 (toggle 6 i)) j) =
        2 * 2 ^ parity i * (1 : Mat) (toggle 4 i) j -
          ((2 : ℤ) ^ parity i * 2 ^ parity (toggle 6 i)) *
            (1 : Mat) (toggle 4 (toggle 6 i)) j := by
        rw [coefficient_pair]
        ring
      _ = _ := by ring

def cartA : Mat := cartX 6 * cartZ 6
def cartS : Mat := cartX 4 + cartZ 4
def D : Mat := (1 + cartA) * cartS

theorem a_mul_B : a * B = B * cartA :=
  product_intertwining _ _ _ _ (X_mul_B 6) (Z_mul_B 6)

theorem S_mul_B : S * B = B * cartS := by
  simp only [S, T, cartS, Matrix.add_mul, Matrix.mul_add, X_mul_B, Z_mul_B]

theorem one_add_a_mul_B : (1 + a) * B = B * (1 + cartA) := by
  rw [Matrix.add_mul, Matrix.one_mul, a_mul_B, Matrix.mul_add, Matrix.mul_one]

/-- Scaled integral Cartesian intertwining, with no inverse basis matrix. -/
theorem two_g_mul_B : (2 : ℤ) • (g * B) = B * D := by
  calc
    (2 : ℤ) • (g * B) = ((2 : ℤ) • g) * B := (Matrix.smul_mul _ _ _).symm
    _ = ((1 + a) * S) * B := by rw [two_g]
    _ = B * ((1 + cartA) * cartS) :=
      product_intertwining _ _ _ _ one_add_a_mul_B S_mul_B
    _ = B * D := rfl

theorem cartA_sq : cartA * cartA = -1 :=
  product_square _ _ (cartX_sq 6) (cartZ_sq 6) (cartZ_mul_cartX 6)

theorem cartA_transpose : cartAᵀ = -cartA := by
  rw [cartA, Matrix.transpose_mul, cartZ_transpose, cartX_transpose, cartZ_mul_cartX]

theorem cartS_sq : cartS * cartS = (2 : ℤ) • (1 : Mat) :=
  sum_square _ _ (cartX_sq 4) (cartZ_sq 4) (cartZ_mul_cartX 4)

theorem cartS_transpose : cartSᵀ = cartS := by
  rw [cartS, Matrix.transpose_add, cartX_transpose, cartZ_transpose]

private theorem one_add_mul_one_sub (A : Mat) (hA : A * A = -1) :
    (1 + A) * (1 - A) = (2 : ℤ) • (1 : Mat) := by
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hA]
  funext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

private theorem smul_mul_smul (r s : ℤ) (M N : Mat) :
    (r • M) * (s • N) = (r * s) • (M * N) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm r s]

private theorem smul_injective (r : ℤ) (hr : r ≠ 0) {M N : Mat}
    (h : r • M = r • N) : M = N := by
  funext i j
  have he := congrFun (congrFun h i) j
  change r * M i j = r * N i j at he
  exact mul_left_cancel₀ hr he

theorem D_mul_transpose : D * Dᵀ = (4 : ℤ) • (1 : Mat) := by
  calc
    D * Dᵀ = (1 + cartA) * (cartS * cartS) * (1 - cartA) := by
      simp only [D, Matrix.transpose_mul, cartS_transpose, Matrix.transpose_add,
        Matrix.transpose_one, cartA_transpose, sub_eq_add_neg, Matrix.mul_assoc]
    _ = (2 : ℤ) • ((1 + cartA) * (1 - cartA)) := by
      rw [cartS_sq]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    _ = (4 : ℤ) • (1 : Mat) := by
      rw [one_add_mul_one_sub cartA cartA_sq, smul_smul]
      norm_num

theorem isometry_of_scaled_intertwining (R C : Mat)
    (h : (2 : ℤ) • (R * B) = B * C)
    (hC : C * Cᵀ = (4 : ℤ) • (1 : Mat)) : R * G * Rᵀ = G := by
  apply smul_injective 64 (by decide)
  calc
    (64 : ℤ) • (R * G * Rᵀ) = (4 : ℤ) • (R * ((16 : ℤ) • G) * Rᵀ) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      norm_num
    _ = (4 : ℤ) • ((R * B) * (R * B)ᵀ) := by
      rw [← B_mul_transpose]
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = ((2 : ℤ) • (R * B)) * ((2 : ℤ) • (R * B))ᵀ := by
      rw [Matrix.transpose_smul, smul_mul_smul]
      norm_num
    _ = (B * C) * (B * C)ᵀ := by rw [h]
    _ = (4 : ℤ) • (B * Bᵀ) := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc C Cᵀ Bᵀ, hC]
      simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]
    _ = (64 : ℤ) • G := by rw [B_mul_transpose, smul_smul]; norm_num

theorem g_isometry : g * G * gᵀ = G :=
  isometry_of_scaled_intertwining g D two_g_mul_B D_mul_transpose

theorem a_sq : a * a = -1 := Y_sq 6
theorem S_sq : S * S = (2 : ℤ) • (1 : Mat) := T_sq 4
theorem a_commute_S : Commute a S := Y_commute_T 6 4 (by decide)

private theorem one_add_sq (A : Mat) (hA : A * A = -1) :
    (1 + A) * (1 + A) = (2 : ℤ) • A := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hA]
  funext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem g_sq : g * g = a := by
  apply smul_injective 4 (by decide)
  calc
    (4 : ℤ) • (g * g) = ((2 : ℤ) • g) * ((2 : ℤ) • g) := by
      rw [smul_mul_smul]
      norm_num
    _ = ((1 + a) * S) * ((1 + a) * S) := by rw [two_g]
    _ = ((1 + a) * (1 + a)) * (S * S) :=
      ((Commute.one_left S).add_left a_commute_S).symm.mul_mul_mul_comm _ _
    _ = ((2 : ℤ) • a) * ((2 : ℤ) • (1 : Mat)) := by
      rw [one_add_sq a a_sq, S_sq]
    _ = (4 : ℤ) • a := by rw [smul_mul_smul, Matrix.mul_one]; norm_num

theorem g_four : g ^ 4 = -1 := by
  calc
    g ^ 4 = (g * g) * (g * g) := by
      simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]
    _ = a * a := by rw [g_sq]
    _ = -1 := a_sq

theorem g_eight : g ^ 8 = 1 := by
  calc
    g ^ 8 = g ^ 4 * g ^ 4 := by rw [← pow_add]
    _ = (-1 : Mat) * (-1) := by rw [g_four]
    _ = 1 := by simp

theorem Z_commute_Y (k l : Fin 7) (h : k ≠ l) : Commute (Z k) (Y l) :=
  (Z_commute_X k l h).mul_right (Z_commute_Z k l)

theorem b_sq : b * b = -1 := by
  calc
    b * b = (Z 6 * Z 6) * (Y 5 * Y 5) :=
      (Z_commute_Y 6 5 (by decide)).symm.mul_mul_mul_comm _ _
    _ = -1 := by rw [Z_sq, Y_sq, Matrix.one_mul]

theorem b_commute_S : Commute b S :=
  (Z_commute_T 6 4 (by decide)).mul_left (Y_commute_T 5 4 (by decide))

theorem Z_mul_a : Z 6 * a = -(a * Z 6) := by
  calc
    Z 6 * a = (Z 6 * X 6) * Z 6 := (Matrix.mul_assoc _ _ _).symm
    _ = (-(X 6 * Z 6)) * Z 6 := by rw [Z_mul_X]
    _ = -(a * Z 6) := by rw [Matrix.neg_mul]; rfl

theorem b_mul_a : b * a = -(a * b) := by
  calc
    b * a = Z 6 * (Y 5 * a) := Matrix.mul_assoc _ _ _
    _ = Z 6 * (a * Y 5) := by rw [(Y_commute_Y 5 6 (by decide)).eq]
    _ = (Z 6 * a) * Y 5 := (Matrix.mul_assoc _ _ _).symm
    _ = -(a * b) := by rw [Z_mul_a, Matrix.neg_mul, Matrix.mul_assoc]

private theorem b_one_add_a_square :
    (b * (1 + a)) * (b * (1 + a)) = (-2 : ℤ) • (1 : Mat) := by
  have hbab : b * a * b = a := by
    rw [b_mul_a, Matrix.neg_mul, Matrix.mul_assoc, b_sq]
    simp
  have hmid : b * (1 + a) * b = -1 + a := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, b_sq, hbab]
  calc
    (b * (1 + a)) * (b * (1 + a)) = (b * (1 + a) * b) * (1 + a) :=
      (Matrix.mul_assoc _ _ _).symm
    _ = (-1 + a) * (1 + a) := by rw [hmid]
    _ = (-2 : ℤ) • (1 : Mat) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.neg_mul,
        Matrix.one_mul, Matrix.mul_one, a_sq]
      funext i j
      simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
      ring

theorem b_g_b_g : b * g * b * g = -1 := by
  apply smul_injective 4 (by decide)
  calc
    (4 : ℤ) • (b * g * b * g) = (b * ((2 : ℤ) • g)) * (b * ((2 : ℤ) • g)) := by
      have hs : b * ((2 : ℤ) • g) = (2 : ℤ) • (b * g) := Matrix.mul_smul _ _ _
      simp only [hs]
      rw [smul_mul_smul]
      norm_num only
      simp only [Matrix.mul_assoc]
    _ = (b * ((1 + a) * S)) * (b * ((1 + a) * S)) := by rw [two_g]
    _ = ((b * (1 + a)) * S) * ((b * (1 + a)) * S) := by
      simp only [Matrix.mul_assoc]
    _ = ((b * (1 + a)) * (b * (1 + a))) * (S * S) := by
      exact (b_commute_S.mul_left
        ((Commute.one_left S).add_left a_commute_S)).symm.mul_mul_mul_comm _ _
    _ = ((-2 : ℤ) • (1 : Mat)) * ((2 : ℤ) • (1 : Mat)) := by
      rw [b_one_add_a_square, S_sq]
    _ = (4 : ℤ) • (-1 : Mat) := by
      rw [smul_mul_smul, Matrix.one_mul]
      funext i j
      simp only [Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
      ring

theorem isometry_mul (R T : Mat) (hR : R * G * Rᵀ = G) (hT : T * G * Tᵀ = G) :
    (R * T) * G * (R * T)ᵀ = G := by
  calc
    (R * T) * G * (R * T)ᵀ = R * (T * G * Tᵀ) * Rᵀ := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = G := by rw [hT, hR]

theorem a_isometry : a * G * aᵀ = G :=
  isometry_mul _ _ (X_isometry 6) (Z_isometry 6)

theorem b_isometry : b * G * bᵀ = G :=
  isometry_mul _ _ (Z_isometry 6) (isometry_mul _ _ (X_isometry 5) (Z_isometry 5))

theorem g_inverse_right : g * g ^ 7 = 1 := by
  rw [← pow_succ', g_eight]

theorem g_inverse_left : g ^ 7 * g = 1 := by
  rw [← pow_succ, g_eight]

def gUnit : Matˣ where
  val := g
  inv := g ^ 7
  val_inv := g_inverse_right
  inv_val := g_inverse_left

def bUnit : Matˣ where
  val := b
  inv := -b
  val_inv := by rw [Matrix.mul_neg, b_sq, neg_neg]
  inv_val := by rw [Matrix.neg_mul, b_sq, neg_neg]

@[simp] theorem gUnit_val : (gUnit : Mat) = g := rfl
@[simp] theorem bUnit_val : (bUnit : Mat) = b := rfl

theorem block_support_mul (R T : Mat)
    (hR : ∀ i j, KRRBlocks.block i ≠ KRRBlocks.block j → R i j = 0)
    (hT : ∀ i j, KRRBlocks.block i ≠ KRRBlocks.block j → T i j = 0) :
    ∀ i j, KRRBlocks.block i ≠ KRRBlocks.block j → (R * T) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : KRRBlocks.block i = KRRBlocks.block k
  · rw [hT k j (fun hkj => hij (hik.trans hkj)), mul_zero]
  · rw [hR i k hik, zero_mul]

theorem a_block_support (i j : Index)
    (h : KRRBlocks.block i ≠ KRRBlocks.block j) : a i j = 0 :=
  block_support_mul _ _ (X_block_support 6 (by decide))
    (Z_block_support 6 (by decide)) i j h

theorem b_block_support (i j : Index)
    (h : KRRBlocks.block i ≠ KRRBlocks.block j) : b i j = 0 :=
  block_support_mul _ _ (Z_block_support 6 (by decide))
    (block_support_mul _ _ (X_block_support 5 (by decide))
      (Z_block_support 5 (by decide))) i j h

theorem g_block_support (i j : Index)
    (h : KRRBlocks.block i ≠ KRRBlocks.block j) : g i j = 0 := by
  have h4 : toggle 4 i ≠ j := by
    intro heq
    exact h ((block_toggle 4 (by decide) i).symm.trans (congrArg KRRBlocks.block heq))
  have h64 : toggle 4 (toggle 6 i) ≠ j := by
    intro heq
    have hb := (block_toggle 4 (by decide) (toggle 6 i)).trans (block_toggle 6 (by decide) i)
    exact h (hb.symm.trans (congrArg KRRBlocks.block heq))
  simp [g, h4, h64]

theorem neg_one_ne_one : (-1 : Mat) ≠ 1 := by
  intro h
  have he := congrFun (congrFun h (0 : Index)) (0 : Index)
  change (-1 : ℤ) = 1 at he
  norm_num at he

theorem g_four_ne_one : g ^ 4 ≠ 1 := by
  rw [g_four]
  exact neg_one_ne_one

end BarnesWall.KRRQ16
