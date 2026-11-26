/-
Copyright (c) 2026 QwersykBot contributors.
SPDX-License-Identifier: MIT
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Boolean cubic vanishing on a hyperbolic quadric

Verification status is recorded in accompanying receipts.
Target: Lean 4.35.0-rc3 and Mathlib
b63f6e8a68d220e3b3bc4f3792bb53650d375f24.

The intended result is uniform for m >= 2 and has a unique affine multiplier.
Boolean inputs are finite supports. Evaluation is the powerset sum of the
squarefree coefficients. No quotient polynomial ring is introduced.

-/

namespace BarnesWall.BooleanCubic

open scoped BigOperators CharTwo

abbrev F2 := ZMod 2
abbrev Var (m : ℕ) := Fin m ⊕ Fin m
abbrev Support (m : ℕ) := Finset (Var m)
abbrev Coeff (m : ℕ) := Support m → F2

def pair {m : ℕ} (i : Fin m) : Support m := {Sum.inl i, Sum.inr i}

def eval {m : ℕ} (c : Coeff m) (S : Support m) : F2 :=
  ∑ T ∈ S.powerset, c T

def degreeLE3 {m : ℕ} (c : Coeff m) : Prop :=
  ∀ S, 3 < S.card → c S = 0

def PairFree {m : ℕ} (S : Support m) : Prop :=
  ∀ i, ¬ pair i ⊆ S

def q {m : ℕ} (S : Support m) : F2 :=
  ∑ i : Fin m, if pair i ⊆ S then 1 else 0

def affineEval {m : ℕ} (δ : F2) (β γ : Fin m → F2) (S : Support m) : F2 :=
  δ + (∑ i : Fin m, if Sum.inl i ∈ S then β i else 0) +
    (∑ i : Fin m, if Sum.inr i ∈ S then γ i else 0)

@[simp] theorem pair_card {m : ℕ} (i : Fin m) : (pair i).card = 2 := by
  simp [pair]

@[simp] theorem pair_subset_iff {m : ℕ} (i : Fin m) (S : Support m) :
    pair i ⊆ S ↔ Sum.inl i ∈ S ∧ Sum.inr i ∈ S := by
  simp [pair, Finset.insert_subset_iff]

@[simp] theorem eval_empty {m : ℕ} (c : Coeff m) : eval c ∅ = c ∅ := by
  simp [eval]

theorem q_eq_zero_of_pairFree {m : ℕ} {S : Support m} (hS : PairFree S) :
    q S = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  simp only [ite_eq_right (hS i)]

theorem pairFree_mono {m : ℕ} {S T : Support m}
    (hST : S ⊆ T) (hT : PairFree T) : PairFree S := by
  intro i hi
  exact hT i (hi.trans hST)

/-- The triangular powerset evaluator is injective. -/
theorem coeff_eq_zero_of_eval_eq_zero {m : ℕ} (c : Coeff m)
    (h : ∀ S, eval c S = 0) : ∀ S, c S = 0 := by
  intro S
  refine Finset.strongInductionOn (p := fun T => c T = 0) S ?_
  intro S ih
  have hsingle : eval c S = c S := by
    unfold eval
    apply Finset.sum_eq_single S
    · intro T hT hne
      exact ih T (Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.mem_powerset.mp hT, hne⟩)
    · simp
  exact hsingle.symm.trans (h S)

theorem eval_injective {m : ℕ} : Function.Injective (@eval m) := by
  intro c d h
  have hz : ∀ S, eval (fun T => c T - d T) S = 0 := by
    intro S
    have he := congrFun h S
    simpa only [eval, Finset.sum_sub_distrib, sub_self] using
      (sub_eq_zero.mpr he)
  funext S
  exact sub_eq_zero.mp (coeff_eq_zero_of_eval_eq_zero _ hz S)

/-- No degree assumption is needed for this coefficient elimination. -/
theorem coeff_eq_zero_of_pairFree {m : ℕ} (c : Coeff m)
    (hvanish : ∀ S, q S = 0 → eval c S = 0) :
    ∀ S, PairFree S → c S = 0 := by
  intro S
  refine Finset.strongInductionOn (p := fun T => PairFree T → c T = 0) S ?_
  intro S ih hS
  have hsingle : eval c S = c S := by
    unfold eval
    apply Finset.sum_eq_single S
    · intro T hT hne
      have hTS := Finset.mem_powerset.mp hT
      exact ih T (Finset.ssubset_iff_subset_ne.mpr ⟨hTS, hne⟩)
        (pairFree_mono hTS hS)
    · simp
  exact hsingle.symm.trans (hvanish S (q_eq_zero_of_pairFree hS))

def atom {m : ℕ} (M : Support m) (a : F2) : Coeff m :=
  fun S => if S = M then a else 0

theorem eval_atom {m : ℕ} (M S : Support m) (a : F2) :
    eval (atom M a) S = if M ⊆ S then a else 0 := by
  classical
  by_cases hMS : M ⊆ S
  · rw [ite_eq_left hMS]
    unfold eval
    rw [Finset.sum_eq_single M]
    · simp [atom]
    · intro T _ hne
      simp [atom, hne]
    · simp [Finset.mem_powerset.mpr hMS]
  · rw [ite_eq_right hMS]
    apply Finset.sum_eq_zero
    intro T hT
    have hne : T ≠ M := by
      intro he
      subst T
      exact hMS (Finset.mem_powerset.mp hT)
    simp [atom, hne]

theorem eval_add {m : ℕ} (c d : Coeff m) (S : Support m) :
    eval (fun T => c T + d T) S = eval c S + eval d S := by
  simp only [eval, Finset.sum_add_distrib]

theorem eval_fintype_sum {m : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → Coeff m) (S : Support m) :
    eval (fun T => ∑ i, c i T) S = ∑ i, eval (c i) S := by
  unfold eval
  exact Finset.sum_comm

/-- The explicit reduced coefficient family of Q times an affine function.
The terms with j=i correctly contribute β_i+γ_i to the quadratic coefficient.
-/
def productCoeff {m : ℕ} (δ : F2) (β γ : Fin m → F2) : Coeff m :=
  fun S => ∑ i : Fin m,
    (atom (pair i) δ S +
      (∑ j : Fin m, atom (insert (Sum.inl j) (pair i)) (β j) S) +
      (∑ j : Fin m, atom (insert (Sum.inr j) (pair i)) (γ j) S))

theorem eval_productCoeff {m : ℕ} (δ : F2) (β γ : Fin m → F2) (S : Support m) :
    eval (productCoeff δ β γ) S = q S * affineEval δ β γ S := by
  classical
  unfold productCoeff
  rw [eval_fintype_sum]
  calc
    _ = ∑ i : Fin m, (if pair i ⊆ S then 1 else 0) * affineEval δ β γ S := by
      apply Finset.sum_congr rfl
      intro i _
      rw [eval_add, eval_add, eval_atom, eval_fintype_sum, eval_fintype_sum]
      simp_rw [eval_atom]
      by_cases hi : pair i ⊆ S <;>
        simp [Finset.insert_subset_iff, hi, affineEval]
    _ = q S * affineEval δ β γ S := by
      rw [← Finset.sum_mul]
      rfl

theorem q_pair {m : ℕ} (i : Fin m) : q (pair i) = 1 := by
  classical
  have hp (k : Fin m) : pair k ⊆ pair i ↔ k = i := by
    constructor
    · intro hk
      have hm : Sum.inl k ∈ pair i := hk (by simp [pair])
      simpa [pair] using hm
    · intro hki
      subst k
      exact Finset.Subset.rfl
  simp [q, hp]

theorem q_insert_inl_pair {m : ℕ} (i j : Fin m) :
    q (insert (Sum.inl j) (pair i)) = 1 := by
  classical
  have hp (k : Fin m) :
      pair k ⊆ insert (Sum.inl j) (pair i) ↔ k = i := by
    constructor
    · intro hk
      have hm : Sum.inr k ∈ insert (Sum.inl j) (pair i) := hk (by simp [pair])
      simpa [pair] using hm
    · intro hki
      subst k
      exact Finset.subset_insert _ _
  simp [q, hp]

theorem q_insert_inr_pair {m : ℕ} (i j : Fin m) :
    q (insert (Sum.inr j) (pair i)) = 1 := by
  classical
  have hp (k : Fin m) :
      pair k ⊆ insert (Sum.inr j) (pair i) ↔ k = i := by
    constructor
    · intro hk
      have hm : Sum.inl k ∈ insert (Sum.inr j) (pair i) := hk (by simp [pair])
      simpa [pair] using hm
    · intro hki
      subst k
      exact Finset.subset_insert _ _
  simp [q, hp]

theorem affineEval_pair {m : ℕ} (δ : F2) (β γ : Fin m → F2) (i : Fin m) :
    affineEval δ β γ (pair i) = δ + β i + γ i := by
  classical
  simp [affineEval, pair]

theorem affineEval_insert_inl {m : ℕ} (δ : F2) (β γ : Fin m → F2)
    (S : Support m) (j : Fin m) (hj : Sum.inl j ∉ S) :
    affineEval δ β γ (insert (Sum.inl j) S) = affineEval δ β γ S + β j := by
  classical
  have hx (k : Fin m) :
      (if Sum.inl k ∈ insert (Sum.inl j) S then β k else 0) =
        (if Sum.inl k ∈ S then β k else 0) + (if k = j then β k else 0) := by
    by_cases hk : k = j
    · subst k
      simp [hj]
    · simp [hk]
  have hsum :
      (∑ k : Fin m, if Sum.inl k ∈ insert (Sum.inl j) S then β k else 0) =
        (∑ k : Fin m, if Sum.inl k ∈ S then β k else 0) + β j := by
    simp_rw [hx]
    rw [Finset.sum_add_distrib]
    simp
  have hright :
      (∑ k : Fin m, if Sum.inr k ∈ insert (Sum.inl j) S then γ k else 0) =
        (∑ k : Fin m, if Sum.inr k ∈ S then γ k else 0) := by
    simp
  unfold affineEval
  rw [hsum, hright, ← add_assoc]
  exact add_right_comm _ _ _

theorem affineEval_insert_inr {m : ℕ} (δ : F2) (β γ : Fin m → F2)
    (S : Support m) (j : Fin m) (hj : Sum.inr j ∉ S) :
    affineEval δ β γ (insert (Sum.inr j) S) = affineEval δ β γ S + γ j := by
  classical
  have hy (k : Fin m) :
      (if Sum.inr k ∈ insert (Sum.inr j) S then γ k else 0) =
        (if Sum.inr k ∈ S then γ k else 0) + (if k = j then γ k else 0) := by
    by_cases hk : k = j
    · subst k
      simp [hj]
    · simp [hk]
  have hsum :
      (∑ k : Fin m, if Sum.inr k ∈ insert (Sum.inr j) S then γ k else 0) =
        (∑ k : Fin m, if Sum.inr k ∈ S then γ k else 0) + γ j := by
    simp_rw [hy]
    rw [Finset.sum_add_distrib]
    simp
  have hleft :
      (∑ k : Fin m, if Sum.inl k ∈ insert (Sum.inr j) S then β k else 0) =
        (∑ k : Fin m, if Sum.inl k ∈ S then β k else 0) := by
    simp
  unfold affineEval
  rw [hleft, hsum]
  exact (add_assoc _ _ _).symm

/-- Uniqueness is an ordinary evaluation/cancellation argument. -/
theorem affine_multiplier_unique {m : ℕ} (hm : 2 ≤ m)
    {δ δ' : F2} {β γ β' γ' : Fin m → F2}
    (h : ∀ S : Support m,
      q S * affineEval δ β γ S = q S * affineEval δ' β' γ' S) :
    δ = δ' ∧ β = β' ∧ γ = γ' := by
  classical
  let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  have heq (S : Support m) (hS : q S = 1) :
      affineEval δ β γ S = affineEval δ' β' γ' S := by
    simpa only [hS, one_mul] using h S
  have hbase (i : Fin m) := heq (pair i) (q_pair i)
  have hβ : β = β' := by
    funext j
    obtain ⟨i, hij⟩ := exists_ne j
    have hj : Sum.inl j ∉ pair i := by simp [pair, Ne.symm hij]
    have hs := heq (insert (Sum.inl j) (pair i)) (q_insert_inl_pair i j)
    rw [affineEval_insert_inl δ β γ (pair i) j hj,
      affineEval_insert_inl δ' β' γ' (pair i) j hj, hbase i] at hs
    exact add_left_cancel hs
  have hγ : γ = γ' := by
    funext j
    obtain ⟨i, hij⟩ := exists_ne j
    have hj : Sum.inr j ∉ pair i := by simp [pair, Ne.symm hij]
    have hs := heq (insert (Sum.inr j) (pair i)) (q_insert_inr_pair i j)
    rw [affineEval_insert_inr δ β γ (pair i) j hj,
      affineEval_insert_inr δ' β' γ' (pair i) j hj, hbase i] at hs
    exact add_left_cancel hs
  have hδ : δ = δ' := by
    let i : Fin m := ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hm⟩
    have hs := hbase i
    simp only [affineEval_pair, hβ, hγ] at hs
    exact add_right_cancel (add_right_cancel hs)
  exact ⟨hδ, hβ, hγ⟩

def quadCoeff {m : ℕ} (c : Coeff m) (i : Fin m) : F2 := c (pair i)

def leftCoeff {m : ℕ} (c : Coeff m) (i j : Fin m) : F2 :=
  c (insert (Sum.inl j) (pair i))

def rightCoeff {m : ℕ} (c : Coeff m) (i j : Fin m) : F2 :=
  c (insert (Sum.inr j) (pair i))

def twoPairs {m : ℕ} (i k : Fin m) : Support m :=
  insert (Sum.inl k) (insert (Sum.inr k) (pair i))

/- The following are schematic powerset expansions on two through five
coordinates. Their size is independent of m; they are not truth tables for the
quadric or for the space of cubic coefficient families. -/

private theorem sum_powerset_singleton {m : ℕ} (a : Var m) (f : Support m → F2) :
    (∑ T ∈ ({a} : Support m).powerset, f T) = f ∅ + f {a} := by
  classical
  simpa using
    (Finset.sum_powerset_insert (s := (∅ : Support m)) (a := a) (by simp) f)

theorem eval_pair_of_pairFree_zero {m : ℕ} (c : Coeff m)
    (hz : ∀ S, PairFree S → c S = 0) (i : Fin m) :
    eval c (pair i) = quadCoeff c i := by
  classical
  simp [eval, quadCoeff, pair, Finset.sum_powerset_insert, sum_powerset_singleton]
  simp (disch := (try simp only [PairFree, pair_subset_iff]; simp)) only
    [hz, zero_add, add_zero]

theorem eval_insert_inl_pair_of_pairFree_zero {m : ℕ} (c : Coeff m)
    (hz : ∀ S, PairFree S → c S = 0) (i j : Fin m) (hji : j ≠ i) :
    eval c (insert (Sum.inl j) (pair i)) = quadCoeff c i + leftCoeff c i j := by
  classical
  simp [eval, quadCoeff, leftCoeff, pair, Finset.sum_powerset_insert,
    sum_powerset_singleton, hji]
  simp (disch := (try simp only [PairFree, pair_subset_iff]; simp [hji, Ne.symm hji])) only [hz, zero_add, add_zero]

theorem eval_insert_inr_pair_of_pairFree_zero {m : ℕ} (c : Coeff m)
    (hz : ∀ S, PairFree S → c S = 0) (i j : Fin m) (hji : j ≠ i) :
    eval c (insert (Sum.inr j) (pair i)) = quadCoeff c i + rightCoeff c i j := by
  classical
  simp [eval, quadCoeff, rightCoeff, pair, Finset.sum_powerset_insert,
    sum_powerset_singleton, hji]
  simp (disch := (try simp only [PairFree, pair_subset_iff]; simp [hji, Ne.symm hji])) only [hz, zero_add, add_zero]

theorem eval_twoPairs {m : ℕ} (c : Coeff m) (hd : degreeLE3 c)
    (hz : ∀ S, PairFree S → c S = 0) (i k : Fin m) (hik : i ≠ k) :
    eval c (twoPairs i k) =
      quadCoeff c i + quadCoeff c k + leftCoeff c i k + rightCoeff c i k +
        leftCoeff c k i + rightCoeff c k i := by
  classical
  have hd' : ∀ S, 3 < S.card → c S = 0 := hd
  simp [eval, twoPairs, quadCoeff, leftCoeff, rightCoeff, pair,
    Finset.sum_powerset_insert, sum_powerset_singleton, Ne.symm hik]
  simp (disch := (simp only [PairFree, pair_subset_iff]; simp [hik, Ne.symm hik])) only [hz, zero_add, add_zero]
  simp (disch := simp [hik, Ne.symm hik]) only [hd', add_zero]
  have hleft : ({Sum.inl k, Sum.inr k, Sum.inl i} : Support m) =
      {Sum.inl i, Sum.inl k, Sum.inr k} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm]
  have hright : ({Sum.inl k, Sum.inr k, Sum.inr i} : Support m) =
      {Sum.inr i, Sum.inl k, Sum.inr k} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm]
  rw [hleft, hright]
  simp only [add_comm, add_left_comm, add_assoc]

theorem eval_insert_inl_twoPairs {m : ℕ} (c : Coeff m) (hd : degreeLE3 c)
    (hz : ∀ S, PairFree S → c S = 0) (i k j : Fin m)
    (hik : i ≠ k) (hji : j ≠ i) (hjk : j ≠ k) :
    eval c (insert (Sum.inl j) (twoPairs i k)) =
      eval c (twoPairs i k) + leftCoeff c i j + leftCoeff c k j := by
  classical
  have hd' : ∀ S, 3 < S.card → c S = 0 := hd
  simp [eval, twoPairs, leftCoeff, pair, Finset.sum_powerset_insert,
    sum_powerset_singleton, Ne.symm hik, hji, hjk]
  simp (disch := (simp only [PairFree, pair_subset_iff]; simp [hik, Ne.symm hik, hji, Ne.symm hji, hjk, Ne.symm hjk])) only
    [hz, zero_add, add_zero]
  simp (disch := simp [hik, Ne.symm hik, hji, Ne.symm hji, hjk, Ne.symm hjk]) only [hd', zero_add, add_zero]
  simp only [add_assoc]

theorem eval_insert_inr_twoPairs {m : ℕ} (c : Coeff m) (hd : degreeLE3 c)
    (hz : ∀ S, PairFree S → c S = 0) (i k j : Fin m)
    (hik : i ≠ k) (hji : j ≠ i) (hjk : j ≠ k) :
    eval c (insert (Sum.inr j) (twoPairs i k)) =
      eval c (twoPairs i k) + rightCoeff c i j + rightCoeff c k j := by
  classical
  have hd' : ∀ S, 3 < S.card → c S = 0 := hd
  simp [eval, twoPairs, rightCoeff, pair, Finset.sum_powerset_insert,
    sum_powerset_singleton, Ne.symm hik, hji, hjk]
  simp (disch := (simp only [PairFree, pair_subset_iff]; simp [hik, Ne.symm hik, hji, Ne.symm hji, hjk, Ne.symm hjk])) only
    [hz, zero_add, add_zero]
  simp (disch := simp [hik, Ne.symm hik, hji, Ne.symm hji, hjk, Ne.symm hjk]) only [hd', zero_add, add_zero]
  simp only [add_comm, add_left_comm, add_assoc]

theorem support_eq_pair_or_triple {m : ℕ} {S : Support m} (i : Fin m)
    (hcard : S.card ≤ 3) (hpair : pair i ⊆ S) :
    S = pair i ∨
      (∃ j, j ≠ i ∧ S = insert (Sum.inl j) (pair i)) ∨
      (∃ j, j ≠ i ∧ S = insert (Sum.inr j) (pair i)) := by
  classical
  have hsmall : (S \ pair i).card ≤ 1 := by
    rw [Finset.card_sdiff_of_subset hpair, pair_card]
    simpa using Nat.sub_le_sub_right hcard 2
  rcases (S \ pair i).eq_empty_or_nonempty with he | ⟨x, hx⟩
  · left
    simpa only [he, Finset.empty_union] using
      (Finset.sdiff_union_of_subset hpair).symm
  · have hxnot : x ∉ pair i := (Finset.mem_sdiff.mp hx).2
    have hrest : S \ pair i = {x} := by
      apply Finset.ext
      intro y
      simp only [Finset.mem_singleton]
      constructor
      · intro hy
        exact Finset.card_le_one.mp hsmall y hy x hx
      · intro hy
        subst y
        exact hx
    have hEq : S = insert x (pair i) := by
      simpa only [hrest, Finset.singleton_union] using
        (Finset.sdiff_union_of_subset hpair).symm
    cases x with
    | inl j =>
        right
        left
        refine ⟨j, ?_, hEq⟩
        intro hji
        subst j
        exact hxnot (by simp [pair])
    | inr j =>
        right
        right
        refine ⟨j, ?_, hEq⟩
        intro hji
        subst j
        exact hxnot (by simp [pair])

theorem q_twoPairs {m : ℕ} (i k : Fin m) (hik : i ≠ k) :
    q (twoPairs i k) = 0 := by
  classical
  have hterm (l : Fin m) :
      (if pair l ⊆ twoPairs i k then (1 : F2) else 0) =
        (if l = i then 1 else 0) + (if l = k then 1 else 0) := by
    by_cases hli : l = i
    · subst l
      simp [twoPairs, pair, Finset.insert_subset_iff, hik]
    · by_cases hlk : l = k
      · subst l
        simp [twoPairs, pair, Finset.insert_subset_iff, Ne.symm hik]
      · simp [twoPairs, pair, Finset.insert_subset_iff, hli, hlk]
  unfold q
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp

theorem q_insert_inl_of_not_mem_right {m : ℕ} (S : Support m) (j : Fin m)
    (hj : Sum.inr j ∉ S) : q (insert (Sum.inl j) S) = q S := by
  classical
  unfold q
  apply Finset.sum_congr rfl
  intro k _
  by_cases hkj : k = j
  · subst k
    simp [pair_subset_iff, hj]
  · simp [pair_subset_iff, hkj]

theorem q_insert_inr_of_not_mem_left {m : ℕ} (S : Support m) (j : Fin m)
    (hj : Sum.inl j ∉ S) : q (insert (Sum.inr j) S) = q S := by
  classical
  unfold q
  apply Finset.sum_congr rfl
  intro k _
  by_cases hkj : k = j
  · subst k
    simp [pair_subset_iff, hj]
  · simp [pair_subset_iff, hkj]

theorem q_insert_inl_twoPairs {m : ℕ} (i k j : Fin m)
    (hik : i ≠ k) (hji : j ≠ i) (hjk : j ≠ k) :
    q (insert (Sum.inl j) (twoPairs i k)) = 0 := by
  have hj : Sum.inr j ∉ twoPairs i k := by simp [twoPairs, pair, hji, hjk]
  rw [q_insert_inl_of_not_mem_right _ _ hj, q_twoPairs i k hik]

theorem q_insert_inr_twoPairs {m : ℕ} (i k j : Fin m)
    (hik : i ≠ k) (hji : j ≠ i) (hjk : j ≠ k) :
    q (insert (Sum.inr j) (twoPairs i k)) = 0 := by
  have hj : Sum.inl j ∉ twoPairs i k := by simp [twoPairs, pair, hji, hjk]
  rw [q_insert_inr_of_not_mem_left _ _ hj, q_twoPairs i k hik]

private theorem eq_of_add_eq_zero_F2 {x y : F2} (h : x + y = 0) : x = y := by
  exact CharTwo.add_eq_zero.mp h

theorem leftCoeff_column_constant {m : ℕ} (c : Coeff m) (hd : degreeLE3 c)
    (hv : ∀ S, q S = 0 → eval c S = 0) (i k j : Fin m)
    (hik : i ≠ k) (hji : j ≠ i) (hjk : j ≠ k) :
    leftCoeff c i j = leftCoeff c k j := by
  have hz := coeff_eq_zero_of_pairFree c hv
  have hbase := hv (twoPairs i k) (q_twoPairs i k hik)
  have hext := hv (insert (Sum.inl j) (twoPairs i k))
    (q_insert_inl_twoPairs i k j hik hji hjk)
  rw [eval_insert_inl_twoPairs c hd hz i k j hik hji hjk, hbase, zero_add] at hext
  exact eq_of_add_eq_zero_F2 hext

theorem rightCoeff_column_constant {m : ℕ} (c : Coeff m) (hd : degreeLE3 c)
    (hv : ∀ S, q S = 0 → eval c S = 0) (i k j : Fin m)
    (hik : i ≠ k) (hji : j ≠ i) (hjk : j ≠ k) :
    rightCoeff c i j = rightCoeff c k j := by
  have hz := coeff_eq_zero_of_pairFree c hv
  have hbase := hv (twoPairs i k) (q_twoPairs i k hik)
  have hext := hv (insert (Sum.inr j) (twoPairs i k))
    (q_insert_inr_twoPairs i k j hik hji hjk)
  rw [eval_insert_inr_twoPairs c hd hz i k j hik hji hjk, hbase, zero_add] at hext
  exact eq_of_add_eq_zero_F2 hext

private theorem atom_eq_zero_of_large_support {m : ℕ} (M S : Support m) (a : F2)
    (hM : M.card ≤ 3) (hS : 3 < S.card) : atom M a S = 0 := by
  have hne : S ≠ M := by
    intro he
    subst S
    exact Nat.not_lt_of_ge hM hS
  simp [atom, hne]

theorem productCoeff_degreeLE3 {m : ℕ} (δ : F2) (β γ : Fin m → F2) :
    degreeLE3 (productCoeff δ β γ) := by
  intro S hS
  unfold productCoeff
  apply Finset.sum_eq_zero
  intro i _
  have h0 : atom (pair i) δ S = 0 :=
    atom_eq_zero_of_large_support _ _ _ (by simp) hS
  have hl (j : Fin m) : atom (insert (Sum.inl j) (pair i)) (β j) S = 0 := by
    apply atom_eq_zero_of_large_support _ _ _ ?_ hS
    by_cases hji : j = i
    · subst j
      simp [pair]
    · simp [pair, hji]
  have hr (j : Fin m) : atom (insert (Sum.inr j) (pair i)) (γ j) S = 0 := by
    apply atom_eq_zero_of_large_support _ _ _ ?_ hS
    by_cases hji : j = i
    · subst j
      simp [pair]
    · simp [pair, hji]
  simp [h0, hl, hr]

theorem productCoeff_pairFree_zero {m : ℕ} (δ : F2) (β γ : Fin m → F2) :
    ∀ S, PairFree S → productCoeff δ β γ S = 0 := by
  apply coeff_eq_zero_of_pairFree
  intro S hS
  rw [eval_productCoeff, hS, zero_mul]

theorem quadCoeff_productCoeff {m : ℕ} (δ : F2) (β γ : Fin m → F2) (i : Fin m) :
    quadCoeff (productCoeff δ β γ) i = δ + β i + γ i := by
  have h1 := eval_pair_of_pairFree_zero (productCoeff δ β γ)
    (productCoeff_pairFree_zero δ β γ) i
  have h2 := eval_productCoeff δ β γ (pair i)
  rw [q_pair, one_mul, affineEval_pair] at h2
  exact h1.symm.trans h2

theorem leftCoeff_productCoeff {m : ℕ} (δ : F2) (β γ : Fin m → F2)
    (i j : Fin m) (hji : j ≠ i) :
    leftCoeff (productCoeff δ β γ) i j = β j := by
  have hj : Sum.inl j ∉ pair i := by simp [pair, hji]
  have h1 := eval_insert_inl_pair_of_pairFree_zero (productCoeff δ β γ)
    (productCoeff_pairFree_zero δ β γ) i j hji
  have h2 := eval_productCoeff δ β γ (insert (Sum.inl j) (pair i))
  rw [q_insert_inl_pair, one_mul,
    affineEval_insert_inl δ β γ (pair i) j hj, affineEval_pair] at h2
  rw [quadCoeff_productCoeff] at h1
  exact add_left_cancel (h1.symm.trans h2)

theorem rightCoeff_productCoeff {m : ℕ} (δ : F2) (β γ : Fin m → F2)
    (i j : Fin m) (hji : j ≠ i) :
    rightCoeff (productCoeff δ β γ) i j = γ j := by
  have hj : Sum.inr j ∉ pair i := by simp [pair, hji]
  have h1 := eval_insert_inr_pair_of_pairFree_zero (productCoeff δ β γ)
    (productCoeff_pairFree_zero δ β γ) i j hji
  have h2 := eval_productCoeff δ β γ (insert (Sum.inr j) (pair i))
  rw [q_insert_inr_pair, one_mul,
    affineEval_insert_inr δ β γ (pair i) j hj, affineEval_pair] at h2
  rw [quadCoeff_productCoeff] at h1
  exact add_left_cancel (h1.symm.trans h2)

def zeroIndex {m : ℕ} (hm : 2 ≤ m) : Fin m :=
  ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hm⟩

def oneIndex {m : ℕ} (hm : 2 ≤ m) : Fin m :=
  ⟨1, Nat.lt_of_lt_of_le (by decide : 1 < 2) hm⟩

def otherIndex {m : ℕ} (hm : 2 ≤ m) (j : Fin m) : Fin m :=
  if j = zeroIndex hm then oneIndex hm else zeroIndex hm

theorem otherIndex_ne {m : ℕ} (hm : 2 ≤ m) (j : Fin m) : otherIndex hm j ≠ j := by
  by_cases hj : j = zeroIndex hm
  · subst j
    simp [otherIndex, zeroIndex, oneIndex]
  · simp [otherIndex, hj, Ne.symm hj]

/-- The constructive coefficient-level factorization. The anchors 0 and 1
work already for m=2; the three-distinct-index lemma is used only when needed.
-/
theorem exists_productCoeff {m : ℕ} (hm : 2 ≤ m) (c : Coeff m)
    (hd : degreeLE3 c) (hv : ∀ S, q S = 0 → eval c S = 0) :
    ∃ (δ : F2) (β γ : Fin m → F2), c = productCoeff δ β γ := by
  classical
  let β : Fin m → F2 := fun j => leftCoeff c (otherIndex hm j) j
  let γ : Fin m → F2 := fun j => rightCoeff c (otherIndex hm j) j
  let o : Fin m := zeroIndex hm
  let δ : F2 := quadCoeff c o + β o + γ o
  have hz := coeff_eq_zero_of_pairFree c hv
  have hβ (i j : Fin m) (hij : i ≠ j) : leftCoeff c i j = β j := by
    by_cases hi : i = otherIndex hm j
    · simp [β, hi]
    · exact leftCoeff_column_constant c hd hv i (otherIndex hm j) j hi
        (Ne.symm hij) (Ne.symm (otherIndex_ne hm j))
  have hγ (i j : Fin m) (hij : i ≠ j) : rightCoeff c i j = γ j := by
    by_cases hi : i = otherIndex hm j
    · simp [γ, hi]
    · exact rightCoeff_column_constant c hd hv i (otherIndex hm j) j hi
        (Ne.symm hij) (Ne.symm (otherIndex_ne hm j))
  have hA (i : Fin m) : quadCoeff c i = δ + β i + γ i := by
    apply eq_of_add_eq_zero_F2
    by_cases hio : i = o
    · simp [δ, hio, add_comm, add_left_comm, add_assoc]
    · have hbase := hv (twoPairs i o) (q_twoPairs i o hio)
      rw [eval_twoPairs c hd hz i o hio,
        hβ i o hio, hγ i o hio, hβ o i (Ne.symm hio), hγ o i (Ne.symm hio)] at hbase
      simpa [δ, add_assoc] using hbase
  refine ⟨δ, β, γ, ?_⟩
  funext S
  by_cases hlarge : 3 < S.card
  · rw [hd S hlarge, productCoeff_degreeLE3 δ β γ S hlarge]
  · have hcard : S.card ≤ 3 := Nat.le_of_not_gt hlarge
    by_cases hfree : PairFree S
    · rw [hz S hfree, productCoeff_pairFree_zero δ β γ S hfree]
    · have hhas : ∃ i, pair i ⊆ S := by
        simpa only [PairFree, not_forall, not_not] using hfree
      obtain ⟨i, hi⟩ := hhas
      rcases support_eq_pair_or_triple i hcard hi with hS | ⟨j, hji, hS⟩ | ⟨j, hji, hS⟩
      · subst S
        change quadCoeff c i = quadCoeff (productCoeff δ β γ) i
        exact (hA i).trans (quadCoeff_productCoeff δ β γ i).symm
      · subst S
        change leftCoeff c i j = leftCoeff (productCoeff δ β γ) i j
        exact (hβ i j (Ne.symm hji)).trans (leftCoeff_productCoeff δ β γ i j hji).symm
      · subst S
        change rightCoeff c i j = rightCoeff (productCoeff δ β γ) i j
        exact (hγ i j (Ne.symm hji)).trans (rightCoeff_productCoeff δ β γ i j hji).symm

abbrev Multiplier (m : ℕ) := F2 × (Fin m → F2) × (Fin m → F2)

/-- Full coefficient theorem, including uniqueness of the affine multiplier. -/
theorem boolean_cubic_factor_unique {m : ℕ} (hm : 2 ≤ m) (c : Coeff m)
    (hd : degreeLE3 c) (hv : ∀ S, q S = 0 → eval c S = 0) :
    ∃! L : Multiplier m, c = productCoeff L.1 L.2.1 L.2.2 := by
  obtain ⟨δ, β, γ, hc⟩ := exists_productCoeff hm c hd hv
  refine ⟨(δ, β, γ), hc, ?_⟩
  intro L hL
  have heq (S : Support m) :
      q S * affineEval L.1 L.2.1 L.2.2 S = q S * affineEval δ β γ S := by
    calc
      _ = eval (productCoeff L.1 L.2.1 L.2.2) S := (eval_productCoeff _ _ _ _).symm
      _ = eval c S := congrArg (fun d => eval d S) hL.symm
      _ = eval (productCoeff δ β γ) S := congrArg (fun d => eval d S) hc
      _ = _ := eval_productCoeff δ β γ S
  obtain ⟨hδ, hβ, hγ⟩ := affine_multiplier_unique hm heq
  exact Prod.ext hδ (Prod.ext hβ hγ)

/-- Function form of the same theorem, with uniqueness retained. -/
theorem boolean_cubic_eval_factor_unique {m : ℕ} (hm : 2 ≤ m) (c : Coeff m)
    (hd : degreeLE3 c) (hv : ∀ S, q S = 0 → eval c S = 0) :
    ∃! L : Multiplier m, ∀ S,
      eval c S = q S * affineEval L.1 L.2.1 L.2.2 S := by
  obtain ⟨δ, β, γ, hc⟩ := exists_productCoeff hm c hd hv
  have hchosen (S : Support m) : eval c S = q S * affineEval δ β γ S := by
    rw [hc, eval_productCoeff]
  refine ⟨(δ, β, γ), hchosen, ?_⟩
  intro L hL
  have heq (S : Support m) :
      q S * affineEval L.1 L.2.1 L.2.2 S = q S * affineEval δ β γ S :=
    (hL S).symm.trans (hchosen S)
  obtain ⟨hδ, hβ, hγ⟩ := affine_multiplier_unique hm heq
  exact Prod.ext hδ (Prod.ext hβ hγ)

/-- Adapter for the cohomological convention: zero constant coefficient and
vanishing at nonzero singular vectors imply the all-singular hypothesis. -/
theorem boolean_cubic_factor_unique_of_nonzero {m : ℕ} (hm : 2 ≤ m) (c : Coeff m)
    (hd : degreeLE3 c) (hzero : c ∅ = 0)
    (hv : ∀ S, S ≠ ∅ → q S = 0 → eval c S = 0) :
    ∃! L : Multiplier m, c = productCoeff L.1 L.2.1 L.2.2 := by
  apply boolean_cubic_factor_unique hm c hd
  intro S hS
  by_cases he : S = ∅
  · subst S
    simpa using hzero
  · exact hv S he hS

end BarnesWall.BooleanCubic
