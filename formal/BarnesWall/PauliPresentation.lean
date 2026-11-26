/-
SPDX-License-Identifier: Apache-2.0
See ../LICENSE-Apache-2.0.txt.
-/
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Hom.Basic

/-!
# A finite family of Pauli generators and its presentation

Multiplication here is ordinary group multiplication. Future comparison with
the KRR right matrix action must retain the reversed word labels
`aLift = alpha (z 6 * x 6)` and
`bLift = alpha (z 5 * x 5 * z 6)`.

The normal form used below is a reduced-list normal form: each X list and Z
list has no repeated index, but neither list is sorted and uniqueness is not
claimed. No group cardinality, plus-type classification, lattice action, or
global multiplicativity of a canonical lattice lift is asserted.
-/

set_option autoImplicit false

namespace BarnesWall.PauliPresentation

inductive Generator (n : ℕ) where
  | central
  | x (i : Fin n)
  | z (i : Fin n)

inductive Relator (n : ℕ) where
  | central_sq
  | x_sq (i : Fin n)
  | z_sq (i : Fin n)
  | central_x (i : Fin n)
  | central_z (i : Fin n)
  | xx (i j : Fin n)
  | zz (i j : Fin n)
  | cross (i j : Fin n)

/-- The exact relations required of the chosen generator images. -/
structure Relations {n : ℕ} {G : Type*} [Group G]
    (c : G) (X Z : Fin n → G) : Prop where
  c_sq : c * c = 1
  x_sq : ∀ i, X i * X i = 1
  z_sq : ∀ i, Z i * Z i = 1
  c_comm_x : ∀ i, Commute c (X i)
  c_comm_z : ∀ i, Commute c (Z i)
  x_comm_x : ∀ i j, Commute (X i) (X j)
  z_comm_z : ∀ i j, Commute (Z i) (Z j)
  x_mul_z : ∀ i j, X i * Z j = (if i = j then c else 1) * (Z j * X i)

def normalWord {n : ℕ} {G : Type*} [Group G]
    (c : G) (X Z : Fin n → G) (e : Bool) (xs zs : List (Fin n)) : G :=
  cond e c 1 * (xs.map X).prod * (zs.map Z).prod

def generatorImage {n : ℕ} {G : Type*} [Group G]
    (c : G) (X Z : Fin n → G) : Generator n → G
  | .central => c
  | .x i => X i
  | .z i => Z i

def relatorValue {n : ℕ} {G : Type*} [Group G]
    (c : G) (X Z : Fin n → G) : Relator n → G
  | .central_sq => c * c
  | .x_sq i => X i * X i
  | .z_sq i => Z i * Z i
  | .central_x i => (c * X i) * (X i * c)⁻¹
  | .central_z i => (c * Z i) * (Z i * c)⁻¹
  | .xx i j => (X i * X j) * (X j * X i)⁻¹
  | .zz i j => (Z i * Z j) * (Z j * Z i)⁻¹
  | .cross i j => (X i * Z j) * ((if i = j then c else 1) * (Z j * X i))⁻¹

private theorem map_relatorValue {n : ℕ} {G K : Type*} [Group G] [Group K]
    (φ : G →* K) (c : G) (X Z : Fin n → G) (r : Relator n) :
    φ (relatorValue c X Z r) =
      relatorValue (φ c) (fun i => φ (X i)) (fun i => φ (Z i)) r := by
  cases r with
  | central_sq => simp [relatorValue]
  | x_sq i => simp [relatorValue]
  | z_sq i => simp [relatorValue]
  | central_x i => simp [relatorValue]
  | central_z i => simp [relatorValue]
  | xx i j => simp [relatorValue]
  | zz i j => simp [relatorValue]
  | cross i j =>
      by_cases hij : i = j <;> simp [relatorValue, hij]

private theorem Relations.relators {n : ℕ} {G : Type*} [Group G]
    {c : G} {X Z : Fin n → G} (h : Relations c X Z) (r : Relator n) :
    relatorValue c X Z r = 1 := by
  cases r with
  | central_sq => exact h.c_sq
  | x_sq i => exact h.x_sq i
  | z_sq i => exact h.z_sq i
  | central_x i =>
      change (c * X i) * (X i * c)⁻¹ = 1
      rw [(h.c_comm_x i).eq, mul_inv_cancel]
  | central_z i =>
      change (c * Z i) * (Z i * c)⁻¹ = 1
      rw [(h.c_comm_z i).eq, mul_inv_cancel]
  | xx i j =>
      change (X i * X j) * (X j * X i)⁻¹ = 1
      rw [(h.x_comm_x i j).eq, mul_inv_cancel]
  | zz i j =>
      change (Z i * Z j) * (Z j * Z i)⁻¹ = 1
      rw [(h.z_comm_z i j).eq, mul_inv_cancel]
  | cross i j =>
      change (X i * Z j) * ((if i = j then c else 1) * (Z j * X i))⁻¹ = 1
      rw [h.x_mul_z i j, mul_inv_cancel]

private theorem relations_of_relators {n : ℕ} {G : Type*} [Group G]
    {c : G} {X Z : Fin n → G}
    (h : ∀ r : Relator n, relatorValue c X Z r = 1) : Relations c X Z := by
  refine ⟨h .central_sq, (fun i => h (.x_sq i)), (fun i => h (.z_sq i)),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    change c * X i = X i * c
    exact eq_of_mul_inv_eq_one (h (.central_x i))
  · intro i
    change c * Z i = Z i * c
    exact eq_of_mul_inv_eq_one (h (.central_z i))
  · intro i j
    change X i * X j = X j * X i
    exact eq_of_mul_inv_eq_one (h (.xx i j))
  · intro i j
    change Z i * Z j = Z j * Z i
    exact eq_of_mul_inv_eq_one (h (.zz i j))
  · intro i j
    exact eq_of_mul_inv_eq_one (h (.cross i j))

def relatorWord {n : ℕ} (r : Relator n) : FreeGroup (Generator n) :=
  relatorValue (FreeGroup.of .central)
    (fun i => FreeGroup.of (.x i)) (fun i => FreeGroup.of (.z i)) r

def rels (n : ℕ) : Set (FreeGroup (Generator n)) := Set.range relatorWord

abbrev Pauli (n : ℕ) := PresentedGroup (rels n)

def central (n : ℕ) : Pauli n := PresentedGroup.of .central

def x {n : ℕ} (i : Fin n) : Pauli n := PresentedGroup.of (.x i)

def z {n : ℕ} (i : Fin n) : Pauli n := PresentedGroup.of (.z i)

private theorem canonical_relator {n : ℕ} (r : Relator n) :
    relatorValue (central n) x z r = 1 := by
  have hmem : relatorWord r ∈ rels n := ⟨r, rfl⟩
  have h := PresentedGroup.one_of_mem hmem
  change relatorValue
    ((PresentedGroup.mk (rels n)) (FreeGroup.of .central))
    (fun i : Fin n => (PresentedGroup.mk (rels n)) (FreeGroup.of (.x i)))
    (fun i : Fin n => (PresentedGroup.mk (rels n)) (FreeGroup.of (.z i))) r = 1
  simpa only [relatorWord, map_relatorValue] using h

/-- The literal generators of the presentation satisfy the displayed relations. -/
theorem relations (n : ℕ) : Relations (central n) x z :=
  relations_of_relators canonical_relator

/-- The existing presented-group universal property applied to the explicit relations. -/
def toGroup {n : ℕ} {G : Type*} [Group G]
    {c : G} {X Z : Fin n → G} (h : Relations c X Z) : Pauli n →* G :=
  PresentedGroup.toGroup (f := generatorImage c X Z) (by
    rintro r ⟨q, rfl⟩
    simpa only [relatorWord, map_relatorValue, FreeGroup.lift_apply_of,
      generatorImage] using h.relators q)

@[simp] theorem toGroup_central {n : ℕ} {G : Type*} [Group G]
    {c : G} {X Z : Fin n → G} (h : Relations c X Z) :
    toGroup h (central n) = c := by
  simp [toGroup, central, generatorImage]

@[simp] theorem toGroup_x {n : ℕ} {G : Type*} [Group G]
    {c : G} {X Z : Fin n → G} (h : Relations c X Z) (i : Fin n) :
    toGroup h (x i) = X i := by
  simp [toGroup, x, generatorImage]

@[simp] theorem toGroup_z {n : ℕ} {G : Type*} [Group G]
    {c : G} {X Z : Fin n → G} (h : Relations c X Z) (i : Fin n) :
    toGroup h (z i) = Z i := by
  simp [toGroup, z, generatorImage]

theorem toGroup_unique {n : ℕ} {G : Type*} [Group G]
    {c : G} {X Z : Fin n → G} (h : Relations c X Z)
    (φ : Pauli n →* G) (hc : φ (central n) = c)
    (hX : ∀ i, φ (x i) = X i) (hZ : ∀ i, φ (z i) = Z i) :
    φ = toGroup h := by
  apply PresentedGroup.ext
  intro a
  cases a with
  | central => exact hc.trans (toGroup_central h).symm
  | x i => exact (hX i).trans (toGroup_x h i).symm
  | z i => exact (hZ i).trans (toGroup_z h i).symm

section FaithfulnessHelpers

variable {n : ℕ} {G : Type*} [Group G] {c : G} {X Z : Fin n → G}

private theorem reverse_twist {a b q : G} (hq : q * q = 1)
    (h : a * b = q * (b * a)) : b * a = q * (a * b) := by
  calc
    b * a = (q * q) * (b * a) := by rw [hq, one_mul]
    _ = q * (q * (b * a)) := mul_assoc _ _ _
    _ = q * (a * b) := by rw [← h]

private theorem z_mul_x (r : Relations c X Z) (i j : Fin n) :
    Z i * X j = (if i = j then c else 1) * (X j * Z i) := by
  by_cases hij : i = j
  · subst j
    have h : X i * Z i = c * (Z i * X i) := by
      simpa using r.x_mul_z i i
    simpa using reverse_twist r.c_sq h
  · simpa [hij, Ne.symm hij] using (r.x_mul_z j i).symm

/-- A duplicate-free family crosses a fixed factor with at most one central twist. -/
private theorem prod_mul_twist (A : Fin n → G) (t : G) (j : Fin n)
    (hc : ∀ i, Commute c (A i))
    (hstep : ∀ i, A i * t = (if i = j then c else 1) * (t * A i))
    (xs : List (Fin n)) : xs.Nodup →
    (xs.map A).prod * t =
      (if j ∈ xs then c else 1) * (t * (xs.map A).prod) := by
  induction xs with
  | nil => intro _; simp
  | cons i xs ih =>
      intro hnd
      have hnot : i ∉ xs := (List.nodup_cons.mp hnd).1
      have htail : xs.Nodup := (List.nodup_cons.mp hnd).2
      have hmove : A i * (if j ∈ xs then c else 1) =
          (if j ∈ xs then c else 1) * A i := by
        by_cases hj : j ∈ xs
        · simpa only [ite_eq_left hj] using (hc i).symm.eq
        · simp only [ite_eq_right hj, mul_one, one_mul]
      have hcoeff :
          (if j ∈ xs then c else 1) * (if i = j then c else 1) =
            (if j ∈ i :: xs then c else 1) := by
        by_cases hij : i = j
        · subst i
          simp [hnot]
        · simp [hij, Ne.symm hij]
      simp only [List.map_cons, List.prod_cons]
      calc
        (A i * (xs.map A).prod) * t = A i * ((xs.map A).prod * t) :=
          mul_assoc _ _ _
        _ = A i * ((if j ∈ xs then c else 1) * (t * (xs.map A).prod)) :=
          by rw [ih htail]
        _ = (A i * (if j ∈ xs then c else 1)) * (t * (xs.map A).prod) :=
          (mul_assoc _ _ _).symm
        _ = ((if j ∈ xs then c else 1) * A i) * (t * (xs.map A).prod) :=
          by rw [hmove]
        _ = (if j ∈ xs then c else 1) * ((A i * t) * (xs.map A).prod) :=
          by simp only [mul_assoc]
        _ = (if j ∈ xs then c else 1) *
            (((if i = j then c else 1) * (t * A i)) * (xs.map A).prod) :=
          by rw [hstep i]
        _ = ((if j ∈ xs then c else 1) * (if i = j then c else 1)) *
            (t * (A i * (xs.map A).prod)) := by simp only [mul_assoc]
        _ = (if j ∈ i :: xs then c else 1) *
            (t * (A i * (xs.map A).prod)) := by rw [hcoeff]

/-- Orientation used to move a new Z generator through the X list. -/
private theorem z_mul_x_prod (r : Relations c X Z) (i : Fin n)
    (xs : List (Fin n)) (hxs : xs.Nodup) :
    Z i * (xs.map X).prod =
      (if i ∈ xs then c else 1) * ((xs.map X).prod * Z i) := by
  have hq : (if i ∈ xs then c else 1) * (if i ∈ xs then c else 1) = 1 := by
    by_cases hi : i ∈ xs <;> simp [hi, r.c_sq]
  exact reverse_twist hq
    (prod_mul_twist X (Z i) i r.c_comm_x (fun j => r.x_mul_z j i) xs hxs)

private theorem family_prod_commute (A : Fin n → G) (t : G)
    (h : ∀ i, Commute (A i) t) (xs : List (Fin n)) :
    Commute (xs.map A).prod t := by
  apply Commute.list_prod_left
  intro a ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  exact h i

private theorem central_cond_commute (e : Bool) (t : G) (h : Commute c t) :
    Commute (cond e c 1) t := by
  cases e with
  | false => exact Commute.one_left t
  | true => exact h

private theorem commute_membership_coeff (a : G) (h : Commute a c)
    (j : Fin n) (xs : List (Fin n)) :
    Commute a (if j ∈ xs then c else 1) := by
  by_cases hj : j ∈ xs
  · simpa only [ite_eq_left hj] using h
  · simpa only [ite_eq_right hj] using Commute.one_right a

private theorem prepend_twist {a b t q : G} (hat : Commute a t)
    (haq : Commute a q) (hbt : b * t = q * (t * b)) :
    (a * b) * t = q * (t * (a * b)) := by
  calc
    (a * b) * t = a * (b * t) := mul_assoc _ _ _
    _ = a * (q * (t * b)) := by rw [hbt]
    _ = (a * q) * (t * b) := (mul_assoc _ _ _).symm
    _ = (q * a) * (t * b) := by rw [haq.eq]
    _ = q * ((a * t) * b) := by simp only [mul_assoc]
    _ = q * ((t * a) * b) := by rw [hat.eq]
    _ = q * (t * (a * b)) := by simp only [mul_assoc]

private theorem append_twist {a b t q : G}
    (hat : a * t = q * (t * a)) (hbt : Commute b t) :
    (a * b) * t = q * (t * (a * b)) := by
  calc
    (a * b) * t = a * (b * t) := mul_assoc _ _ _
    _ = a * (t * b) := by rw [hbt.eq]
    _ = (a * t) * b := (mul_assoc _ _ _).symm
    _ = (q * (t * a)) * b := by rw [hat]
    _ = q * (t * (a * b)) := by simp only [mul_assoc]

/-- Testing against X detects membership of its index in the reduced Z list. -/
private theorem normalWord_mul_x (r : Relations c X Z) (e : Bool)
    (xs zs : List (Fin n)) (hzs : zs.Nodup) (j : Fin n) :
    normalWord c X Z e xs zs * X j =
      (if j ∈ zs then c else 1) * (X j * normalWord c X Z e xs zs) := by
  let a : G := cond e c 1 * (xs.map X).prod
  have hat : Commute a (X j) :=
    (central_cond_commute e (X j) (r.c_comm_x j)).mul_left
      (family_prod_commute X (X j) (fun i => r.x_comm_x i j) xs)
  have hac : Commute a c :=
    (central_cond_commute e c (Commute.refl c)).mul_left
      (family_prod_commute X c (fun i => (r.c_comm_x i).symm) xs)
  have haq := commute_membership_coeff a hac j zs
  have htail := prod_mul_twist Z (X j) j r.c_comm_z
    (fun i => z_mul_x r i j) zs hzs
  simpa only [normalWord, a] using prepend_twist hat haq htail

/-- Testing against Z detects membership of its index in the reduced X list. -/
private theorem normalWord_mul_z (r : Relations c X Z) (e : Bool)
    (xs zs : List (Fin n)) (hxs : xs.Nodup) (j : Fin n) :
    normalWord c X Z e xs zs * Z j =
      (if j ∈ xs then c else 1) * (Z j * normalWord c X Z e xs zs) := by
  have hat := central_cond_commute e (Z j) (r.c_comm_z j)
  have haq := commute_membership_coeff (cond e c 1)
    (central_cond_commute e c (Commute.refl c)) j xs
  have hx := prod_mul_twist X (Z j) j r.c_comm_x
    (fun i => r.x_mul_z i j) xs hxs
  have hp := prepend_twist hat haq hx
  have hz := family_prod_commute Z (Z j) (fun i => r.z_comm_z i j) zs
  simpa only [normalWord] using append_twist hp hz

/-- Existence of reduced words, not uniqueness, suffices for this kernel argument.
The presentation-specific theorem must supply its proved existence theorem. -/
private theorem injective_of_normal_forms (r : Relations c X Z)
    (hNF : ∀ g : G, ∃ (e : Bool) (xs zs : List (Fin n)),
      xs.Nodup ∧ zs.Nodup ∧ g = normalWord c X Z e xs zs)
    {K : Type*} [Group K] (φ : G →* K) (hc : φ c ≠ 1) :
    Function.Injective φ := by
  apply (injective_iff_map_eq_one φ).2
  intro g hg
  obtain ⟨e, xs, zs, hxs, hzs, hword⟩ := hNF g
  subst g
  have hxs0 : xs = [] := by
    cases xs with
    | nil => rfl
    | cons i tail =>
        have hi : i ∈ i :: tail := by simp
        have ht := congrArg φ (normalWord_mul_z r e (i :: tail) zs hxs i)
        have htest : φ (Z i) = φ c * φ (Z i) := by
          simpa only [map_mul, ite_eq_left hi, hg, one_mul, mul_one] using ht
        have hc1 : φ c = 1 := mul_right_cancel
          (show φ c * φ (Z i) = 1 * φ (Z i) by
            simpa only [one_mul] using htest.symm)
        exact (hc hc1).elim
  have hzs0 : zs = [] := by
    cases zs with
    | nil => rfl
    | cons i tail =>
        have hi : i ∈ i :: tail := by simp
        have ht := congrArg φ (normalWord_mul_x r e xs (i :: tail) hzs i)
        have htest : φ (X i) = φ c * φ (X i) := by
          simpa only [map_mul, ite_eq_left hi, hg, one_mul, mul_one] using ht
        have hc1 : φ c = 1 := mul_right_cancel
          (show φ c * φ (X i) = 1 * φ (X i) by
            simpa only [one_mul] using htest.symm)
        exact (hc hc1).elim
  subst xs
  subst zs
  cases e with
  | false => simp [normalWord]
  | true =>
      have hc1 : φ c = 1 := by simpa [normalWord] using hg
      exact (hc hc1).elim

end FaithfulnessHelpers

section ToggleList

variable {α G : Type*} [DecidableEq α] [Group G]

/-- Insert a missing index, or remove its single occurrence from a reduced list. -/
private def toggleList (i : α) (xs : List α) : List α :=
  if i ∈ xs then xs.erase i else i :: xs

private theorem toggleList_nodup (i : α) {xs : List α} (hxs : xs.Nodup) :
    (toggleList i xs).Nodup := by
  unfold toggleList
  split_ifs with hi
  · exact List.Nodup.erase i hxs
  · exact List.nodup_cons.mpr ⟨hi, hxs⟩

/-- The noncommutative analogue of prod_map_erase for a commuting family.
No injectivity of F and no Nodup hypothesis are used here. -/
private theorem factor_prod_erase (F : α → G)
    (hcomm : ∀ i j, Commute (F i) (F j)) (i : α)
    (xs : List α) (hi : i ∈ xs) :
    F i * ((xs.erase i).map F).prod = (xs.map F).prod := by
  induction xs with
  | nil => simp only [List.not_mem_nil] at hi
  | cons j ys ih =>
      obtain rfl | ⟨hne, hmem⟩ := List.eq_or_ne_mem_of_mem hi
      · simp only [List.erase_cons_head, List.map_cons, List.prod_cons]
      · calc
          F i * (((j :: ys).erase i).map F).prod =
              F i * (F j * ((ys.erase i).map F).prod) := by
                rw [List.erase_cons_tail (not_beq_of_ne hne.symm),
                  List.map_cons, List.prod_cons]
          _ = F j * (F i * ((ys.erase i).map F).prod) :=
                (hcomm i j).left_comm _
          _ = F j * (ys.map F).prod := by rw [ih hmem]
          _ = ((j :: ys).map F).prod := by
                rw [List.map_cons, List.prod_cons]

/-- Multiplication by an involutory member toggles its index in a commuting word. -/
private theorem prod_toggleList (F : α → G)
    (hcomm : ∀ i j, Commute (F i) (F j))
    (hsq : ∀ i, F i * F i = 1) (i : α) (xs : List α) :
    ((toggleList i xs).map F).prod = F i * (xs.map F).prod := by
  unfold toggleList
  split_ifs with hi
  · have he := factor_prod_erase F hcomm i xs hi
    calc
      ((xs.erase i).map F).prod =
          (F i * F i) * ((xs.erase i).map F).prod := by rw [hsq, one_mul]
      _ = F i * (F i * ((xs.erase i).map F).prod) := mul_assoc _ _ _
      _ = F i * (xs.map F).prod := by rw [he]
  · simp only [List.map_cons, List.prod_cons]

end ToggleList

section LeftNormalization

variable {n : ℕ} {G : Type*} [Group G]
variable {c : G} {X Z : Fin n → G}

private theorem normalWord_left_c (h : Relations c X Z)
    (e : Bool) (xs zs : List (Fin n)) :
    c * normalWord c X Z e xs zs = normalWord c X Z (!e) xs zs := by
  cases e with
  | false =>
      change c * (1 * (xs.map X).prod * (zs.map Z).prod) =
        c * (xs.map X).prod * (zs.map Z).prod
      simp only [one_mul, mul_assoc]
  | true =>
      change c * (c * (xs.map X).prod * (zs.map Z).prod) =
        1 * (xs.map X).prod * (zs.map Z).prod
      simp only [← mul_assoc, h.c_sq, one_mul]

private theorem normalWord_left_x (h : Relations c X Z) (i : Fin n)
    (e : Bool) (xs zs : List (Fin n)) :
    X i * normalWord c X Z e xs zs =
      normalWord c X Z e (toggleList i xs) zs := by
  have hcx : X i * cond e c 1 = cond e c 1 * X i := by
    cases e with
    | false => simp
    | true => exact (h.c_comm_x i).symm.eq
  unfold normalWord
  calc
    X i * (cond e c 1 * (xs.map X).prod * (zs.map Z).prod) =
        (X i * cond e c 1) * (xs.map X).prod * (zs.map Z).prod := by
          simp only [mul_assoc]
    _ = (cond e c 1 * X i) * (xs.map X).prod * (zs.map Z).prod := by rw [hcx]
    _ = cond e c 1 * (X i * (xs.map X).prod) * (zs.map Z).prod := by
          simp only [mul_assoc]
    _ = cond e c 1 * ((toggleList i xs).map X).prod * (zs.map Z).prod := by
          rw [prod_toggleList X h.x_comm_x h.x_sq i xs]

/-- The cross-product lemma is supplied by the separately reviewed commutator fragment. -/
private theorem normalWord_left_z (h : Relations c X Z) (i : Fin n)
    (e : Bool) (xs zs : List (Fin n)) (hxs : xs.Nodup) :
    Z i * normalWord c X Z e xs zs =
      normalWord c X Z (if i ∈ xs then !e else e) xs (toggleList i zs) := by
  have hcz : Z i * cond e c 1 = cond e c 1 * Z i := by
    cases e with
    | false => simp
    | true => exact (h.c_comm_z i).symm.eq
  have hphase : cond e c 1 * (if i ∈ xs then c else 1) =
      cond (if i ∈ xs then !e else e) c 1 := by
    by_cases hi : i ∈ xs
    · simp only [ite_eq_left hi]
      cases e with
      | false => exact one_mul c
      | true => exact h.c_sq
    · simp only [ite_eq_right hi, mul_one]
  unfold normalWord
  calc
    Z i * (cond e c 1 * (xs.map X).prod * (zs.map Z).prod) =
        (Z i * cond e c 1) * (xs.map X).prod * (zs.map Z).prod := by
          simp only [mul_assoc]
    _ = (cond e c 1 * Z i) * (xs.map X).prod * (zs.map Z).prod := by rw [hcz]
    _ = cond e c 1 * (Z i * (xs.map X).prod) * (zs.map Z).prod := by
          simp only [mul_assoc]
    _ = cond e c 1 * ((if i ∈ xs then c else 1) *
          ((xs.map X).prod * Z i)) * (zs.map Z).prod := by
          rw [z_mul_x_prod h i xs hxs]
    _ = (cond e c 1 * (if i ∈ xs then c else 1)) *
          (xs.map X).prod * (Z i * (zs.map Z).prod) := by
          simp only [mul_assoc]
    _ = cond (if i ∈ xs then !e else e) c 1 *
          (xs.map X).prod * (Z i * (zs.map Z).prod) := by rw [hphase]
    _ = cond (if i ∈ xs then !e else e) c 1 *
          (xs.map X).prod * ((toggleList i zs).map Z).prod := by
          rw [prod_toggleList Z h.z_comm_z h.z_sq i zs]

end LeftNormalization

section FreeWordExistence

variable {n : ℕ} {G : Type*} [Group G]
variable {c : G} {X Z : Fin n → G}

private theorem self_inverse_of_square (a : G) (ha : a * a = 1) : a⁻¹ = a := by
  calc
    a⁻¹ = a⁻¹ * 1 := (mul_one _).symm
    _ = a⁻¹ * (a * a) := by rw [ha]
    _ = (a⁻¹ * a) * a := (mul_assoc _ _ _).symm
    _ = a := by rw [inv_mul_cancel, one_mul]

private theorem generatorImage_inverse (h : Relations c X Z) (a : Generator n) :
    (generatorImage c X Z a)⁻¹ = generatorImage c X Z a := by
  cases a with
  | central => exact self_inverse_of_square c h.c_sq
  | x i => exact self_inverse_of_square (X i) (h.x_sq i)
  | z i => exact self_inverse_of_square (Z i) (h.z_sq i)

/-- Existence comes from actual signed words; no normal-form premise is introduced. -/
private theorem exists_normalWord_of_freeWord (h : Relations c X Z)
    (w : FreeGroup (Generator n)) :
    ∃ (e : Bool) (xs zs : List (Fin n)), xs.Nodup ∧ zs.Nodup ∧
      FreeGroup.lift (generatorImage c X Z) w = normalWord c X Z e xs zs := by
  refine Quot.inductionOn w ?_
  intro L
  change ∃ (e : Bool) (xs zs : List (Fin n)), xs.Nodup ∧ zs.Nodup ∧
    (L.map (fun a : Generator n × Bool =>
      cond a.2 (generatorImage c X Z a.1) (generatorImage c X Z a.1)⁻¹)).prod =
      normalWord c X Z e xs zs
  induction L with
  | nil =>
      refine ⟨false, [], [], ?_, ?_, ?_⟩
      · simp
      · simp
      · simp [normalWord]
  | cons a L ih =>
      obtain ⟨q, sign⟩ := a
      obtain ⟨e, xs, zs, hxs, hzs, he⟩ := ih
      have hsign : cond sign (generatorImage c X Z q)
          (generatorImage c X Z q)⁻¹ = generatorImage c X Z q := by
        cases sign with
        | false => exact generatorImage_inverse h q
        | true => rfl
      simp only [List.map_cons, List.prod_cons]
      rw [hsign, he]
      cases q with
      | central =>
          exact ⟨!e, xs, zs, hxs, hzs, normalWord_left_c h e xs zs⟩
      | x i =>
          exact ⟨e, toggleList i xs, zs, toggleList_nodup i hxs, hzs,
            normalWord_left_x h i e xs zs⟩
      | z i =>
          exact ⟨(if i ∈ xs then !e else e), xs, toggleList i zs,
            hxs, toggleList_nodup i hzs, normalWord_left_z h i e xs zs hxs⟩

end FreeWordExistence

/-- Every element of the actual presentation has a reduced-list Pauli word. -/
theorem exists_normalWord {n : ℕ} (g : Pauli n) :
    ∃ (e : Bool) (xs zs : List (Fin n)), xs.Nodup ∧ zs.Nodup ∧
      g = normalWord (central n) x z e xs zs := by
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective (rels n) g
  have hmk : PresentedGroup.mk (rels n) w =
      FreeGroup.lift (generatorImage (central n) x z) w := by
    apply FreeGroup.lift_unique
    intro a
    cases a <;> rfl
  rw [hmk]
  exact exists_normalWord_of_freeWord (relations n) w

/-- Every homomorphism from this presentation with nontrivial central image is faithful.
The normal-form premise of the internal kernel lemma is discharged by the proved
reduced-list existence theorem. -/
theorem injective_of_central_ne_one {n : ℕ} {G : Type*} [Group G]
    (φ : Pauli n →* G) (hc : φ (central n) ≠ 1) : Function.Injective φ :=
  injective_of_normal_forms (relations n) exists_normalWord φ hc

/-- The universal map is faithful when its specified central image is nontrivial. -/
theorem toGroup_injective {n : ℕ} {G : Type*} [Group G]
    {c : G} {X Z : Fin n → G} (h : Relations c X Z) (hc : c ≠ 1) :
    Function.Injective (toGroup h) :=
  injective_of_central_ne_one (toGroup h) (by simpa only [toGroup_central] using hc)

end BarnesWall.PauliPresentation
