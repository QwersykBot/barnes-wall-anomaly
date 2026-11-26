/-
SPDX-License-Identifier: Apache-2.0
See ../LICENSE-Apache-2.0.txt.
-/
import BarnesWall.KRRSupport
import BarnesWall.KRRCanonical

/-!
# Canonical lifts with small coordinate support

These wrappers retain the existing ordered half-Gram matrix,
identity coordinates, and one global cocycle transport. Multiplicativity is
asserted only for the explicit common support and isometry hypotheses below.
-/

set_option autoImplicit false

noncomputable section

namespace BarnesWall.KRRCanonical

open Matrix VOA VOA.LatGen BarnesWall.Lattice128
open scoped Matrix

/-- Common support of size at most three gives composition on all states. -/
theorem liftMap_mul_of_small_support (s : Finset (Fin 7)) (hs : s.card ≤ 3)
    (R T : Matrix Index Index ℤ)
    (hRs : KRRSupport.Supported s R) (hTs : KRRSupport.Supported s T)
    (hR : R * G * Rᵀ = G) (hT : T * G * Tᵀ = G) :
    liftMap (R * T) = (liftMap T).comp (liftMap R) :=
  CanonicalLift.liftMap_mul coordinates lattice_posDef H G R T
    (block := KRRSupport.block s) H_add_transpose
    (fun _ _ h => KRRSupport.H_even_of_same_block (s := s) hs h) hRs hTs hR hT

/-- Ordinary automorphism multiplication applies the lift of `R` first. -/
theorem lift_mul_of_small_support (s : Finset (Fin 7)) (hs : s.card ≤ 3)
    (R T : (Matrix Index Index ℤ)ˣ)
    (hRs : KRRSupport.Supported s (R : Matrix Index Index ℤ))
    (hTs : KRRSupport.Supported s (T : Matrix Index Index ℤ))
    (hR : (R : Matrix Index Index ℤ) * G * (R : Matrix Index Index ℤ)ᵀ = G)
    (hT : (T : Matrix Index Index ℤ) * G * (T : Matrix Index Index ℤ)ᵀ = G) :
    lift (R * T)
        (by
          simpa only [Units.val_mul] using
            (CanonicalLift.matrix_isometry_mul G
              (R : Matrix Index Index ℤ) (T : Matrix Index Index ℤ) hR hT)) =
      lift T hT * lift R hR :=
  CanonicalLift.liftAut_mul coordinates lattice_even lattice_posDef H G R T
    (block := KRRSupport.block s) gram_in_coordinates H_add_transpose
    (fun _ _ h => KRRSupport.H_even_of_same_block (s := s) hs h) hRs hTs hR hT

end BarnesWall.KRRCanonical
