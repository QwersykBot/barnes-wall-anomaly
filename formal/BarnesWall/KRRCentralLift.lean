/-
SPDX-License-Identifier: Apache-2.0
See ../LICENSE-Apache-2.0.txt.
-/
import BarnesWall.CentralLift
import BarnesWall.KRRQuaternionAction

/-!
# The central element of the concrete KRR quaternion action

The actual central matrix unit has value `-1`. Specializing the generic
all-state comparison identifies its canonical lift with upstream `thetaAut`,
and hence identifies the image of `QuaternionGroup.a 4` under the existing
conformal automorphism action. These declarations are checked by the separate
local-bridge stage; the dependency audit alone does not certify them.
-/

set_option autoImplicit false

namespace BarnesWall.KRRCentralLift

open VOA.LatGen BarnesWall.Lattice128

/-- The concrete canonical central lift is exactly the prescribed lattice involution. -/
theorem centralLift_eq_thetaAut :
    KRRQuaternionAction.centralLift = thetaAut lattice lattice_even lattice_posDef := by
  exact CanonicalLift.liftAut_eq_thetaAut_of_val_neg_one
    KRRCanonical.coordinates lattice_even lattice_posDef H G
    KRRQuaternionAction.centralUnit KRRCanonical.gram_in_coordinates H_add_transpose
    KRRQuaternionAction.centralUnit_isometry KRRQuaternionAction.centralUnit_val

/-- The central quaternion element acts by the same full lattice-VOA involution. -/
theorem action_a_four_eq_thetaAut :
    KRRQuaternionAction.action (QuaternionGroup.a 4) =
      thetaAut lattice lattice_even lattice_posDef :=
  KRRQuaternionAction.action_a_four.trans centralLift_eq_thetaAut

end BarnesWall.KRRCentralLift
