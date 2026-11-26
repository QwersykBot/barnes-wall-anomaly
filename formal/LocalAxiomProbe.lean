import BarnesWall.BlockPhase
import BarnesWall.IntegerPhase
import BarnesWall.Lattice128
import BarnesWall.KRRBlocks
import BarnesWall.KRRPauli
import BarnesWall.KRRSupport
import BarnesWall.KRRQ16
import BarnesWall.CocycleTransport
import BarnesWall.LatticeComposition
import BarnesWall.CanonicalLift
import BarnesWall.CanonicalFaithfulness
import BarnesWall.KRRCanonical
import BarnesWall.KRRSupportedLift
import BarnesWall.QuaternionLift
import BarnesWall.KRRQuaternionAction
import BarnesWall.CentralLift
import BarnesWall.KRRCentralLift
import BarnesWall.KRRPauliLift
import BarnesWall.PauliPresentation
import BarnesWall.KRRPauliMatrix
import BarnesWall.KRRPauliAction
import BarnesWall.BooleanCubic

#check BarnesWall.transportDiscrepancy_symm_even
#print axioms BarnesWall.transportDiscrepancy_symm_even

#check BarnesWall.globalTau_zero
#print axioms BarnesWall.globalTau_zero

#check BarnesWall.globalTau_ne_zero
#print axioms BarnesWall.globalTau_ne_zero

#check BarnesWall.globalTau_neg
#print axioms BarnesWall.globalTau_neg

#check BarnesWall.globalTau_add
#print axioms BarnesWall.globalTau_add

#check BarnesWall.globalTau_cocycle
#print axioms BarnesWall.globalTau_cocycle

#check BarnesWall.transportedPhase_zero
#print axioms BarnesWall.transportedPhase_zero

#check BarnesWall.transportedPhase_ne_zero
#print axioms BarnesWall.transportedPhase_ne_zero

#check BarnesWall.transportedPhase_neg
#print axioms BarnesWall.transportedPhase_neg

#check BarnesWall.transportedPhase_cocycle
#print axioms BarnesWall.transportedPhase_cocycle

#check BarnesWall.latMorphC_surjective
#print axioms BarnesWall.latMorphC_surjective

#check BarnesWall.latticeAutOfPhase
#print axioms BarnesWall.latticeAutOfPhase

#check BarnesWall.latticeAutOfPhase_apply
#print axioms BarnesWall.latticeAutOfPhase_apply

#check BarnesWall.transportedAut
#print axioms BarnesWall.transportedAut

#check BarnesWall.BlockPhase.strictLower_add_transpose
#print axioms BarnesWall.BlockPhase.strictLower_add_transpose

#check BarnesWall.BlockPhase.liftDefect_diagonal
#print axioms BarnesWall.BlockPhase.liftDefect_diagonal

#check BarnesWall.BlockPhase.canonicalMatrix_add_transpose
#print axioms BarnesWall.BlockPhase.canonicalMatrix_add_transpose

#check BarnesWall.BlockPhase.compositionDefect_diagonal
#print axioms BarnesWall.BlockPhase.compositionDefect_diagonal

#check BarnesWall.BlockPhase.compositionDefect_add_transpose
#print axioms BarnesWall.BlockPhase.compositionDefect_add_transpose

#check BarnesWall.BlockPhase.quadratic_zero_of_symmetric_zero_diagonal
#print axioms BarnesWall.BlockPhase.quadratic_zero_of_symmetric_zero_diagonal

#check BarnesWall.BlockPhase.canonicalPhase_mul
#print axioms BarnesWall.BlockPhase.canonicalPhase_mul

#check BarnesWall.latMatrix_comp
#print axioms BarnesWall.latMatrix_comp

#check BarnesWall.frameMatrix_comp
#print axioms BarnesWall.frameMatrix_comp

#check BarnesWall.oscMatrix_comp
#print axioms BarnesWall.oscMatrix_comp

#check BarnesWall.latMorphC_comp
#print axioms BarnesWall.latMorphC_comp

#check BarnesWall.transportedPhase_comp
#print axioms BarnesWall.transportedPhase_comp

#check BarnesWall.transported_latMorphC_comp
#print axioms BarnesWall.transported_latMorphC_comp

#check BarnesWall.IntegerPhase.reduce_exponent
#print axioms BarnesWall.IntegerPhase.reduce_exponent

#check BarnesWall.IntegerPhase.liftDefect_diagonal
#print axioms BarnesWall.IntegerPhase.liftDefect_diagonal

#check BarnesWall.IntegerPhase.exponent_cocycle_mod_two
#print axioms BarnesWall.IntegerPhase.exponent_cocycle_mod_two

#check BarnesWall.IntegerPhase.neg_one_zpow_eq_of_mod_two
#print axioms BarnesWall.IntegerPhase.neg_one_zpow_eq_of_mod_two

#check BarnesWall.IntegerPhase.phase_zero
#print axioms BarnesWall.IntegerPhase.phase_zero

#check BarnesWall.IntegerPhase.phase_ne_zero
#print axioms BarnesWall.IntegerPhase.phase_ne_zero

#check BarnesWall.IntegerPhase.phase_neg
#print axioms BarnesWall.IntegerPhase.phase_neg

#check BarnesWall.IntegerPhase.phase_cocycle
#print axioms BarnesWall.IntegerPhase.phase_cocycle

#check BarnesWall.IntegerPhase.phase_cocycle_of_form
#print axioms BarnesWall.IntegerPhase.phase_cocycle_of_form

#check BarnesWall.IntegerPhase.exponent_mul_mod_two
#print axioms BarnesWall.IntegerPhase.exponent_mul_mod_two

#check BarnesWall.IntegerPhase.phase_mul
#print axioms BarnesWall.IntegerPhase.phase_mul

#check BarnesWall.Lattice128.support_injective
#print axioms BarnesWall.Lattice128.support_injective

#check BarnesWall.Lattice128.card_support_subsets
#print axioms BarnesWall.Lattice128.card_support_subsets

#check BarnesWall.Lattice128.gramPower_ge_four
#print axioms BarnesWall.Lattice128.gramPower_ge_four

#check BarnesWall.Lattice128.B_mul_transpose
#print axioms BarnesWall.Lattice128.B_mul_transpose

#check BarnesWall.Lattice128.basisMatrix_gram
#print axioms BarnesWall.Lattice128.basisMatrix_gram

#check BarnesWall.Lattice128.B_lower_triangular
#print axioms BarnesWall.Lattice128.B_lower_triangular

#check BarnesWall.Lattice128.B_det_ne_zero
#print axioms BarnesWall.Lattice128.B_det_ne_zero

#check BarnesWall.Lattice128.H_add_transpose
#print axioms BarnesWall.Lattice128.H_add_transpose

#check BarnesWall.Lattice128.halfForm_symmetrization
#print axioms BarnesWall.Lattice128.halfForm_symmetrization

#check BarnesWall.Lattice128.form_orderedBasis
#print axioms BarnesWall.Lattice128.form_orderedBasis

#check BarnesWall.Lattice128.halfForm_orderedBasis
#print axioms BarnesWall.Lattice128.halfForm_orderedBasis

#check BarnesWall.Lattice128.lattice_rank
#print axioms BarnesWall.Lattice128.lattice_rank

#check BarnesWall.Lattice128.lattice_even
#print axioms BarnesWall.Lattice128.lattice_even

#check BarnesWall.Lattice128.scaled_form
#print axioms BarnesWall.Lattice128.scaled_form

#check BarnesWall.Lattice128.lattice_posDef
#print axioms BarnesWall.Lattice128.lattice_posDef

#check BarnesWall.KRRBlocks.H_even_of_same_block
#print axioms BarnesWall.KRRBlocks.H_even_of_same_block

#check BarnesWall.KRRBlocks.block_eq_iff
#print axioms BarnesWall.KRRBlocks.block_eq_iff

#check BarnesWall.KRRBlocks.block_surjective
#print axioms BarnesWall.KRRBlocks.block_surjective

#check BarnesWall.KRRBlocks.block_val
#print axioms BarnesWall.KRRBlocks.block_val

#check BarnesWall.KRRBlocks.four_dvd_G_of_same_block
#print axioms BarnesWall.KRRBlocks.four_dvd_G_of_same_block

#check BarnesWall.KRRBlocks.four_dvd_H_of_same_block
#print axioms BarnesWall.KRRBlocks.four_dvd_H_of_same_block

#check BarnesWall.KRRBlocks.gramPower_ge_six_of_same_block
#print axioms BarnesWall.KRRBlocks.gramPower_ge_six_of_same_block

#check BarnesWall.KRRBlocks.low_testBit_eq
#print axioms BarnesWall.KRRBlocks.low_testBit_eq

#check BarnesWall.KRRBlocks.mem_support_low_iff
#print axioms BarnesWall.KRRBlocks.mem_support_low_iff

#check BarnesWall.KRRBlocks.support_difference_subset
#print axioms BarnesWall.KRRBlocks.support_difference_subset

#check BarnesWall.KRRBlocks.support_union_card_le
#print axioms BarnesWall.KRRBlocks.support_union_card_le

#check BarnesWall.KRRPauli.support_indexOfSupport
#print axioms BarnesWall.KRRPauli.support_indexOfSupport

#check BarnesWall.KRRPauli.toggle_toggle
#print axioms BarnesWall.KRRPauli.toggle_toggle

#check BarnesWall.KRRPauli.parity_toggle
#print axioms BarnesWall.KRRPauli.parity_toggle

#check BarnesWall.KRRPauli.block_toggle
#print axioms BarnesWall.KRRPauli.block_toggle

#check BarnesWall.KRRPauli.X_mul_B
#print axioms BarnesWall.KRRPauli.X_mul_B

#check BarnesWall.KRRPauli.Z_mul_B
#print axioms BarnesWall.KRRPauli.Z_mul_B

#check BarnesWall.KRRPauli.isometry_of_intertwining
#print axioms BarnesWall.KRRPauli.isometry_of_intertwining

#check BarnesWall.KRRPauli.X_isometry
#print axioms BarnesWall.KRRPauli.X_isometry

#check BarnesWall.KRRPauli.Z_isometry
#print axioms BarnesWall.KRRPauli.Z_isometry

#check BarnesWall.KRRPauli.X_sq
#print axioms BarnesWall.KRRPauli.X_sq

#check BarnesWall.KRRPauli.Z_sq
#print axioms BarnesWall.KRRPauli.Z_sq

#check BarnesWall.KRRPauli.XUnit
#print axioms BarnesWall.KRRPauli.XUnit

#check BarnesWall.KRRPauli.ZUnit
#print axioms BarnesWall.KRRPauli.ZUnit

#check BarnesWall.KRRPauli.X_block_support
#print axioms BarnesWall.KRRPauli.X_block_support

#check BarnesWall.KRRPauli.Z_block_support
#print axioms BarnesWall.KRRPauli.Z_block_support

#check BarnesWall.CanonicalLift.halfForm_symmetrization
#print axioms BarnesWall.CanonicalLift.halfForm_symmetrization

#check BarnesWall.CanonicalLift.even_of_halfForm
#print axioms BarnesWall.CanonicalLift.even_of_halfForm

#check BarnesWall.CanonicalLift.rowEquiv
#print axioms BarnesWall.CanonicalLift.rowEquiv

#check BarnesWall.CanonicalLift.rowMap_mul
#print axioms BarnesWall.CanonicalLift.rowMap_mul

#check BarnesWall.CanonicalLift.rowMap_isometry
#print axioms BarnesWall.CanonicalLift.rowMap_isometry

#check BarnesWall.CanonicalLift.phase_zero
#print axioms BarnesWall.CanonicalLift.phase_zero

#check BarnesWall.CanonicalLift.phase_ne_zero
#print axioms BarnesWall.CanonicalLift.phase_ne_zero

#check BarnesWall.CanonicalLift.phase_neg
#print axioms BarnesWall.CanonicalLift.phase_neg

#check BarnesWall.CanonicalLift.phase_cocycle
#print axioms BarnesWall.CanonicalLift.phase_cocycle

#check BarnesWall.CanonicalLift.liftAut
#print axioms BarnesWall.CanonicalLift.liftAut

#check BarnesWall.CanonicalLift.liftAut_apply
#print axioms BarnesWall.CanonicalLift.liftAut_apply

#check BarnesWall.CanonicalLift.phase_mul
#print axioms BarnesWall.CanonicalLift.phase_mul

#check BarnesWall.CanonicalLift.liftMap_mul
#print axioms BarnesWall.CanonicalLift.liftMap_mul

#check BarnesWall.CanonicalLift.liftAut_mul
#print axioms BarnesWall.CanonicalLift.liftAut_mul

#check BarnesWall.CanonicalFaithfulness.charge_eq_of_smul_eq
#print axioms BarnesWall.CanonicalFaithfulness.charge_eq_of_smul_eq

#check BarnesWall.CanonicalFaithfulness.latticeMap_eq_of_latMorphC_eq
#print axioms BarnesWall.CanonicalFaithfulness.latticeMap_eq_of_latMorphC_eq

#check BarnesWall.CanonicalFaithfulness.rowMap_injective
#print axioms BarnesWall.CanonicalFaithfulness.rowMap_injective

#check BarnesWall.CanonicalFaithfulness.liftMap_injective
#print axioms BarnesWall.CanonicalFaithfulness.liftMap_injective

#check BarnesWall.KRRQ16.toggle_commute
#print axioms BarnesWall.KRRQ16.toggle_commute

#check BarnesWall.KRRQ16.Z_mul_X
#print axioms BarnesWall.KRRQ16.Z_mul_X

#check BarnesWall.KRRQ16.two_g
#print axioms BarnesWall.KRRQ16.two_g

#check BarnesWall.KRRQ16.two_g_mul_B
#print axioms BarnesWall.KRRQ16.two_g_mul_B

#check BarnesWall.KRRQ16.D_mul_transpose
#print axioms BarnesWall.KRRQ16.D_mul_transpose

#check BarnesWall.KRRQ16.g_isometry
#print axioms BarnesWall.KRRQ16.g_isometry

#check BarnesWall.KRRQ16.a_isometry
#print axioms BarnesWall.KRRQ16.a_isometry

#check BarnesWall.KRRQ16.b_isometry
#print axioms BarnesWall.KRRQ16.b_isometry

#check BarnesWall.KRRQ16.g_sq
#print axioms BarnesWall.KRRQ16.g_sq

#check BarnesWall.KRRQ16.g_four
#print axioms BarnesWall.KRRQ16.g_four

#check BarnesWall.KRRQ16.b_sq
#print axioms BarnesWall.KRRQ16.b_sq

#check BarnesWall.KRRQ16.b_g_b_g
#print axioms BarnesWall.KRRQ16.b_g_b_g

#check BarnesWall.KRRQ16.g_eight
#print axioms BarnesWall.KRRQ16.g_eight

#check BarnesWall.KRRQ16.gUnit
#print axioms BarnesWall.KRRQ16.gUnit

#check BarnesWall.KRRQ16.bUnit
#print axioms BarnesWall.KRRQ16.bUnit

#check BarnesWall.KRRQ16.a_block_support
#print axioms BarnesWall.KRRQ16.a_block_support

#check BarnesWall.KRRQ16.b_block_support
#print axioms BarnesWall.KRRQ16.b_block_support

#check BarnesWall.KRRQ16.g_block_support
#print axioms BarnesWall.KRRQ16.g_block_support

#check BarnesWall.KRRQ16.neg_one_ne_one
#print axioms BarnesWall.KRRQ16.neg_one_ne_one

#check BarnesWall.KRRQ16.g_four_ne_one
#print axioms BarnesWall.KRRQ16.g_four_ne_one

#check BarnesWall.KRRCanonical.coordinates_apply
#print axioms BarnesWall.KRRCanonical.coordinates_apply

#check BarnesWall.KRRCanonical.gram_in_coordinates
#print axioms BarnesWall.KRRCanonical.gram_in_coordinates

#check BarnesWall.KRRCanonical.canonicalHalfForm_eq
#print axioms BarnesWall.KRRCanonical.canonicalHalfForm_eq

#check BarnesWall.KRRCanonical.lift
#print axioms BarnesWall.KRRCanonical.lift

#check BarnesWall.KRRCanonical.lift_apply
#print axioms BarnesWall.KRRCanonical.lift_apply

#check BarnesWall.KRRCanonical.liftMap_mul
#print axioms BarnesWall.KRRCanonical.liftMap_mul

#check BarnesWall.KRRCanonical.lift_mul
#print axioms BarnesWall.KRRCanonical.lift_mul

#check BarnesWall.KRRCanonical.liftMap_injective
#print axioms BarnesWall.KRRCanonical.liftMap_injective

#check BarnesWall.KRRCanonical.matrix_eq_of_lift_eq
#print axioms BarnesWall.KRRCanonical.matrix_eq_of_lift_eq

#check BarnesWall.QuaternionLift.ofRelations
#print axioms BarnesWall.QuaternionLift.ofRelations

#check BarnesWall.QuaternionLift.ofRelations_a_natCast
#print axioms BarnesWall.QuaternionLift.ofRelations_a_natCast

#check BarnesWall.QuaternionLift.ofRelations_a_one
#print axioms BarnesWall.QuaternionLift.ofRelations_a_one

#check BarnesWall.QuaternionLift.ofRelations_a_two
#print axioms BarnesWall.QuaternionLift.ofRelations_a_two

#check BarnesWall.QuaternionLift.ofRelations_a_four
#print axioms BarnesWall.QuaternionLift.ofRelations_a_four

#check BarnesWall.QuaternionLift.ofRelations_xa_zero
#print axioms BarnesWall.QuaternionLift.ofRelations_xa_zero

#check BarnesWall.QuaternionLift.ofRelations_injective
#print axioms BarnesWall.QuaternionLift.ofRelations_injective

#check BarnesWall.KRRQuaternionAction.one_isometry
#print axioms BarnesWall.KRRQuaternionAction.one_isometry

#check BarnesWall.KRRQuaternionAction.lift_one
#print axioms BarnesWall.KRRQuaternionAction.lift_one

#check BarnesWall.KRRQuaternionAction.pow_isometry
#print axioms BarnesWall.KRRQuaternionAction.pow_isometry

#check BarnesWall.KRRQuaternionAction.lift_pow
#print axioms BarnesWall.KRRQuaternionAction.lift_pow

#check BarnesWall.KRRQuaternionAction.aUnit_val
#print axioms BarnesWall.KRRQuaternionAction.aUnit_val

#check BarnesWall.KRRQuaternionAction.aUnit_isometry
#print axioms BarnesWall.KRRQuaternionAction.aUnit_isometry

#check BarnesWall.KRRQuaternionAction.centralUnit_val
#print axioms BarnesWall.KRRQuaternionAction.centralUnit_val

#check BarnesWall.KRRQuaternionAction.centralUnit_isometry
#print axioms BarnesWall.KRRQuaternionAction.centralUnit_isometry

#check BarnesWall.KRRQuaternionAction.gLift_sq
#print axioms BarnesWall.KRRQuaternionAction.gLift_sq

#check BarnesWall.KRRQuaternionAction.gLift_four
#print axioms BarnesWall.KRRQuaternionAction.gLift_four

#check BarnesWall.KRRQuaternionAction.reversed_unit_word
#print axioms BarnesWall.KRRQuaternionAction.reversed_unit_word

#check BarnesWall.KRRQuaternionAction.gLift_eight
#print axioms BarnesWall.KRRQuaternionAction.gLift_eight

#check BarnesWall.KRRQuaternionAction.bLift_sq
#print axioms BarnesWall.KRRQuaternionAction.bLift_sq

#check BarnesWall.KRRQuaternionAction.gLift_mul_bLift
#print axioms BarnesWall.KRRQuaternionAction.gLift_mul_bLift

#check BarnesWall.KRRQuaternionAction.gLift_four_ne_one
#print axioms BarnesWall.KRRQuaternionAction.gLift_four_ne_one

#check BarnesWall.KRRQuaternionAction.action
#print axioms BarnesWall.KRRQuaternionAction.action

#check BarnesWall.KRRQuaternionAction.action_a_one
#print axioms BarnesWall.KRRQuaternionAction.action_a_one

#check BarnesWall.KRRQuaternionAction.action_xa_zero
#print axioms BarnesWall.KRRQuaternionAction.action_xa_zero

#check BarnesWall.KRRQuaternionAction.action_a_two
#print axioms BarnesWall.KRRQuaternionAction.action_a_two

#check BarnesWall.KRRQuaternionAction.action_a_four
#print axioms BarnesWall.KRRQuaternionAction.action_a_four

#check BarnesWall.KRRQuaternionAction.action_xa_nat
#print axioms BarnesWall.KRRQuaternionAction.action_xa_nat

#check BarnesWall.KRRQuaternionAction.action_injective
#print axioms BarnesWall.KRRQuaternionAction.action_injective

#check BarnesWall.CanonicalLift.liftMap_neg_one
#print axioms BarnesWall.CanonicalLift.liftMap_neg_one

#check BarnesWall.CanonicalLift.liftAut_eq_thetaAut_of_val_neg_one
#print axioms BarnesWall.CanonicalLift.liftAut_eq_thetaAut_of_val_neg_one

#check BarnesWall.KRRCentralLift.centralLift_eq_thetaAut
#print axioms BarnesWall.KRRCentralLift.centralLift_eq_thetaAut

#check BarnesWall.KRRCentralLift.action_a_four_eq_thetaAut
#print axioms BarnesWall.KRRCentralLift.action_a_four_eq_thetaAut

#check BarnesWall.BooleanCubic.eval_injective
#print axioms BarnesWall.BooleanCubic.eval_injective

#check BarnesWall.BooleanCubic.coeff_eq_zero_of_pairFree
#print axioms BarnesWall.BooleanCubic.coeff_eq_zero_of_pairFree

#check BarnesWall.BooleanCubic.eval_productCoeff
#print axioms BarnesWall.BooleanCubic.eval_productCoeff

#check BarnesWall.BooleanCubic.affine_multiplier_unique
#print axioms BarnesWall.BooleanCubic.affine_multiplier_unique

#check BarnesWall.BooleanCubic.exists_productCoeff
#print axioms BarnesWall.BooleanCubic.exists_productCoeff

#check BarnesWall.BooleanCubic.boolean_cubic_factor_unique
#print axioms BarnesWall.BooleanCubic.boolean_cubic_factor_unique

#check BarnesWall.BooleanCubic.boolean_cubic_eval_factor_unique
#print axioms BarnesWall.BooleanCubic.boolean_cubic_eval_factor_unique

#check BarnesWall.BooleanCubic.boolean_cubic_factor_unique_of_nonzero
#print axioms BarnesWall.BooleanCubic.boolean_cubic_factor_unique_of_nonzero

#check BarnesWall.KRRSupport.H_even_of_same_block
#print axioms BarnesWall.KRRSupport.H_even_of_same_block

#check BarnesWall.KRRSupport.X_supported
#print axioms BarnesWall.KRRSupport.X_supported

#check BarnesWall.KRRSupport.Z_supported
#print axioms BarnesWall.KRRSupport.Z_supported

#check BarnesWall.KRRCanonical.liftMap_mul_of_small_support
#print axioms BarnesWall.KRRCanonical.liftMap_mul_of_small_support

#check BarnesWall.KRRCanonical.lift_mul_of_small_support
#print axioms BarnesWall.KRRCanonical.lift_mul_of_small_support

#check BarnesWall.KRRPauliLift.xLift
#print axioms BarnesWall.KRRPauliLift.xLift

#check BarnesWall.KRRPauliLift.zLift
#print axioms BarnesWall.KRRPauliLift.zLift

#check BarnesWall.KRRPauliLift.xLift_sq
#print axioms BarnesWall.KRRPauliLift.xLift_sq

#check BarnesWall.KRRPauliLift.zLift_sq
#print axioms BarnesWall.KRRPauliLift.zLift_sq

#check BarnesWall.KRRPauliLift.xLift_commute_xLift
#print axioms BarnesWall.KRRPauliLift.xLift_commute_xLift

#check BarnesWall.KRRPauliLift.zLift_commute_zLift
#print axioms BarnesWall.KRRPauliLift.zLift_commute_zLift

#check BarnesWall.KRRPauliLift.xLift_commute_zLift_of_ne
#print axioms BarnesWall.KRRPauliLift.xLift_commute_zLift_of_ne

#check BarnesWall.KRRPauliLift.theta_commute_xLift
#print axioms BarnesWall.KRRPauliLift.theta_commute_xLift

#check BarnesWall.KRRPauliLift.theta_commute_zLift
#print axioms BarnesWall.KRRPauliLift.theta_commute_zLift

#check BarnesWall.KRRPauliLift.xLift_mul_zLift
#print axioms BarnesWall.KRRPauliLift.xLift_mul_zLift

#check BarnesWall.KRRPauliLift.theta_sq
#print axioms BarnesWall.KRRPauliLift.theta_sq

#check BarnesWall.KRRPauliLift.theta_ne_one
#print axioms BarnesWall.KRRPauliLift.theta_ne_one

#check BarnesWall.KRRPauliLift.theta_orderOf
#print axioms BarnesWall.KRRPauliLift.theta_orderOf

#check BarnesWall.KRRPauliLift.aLift_eq_zLift_mul_xLift
#print axioms BarnesWall.KRRPauliLift.aLift_eq_zLift_mul_xLift

#check BarnesWall.KRRPauliLift.bLift_eq_zLift_mul_xLift_mul_zLift
#print axioms BarnesWall.KRRPauliLift.bLift_eq_zLift_mul_xLift_mul_zLift

#check BarnesWall.PauliPresentation.relations
#print axioms BarnesWall.PauliPresentation.relations

#check BarnesWall.PauliPresentation.toGroup
#print axioms BarnesWall.PauliPresentation.toGroup

#check BarnesWall.PauliPresentation.toGroup_central
#print axioms BarnesWall.PauliPresentation.toGroup_central

#check BarnesWall.PauliPresentation.toGroup_x
#print axioms BarnesWall.PauliPresentation.toGroup_x

#check BarnesWall.PauliPresentation.toGroup_z
#print axioms BarnesWall.PauliPresentation.toGroup_z

#check BarnesWall.PauliPresentation.toGroup_unique
#print axioms BarnesWall.PauliPresentation.toGroup_unique

#check BarnesWall.PauliPresentation.exists_normalWord
#print axioms BarnesWall.PauliPresentation.exists_normalWord

#check BarnesWall.PauliPresentation.injective_of_central_ne_one
#print axioms BarnesWall.PauliPresentation.injective_of_central_ne_one

#check BarnesWall.PauliPresentation.toGroup_injective
#print axioms BarnesWall.PauliPresentation.toGroup_injective

#check BarnesWall.KRRPauliMatrix.centralImage_val
#print axioms BarnesWall.KRRPauliMatrix.centralImage_val

#check BarnesWall.KRRPauliMatrix.xImage_val
#print axioms BarnesWall.KRRPauliMatrix.xImage_val

#check BarnesWall.KRRPauliMatrix.zImage_val
#print axioms BarnesWall.KRRPauliMatrix.zImage_val

#check BarnesWall.KRRPauliMatrix.matrixRelations
#print axioms BarnesWall.KRRPauliMatrix.matrixRelations

#check BarnesWall.KRRPauliMatrix.centralImage_ne_one
#print axioms BarnesWall.KRRPauliMatrix.centralImage_ne_one

#check BarnesWall.KRRPauliMatrix.matrixHom
#print axioms BarnesWall.KRRPauliMatrix.matrixHom

#check BarnesWall.KRRPauliMatrix.matrixHom_central
#print axioms BarnesWall.KRRPauliMatrix.matrixHom_central

#check BarnesWall.KRRPauliMatrix.matrixHom_x
#print axioms BarnesWall.KRRPauliMatrix.matrixHom_x

#check BarnesWall.KRRPauliMatrix.matrixHom_z
#print axioms BarnesWall.KRRPauliMatrix.matrixHom_z

#check BarnesWall.KRRPauliMatrix.matrixHom_injective
#print axioms BarnesWall.KRRPauliMatrix.matrixHom_injective

#check BarnesWall.KRRPauliMatrix.matrixHom_aWord
#print axioms BarnesWall.KRRPauliMatrix.matrixHom_aWord

#check BarnesWall.KRRPauliMatrix.matrixHom_bWord
#print axioms BarnesWall.KRRPauliMatrix.matrixHom_bWord

#check BarnesWall.KRRPauliMatrix.generated
#print axioms BarnesWall.KRRPauliMatrix.generated

#check BarnesWall.KRRPauliMatrix.matrixHom_range
#print axioms BarnesWall.KRRPauliMatrix.matrixHom_range

#check BarnesWall.KRRPauliMatrix.matrixEquiv
#print axioms BarnesWall.KRRPauliMatrix.matrixEquiv

#check BarnesWall.KRRPauliMatrix.matrixEquiv_coe
#print axioms BarnesWall.KRRPauliMatrix.matrixEquiv_coe

#check BarnesWall.KRRPauliAction.relations
#print axioms BarnesWall.KRRPauliAction.relations

#check BarnesWall.KRRPauliAction.action
#print axioms BarnesWall.KRRPauliAction.action

#check BarnesWall.KRRPauliAction.action_central
#print axioms BarnesWall.KRRPauliAction.action_central

#check BarnesWall.KRRPauliAction.action_x
#print axioms BarnesWall.KRRPauliAction.action_x

#check BarnesWall.KRRPauliAction.action_z
#print axioms BarnesWall.KRRPauliAction.action_z

#check BarnesWall.KRRPauliAction.action_injective
#print axioms BarnesWall.KRRPauliAction.action_injective

#check BarnesWall.KRRPauliAction.action_a_word
#print axioms BarnesWall.KRRPauliAction.action_a_word

#check BarnesWall.KRRPauliAction.action_b_word
#print axioms BarnesWall.KRRPauliAction.action_b_word

#check BarnesWall.KRRPauliAction.concreteAction
#print axioms BarnesWall.KRRPauliAction.concreteAction

#check BarnesWall.KRRPauliAction.concreteAction_injective
#print axioms BarnesWall.KRRPauliAction.concreteAction_injective

#check BarnesWall.KRRPauliAction.concreteAction_matrixEquiv
#print axioms BarnesWall.KRRPauliAction.concreteAction_matrixEquiv
