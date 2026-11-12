import Erdos335

/-! Exact integrated declaration and axiom audit. -/

#check @Erdos335.count_zero
#print axioms Erdos335.count_zero
#check @Erdos335.count_succ
#print axioms Erdos335.count_succ
#check @Erdos335.tendsto_div_of_bounded
#print axioms Erdos335.tendsto_div_of_bounded
#check @Erdos335.count_le_count_add
#print axioms Erdos335.count_le_count_add
#check @Erdos335.HasDensity.of_eventually_eq
#print axioms Erdos335.HasDensity.of_eventually_eq
#check @Erdos335.nat_count_period
#print axioms Erdos335.nat_count_period
#check @Erdos335.nat_count_periodic
#print axioms Erdos335.nat_count_periodic
#check @Erdos335.count_periodicSet_add
#print axioms Erdos335.count_periodicSet_add
#check @Erdos335.count_periodicSet_div_mod
#print axioms Erdos335.count_periodicSet_div_mod
#check @Erdos335.hasDensity_periodicSet
#print axioms Erdos335.hasDensity_periodicSet
#check @Erdos335.mem_periodicSet_add_iff
#print axioms Erdos335.mem_periodicSet_add_iff
#check @Erdos335.periodicSet_isErdos335Pair
#print axioms Erdos335.periodicSet_isErdos335Pair
#check @Erdos335.mem_residues
#print axioms Erdos335.mem_residues
#check @Erdos335.residues_add
#print axioms Erdos335.residues_add
#check @Erdos335.subset_periodic_residues
#print axioms Erdos335.subset_periodic_residues
#check @Erdos335.escaping_sum_eq
#print axioms Erdos335.escaping_sum_eq
#check @Erdos335.count_mono
#print axioms Erdos335.count_mono
#check @Erdos335.count_le
#print axioms Erdos335.count_le
#check @Erdos335.HasDensity.unique
#print axioms Erdos335.HasDensity.unique
#check @Erdos335.HasDensity.nonneg
#print axioms Erdos335.HasDensity.nonneg
#check @Erdos335.HasDensity.le_one
#print axioms Erdos335.HasDensity.le_one
#check @Erdos335.HasDensity.mono
#print axioms Erdos335.HasDensity.mono
#check @Erdos335.HasDensity.le_residue_cover
#print axioms Erdos335.HasDensity.le_residue_cover
#check @Erdos335.modularCapacity_nonneg
#print axioms Erdos335.modularCapacity_nonneg
#check @Erdos335.density_sum_le_gamma
#print axioms Erdos335.density_sum_le_gamma
#check @Erdos335.no_density_equality_of_gamma_lt
#print axioms Erdos335.no_density_equality_of_gamma_lt
#check @Erdos335.no_density_equality_of_one_lt
#print axioms Erdos335.no_density_equality_of_one_lt
#check @Erdos335.IntervalPacking.overlapping_subset_enlargement
#print axioms Erdos335.IntervalPacking.overlapping_subset_enlargement
#check @Erdos335.IntervalPacking.enlargement_card_le
#print axioms Erdos335.IntervalPacking.enlargement_card_le
#check @Erdos335.IntervalPacking.disjoint_weight_eq_card
#print axioms Erdos335.IntervalPacking.disjoint_weight_eq_card
#check @Erdos335.IntervalPacking.exists_disjoint_cover_bound
#print axioms Erdos335.IntervalPacking.exists_disjoint_cover_bound
#check @Erdos335.IntervalPacking.packingSize_le_card
#print axioms Erdos335.IntervalPacking.packingSize_le_card
#check @Erdos335.IntervalPacking.card_le_three_mul_packingSize
#print axioms Erdos335.IntervalPacking.card_le_three_mul_packingSize
#check @Erdos335.IntervalPacking.mem_sum_interval_iff
#print axioms Erdos335.IntervalPacking.mem_sum_interval_iff
#check @Erdos335.IntervalPacking.packing_vanishes_iff_covered_vanishes
#print axioms Erdos335.IntervalPacking.packing_vanishes_iff_covered_vanishes
#check @Erdos335.FiniteKneser.subset_add_stabilizer_right
#print axioms Erdos335.FiniteKneser.subset_add_stabilizer_right
#check @Erdos335.FiniteKneser.critical_card_identity
#print axioms Erdos335.FiniteKneser.critical_card_identity
#check @Erdos335.FiniteKneser.exact_completion_mem_saturation
#print axioms Erdos335.FiniteKneser.exact_completion_mem_saturation
#check @Erdos335.FiniteKneser.translate_coset_disjoint
#print axioms Erdos335.FiniteKneser.translate_coset_disjoint
#check @Erdos335.FiniteKneser.completion_mem_saturation
#print axioms Erdos335.FiniteKneser.completion_mem_saturation
#check @Erdos335.FiniteKneser.strict_completion
#print axioms Erdos335.FiniteKneser.strict_completion
#check @Erdos335.FiniteKneser.sum_completions_subset
#print axioms Erdos335.FiniteKneser.sum_completions_subset
#check @Erdos335.FiniteKneser.extended_support_sum_subset
#print axioms Erdos335.FiniteKneser.extended_support_sum_subset
#check @Erdos335.FiniteKneser.equality_boundary_counterexample
#print axioms Erdos335.FiniteKneser.equality_boundary_counterexample
#check @Erdos335.FiniteProfiles.periodic_output_forces_full_inputs
#print axioms Erdos335.FiniteProfiles.periodic_output_forces_full_inputs
#check @Erdos335.hasDensity_empty
#print axioms Erdos335.hasDensity_empty
#check @Erdos335.count_union_le
#print axioms Erdos335.count_union_le
#check @Erdos335.count_union_of_disjoint
#print axioms Erdos335.count_union_of_disjoint
#check @Erdos335.count_partition
#print axioms Erdos335.count_partition
#check @Erdos335.count_balance
#print axioms Erdos335.count_balance
#check @Erdos335.Negligible.mono
#print axioms Erdos335.Negligible.mono
#check @Erdos335.Negligible.union
#print axioms Erdos335.Negligible.union
#check @Erdos335.densityEquivalent_iff_symmetric_difference
#print axioms Erdos335.densityEquivalent_iff_symmetric_difference
#check @Erdos335.Negligible.of_bounded
#print axioms Erdos335.Negligible.of_bounded
#check @Erdos335.DensityEquivalent.refl
#print axioms Erdos335.DensityEquivalent.refl
#check @Erdos335.DensityEquivalent.symm
#print axioms Erdos335.DensityEquivalent.symm
#check @Erdos335.DensityEquivalent.trans
#print axioms Erdos335.DensityEquivalent.trans
#check @Erdos335.DensityEquivalent.hasDensity
#print axioms Erdos335.DensityEquivalent.hasDensity
#check @Erdos335.DensityEquivalent.hasDensity_iff
#print axioms Erdos335.DensityEquivalent.hasDensity_iff
#check @Erdos335.count_add_le
#print axioms Erdos335.count_add_le
#check @Erdos335.count_le_count_shift
#print axioms Erdos335.count_le_count_shift
#check @Erdos335.count_shift_le_count_add_one
#print axioms Erdos335.count_shift_le_count_add_one
#check @Erdos335.count_shift_error
#print axioms Erdos335.count_shift_error
#check @Erdos335.HasDensity.shift
#print axioms Erdos335.HasDensity.shift
#check @Erdos335.Negligible.shift
#print axioms Erdos335.Negligible.shift
#check @Erdos335.shift_sdiff
#print axioms Erdos335.shift_sdiff
#check @Erdos335.DensityEquivalent.shift
#print axioms Erdos335.DensityEquivalent.shift
#check @Erdos335.DensityEquivalent.of_eventually_eq
#print axioms Erdos335.DensityEquivalent.of_eventually_eq
#check @Erdos335.negligible_finiteUnion
#print axioms Erdos335.negligible_finiteUnion
#check @Erdos335.periodicSet_mono
#print axioms Erdos335.periodicSet_mono
#check @Erdos335.shift_periodic_equiv
#print axioms Erdos335.shift_periodic_equiv
#check @Erdos335.shift_subset_sum
#print axioms Erdos335.shift_subset_sum
#check @Erdos335.periodic_core_subset_residues
#print axioms Erdos335.periodic_core_subset_residues
#check @Erdos335.HasDensity.sdiff_of_negligible_reverse
#print axioms Erdos335.HasDensity.sdiff_of_negligible_reverse
#check @Erdos335.negligible_periodic_diff_of_singletons
#print axioms Erdos335.negligible_periodic_diff_of_singletons
#check @Erdos335.missing_left_baseline_singleton
#print axioms Erdos335.missing_left_baseline_singleton
#check @Erdos335.periodic_baseline_missing_negligible
#print axioms Erdos335.periodic_baseline_missing_negligible
#check @Erdos335.sumset_positive
#print axioms Erdos335.sumset_positive
#check @Erdos335.periodic_inputs_criterion
#print axioms Erdos335.periodic_inputs_criterion
#check @Erdos335.periodic_inputs_fringe_criterion
#print axioms Erdos335.periodic_inputs_fringe_criterion
#check @Erdos335.periodic_inputs_isErdos335Pair_iff
#print axioms Erdos335.periodic_inputs_isErdos335Pair_iff
#check @Erdos335.hasDensity_shift_iff
#print axioms Erdos335.hasDensity_shift_iff
#check @Erdos335.negligible_shift_iff
#print axioms Erdos335.negligible_shift_iff
#check @Erdos335.gamma_le_modularCapacity
#print axioms Erdos335.gamma_le_modularCapacity
#check @Erdos335.gamma_le_of_residue_sum_subset
#print axioms Erdos335.gamma_le_of_residue_sum_subset
#check @Erdos335.mem_positiveResidues
#print axioms Erdos335.mem_positiveResidues
#check @Erdos335.positiveResidues_subset_residues
#print axioms Erdos335.positiveResidues_subset_residues
#check @Erdos335.outside_positiveResidues_negligible
#print axioms Erdos335.outside_positiveResidues_negligible
#check @Erdos335.positiveResidues_nonempty
#print axioms Erdos335.positiveResidues_nonempty
#check @Erdos335.density_le_positiveResidues_card
#print axioms Erdos335.density_le_positiveResidues_card
#check @Erdos335.shift_fiber_subset_outside
#print axioms Erdos335.shift_fiber_subset_outside
#check @Erdos335.positive_cross_subset
#print axioms Erdos335.positive_cross_subset
#check @Erdos335.periodic_output_forces_periodic_inputs
#print axioms Erdos335.periodic_output_forces_periodic_inputs
#check @Erdos335.periodic_output_reduction
#print axioms Erdos335.periodic_output_reduction
#check @Erdos335.one_periodic_saturated_baseline
#print axioms Erdos335.one_periodic_saturated_baseline
#check @Finset.add_kneser
#print axioms Finset.add_kneser
#check @Finset.add_strict_kneser
#print axioms Finset.add_strict_kneser
#check @Erdos335.Proposed.prefixRun_exists
#print axioms Erdos335.Proposed.prefixRun_exists
#check @Erdos335.Proposed.prefixRun_constant
#print axioms Erdos335.Proposed.prefixRun_constant
#check @Erdos335.Proposed.prefixRun_bounds
#print axioms Erdos335.Proposed.prefixRun_bounds
#check @Erdos335.Proposed.prefixRun_maskA
#print axioms Erdos335.Proposed.prefixRun_maskA
#check @Erdos335.Proposed.prefixRun_maskB
#print axioms Erdos335.Proposed.prefixRun_maskB
#check @Erdos335.Proposed.prefixRun_outputMask
#print axioms Erdos335.Proposed.prefixRun_outputMask
#check @Erdos335.Proposed.mem_mask
#print axioms Erdos335.Proposed.mem_mask
#check @Erdos335.Proposed.block_value_add
#print axioms Erdos335.Proposed.block_value_add
#check @Erdos335.Proposed.mem_clippedInterval_iff
#print axioms Erdos335.Proposed.mem_clippedInterval_iff
#check @Erdos335.Proposed.mem_covered_escapingIntervals_iff
#print axioms Erdos335.Proposed.mem_covered_escapingIntervals_iff
#check @Erdos335.Proposed.covered_escapingIntervals_bounds
#print axioms Erdos335.Proposed.covered_escapingIntervals_bounds
#check @Erdos335.Proposed.covered_escapingIntervals_eq_image
#print axioms Erdos335.Proposed.covered_escapingIntervals_eq_image
#check @Erdos335.Proposed.card_escapingIndices
#print axioms Erdos335.Proposed.card_escapingIndices
#check @Erdos335.Proposed.escapingPackingVanishes_iff
#print axioms Erdos335.Proposed.escapingPackingVanishes_iff
#check @Erdos335.prefixCount_succ
#print axioms Erdos335.prefixCount_succ
#check @Erdos335.prefixCount_succ_eq_count
#print axioms Erdos335.prefixCount_succ_eq_count
#check @Erdos335.prefixCount_balance
#print axioms Erdos335.prefixCount_balance
#check @Erdos335.prefixCount_error
#print axioms Erdos335.prefixCount_error
#check @Erdos335.hasDensity_iff_prefixCount
#print axioms Erdos335.hasDensity_iff_prefixCount
#check @Erdos335.prefixCount_mono
#print axioms Erdos335.prefixCount_mono
#check @Erdos335.prefixCount_add_le
#print axioms Erdos335.prefixCount_add_le
#check @Erdos335.prefixCount_multiple_error
#print axioms Erdos335.prefixCount_multiple_error
#check @Erdos335.hasDensity_iff_prefixCount_multiples
#print axioms Erdos335.hasDensity_iff_prefixCount_multiples
#check @Erdos335.prefixCount_blockSet
#print axioms Erdos335.prefixCount_blockSet
#check @Erdos335.hasDensity_blockSet_iff
#print axioms Erdos335.hasDensity_blockSet_iff
#check @Erdos335.prefixCount_liftBlocks
#print axioms Erdos335.prefixCount_liftBlocks
#check @Erdos335.Negligible.liftBlocks
#print axioms Erdos335.Negligible.liftBlocks
#check @Erdos335.prefixCount_arithmetic_preimage_le
#print axioms Erdos335.prefixCount_arithmetic_preimage_le
#check @Erdos335.Negligible.arithmetic_preimage
#print axioms Erdos335.Negligible.arithmetic_preimage
#check @Erdos335.Negligible.add_preimage
#print axioms Erdos335.Negligible.add_preimage
#check @Erdos335.eq_of_no_transition
#print axioms Erdos335.eq_of_no_transition
#check @Erdos335.Negligible.forward_difference
#print axioms Erdos335.Negligible.forward_difference
#check @Erdos335.Negligible.backward_difference
#print axioms Erdos335.Negligible.backward_difference
#check @Erdos335.Proposed.sparseTransitions_iff
#print axioms Erdos335.Proposed.sparseTransitions_iff
#check @Erdos335.Proposed.SparseTransitions.maskA
#print axioms Erdos335.Proposed.SparseTransitions.maskA
#check @Erdos335.Proposed.SparseTransitions.maskB
#print axioms Erdos335.Proposed.SparseTransitions.maskB
#check @Erdos335.Proposed.mem_shift_iff_mask
#print axioms Erdos335.Proposed.mem_shift_iff_mask
#check @Erdos335.Proposed.block_lag_bound
#print axioms Erdos335.Proposed.block_lag_bound
#check @Erdos335.Proposed.translated_mask_equiv
#print axioms Erdos335.Proposed.translated_mask_equiv
#check @Erdos335.Proposed.missing_left_output_negligible
#print axioms Erdos335.Proposed.missing_left_output_negligible
#check @Erdos335.Proposed.missing_output_negligible
#print axioms Erdos335.Proposed.missing_output_negligible
#check @Erdos335.Proposed.escaping_negligible_of_packing
#print axioms Erdos335.Proposed.escaping_negligible_of_packing
#check @Erdos335.Proposed.escapingPackingVanishes_iff_negligible
#print axioms Erdos335.Proposed.escapingPackingVanishes_iff_negligible
#check @Erdos335.Proposed.maskBranch_hasDensity
#print axioms Erdos335.Proposed.maskBranch_hasDensity
#check @Erdos335.Proposed.isErdos335Pair_of_maskBranch
#print axioms Erdos335.Proposed.isErdos335Pair_of_maskBranch
#check @Erdos335.Proposed.section_eq_zeroSection
#print axioms Erdos335.Proposed.section_eq_zeroSection
#check @Erdos335.Proposed.hasDensity_zeroSection
#print axioms Erdos335.Proposed.hasDensity_zeroSection
#check @Erdos335.Proposed.prefixCount_residueFiber
#print axioms Erdos335.Proposed.prefixCount_residueFiber
#check @Erdos335.Proposed.hasDensity_residueFiber
#print axioms Erdos335.Proposed.hasDensity_residueFiber
#check @Erdos335.Proposed.full_residueFiber
#print axioms Erdos335.Proposed.full_residueFiber
#check @Erdos335.Proposed.hasDensity_union_of_disjoint
#print axioms Erdos335.Proposed.hasDensity_union_of_disjoint
#check @Erdos335.Proposed.positiveRepresentative_pos
#print axioms Erdos335.Proposed.positiveRepresentative_pos
#check @Erdos335.Proposed.positiveRepresentative_cast
#print axioms Erdos335.Proposed.positiveRepresentative_cast
#check @Erdos335.Proposed.sectionPoint_pos
#print axioms Erdos335.Proposed.sectionPoint_pos
#check @Erdos335.Proposed.sectionPoint_cast
#print axioms Erdos335.Proposed.sectionPoint_cast
#check @Erdos335.Proposed.residueFiber_eq_image
#print axioms Erdos335.Proposed.residueFiber_eq_image
#check @Erdos335.Proposed.singleton_residueFiber
#print axioms Erdos335.Proposed.singleton_residueFiber
#check @Erdos335.Proposed.missing_fiber_of_full_section
#print axioms Erdos335.Proposed.missing_fiber_of_full_section
#check @Erdos335.Proposed.hasDensity_from_residue_background
#print axioms Erdos335.Proposed.hasDensity_from_residue_background
#check @Erdos335.Proposed.missing_output_of_full_right
#print axioms Erdos335.Proposed.missing_output_of_full_right
#check @Erdos335.Proposed.FiniteFrame.outputFiber_eq
#print axioms Erdos335.Proposed.FiniteFrame.outputFiber_eq
#check @Erdos335.Proposed.FiniteFrame.output_background
#print axioms Erdos335.Proposed.FiniteFrame.output_background
#check @Erdos335.Proposed.singleton_add_eq_shift
#print axioms Erdos335.Proposed.singleton_add_eq_shift
#check @Erdos335.Proposed.FiniteFrame.hasDensity_of_active_sum
#print axioms Erdos335.Proposed.FiniteFrame.hasDensity_of_active_sum
#check @Erdos335.Proposed.FiniteFrame.singleton_left_hasDensity
#print axioms Erdos335.Proposed.FiniteFrame.singleton_left_hasDensity
#check @Erdos335.Proposed.SingletonBranch.hasDensity
#print axioms Erdos335.Proposed.SingletonBranch.hasDensity
#check @Erdos335.Proposed.isErdos335Pair_of_singletonBranch
#print axioms Erdos335.Proposed.isErdos335Pair_of_singletonBranch
#check @NumStability.integral_finUniformProbability
#print axioms NumStability.integral_finUniformProbability
#check @NumStability.integral_empiricalProbability
#print axioms NumStability.integral_empiricalProbability
#check @NumStability.fourier_nsmul
#print axioms NumStability.fourier_nsmul
#check @NumStability.fourier_ne_one_of_infinite_addOrder
#print axioms NumStability.fourier_ne_one_of_infinite_addOrder
#check @NumStability.integral_fourier
#print axioms NumStability.integral_fourier
#check @NumStability.fourier_geom_sum_norm_bounded
#print axioms NumStability.fourier_geom_sum_norm_bounded
#check @NumStability.tendsto_fourier_average
#print axioms NumStability.tendsto_fourier_average
#check @NumStability.tendsto_integral_empirical_fourier
#print axioms NumStability.tendsto_integral_empirical_fourier
#check @NumStability.norm_integral_sub_le_norm
#print axioms NumStability.norm_integral_sub_le_norm
#check @NumStability.tendsto_integral_empirical_span_fourier
#print axioms NumStability.tendsto_integral_empirical_span_fourier
#check @NumStability.tendsto_integral_empirical_continuous
#print axioms NumStability.tendsto_integral_empirical_continuous
#check @NumStability.empiricalProbability_tendsto_haar
#print axioms NumStability.empiricalProbability_tendsto_haar
#check @NumStability.haar_eq_volume_unit
#print axioms NumStability.haar_eq_volume_unit
#check @NumStability.volume_sphere_eq_zero
#print axioms NumStability.volume_sphere_eq_zero
#check @NumStability.haar_frontier_ball_eq_zero
#print axioms NumStability.haar_frontier_ball_eq_zero
#check @NumStability.haar_ball_eq_of_two_mul_le_one
#print axioms NumStability.haar_ball_eq_of_two_mul_le_one
#check @NumStability.empiricalProbability_ball_tendsto
#print axioms NumStability.empiricalProbability_ball_tendsto
#check @NumStability.empiricalProbability_apply
#print axioms NumStability.empiricalProbability_apply
#check @NumStability.orbit_ball_frequency_tendsto
#print axioms NumStability.orbit_ball_frequency_tendsto
#check @NumStability.mem_centered_ball_coe_iff_exists_int_sub_mem_Ioo
#print axioms NumStability.mem_centered_ball_coe_iff_exists_int_sub_mem_Ioo
#check @NumStability.coe_eq_coe_iff_exists_int_sub_eq
#print axioms NumStability.coe_eq_coe_iff_exists_int_sub_eq
#check @NumStability.mem_halfOpenArc_coe_iff_exists_int_sub_mem_Ico
#print axioms NumStability.mem_halfOpenArc_coe_iff_exists_int_sub_mem_Ico
#check @NumStability.measurableSet_halfOpenArc
#print axioms NumStability.measurableSet_halfOpenArc
#check @NumStability.haar_singleton_eq_zero
#print axioms NumStability.haar_singleton_eq_zero
#check @NumStability.haar_frontier_singleton_eq_zero
#print axioms NumStability.haar_frontier_singleton_eq_zero
#check @NumStability.haar_frontier_halfOpenArc_eq_zero
#print axioms NumStability.haar_frontier_halfOpenArc_eq_zero
#check @NumStability.haar_halfOpenArc_eq_of_two_mul_le_one
#print axioms NumStability.haar_halfOpenArc_eq_of_two_mul_le_one
#check @NumStability.empiricalProbability_halfOpenArc_tendsto
#print axioms NumStability.empiricalProbability_halfOpenArc_tendsto
#check @NumStability.orbit_halfOpenArc_frequency_tendsto
#print axioms NumStability.orbit_halfOpenArc_frequency_tendsto
#check @Erdos335.Proposed.irrational_addOrder
#print axioms Erdos335.Proposed.irrational_addOrder
#check @Erdos335.Proposed.fin_count_eq_prefixCount
#print axioms Erdos335.Proposed.fin_count_eq_prefixCount
#check @Erdos335.Proposed.halfOpenOrbit_hasDensity
#print axioms Erdos335.Proposed.halfOpenOrbit_hasDensity
#check @Erdos335.Proposed.negligible_of_subsingleton
#print axioms Erdos335.Proposed.negligible_of_subsingleton
#check @Erdos335.Proposed.irrational_orbitPoint_negligible
#print axioms Erdos335.Proposed.irrational_orbitPoint_negligible
#check @Erdos335.Proposed.nsmul_coe_real
#print axioms Erdos335.Proposed.nsmul_coe_real
#check @Erdos335.Proposed.closedArcPullback_hasDensity
#print axioms Erdos335.Proposed.closedArcPullback_hasDensity
#check @Erdos335.Proposed.filled_closedArc_hasDensity
#print axioms Erdos335.Proposed.filled_closedArc_hasDensity
#check @Erdos335.Proposed.sum_closedArc_subset
#print axioms Erdos335.Proposed.sum_closedArc_subset
#check @Erdos335.Proposed.closedArc_sum_upper_bound
#print axioms Erdos335.Proposed.closedArc_sum_upper_bound
#check @Erdos335.Proposed.exists_good_complement
#print axioms Erdos335.Proposed.exists_good_complement
#check @Erdos335.Proposed.exists_stable_overlap_interval
#print axioms Erdos335.Proposed.exists_stable_overlap_interval
#check @Erdos335.Proposed.finite_overlap_cover
#print axioms Erdos335.Proposed.finite_overlap_cover
#check @Erdos335.Proposed.eventual_inner_arc_subset_sum
#print axioms Erdos335.Proposed.eventual_inner_arc_subset_sum
#check @Erdos335.Proposed.filled_closedArcs_sum_hasDensity
#print axioms Erdos335.Proposed.filled_closedArcs_sum_hasDensity
#check @Erdos335.Proposed.dilate_positive
#print axioms Erdos335.Proposed.dilate_positive
#check @Erdos335.Proposed.zeroSection_dilate
#print axioms Erdos335.Proposed.zeroSection_dilate
#check @Erdos335.Proposed.residueFiber_dilate
#print axioms Erdos335.Proposed.residueFiber_dilate
#check @Erdos335.Proposed.hasDensity_dilate
#print axioms Erdos335.Proposed.hasDensity_dilate
#check @Erdos335.Proposed.shift_add
#print axioms Erdos335.Proposed.shift_add
#check @Erdos335.Proposed.dilate_add
#print axioms Erdos335.Proposed.dilate_add
#check @Erdos335.Proposed.sectionPoint_add_modulus
#print axioms Erdos335.Proposed.sectionPoint_add_modulus
#check @Erdos335.Proposed.shift_fiber_eq_dilate
#print axioms Erdos335.Proposed.shift_fiber_eq_dilate
#check @Erdos335.Proposed.fiber_sum_hasDensity
#print axioms Erdos335.Proposed.fiber_sum_hasDensity
#check @Erdos335.Proposed.BohrBranch.hasDensity
#print axioms Erdos335.Proposed.BohrBranch.hasDensity
#check @Erdos335.Proposed.isErdos335Pair_of_bohrBranch
#print axioms Erdos335.Proposed.isErdos335Pair_of_bohrBranch
#check @Erdos335.count_ratio_nonneg
#print axioms Erdos335.count_ratio_nonneg
#check @Erdos335.count_ratio_le_one
#print axioms Erdos335.count_ratio_le_one
#check @Erdos335.count_ratio_bounded_below
#print axioms Erdos335.count_ratio_bounded_below
#check @Erdos335.count_ratio_bounded_above
#print axioms Erdos335.count_ratio_bounded_above
#check @Erdos335.lowerDensity_nonneg
#print axioms Erdos335.lowerDensity_nonneg
#check @Erdos335.upperDensity_le_one
#print axioms Erdos335.upperDensity_le_one
#check @Erdos335.lowerDensity_le_upperDensity
#print axioms Erdos335.lowerDensity_le_upperDensity
#check @Erdos335.lowerDensity_mono
#print axioms Erdos335.lowerDensity_mono
#check @Erdos335.upperDensity_mono
#print axioms Erdos335.upperDensity_mono
#check @Erdos335.HasDensity.lowerDensity_eq
#print axioms Erdos335.HasDensity.lowerDensity_eq
#check @Erdos335.HasDensity.upperDensity_eq
#print axioms Erdos335.HasDensity.upperDensity_eq
#check @Erdos335.hasDensity_of_lowerDensity_ge_upperDensity_le
#print axioms Erdos335.hasDensity_of_lowerDensity_ge_upperDensity_le
#check @Erdos335.hasDensity_iff_lowerDensity_eq_upperDensity_eq
#print axioms Erdos335.hasDensity_iff_lowerDensity_eq_upperDensity_eq
#check @Erdos335.upperDensity_sum_le_gamma
#print axioms Erdos335.upperDensity_sum_le_gamma
#check @Erdos335.density_sum_of_lowerDensity_ge_gamma
#print axioms Erdos335.density_sum_of_lowerDensity_ge_gamma
#check @Erdos335.ultimately_periodic_of_bounded_tails
#print axioms Erdos335.ultimately_periodic_of_bounded_tails
#check @Erdos335.density_of_bounded_tails
#print axioms Erdos335.density_of_bounded_tails
#check @Erdos335.density_sum_of_bounded_tails
#print axioms Erdos335.density_sum_of_bounded_tails
#check @Erdos335.progression_tail_of_literal_periodicity
#print axioms Erdos335.progression_tail_of_literal_periodicity
#check @Erdos335.ultimately_periodic_of_periodic_subsets
#print axioms Erdos335.ultimately_periodic_of_periodic_subsets
#check @Erdos335.density_sum_of_kneser_alternative
#print axioms Erdos335.density_sum_of_kneser_alternative
#check @Erdos335.subset_dysonLeft
#print axioms Erdos335.subset_dysonLeft
#check @Erdos335.dysonRight_subset
#print axioms Erdos335.dysonRight_subset
#check @Erdos335.dyson_shift_subset
#print axioms Erdos335.dyson_shift_subset
#check @Erdos335.dyson_shift_eq_inter
#print axioms Erdos335.dyson_shift_eq_inter
#check @Erdos335.dyson_sum_subset
#print axioms Erdos335.dyson_sum_subset
#check @Erdos335.zero_mem_dysonLeft
#print axioms Erdos335.zero_mem_dysonLeft
#check @Erdos335.zero_mem_dysonRight
#print axioms Erdos335.zero_mem_dysonRight
#check @Erdos335.prefixCount_union_add_inter
#print axioms Erdos335.prefixCount_union_add_inter
#check @Erdos335.prefixCount_shift
#print axioms Erdos335.prefixCount_shift
#check @Erdos335.dyson_prefix_invariant
#print axioms Erdos335.dyson_prefix_invariant
#check @Erdos335.dyson_prefix_error
#print axioms Erdos335.dyson_prefix_error
#check @Erdos335.dyson_count_error
#print axioms Erdos335.dyson_count_error
#check @Erdos335.dyson_count_difference_tendsto
#print axioms Erdos335.dyson_count_difference_tendsto
#check @Erdos335.DysonDerived.left_subset
#print axioms Erdos335.DysonDerived.left_subset
#check @Erdos335.DysonDerived.right_subset
#print axioms Erdos335.DysonDerived.right_subset
#check @Erdos335.DysonDerived.sum_subset
#print axioms Erdos335.DysonDerived.sum_subset
#check @Erdos335.DysonDerived.zero_mem
#print axioms Erdos335.DysonDerived.zero_mem
#check @Erdos335.DysonDerived.count_difference_tendsto
#print axioms Erdos335.DysonDerived.count_difference_tendsto
#check @Erdos335.exists_dysonDerived_cover_finite
#print axioms Erdos335.exists_dysonDerived_cover_finite
#check @Erdos335.jointCount_bounded_below
#print axioms Erdos335.jointCount_bounded_below
#check @Erdos335.jointCount_bounded_above
#print axioms Erdos335.jointCount_bounded_above
#check @Erdos335.jointLowerDensity_eq_of_hasDensity
#print axioms Erdos335.jointLowerDensity_eq_of_hasDensity
#check @Erdos335.liminf_add_of_tendsto_zero
#print axioms Erdos335.liminf_add_of_tendsto_zero
#check @Erdos335.DysonDerived.jointLowerDensity_eq
#print axioms Erdos335.DysonDerived.jointLowerDensity_eq
#check @Erdos335.jointLowerDensity_le_upperDensity_add_lowerDensity
#print axioms Erdos335.jointLowerDensity_le_upperDensity_add_lowerDensity
#check @Erdos335.count_le_div_add_one_of_separated
#print axioms Erdos335.count_le_div_add_one_of_separated
#check @Erdos335.upperDensity_le_inv_of_separated
#print axioms Erdos335.upperDensity_le_inv_of_separated
#check @Erdos335.DysonDerived.lowerDensity_sum_ge_of_separated
#print axioms Erdos335.DysonDerived.lowerDensity_sum_ge_of_separated
#check @Erdos335.lowerDensity_sum_ge_of_unbounded_dyson_gaps
#print axioms Erdos335.lowerDensity_sum_ge_of_unbounded_dyson_gaps
#check @LeanLab.Ramare1995.Theorem91.cnt_zero
#print axioms LeanLab.Ramare1995.Theorem91.cnt_zero
#check @LeanLab.Ramare1995.Theorem91.cnt_split
#print axioms LeanLab.Ramare1995.Theorem91.cnt_split
#check @LeanLab.Ramare1995.Theorem91.cnt_mono_set
#print axioms LeanLab.Ramare1995.Theorem91.cnt_mono_set
#check @LeanLab.Ramare1995.Theorem91.cnt_mono
#print axioms LeanLab.Ramare1995.Theorem91.cnt_mono
#check @LeanLab.Ramare1995.Theorem91.cnt_le
#print axioms LeanLab.Ramare1995.Theorem91.cnt_le
#check @LeanLab.Ramare1995.Theorem91.cnt_eq_zero
#print axioms LeanLab.Ramare1995.Theorem91.cnt_eq_zero
#check @LeanLab.Ramare1995.Theorem91.cnt_pos
#print axioms LeanLab.Ramare1995.Theorem91.cnt_pos
#check @LeanLab.Ramare1995.Theorem91.cnt_diff
#print axioms LeanLab.Ramare1995.Theorem91.cnt_diff
#check @LeanLab.Ramare1995.Theorem91.cnt_sub_le
#print axioms LeanLab.Ramare1995.Theorem91.cnt_sub_le
#check @LeanLab.Ramare1995.Theorem91.cnt_last
#print axioms LeanLab.Ramare1995.Theorem91.cnt_last
#check @LeanLab.Ramare1995.Theorem91.sum_two
#print axioms LeanLab.Ramare1995.Theorem91.sum_two
#check @LeanLab.Ramare1995.Theorem91.sum_one
#print axioms LeanLab.Ramare1995.Theorem91.sum_one
#check @LeanLab.Ramare1995.Theorem91.tr_last
#print axioms LeanLab.Ramare1995.Theorem91.tr_last
#check @LeanLab.Ramare1995.Theorem91.tr_l
#print axioms LeanLab.Ramare1995.Theorem91.tr_l
#check @LeanLab.Ramare1995.Theorem91.tr_ne
#print axioms LeanLab.Ramare1995.Theorem91.tr_ne
#check @LeanLab.Ramare1995.Theorem91.rep_back
#print axioms LeanLab.Ramare1995.Theorem91.rep_back
#check @LeanLab.Ramare1995.Theorem91.cnt_union_shift
#print axioms LeanLab.Ramare1995.Theorem91.cnt_union_shift
#check @LeanLab.Ramare1995.Theorem91.cnt_shift_lower
#print axioms LeanLab.Ramare1995.Theorem91.cnt_shift_lower
#check @LeanLab.Schnirelmann.Mann.cnt_mono_le
#print axioms LeanLab.Schnirelmann.Mann.cnt_mono_le
#check @LeanLab.Schnirelmann.Mann.rep_succ
#print axioms LeanLab.Schnirelmann.Mann.rep_succ
#check @LeanLab.Schnirelmann.Mann.hyp_trR
#print axioms LeanLab.Schnirelmann.Mann.hyp_trR
#check @LeanLab.Schnirelmann.Mann.dysonR
#print axioms LeanLab.Schnirelmann.Mann.dysonR
#check @LeanLab.Schnirelmann.Mann.card_ioc_eq_cnt
#print axioms LeanLab.Schnirelmann.Mann.card_ioc_eq_cnt
#check @LeanLab.Schnirelmann.Mann.density_mul_le_cnt
#print axioms LeanLab.Schnirelmann.Mann.density_mul_le_cnt
#check @LeanLab.Schnirelmann.Mann.le_density_of
#print axioms LeanLab.Schnirelmann.Mann.le_density_of
#check @LeanLab.Schnirelmann.Mann.mann_sum
#print axioms LeanLab.Schnirelmann.Mann.mann_sum
#check @LeanLab.Schnirelmann.Mann.mann
#print axioms LeanLab.Schnirelmann.Mann.mann
#check @Erdos335.dyson_prefix_lower_bound
#print axioms Erdos335.dyson_prefix_lower_bound
#check @Erdos335.lowerDensity_sum_ge_of_joint_prefix
#print axioms Erdos335.lowerDensity_sum_ge_of_joint_prefix
#check @Erdos335.lowerDensity_sum_ge_mann
#print axioms Erdos335.lowerDensity_sum_ge_mann
#check @Erdos335.hasDensity_sum_one_of_joint_prefix
#print axioms Erdos335.hasDensity_sum_one_of_joint_prefix
#check @Erdos335.DysonDerived.trans
#print axioms Erdos335.DysonDerived.trans
#check @Erdos335.exists_bound_on_dyson_gaps
#print axioms Erdos335.exists_bound_on_dyson_gaps
#check @Erdos335.setGcd_bounds_of_close_pair
#print axioms Erdos335.setGcd_bounds_of_close_pair
#check @Erdos335.exists_dysonDerived_stable_gcd
#print axioms Erdos335.exists_dysonDerived_stable_gcd
#check @Erdos335.exists_minimum_gap
#print axioms Erdos335.exists_minimum_gap
#check @Erdos335.Separated.mono_set
#print axioms Erdos335.Separated.mono_set
#check @Erdos335.exists_dysonDerived_stable_gap
#print axioms Erdos335.exists_dysonDerived_stable_gap
#check @Erdos335.exists_dysonDerived_stable_residues
#print axioms Erdos335.exists_dysonDerived_stable_residues
#check @Erdos335.prefixCount_mono_set
#print axioms Erdos335.prefixCount_mono_set
#check @Erdos335.count_mono_cutoff
#print axioms Erdos335.count_mono_cutoff
#check @Erdos335.dysonLeft_mem_iff_of_le
#print axioms Erdos335.dysonLeft_mem_iff_of_le
#check @Erdos335.dyson_count0_invariant
#print axioms Erdos335.dyson_count0_invariant
#check @Erdos335.prefixCount_translated_block_le
#print axioms Erdos335.prefixCount_translated_block_le
#check @Erdos335.strengthen_shifted_prefix_bound
#print axioms Erdos335.strengthen_shifted_prefix_bound
#check @Erdos335.exists_dysonDerived_shifted_prefix_bound
#print axioms Erdos335.exists_dysonDerived_shifted_prefix_bound
#check @Erdos335.zero_based_dyson_counting
#print axioms Erdos335.zero_based_dyson_counting
#check @Erdos335.exists_dysonDerived_translate_of_residue_word
#print axioms Erdos335.exists_dysonDerived_translate_of_residue_word
#check @Erdos335.residue_word_of_mem_closure
#print axioms Erdos335.residue_word_of_mem_closure
#check @Erdos335.exists_residue_word_setGcd
#print axioms Erdos335.exists_residue_word_setGcd
#check @Erdos335.exists_dysonDerived_two_translates
#print axioms Erdos335.exists_dysonDerived_two_translates
#check @Erdos335.exists_dysonDerived_progressions
#print axioms Erdos335.exists_dysonDerived_progressions
#check @Erdos335.exists_dysonDerived_long_progressions
#print axioms Erdos335.exists_dysonDerived_long_progressions
#check @Erdos335.prefixCount_le
#print axioms Erdos335.prefixCount_le
#check @Erdos335.prefixCount_add_tailShift
#print axioms Erdos335.prefixCount_add_tailShift
#check @Erdos335.count_tailShift_error
#print axioms Erdos335.count_tailShift_error
#check @Erdos335.count_difference_tendsto_zero_of_bounded
#print axioms Erdos335.count_difference_tendsto_zero_of_bounded
#check @Erdos335.lowerDensity_eq_of_bounded_count_error
#print axioms Erdos335.lowerDensity_eq_of_bounded_count_error
#check @Erdos335.HasDensity.of_bounded_count_error
#print axioms Erdos335.HasDensity.of_bounded_count_error
#check @Erdos335.lowerDensity_shift
#print axioms Erdos335.lowerDensity_shift
#check @Erdos335.lowerDensity_tailShift
#print axioms Erdos335.lowerDensity_tailShift
#check @Erdos335.HasDensity.tailShift
#print axioms Erdos335.HasDensity.tailShift
#check @Erdos335.jointLowerDensity_tailShift
#print axioms Erdos335.jointLowerDensity_tailShift
#check @Erdos335.shift_tailShift
#print axioms Erdos335.shift_tailShift
#check @Erdos335.shift_tailShift_sum_subset
#print axioms Erdos335.shift_tailShift_sum_subset
#check @Erdos335.lowerDensity_ge_of_prefixCount
#print axioms Erdos335.lowerDensity_ge_of_prefixCount
#check @Erdos335.eq_univ_of_full_prefixCount
#print axioms Erdos335.eq_univ_of_full_prefixCount
#check @Erdos335.lowerDensity_sum_ge_joint_of_finite_right
#print axioms Erdos335.lowerDensity_sum_ge_joint_of_finite_right
#check @Erdos335.infinite_right_of_lowerDensity_sum_lt
#print axioms Erdos335.infinite_right_of_lowerDensity_sum_lt
#check @Erdos335.prefixCount_tailShift_eq_window
#print axioms Erdos335.prefixCount_tailShift_eq_window
#check @Erdos335.joint_window_lower_bound
#print axioms Erdos335.joint_window_lower_bound
#check @Erdos335.exists_joint_window_start
#print axioms Erdos335.exists_joint_window_start
#check @Erdos335.joint_window_start_mem_left
#print axioms Erdos335.joint_window_start_mem_left
#check @Erdos335.prefixCount_tailShift_eq_zero_before
#print axioms Erdos335.prefixCount_tailShift_eq_zero_before
#check @Erdos335.prefixCount_tailShift_mono_first
#print axioms Erdos335.prefixCount_tailShift_mono_first
#check @Erdos335.prefixCount_tailShift_le_count_first
#print axioms Erdos335.prefixCount_tailShift_le_count_first
#check @Erdos335.window_count_after_first_lower_bound
#print axioms Erdos335.window_count_after_first_lower_bound
#check @Erdos335.prefixCount_full_block
#print axioms Erdos335.prefixCount_full_block
#check @Erdos335.prefixCount_full_block_lower
#print axioms Erdos335.prefixCount_full_block_lower
#check @Erdos335.weighted_count_bound
#print axioms Erdos335.weighted_count_bound
#check @Erdos335.initial_segment_count_bound
#print axioms Erdos335.initial_segment_count_bound
#check @Erdos335.after_first_window_count_bound
#print axioms Erdos335.after_first_window_count_bound
#check @Erdos335.normalized_sum_prefix_bounds
#print axioms Erdos335.normalized_sum_prefix_bounds
#check @Erdos335.lowerDensity_sum_ge_of_block_cover
#print axioms Erdos335.lowerDensity_sum_ge_of_block_cover
#check @Erdos335.cofinite_sum_of_block_cover
#print axioms Erdos335.cofinite_sum_of_block_cover
#check @Erdos335.lowerDensity_sum_ge_of_initial_interval
#print axioms Erdos335.lowerDensity_sum_ge_of_initial_interval
#check @Erdos335.cofinite_sum_of_initial_interval
#print axioms Erdos335.cofinite_sum_of_initial_interval
#check @Erdos335.lowerDensity_sum_ge_of_interval
#print axioms Erdos335.lowerDensity_sum_ge_of_interval
#check @Erdos335.cofinite_sum_of_interval
#print axioms Erdos335.cofinite_sum_of_interval
#check @Erdos335.lowerDensity_sum_ge_min_of_long_derived_intervals
#print axioms Erdos335.lowerDensity_sum_ge_min_of_long_derived_intervals
#check @Erdos335.cofinite_sum_of_long_derived_intervals
#print axioms Erdos335.cofinite_sum_of_long_derived_intervals
#check @Erdos335.stable_gcd_one_alternative
#print axioms Erdos335.stable_gcd_one_alternative
#check @Erdos335.cofinite_sum_of_stable_gcd_one
#print axioms Erdos335.cofinite_sum_of_stable_gcd_one
#check @Erdos335.count_ratio_rounding_error
#print axioms Erdos335.count_ratio_rounding_error
#check @Erdos335.count_ratio_rounding_tendsto_zero
#print axioms Erdos335.count_ratio_rounding_tendsto_zero
#check @Erdos335.liminf_eq_liminf_multiples_of_rounding
#print axioms Erdos335.liminf_eq_liminf_multiples_of_rounding
#check @Erdos335.lowerDensity_eq_liminf_multiples
#print axioms Erdos335.lowerDensity_eq_liminf_multiples
#check @Erdos335.jointLowerDensity_eq_liminf_multiples
#print axioms Erdos335.jointLowerDensity_eq_liminf_multiples
#check @Erdos335.prefix_count_difference_tendsto
#print axioms Erdos335.prefix_count_difference_tendsto
#check @Erdos335.tendsto_mul_nat_atTop
#print axioms Erdos335.tendsto_mul_nat_atTop
#check @Erdos335.lowerDensity_eq_liminf_prefix_multiples
#print axioms Erdos335.lowerDensity_eq_liminf_prefix_multiples
#check @Erdos335.jointLowerDensity_eq_liminf_prefix_multiples
#print axioms Erdos335.jointLowerDensity_eq_liminf_prefix_multiples
#check @Erdos335.liminf_const_mul_of_nonneg
#print axioms Erdos335.liminf_const_mul_of_nonneg
#check @Erdos335.lowerDensity_scale_of_prefix_identity
#print axioms Erdos335.lowerDensity_scale_of_prefix_identity
#check @Erdos335.jointLowerDensity_scale_of_prefix_identities
#print axioms Erdos335.jointLowerDensity_scale_of_prefix_identities
#check @Erdos335.packedCode_div
#print axioms Erdos335.packedCode_div
#check @Erdos335.packedCode_mod
#print axioms Erdos335.packedCode_mod
#check @Erdos335.packedCode_lt_block
#print axioms Erdos335.packedCode_lt_block
#check @Erdos335.packedCode_injOn
#print axioms Erdos335.packedCode_injOn
#check @Erdos335.prefixCount_packedSet
#print axioms Erdos335.prefixCount_packedSet
#check @Erdos335.lowerDensity_packedSet
#print axioms Erdos335.lowerDensity_packedSet
#check @Erdos335.packedCode_add_of_dvd
#print axioms Erdos335.packedCode_add_of_dvd
#check @Erdos335.packedSet_add
#print axioms Erdos335.packedSet_add
#check @Erdos335.prefixCount_packed_multiples
#print axioms Erdos335.prefixCount_packed_multiples
#check @Erdos335.jointLowerDensity_packed
#print axioms Erdos335.jointLowerDensity_packed
#check @Erdos335.lowerDensity_packed_sum
#print axioms Erdos335.lowerDensity_packed_sum
#check @Erdos335.zero_mem_packed_multiples
#print axioms Erdos335.zero_mem_packed_multiples
#check @Erdos335.exists_residue_label
#print axioms Erdos335.exists_residue_label
#check @Erdos335.packedSet_mem_iff
#print axioms Erdos335.packedSet_mem_iff
#check @Erdos335.cofinite_packed_sum_reflect
#print axioms Erdos335.cofinite_packed_sum_reflect
#check @Erdos335.DysonDerived.residues_left_of_dvd
#print axioms Erdos335.DysonDerived.residues_left_of_dvd
#check @Erdos335.exists_finite_residue_representatives
#print axioms Erdos335.exists_finite_residue_representatives
#check @Erdos335.packed_interval_of_progressions
#print axioms Erdos335.packed_interval_of_progressions
#check @Erdos335.exists_dysonDerived_packed_intervals
#print axioms Erdos335.exists_dysonDerived_packed_intervals
#check @Erdos335.exists_periodic_derived_sum
#print axioms Erdos335.exists_periodic_derived_sum
#check @Erdos335.stable_periodic_subset_through_zero
#print axioms Erdos335.stable_periodic_subset_through_zero
#check @Erdos335.periodic_subset_through_zero
#print axioms Erdos335.periodic_subset_through_zero
#check @Erdos335.kneser_progression_tail_through_point
#print axioms Erdos335.kneser_progression_tail_through_point
#check @Erdos335.integer_kneser_alternative
#print axioms Erdos335.integer_kneser_alternative
#check @Erdos335.density_integer_kneser_alternative
#print axioms Erdos335.density_integer_kneser_alternative
#check @Erdos335.hasDensity_sum_of_gamma_eq
#print axioms Erdos335.hasDensity_sum_of_gamma_eq
#check @Erdos335.Proposed.Classified.hasDensity
#print axioms Erdos335.Proposed.Classified.hasDensity
#check @Erdos335.Proposed.isErdos335Pair_of_classified
#print axioms Erdos335.Proposed.isErdos335Pair_of_classified
#check @Erdos335.FiniteKneser.neg_mem_addStab
#print axioms Erdos335.FiniteKneser.neg_mem_addStab
#check @Erdos335.FiniteKneser.deficit_le_representation_count
#print axioms Erdos335.FiniteKneser.deficit_le_representation_count
#check @Erdos335.FiniteKneser.card_sum_ge_of_unique_expression
#print axioms Erdos335.FiniteKneser.card_sum_ge_of_unique_expression
#check @Erdos335.FiniteKneser.card_of_unique_extra_sum
#print axioms Erdos335.FiniteKneser.card_of_unique_extra_sum
#check @Erdos335.Proposed.blockSet_mask_eq
#print axioms Erdos335.Proposed.blockSet_mask_eq
#check @Erdos335.Proposed.shift_equivalent_of_sparse_mask
#print axioms Erdos335.Proposed.shift_equivalent_of_sparse_mask
#check @Erdos335.Proposed.sparse_mask_of_shift_equivalent
#print axioms Erdos335.Proposed.sparse_mask_of_shift_equivalent
#check @Erdos335.Proposed.sparseTransitions_iff_shift_equivalent
#print axioms Erdos335.Proposed.sparseTransitions_iff_shift_equivalent
#check @Erdos335.DensityEquivalent.union
#print axioms Erdos335.DensityEquivalent.union
#check @Erdos335.Proposed.finite_shifts_outside_left_mask_negligible
#print axioms Erdos335.Proposed.finite_shifts_outside_left_mask_negligible
#check @Erdos335.Proposed.left_mask_missing_finite_shifts_negligible
#print axioms Erdos335.Proposed.left_mask_missing_finite_shifts_negligible
#check @Erdos335.Proposed.finite_shifts_equiv_left_mask
#print axioms Erdos335.Proposed.finite_shifts_equiv_left_mask
#check @Erdos335.Proposed.output_mask_decomposition
#print axioms Erdos335.Proposed.output_mask_decomposition
#check @Erdos335.Proposed.finite_translate_cover_equiv_output_mask
#print axioms Erdos335.Proposed.finite_translate_cover_equiv_output_mask
#check @Erdos335.Proposed.finite_translate_cover_outside_output_negligible
#print axioms Erdos335.Proposed.finite_translate_cover_outside_output_negligible
#check @Erdos335.Proposed.maskBranch_of_finite_translate_cover
#print axioms Erdos335.Proposed.maskBranch_of_finite_translate_cover
#check @Erdos335.Proposed.MaskBranch.finite_translate_cover
#print axioms Erdos335.Proposed.MaskBranch.finite_translate_cover
#check @Erdos335.Proposed.maskBranch_iff_sparse_density_finite_translate_cover
#print axioms Erdos335.Proposed.maskBranch_iff_sparse_density_finite_translate_cover
#check @Erdos335.Proposed.maskBranch_iff_common_period_finite_translate_cover
#print axioms Erdos335.Proposed.maskBranch_iff_common_period_finite_translate_cover
#check @Erdos335.count_error_le_prefixError
#print axioms Erdos335.count_error_le_prefixError
#check @Erdos335.prefixError_nonneg
#print axioms Erdos335.prefixError_nonneg
#check @Erdos335.HasDensity.uniform_linear_error
#print axioms Erdos335.HasDensity.uniform_linear_error
#check @Erdos335.prefixError_le_of_linear_error
#print axioms Erdos335.prefixError_le_of_linear_error
#check @Erdos335.HasDensity.prefixError_tendsto_zero
#print axioms Erdos335.HasDensity.prefixError_tendsto_zero
#check @Erdos335.window_error_le_prefixError
#print axioms Erdos335.window_error_le_prefixError
#check @Erdos335.exists_intermediate_scale
#print axioms Erdos335.exists_intermediate_scale
#check @Erdos335.HasDensity.prefixError_mul_tendsto_zero
#print axioms Erdos335.HasDensity.prefixError_mul_tendsto_zero
#check @Erdos335.exists_common_error_dominating_scale
#print axioms Erdos335.exists_common_error_dominating_scale
#check @Erdos335.prefixCount_positive_window
#print axioms Erdos335.prefixCount_positive_window
#check @Erdos335.positive_window_error_le
#print axioms Erdos335.positive_window_error_le
#check @Erdos335.moving_window_density_of_prefix_error
#print axioms Erdos335.moving_window_density_of_prefix_error
#check @Erdos335.prefix_error_control_of_scale_domination
#print axioms Erdos335.prefix_error_control_of_scale_domination
#check @Erdos335.exists_natural_cyclic_quotient
#print axioms Erdos335.exists_natural_cyclic_quotient
#check @Erdos335.residues_image_of_natCast
#print axioms Erdos335.residues_image_of_natCast
#check @Erdos335.card_image_eq_card_image_quotient
#print axioms Erdos335.card_image_eq_card_image_quotient
#check @Erdos335.card_stabilizer_quotient
#print axioms Erdos335.card_stabilizer_quotient
#check @Erdos335.critical_quotient_card_identity
#print axioms Erdos335.critical_quotient_card_identity
#check @Erdos335.stabilizer_image_quotient_eq_zero
#print axioms Erdos335.stabilizer_image_quotient_eq_zero
#check @Erdos335.natCard_stabilizer_eq_card
#print axioms Erdos335.natCard_stabilizer_eq_card
#check @Erdos335.card_deficit_le_stabilizer
#print axioms Erdos335.card_deficit_le_stabilizer
#check @Erdos335.exists_bounded_critical_cyclic_quotient
#print axioms Erdos335.exists_bounded_critical_cyclic_quotient
#check @Erdos335.FiniteProfiles.coordinate_ge_sum_sub_card
#print axioms Erdos335.FiniteProfiles.coordinate_ge_sum_sub_card
#check @Erdos335.FiniteProfiles.extra_residue_forces_full_profile
#print axioms Erdos335.FiniteProfiles.extra_residue_forces_full_profile
#check @Erdos335.FiniteProfiles.extra_output_is_singleton
#print axioms Erdos335.FiniteProfiles.extra_output_is_singleton
#check @Erdos335.FiniteProfiles.local_deficit_template
#print axioms Erdos335.FiniteProfiles.local_deficit_template
#check @Erdos335.Loeb.mem_internalSet_iff
#print axioms Erdos335.Loeb.mem_internalSet_iff
#check @Erdos335.Loeb.internalSet_empty
#print axioms Erdos335.Loeb.internalSet_empty
#check @Erdos335.Loeb.internalSet_univ
#print axioms Erdos335.Loeb.internalSet_univ
#check @Erdos335.Loeb.internalSet_inter
#print axioms Erdos335.Loeb.internalSet_inter
#check @Erdos335.Loeb.internalSet_union
#print axioms Erdos335.Loeb.internalSet_union
#check @Erdos335.Loeb.internalSet_compl
#print axioms Erdos335.Loeb.internalSet_compl
#check @Erdos335.Loeb.internalSet_sdiff
#print axioms Erdos335.Loeb.internalSet_sdiff
#check @Erdos335.Loeb.internalSet_biInter_finset
#print axioms Erdos335.Loeb.internalSet_biInter_finset
#check @Erdos335.Loeb.isSetAlgebra_internalSets
#print axioms Erdos335.Loeb.isSetAlgebra_internalSets
#check @Erdos335.Loeb.internalSet_nonempty_iff
#print axioms Erdos335.Loeb.internalSet_nonempty_iff
#check @Erdos335.Loeb.internalSet_subset_iff
#print axioms Erdos335.Loeb.internalSet_subset_iff
#check @Erdos335.Loeb.internalSet_eq_iff
#print axioms Erdos335.Loeb.internalSet_eq_iff
#check @Erdos335.Loeb.exists_representative_of_eventually_finite
#print axioms Erdos335.Loeb.exists_representative_of_eventually_finite
#check @Erdos335.Loeb.countable_saturation
#print axioms Erdos335.Loeb.countable_saturation
#check @Erdos335.Loeb.countable_saturation_internal
#print axioms Erdos335.Loeb.countable_saturation_internal
#check @Erdos335.Loeb.internal_countable_cover_has_finite
#print axioms Erdos335.Loeb.internal_countable_cover_has_finite
#check @Erdos335.Loeb.countingRatio_empty
#print axioms Erdos335.Loeb.countingRatio_empty
#check @Erdos335.Loeb.countingRatio_univ
#print axioms Erdos335.Loeb.countingRatio_univ
#check @Erdos335.Loeb.countingRatio_le_one
#print axioms Erdos335.Loeb.countingRatio_le_one
#check @Erdos335.Loeb.countingRatio_union
#print axioms Erdos335.Loeb.countingRatio_union
#check @Erdos335.Loeb.tendsto_ultraCount
#print axioms Erdos335.Loeb.tendsto_ultraCount
#check @Erdos335.Loeb.ultraCount_congr
#print axioms Erdos335.Loeb.ultraCount_congr
#check @Erdos335.Loeb.ultraCount_empty
#print axioms Erdos335.Loeb.ultraCount_empty
#check @Erdos335.Loeb.ultraCount_univ
#print axioms Erdos335.Loeb.ultraCount_univ
#check @Erdos335.Loeb.ultraCount_le_one
#print axioms Erdos335.Loeb.ultraCount_le_one
#check @Erdos335.Loeb.ultraCount_union
#print axioms Erdos335.Loeb.ultraCount_union
#check @Erdos335.Loeb.internalMass_internal
#print axioms Erdos335.Loeb.internalMass_internal
#check @Erdos335.Loeb.internalMass_empty
#print axioms Erdos335.Loeb.internalMass_empty
#check @Erdos335.Loeb.internalMass_univ
#print axioms Erdos335.Loeb.internalMass_univ
#check @Erdos335.Loeb.internalMass_le_one
#print axioms Erdos335.Loeb.internalMass_le_one
#check @Erdos335.Loeb.internalMass_union
#print axioms Erdos335.Loeb.internalMass_union
#check @Erdos335.Loeb.internalCountingContent_apply
#print axioms Erdos335.Loeb.internalCountingContent_apply
#check @Erdos335.Loeb.internalCountingContent_internal
#print axioms Erdos335.Loeb.internalCountingContent_internal
#check @Erdos335.Loeb.internalCountingContent_sigmaSubadditive
#print axioms Erdos335.Loeb.internalCountingContent_sigmaSubadditive
#check @Erdos335.Loeb.loebMeasure_internal
#print axioms Erdos335.Loeb.loebMeasure_internal
#check @Erdos335.Loeb.loebMeasure_univ
#print axioms Erdos335.Loeb.loebMeasure_univ
#check @Erdos335.Loeb.measurable_internalSet
#print axioms Erdos335.Loeb.measurable_internalSet
#check @Erdos335.Loeb.isProbabilityMeasure_loebMeasure
#print axioms Erdos335.Loeb.isProbabilityMeasure_loebMeasure
#check @Erdos335.Loeb.internalSet_add
#print axioms Erdos335.Loeb.internalSet_add
#check @Erdos335.Loeb.internalSet_preimage
#print axioms Erdos335.Loeb.internalSet_preimage
#check @Erdos335.Loeb.internalSet_image_equiv
#print axioms Erdos335.Loeb.internalSet_image_equiv
#check @Erdos335.Loeb.internalSets_preimage_equiv_iff
#print axioms Erdos335.Loeb.internalSets_preimage_equiv_iff
#check @Erdos335.Loeb.countingRatio_preimage_equiv
#print axioms Erdos335.Loeb.countingRatio_preimage_equiv
#check @Erdos335.Loeb.ultraCount_preimage_equiv
#print axioms Erdos335.Loeb.ultraCount_preimage_equiv
#check @Erdos335.Loeb.internalMass_preimage_equiv
#print axioms Erdos335.Loeb.internalMass_preimage_equiv
#check @Erdos335.Loeb.internalSet_biUnion_finset
#print axioms Erdos335.Loeb.internalSet_biUnion_finset
#check @Erdos335.Loeb.exists_internal_upper_bound
#print axioms Erdos335.Loeb.exists_internal_upper_bound
#check @Erdos335.Loeb.exists_internal_cover_of_countable
#print axioms Erdos335.Loeb.exists_internal_cover_of_countable
#check @Erdos335.Loeb.exists_countable_internal_cover_lt
#print axioms Erdos335.Loeb.exists_countable_internal_cover_lt
#check @Erdos335.Loeb.exists_internal_cover_lt
#print axioms Erdos335.Loeb.exists_internal_cover_lt
#check @Erdos335.Loeb.measurable_of_loebMeasure_zero
#print axioms Erdos335.Loeb.measurable_of_loebMeasure_zero
#check @Erdos335.Loeb.exists_internal_approximation
#print axioms Erdos335.Loeb.exists_internal_approximation
#check @Erdos335.Loeb.loebOuterMeasure_map_equiv
#print axioms Erdos335.Loeb.loebOuterMeasure_map_equiv
#check @Erdos335.Loeb.loebMeasure_preimage_equiv
#print axioms Erdos335.Loeb.loebMeasure_preimage_equiv
#check @Erdos335.Loeb.measurable_productEquiv
#print axioms Erdos335.Loeb.measurable_productEquiv
#check @Erdos335.Loeb.exists_eventually_eq_const
#print axioms Erdos335.Loeb.exists_eventually_eq_const
#check @Erdos335.Loeb.eventually_eq_finiteValue
#print axioms Erdos335.Loeb.eventually_eq_finiteValue
#check @Erdos335.Loeb.finiteValue_eq_of_eventually
#print axioms Erdos335.Loeb.finiteValue_eq_of_eventually
#check @Erdos335.Loeb.finiteValue_const
#print axioms Erdos335.Loeb.finiteValue_const
#check @Erdos335.Loeb.finiteValue_congr
#print axioms Erdos335.Loeb.finiteValue_congr
#check @Erdos335.Loeb.finiteValue_eq_iff
#print axioms Erdos335.Loeb.finiteValue_eq_iff
#check @Erdos335.Loeb.finiteProjection_surjective
#print axioms Erdos335.Loeb.finiteProjection_surjective
#check @Erdos335.Loeb.finiteQuotient_surjective
#print axioms Erdos335.Loeb.finiteQuotient_surjective
#check @Erdos335.Loeb.internalAddSubgroup_carrier
#print axioms Erdos335.Loeb.internalAddSubgroup_carrier
#check @Erdos335.Loeb.finiteQuotient_ker
#print axioms Erdos335.Loeb.finiteQuotient_ker
#check @Erdos335.Loeb.internalAddSubgroup_index_of_quotients
#print axioms Erdos335.Loeb.internalAddSubgroup_index_of_quotients
#check @Erdos335.Loeb.countingRatio_subgroup
#print axioms Erdos335.Loeb.countingRatio_subgroup
#check @Erdos335.Loeb.loebMeasure_internalSubgroup_of_quotients
#print axioms Erdos335.Loeb.loebMeasure_internalSubgroup_of_quotients
#check @Erdos335.Loeb.productEquiv_add_left
#print axioms Erdos335.Loeb.productEquiv_add_left
#check @Erdos335.Loeb.loebMeasure_preimage_add_left
#print axioms Erdos335.Loeb.loebMeasure_preimage_add_left
#check @Erdos335.Loeb.measurable_add_left
#print axioms Erdos335.Loeb.measurable_add_left
#check @Erdos335.Loeb.loebMeasure_image_add_left
#print axioms Erdos335.Loeb.loebMeasure_image_add_left
#check @Erdos335.Loeb.finiteFunction_preimage
#print axioms Erdos335.Loeb.finiteFunction_preimage
#check @Erdos335.Loeb.measurable_finiteFunction
#print axioms Erdos335.Loeb.measurable_finiteFunction
#check @Erdos335.Loeb.loebMeasure_finiteFunction_preimage
#print axioms Erdos335.Loeb.loebMeasure_finiteFunction_preimage
#check @Erdos335.Loeb.tendsto_ultralimitFunction
#print axioms Erdos335.Loeb.tendsto_ultralimitFunction
#check @Erdos335.Loeb.ultralimitFunction_mem_open_iff
#print axioms Erdos335.Loeb.ultralimitFunction_mem_open_iff
#check @Erdos335.Loeb.ultralimitFunction_preimage_open
#print axioms Erdos335.Loeb.ultralimitFunction_preimage_open
#check @Erdos335.Loeb.measurable_ultralimitFunction
#print axioms Erdos335.Loeb.measurable_ultralimitFunction
#check @Erdos335.Loeb.ultralimitFunction_comp_continuous
#print axioms Erdos335.Loeb.ultralimitFunction_comp_continuous
#check @Erdos335.Loeb.ultralimitFunction_of_finite_index
#print axioms Erdos335.Loeb.ultralimitFunction_of_finite_index
#check @Erdos335.Loeb.ultralimitFunction_dist_le
#print axioms Erdos335.Loeb.ultralimitFunction_dist_le
#check @Erdos335.Loeb.continuous_finite_approximation_bound
#print axioms Erdos335.Loeb.continuous_finite_approximation_bound
#check @Erdos335.Loeb.integral_finiteFunction
#print axioms Erdos335.Loeb.integral_finiteFunction
#check @Erdos335.Loeb.tendsto_finite_weighted_averages
#print axioms Erdos335.Loeb.tendsto_finite_weighted_averages
#check @Erdos335.Loeb.countingRatio_toReal
#print axioms Erdos335.Loeb.countingRatio_toReal
#check @Erdos335.Loeb.finite_weighted_average
#print axioms Erdos335.Loeb.finite_weighted_average
#check @Erdos335.Loeb.exists_finite_continuous_approximation
#print axioms Erdos335.Loeb.exists_finite_continuous_approximation
#check @Erdos335.Loeb.dist_finite_averages_le
#print axioms Erdos335.Loeb.dist_finite_averages_le
#check @Erdos335.Loeb.dist_integrals_le_of_pointwise
#print axioms Erdos335.Loeb.dist_integrals_le_of_pointwise
#check @Erdos335.Loeb.integrable_continuous_ultralimit
#print axioms Erdos335.Loeb.integrable_continuous_ultralimit
#check @Erdos335.Loeb.integrable_finiteFunction
#print axioms Erdos335.Loeb.integrable_finiteFunction
#check @Erdos335.Loeb.tendsto_continuous_coordinate_averages
#print axioms Erdos335.Loeb.tendsto_continuous_coordinate_averages
#check @Erdos335.Loeb.boundedRealFunction_bound
#print axioms Erdos335.Loeb.boundedRealFunction_bound
#check @Erdos335.Loeb.tendsto_boundedRealFunction
#print axioms Erdos335.Loeb.tendsto_boundedRealFunction
#check @Erdos335.Loeb.boundedRealFunction_independent_bound
#print axioms Erdos335.Loeb.boundedRealFunction_independent_bound
#check @Erdos335.Loeb.measurable_boundedRealFunction
#print axioms Erdos335.Loeb.measurable_boundedRealFunction
#check @Erdos335.Loeb.tendsto_boundedRealFunction_averages
#print axioms Erdos335.Loeb.tendsto_boundedRealFunction_averages
#check @Erdos335.Loeb.boundedComplexFunction_bound
#print axioms Erdos335.Loeb.boundedComplexFunction_bound
#check @Erdos335.Loeb.measurable_boundedComplexFunction
#print axioms Erdos335.Loeb.measurable_boundedComplexFunction
#check @Erdos335.Loeb.integrable_boundedComplexFunction
#print axioms Erdos335.Loeb.integrable_boundedComplexFunction
#check @Erdos335.Loeb.tendsto_boundedComplex_component_averages
#print axioms Erdos335.Loeb.tendsto_boundedComplex_component_averages
#check @Erdos335.Loeb.tendsto_boundedComplexFunction_averages
#print axioms Erdos335.Loeb.tendsto_boundedComplexFunction_averages
#check @Erdos335.Loeb.tendsto_boundedComplexFunction
#print axioms Erdos335.Loeb.tendsto_boundedComplexFunction
#check @Erdos335.Loeb.boundedComplexFunction_independent_bound
#print axioms Erdos335.Loeb.boundedComplexFunction_independent_bound
#check @Erdos335.Loeb.boundedComplexFunction_add
#print axioms Erdos335.Loeb.boundedComplexFunction_add
#check @Erdos335.Loeb.boundedComplexFunction_mul
#print axioms Erdos335.Loeb.boundedComplexFunction_mul
#check @Erdos335.Loeb.boundedComplexFunction_precompose
#print axioms Erdos335.Loeb.boundedComplexFunction_precompose
#check @Erdos335.Loeb.productMap_sub_left
#print axioms Erdos335.Loeb.productMap_sub_left
#check @Erdos335.Loeb.tendsto_coordinate_convolution
#print axioms Erdos335.Loeb.tendsto_coordinate_convolution
#check @Erdos335.Loeb.exists_ultralimit_preimage_of_approximation
#print axioms Erdos335.Loeb.exists_ultralimit_preimage_of_approximation
#check @Erdos335.Loeb.isClosed_range_ultralimitFunction
#print axioms Erdos335.Loeb.isClosed_range_ultralimitFunction
#check @Erdos335.Loeb.isCompact_range_ultralimitFunction
#print axioms Erdos335.Loeb.isCompact_range_ultralimitFunction
#check @Erdos335.Loeb.isClosed_range_ultralimitAddHom
#print axioms Erdos335.Loeb.isClosed_range_ultralimitAddHom
#check @Erdos335.Loeb.isCompact_range_ultralimitAddHom
#print axioms Erdos335.Loeb.isCompact_range_ultralimitAddHom
#check @Erdos335.Loeb.measurable_ultralimitAddHom
#print axioms Erdos335.Loeb.measurable_ultralimitAddHom
#check @Erdos335.Loeb.measurable_rangeRestrict_ultralimitAddHom
#print axioms Erdos335.Loeb.measurable_rangeRestrict_ultralimitAddHom
#check @Erdos335.Loeb.loebMeasure_map_add_left
#print axioms Erdos335.Loeb.loebMeasure_map_add_left
#check @Erdos335.Loeb.loebMeasure_map_hom_isAddLeftInvariant
#print axioms Erdos335.Loeb.loebMeasure_map_hom_isAddLeftInvariant
#check @Erdos335.Loeb.loebMeasure_map_hom_isAddHaarMeasure
#print axioms Erdos335.Loeb.loebMeasure_map_hom_isAddHaarMeasure
#check @Erdos335.Loeb.loebMeasure_compact_factor_isAddHaarMeasure
#print axioms Erdos335.Loeb.loebMeasure_compact_factor_isAddHaarMeasure
#check @Erdos335.Loeb.finiteQuotient_comp
#print axioms Erdos335.Loeb.finiteQuotient_comp
#check @Erdos335.Loeb.finiteQuotient_surjective_of_eventually
#print axioms Erdos335.Loeb.finiteQuotient_surjective_of_eventually
#check @Erdos335.Loeb.internalAddSubgroup_index_of_eventually_quotients
#print axioms Erdos335.Loeb.internalAddSubgroup_index_of_eventually_quotients
#check @Erdos335.Loeb.loebMeasure_internalSubgroup_of_eventually_quotients
#print axioms Erdos335.Loeb.loebMeasure_internalSubgroup_of_eventually_quotients
#check @Erdos335.Loeb.eventually_bounded_index_of_positive_loebMeasure
#print axioms Erdos335.Loeb.eventually_bounded_index_of_positive_loebMeasure
#check @Erdos335.Loeb.exists_eventually_constant_of_bounded_nat
#print axioms Erdos335.Loeb.exists_eventually_constant_of_bounded_nat
#check @Erdos335.Loeb.exists_fixed_natural_cyclic_quotient
#print axioms Erdos335.Loeb.exists_fixed_natural_cyclic_quotient
#check @Erdos335.Loeb.finiteQuotient_natCast_of_eventually
#print axioms Erdos335.Loeb.finiteQuotient_natCast_of_eventually
#check @Erdos335.Loeb.exists_natural_quotient_of_positive_loebMeasure
#print axioms Erdos335.Loeb.exists_natural_quotient_of_positive_loebMeasure
#check @Erdos335.Loeb.exists_natural_quotient_of_supergroup
#print axioms Erdos335.Loeb.exists_natural_quotient_of_supergroup
#check @Erdos335.Loeb.countingRatio_add_le
#print axioms Erdos335.Loeb.countingRatio_add_le
#check @Erdos335.Loeb.loebMeasure_internal_add_le
#print axioms Erdos335.Loeb.loebMeasure_internal_add_le
#check @Erdos335.Loeb.internal_stabilizer_add_mem
#print axioms Erdos335.Loeb.internal_stabilizer_add_mem
#check @Erdos335.Loeb.internal_stabilizer_le_of_subset
#print axioms Erdos335.Loeb.internal_stabilizer_le_of_subset
#check @Erdos335.Loeb.exists_internal_inner_approximation
#print axioms Erdos335.Loeb.exists_internal_inner_approximation
#check @Erdos335.Loeb.exists_positive_internal_subgroup
#print axioms Erdos335.Loeb.exists_positive_internal_subgroup
#check @Erdos335.Loeb.positive_measurable_subgroup_is_natural_finite_kernel
#print axioms Erdos335.Loeb.positive_measurable_subgroup_is_natural_finite_kernel
#check @Erdos335.Loeb.internalSet_singleton
#print axioms Erdos335.Loeb.internalSet_singleton
#check @Erdos335.Loeb.internalSet_vadd
#print axioms Erdos335.Loeb.internalSet_vadd
#check @Erdos335.Loeb.internalAddSubgroup_stabilizer
#print axioms Erdos335.Loeb.internalAddSubgroup_stabilizer
#check @Erdos335.Loeb.countingRatio_critical_identity
#print axioms Erdos335.Loeb.countingRatio_critical_identity
#check @Erdos335.Loeb.eventually_card_subcritical
#print axioms Erdos335.Loeb.eventually_card_subcritical
#check @Erdos335.Loeb.loebMeasure_critical_identity
#print axioms Erdos335.Loeb.loebMeasure_critical_identity
#check @Erdos335.Loeb.subcritical_stabilizer_positive
#print axioms Erdos335.Loeb.subcritical_stabilizer_positive
#check @Erdos335.Loeb.subcritical_cyclic_stabilizer
#print axioms Erdos335.Loeb.subcritical_cyclic_stabilizer
#check @Erdos335.Loeb.positive_measurable_subgroup_index
#print axioms Erdos335.Loeb.positive_measurable_subgroup_index
#check @Erdos335.Loeb.twice_index_le_of_proper_subgroup
#print axioms Erdos335.Loeb.twice_index_le_of_proper_subgroup
#check @Erdos335.Loeb.positive_subgroup_index_le_of_measure_bound
#print axioms Erdos335.Loeb.positive_subgroup_index_le_of_measure_bound
#check @Erdos335.Loeb.exists_nat_reciprocal_lt
#print axioms Erdos335.Loeb.exists_nat_reciprocal_lt
#check @Erdos335.Loeb.no_infinite_proper_refinements_of_measure_bound
#print axioms Erdos335.Loeb.no_infinite_proper_refinements_of_measure_bound
#check @Erdos335.Loeb.subgroup_le_of_positive_almost_periodic_coset
#print axioms Erdos335.Loeb.subgroup_le_of_positive_almost_periodic_coset
#check @Erdos335.Loeb.almost_periodic_of_subgroup_le
#print axioms Erdos335.Loeb.almost_periodic_of_subgroup_le
#check @Erdos335.Loeb.almost_periodic_union
#print axioms Erdos335.Loeb.almost_periodic_union
#check @Erdos335.Loeb.almost_periodic_nested_background
#print axioms Erdos335.Loeb.almost_periodic_nested_background
#check @Erdos335.Loeb.proper_subgroup_of_positive_background
#print axioms Erdos335.Loeb.proper_subgroup_of_positive_background
#check @Erdos335.FiniteFourier.wInner_sum_right
#print axioms Erdos335.FiniteFourier.wInner_sum_right
#check @Erdos335.FiniteFourier.coefficient_eq_basis_repr
#print axioms Erdos335.FiniteFourier.coefficient_eq_basis_repr
#check @Erdos335.FiniteFourier.expansion
#print axioms Erdos335.FiniteFourier.expansion
#check @Erdos335.FiniteFourier.inner_eq_sum_coefficients
#print axioms Erdos335.FiniteFourier.inner_eq_sum_coefficients
#check @Erdos335.FiniteFourier.parseval
#print axioms Erdos335.FiniteFourier.parseval
#check @Erdos335.FiniteFourier.coefficient_add
#print axioms Erdos335.FiniteFourier.coefficient_add
#check @Erdos335.FiniteFourier.coefficient_sub
#print axioms Erdos335.FiniteFourier.coefficient_sub
#check @Erdos335.FiniteFourier.coefficient_truncation
#print axioms Erdos335.FiniteFourier.coefficient_truncation
#check @Erdos335.FiniteFourier.largeSpectrum_card_mul_sq_le
#print axioms Erdos335.FiniteFourier.largeSpectrum_card_mul_sq_le
#check @Erdos335.FiniteFourier.normalized_energy_le_one
#print axioms Erdos335.FiniteFourier.normalized_energy_le_one
#check @Erdos335.FiniteFourier.largeSpectrum_card_bound
#print axioms Erdos335.FiniteFourier.largeSpectrum_card_bound
#check @Erdos335.Loeb.countableUltralimitHom_apply
#print axioms Erdos335.Loeb.countableUltralimitHom_apply
#check @Erdos335.Loeb.isCompact_range_countableUltralimitHom
#print axioms Erdos335.Loeb.isCompact_range_countableUltralimitHom
#check @Erdos335.Loeb.measurable_countableUltralimitHom
#print axioms Erdos335.Loeb.measurable_countableUltralimitHom
#check @Erdos335.Loeb.countableUltralimitHom_haar
#print axioms Erdos335.Loeb.countableUltralimitHom_haar
#check @Erdos335.Loeb.continuous_countable_factor_coordinate
#print axioms Erdos335.Loeb.continuous_countable_factor_coordinate
#check @Erdos335.FiniteFourier.coefficient_eq_expect
#print axioms Erdos335.FiniteFourier.coefficient_eq_expect
#check @Erdos335.FiniteFourier.coefficient_convolution
#print axioms Erdos335.FiniteFourier.coefficient_convolution
#check @Erdos335.FiniteFourier.coefficient_ext
#print axioms Erdos335.FiniteFourier.coefficient_ext
#check @Erdos335.FiniteFourier.convolution_comm
#print axioms Erdos335.FiniteFourier.convolution_comm
#check @Erdos335.FiniteFourier.convolution_truncation_energy_bound
#print axioms Erdos335.FiniteFourier.convolution_truncation_energy_bound
#check @Erdos335.Loeb.boundedComplexFunction_sub
#print axioms Erdos335.Loeb.boundedComplexFunction_sub
#check @Erdos335.Loeb.tendsto_boundedComplex_sqNorm_averages
#print axioms Erdos335.Loeb.tendsto_boundedComplex_sqNorm_averages
#check @Erdos335.Loeb.tendsto_boundedComplex_sqDistance_averages
#print axioms Erdos335.Loeb.tendsto_boundedComplex_sqDistance_averages
#check @Erdos335.Loeb.loeb_sqDistance_le_of_eventually
#print axioms Erdos335.Loeb.loeb_sqDistance_le_of_eventually
#check @Erdos335.FiniteFourier.coefficient_norm_le_one
#print axioms Erdos335.FiniteFourier.coefficient_norm_le_one
#check @Erdos335.FiniteFourier.pad_character_polynomial
#print axioms Erdos335.FiniteFourier.pad_character_polynomial
#check @Erdos335.FiniteFourier.exists_uniform_spectral_polynomial
#print axioms Erdos335.FiniteFourier.exists_uniform_spectral_polynomial
#check @Erdos335.Loeb.exists_limit_bounded_complex
#print axioms Erdos335.Loeb.exists_limit_bounded_complex
#check @Erdos335.Loeb.tendsto_character_polynomial
#print axioms Erdos335.Loeb.tendsto_character_polynomial
#check @Erdos335.Loeb.character_polynomial_norm_le
#print axioms Erdos335.Loeb.character_polynomial_norm_le
#check @Erdos335.Loeb.exists_character_polynomial_standardPart
#print axioms Erdos335.Loeb.exists_character_polynomial_standardPart
#check @Erdos335.Loeb.normalized_convolution_norm_le_one
#print axioms Erdos335.Loeb.normalized_convolution_norm_le_one
#check @Erdos335.Loeb.boundedComplex_convolution_eq
#print axioms Erdos335.Loeb.boundedComplex_convolution_eq
#check @Erdos335.Loeb.exists_loeb_convolution_polynomial
#print axioms Erdos335.Loeb.exists_loeb_convolution_polynomial
#check @Erdos335.Loeb.exists_compact_convolution_approximations
#print axioms Erdos335.Loeb.exists_compact_convolution_approximations
#check @Erdos335.Loeb.exists_factor_of_tendstoInMeasure
#print axioms Erdos335.Loeb.exists_factor_of_tendstoInMeasure
#check @Erdos335.Loeb.eLpNorm_two_eq_sqrt_integral
#print axioms Erdos335.Loeb.eLpNorm_two_eq_sqrt_integral
#check @Erdos335.Loeb.tendstoInMeasure_of_sqIntegral_tendsto_zero
#print axioms Erdos335.Loeb.tendstoInMeasure_of_sqIntegral_tendsto_zero
#check @Erdos335.Loeb.exists_compact_convolution_factor
#print axioms Erdos335.Loeb.exists_compact_convolution_factor
#check @Erdos335.Loeb.positive_support_condExp
#print axioms Erdos335.Loeb.positive_support_condExp
#check @Erdos335.Loeb.exists_unitInterval_conditional_factor
#print axioms Erdos335.Loeb.exists_unitInterval_conditional_factor
#check @Erdos335.Loeb.setIntegral_conditional_factor
#print axioms Erdos335.Loeb.setIntegral_conditional_factor
#check @Erdos335.Loeb.boundedRealFunction_mem_Icc
#print axioms Erdos335.Loeb.boundedRealFunction_mem_Icc
#check @Erdos335.Loeb.boundedComplexFunction_ofReal
#print axioms Erdos335.Loeb.boundedComplexFunction_ofReal
#check @Erdos335.Loeb.integrable_boundedRealFunction
#print axioms Erdos335.Loeb.integrable_boundedRealFunction
#check @Erdos335.Loeb.boundedReal_complex_convolution
#print axioms Erdos335.Loeb.boundedReal_complex_convolution
#check @Erdos335.Loeb.exists_compact_real_convolution_factor
#print axioms Erdos335.Loeb.exists_compact_real_convolution_factor
#check @Erdos335.Loeb.exists_compact_positive_input_factor
#print axioms Erdos335.Loeb.exists_compact_positive_input_factor
#check @Erdos335.Loeb.integral_smul_conditional_factor
#print axioms Erdos335.Loeb.integral_smul_conditional_factor
#check @Erdos335.Loeb.boundedComplexFunction_conj_character
#print axioms Erdos335.Loeb.boundedComplexFunction_conj_character
#check @Erdos335.Loeb.tendsto_internal_fourier_coefficients
#print axioms Erdos335.Loeb.tendsto_internal_fourier_coefficients
#check @Erdos335.Loeb.internal_fourier_convolution
#print axioms Erdos335.Loeb.internal_fourier_convolution
#check @Erdos335.Loeb.integral_convolution_character
#print axioms Erdos335.Loeb.integral_convolution_character
#check @Erdos335.Loeb.separating_multiplicative_span_dense
#print axioms Erdos335.Loeb.separating_multiplicative_span_dense
#check @Erdos335.Loeb.separating_multiplicative_Lp_span_dense
#print axioms Erdos335.Loeb.separating_multiplicative_Lp_span_dense
#check @Erdos335.Loeb.separating_multiplicative_L2_ext
#print axioms Erdos335.Loeb.separating_multiplicative_L2_ext
#check @Erdos335.Loeb.ultralimitAddHom_zero_family
#print axioms Erdos335.Loeb.ultralimitAddHom_zero_family
#check @Erdos335.Loeb.ultralimitAddHom_add_family
#print axioms Erdos335.Loeb.ultralimitAddHom_add_family
#check @Erdos335.Loeb.ultralimitAddHom_neg_family
#print axioms Erdos335.Loeb.ultralimitAddHom_neg_family
#check @Erdos335.Loeb.internalCharacterFunctions
#print axioms Erdos335.Loeb.internalCharacterFunctions
#check @Erdos335.Loeb.one_mem_internalCharacterFunctions
#print axioms Erdos335.Loeb.one_mem_internalCharacterFunctions
#check @Erdos335.Loeb.mul_mem_internalCharacterFunctions
#print axioms Erdos335.Loeb.mul_mem_internalCharacterFunctions
#check @Erdos335.Loeb.star_mem_internalCharacterFunctions
#print axioms Erdos335.Loeb.star_mem_internalCharacterFunctions
#check @Erdos335.Loeb.coordinate_mem_internalCharacterFunctions
#print axioms Erdos335.Loeb.coordinate_mem_internalCharacterFunctions
#check @Erdos335.Loeb.internalCharacterFunctions_separate
#print axioms Erdos335.Loeb.internalCharacterFunctions_separate
#check @Erdos335.Loeb.internalCharacterFunctions_span_dense
#print axioms Erdos335.Loeb.internalCharacterFunctions_span_dense
#check @Erdos335.Loeb.internalCharacterFunctions_norm
#print axioms Erdos335.Loeb.internalCharacterFunctions_norm
#check @Erdos335.Loeb.internalCharacterFunctions_map_add
#print axioms Erdos335.Loeb.internalCharacterFunctions_map_add
#check @Erdos335.Loeb.internalCharacterFunctions_map_zero
#print axioms Erdos335.Loeb.internalCharacterFunctions_map_zero
#check @Erdos335.Loeb.internalCharacterFunctions_addChar
#print axioms Erdos335.Loeb.internalCharacterFunctions_addChar
#check @Erdos335.Loeb.probability_convolution_norm_le_one
#print axioms Erdos335.Loeb.probability_convolution_norm_le_one
#check @Erdos335.Loeb.probability_convolution_memLp_two
#print axioms Erdos335.Loeb.probability_convolution_memLp_two
#check @Erdos335.Loeb.factor_memLp_two_of_ae_eq
#print axioms Erdos335.Loeb.factor_memLp_two_of_ae_eq
#check @Erdos335.Loeb.inner_continuous_test_toLp
#print axioms Erdos335.Loeb.inner_continuous_test_toLp
#check @Erdos335.Loeb.ae_eq_of_separating_multiplicative_integrals
#print axioms Erdos335.Loeb.ae_eq_of_separating_multiplicative_integrals
#check @Erdos335.Loeb.integral_factor_conjugate_test
#print axioms Erdos335.Loeb.integral_factor_conjugate_test
#check @Erdos335.Loeb.integral_conditional_conjugate_test
#print axioms Erdos335.Loeb.integral_conditional_conjugate_test
#check @Erdos335.Loeb.loeb_convolution_projection
#print axioms Erdos335.Loeb.loeb_convolution_projection
#check @Erdos335.Loeb.exists_compact_positive_convolution_model
#print axioms Erdos335.Loeb.exists_compact_positive_convolution_model
#check @Erdos335.Loeb.indicator_one_abs_le
#print axioms Erdos335.Loeb.indicator_one_abs_le
#check @Erdos335.Loeb.boundedRealFunction_indicator
#print axioms Erdos335.Loeb.boundedRealFunction_indicator
#check @Erdos335.Loeb.integral_boundedRealFunction_indicator
#print axioms Erdos335.Loeb.integral_boundedRealFunction_indicator
#check @Erdos335.Loeb.indicator_convolution_eq_zero_of_not_mem_add
#print axioms Erdos335.Loeb.indicator_convolution_eq_zero_of_not_mem_add
#check @Erdos335.Loeb.positive_indicator_convolution_subset_add
#print axioms Erdos335.Loeb.positive_indicator_convolution_subset_add
#check @Erdos335.Loeb.positive_internal_convolution_subset_add
#print axioms Erdos335.Loeb.positive_internal_convolution_subset_add
#check @Erdos335.Loeb.measure_inter_pos_of_sum_gt
#print axioms Erdos335.Loeb.measure_inter_pos_of_sum_gt
#check @Erdos335.Loeb.indicator_convolution_eq_measure_inter
#print axioms Erdos335.Loeb.indicator_convolution_eq_measure_inter
#check @Erdos335.Loeb.positive_indicator_convolution_of_local_overlap
#print axioms Erdos335.Loeb.positive_indicator_convolution_of_local_overlap
#check @Erdos335.Loeb.continuous_integral_norm_add_sub
#print axioms Erdos335.Loeb.continuous_integral_norm_add_sub
#check @Erdos335.Loeb.tendsto_integral_norm_add_sub_zero
#print axioms Erdos335.Loeb.tendsto_integral_norm_add_sub_zero
#check @Erdos335.Loeb.integral_norm_probability_average_le
#print axioms Erdos335.Loeb.integral_norm_probability_average_le
#check @Erdos335.Loeb.integral_norm_probability_average_sub_le
#print axioms Erdos335.Loeb.integral_norm_probability_average_sub_le
#check @Erdos335.Loeb.tendstoInMeasure_of_integral_norm_tendsto_zero
#print axioms Erdos335.Loeb.tendstoInMeasure_of_integral_norm_tendsto_zero
#check @Erdos335.Loeb.isProbabilityMeasure_normalized_restrict
#print axioms Erdos335.Loeb.isProbabilityMeasure_normalized_restrict
#check @Erdos335.Loeb.integral_norm_translate_average_sub_le
#print axioms Erdos335.Loeb.integral_norm_translate_average_sub_le
#check @Erdos335.Loeb.exists_common_local_average
#print axioms Erdos335.Loeb.exists_common_local_average
#check @Erdos335.Loeb.exists_common_local_average_ae
#print axioms Erdos335.Loeb.exists_common_local_average_ae
#check @Erdos335.Loeb.local_indicator_average_eq
#print axioms Erdos335.Loeb.local_indicator_average_eq
#check @Erdos335.Loeb.positive_indicator_convolution_of_local_limits
#print axioms Erdos335.Loeb.positive_indicator_convolution_of_local_limits
#check @Erdos335.Loeb.exists_full_measure_indicator_representatives
#print axioms Erdos335.Loeb.exists_full_measure_indicator_representatives
#check @Erdos335.Loeb.exists_full_measure_sigmaCompact_subset
#print axioms Erdos335.Loeb.exists_full_measure_sigmaCompact_subset
#check @Erdos335.Loeb.positive_convolution_of_positive_level
#print axioms Erdos335.Loeb.positive_convolution_of_positive_level
#check @Erdos335.Loeb.exists_positive_support_representatives
#print axioms Erdos335.Loeb.exists_positive_support_representatives
#check @Erdos335.Loeb.sigmaCompact_add_measurable
#print axioms Erdos335.Loeb.sigmaCompact_add_measurable
#check @Erdos335.Loeb.exists_positive_support_sigmaCompact_representatives
#print axioms Erdos335.Loeb.exists_positive_support_sigmaCompact_representatives
#check @Erdos335.Loeb.exists_compact_internal_set_model
#print axioms Erdos335.Loeb.exists_compact_internal_set_model
#check @Erdos335.Loeb.continuous_bounded_real_convolution
#print axioms Erdos335.Loeb.continuous_bounded_real_convolution
#check @Erdos335.Loeb.isOpen_positive_bounded_real_convolution
#print axioms Erdos335.Loeb.isOpen_positive_bounded_real_convolution
#check @Erdos335.Loeb.isClosed_ae_function_periods
#print axioms Erdos335.Loeb.isClosed_ae_function_periods
#check @Erdos335.Loeb.isClosed_aestabilizer
#print axioms Erdos335.Loeb.isClosed_aestabilizer
#check @Erdos335.Loeb.productEquiv_sub_left
#print axioms Erdos335.Loeb.productEquiv_sub_left
#check @Erdos335.Loeb.loebMeasurePreserving_sub_left
#print axioms Erdos335.Loeb.loebMeasurePreserving_sub_left
#check @Erdos335.Loeb.loeb_convolution_congr_ae
#print axioms Erdos335.Loeb.loeb_convolution_congr_ae
#check @Erdos335.Loeb.loeb_indicator_convolution_congr_ae
#print axioms Erdos335.Loeb.loeb_indicator_convolution_congr_ae
#check @Erdos335.Loeb.loeb_positive_model_subset_of_ae_variants
#print axioms Erdos335.Loeb.loeb_positive_model_subset_of_ae_variants
#check @Erdos335.Loeb.exists_common_period_of_finite_tests
#print axioms Erdos335.Loeb.exists_common_period_of_finite_tests
#check @Erdos335.Loeb.exists_reciprocal_modulus_bound
#print axioms Erdos335.Loeb.exists_reciprocal_modulus_bound
#check @Erdos335.Loeb.exists_internalSet_of_finite
#print axioms Erdos335.Loeb.exists_internalSet_of_finite
#check @Erdos335.Loeb.exists_internalSet_finite_augmentation
#print axioms Erdos335.Loeb.exists_internalSet_finite_augmentation
#check @Erdos335.Loeb.finiteQuotient_eq_of_eventually_natural
#print axioms Erdos335.Loeb.finiteQuotient_eq_of_eventually_natural
#check @Erdos335.Loeb.naturalCyclicKernel
#print axioms Erdos335.Loeb.naturalCyclicKernel
#check @Erdos335.Loeb.naturalCyclicKernel_eq
#print axioms Erdos335.Loeb.naturalCyclicKernel_eq
#check @Erdos335.Loeb.positive_measurable_subgroup_eq_natural_kernel
#print axioms Erdos335.Loeb.positive_measurable_subgroup_eq_natural_kernel
#check @Erdos335.Loeb.measurable_naturalCyclicKernel
#print axioms Erdos335.Loeb.measurable_naturalCyclicKernel
#check @Erdos335.Loeb.naturalCyclicKernel_measure_pos
#print axioms Erdos335.Loeb.naturalCyclicKernel_measure_pos
#check @Erdos335.Loeb.internalInnerMeasure
#print axioms Erdos335.Loeb.internalInnerMeasure
#check @Erdos335.Loeb.internalInnerMeasure_mono
#print axioms Erdos335.Loeb.internalInnerMeasure_mono
#check @Erdos335.Loeb.internalInnerMeasure_le
#print axioms Erdos335.Loeb.internalInnerMeasure_le
#check @Erdos335.Loeb.internalInnerMeasure_eq
#print axioms Erdos335.Loeb.internalInnerMeasure_eq
#check @Erdos335.Loeb.internalInnerMeasure_eq_iSup_measurable
#print axioms Erdos335.Loeb.internalInnerMeasure_eq_iSup_measurable
#check @Erdos335.Loeb.ultraCount_le_internalInnerMeasure
#print axioms Erdos335.Loeb.ultraCount_le_internalInnerMeasure
#check @Erdos335.Loeb.exists_internal_subset_measure_gt
#print axioms Erdos335.Loeb.exists_internal_subset_measure_gt
#check @Erdos335.Loeb.exists_uniform_natural_period_bound
#print axioms Erdos335.Loeb.exists_uniform_natural_period_bound
#check @Erdos335.Loeb.exists_natural_period_of_internal_lower_bounds
#print axioms Erdos335.Loeb.exists_natural_period_of_internal_lower_bounds
#check @Erdos335.Loeb.exists_internalSet_of_finiteQuotient_period
#print axioms Erdos335.Loeb.exists_internalSet_of_finiteQuotient_period
#check @Erdos335.Loeb.exists_internalSet_of_natural_kernel_period
#print axioms Erdos335.Loeb.exists_internalSet_of_natural_kernel_period
#check @Erdos335.Loeb.loeb_measurable_subcritical_period
#print axioms Erdos335.Loeb.loeb_measurable_subcritical_period
#check @Erdos335.Loeb.loeb_measurable_subcritical_sum_internal
#print axioms Erdos335.Loeb.loeb_measurable_subcritical_sum_internal
#check @Erdos335.Loeb.loeb_measurable_kneser_identity
#print axioms Erdos335.Loeb.loeb_measurable_kneser_identity
#check @Erdos335.Loeb.loebMeasure_sdiff_eq_zero_of_full_inner
#print axioms Erdos335.Loeb.loebMeasure_sdiff_eq_zero_of_full_inner
#check @Erdos335.Loeb.measurable_of_subset_full_inner
#print axioms Erdos335.Loeb.measurable_of_subset_full_inner
#check @Erdos335.Loeb.extendible_equality_pair_has_essential_period
#print axioms Erdos335.Loeb.extendible_equality_pair_has_essential_period
#check @Erdos335.Loeb.extendible_inner_equality_pair_has_essential_period
#print axioms Erdos335.Loeb.extendible_inner_equality_pair_has_essential_period
#check @Erdos335.Loeb.measurable_loeb_coset
#print axioms Erdos335.Loeb.measurable_loeb_coset
#check @Erdos335.Loeb.loebMeasure_coset
#print axioms Erdos335.Loeb.loebMeasure_coset
#check @Erdos335.Loeb.loeb_coset_subset_add_of_measure_sum_gt
#print axioms Erdos335.Loeb.loeb_coset_subset_add_of_measure_sum_gt
#check @Erdos335.Loeb.loeb_coset_section_measure_le
#print axioms Erdos335.Loeb.loeb_coset_section_measure_le
#check @Erdos335.Loeb.loeb_coset_sections_gt_of_saturated_deficit
#print axioms Erdos335.Loeb.loeb_coset_sections_gt_of_saturated_deficit
#check @Erdos335.Loeb.loeb_add_periodic_of_saturated_deficit
#print axioms Erdos335.Loeb.loeb_add_periodic_of_saturated_deficit
#check @Erdos335.Loeb.loeb_coset_section_bound_of_kneser_identity
#print axioms Erdos335.Loeb.loeb_coset_section_bound_of_kneser_identity
#check @Erdos335.Loeb.loeb_coset_section_positive_of_kneser_identity
#print axioms Erdos335.Loeb.loeb_coset_section_positive_of_kneser_identity
#check @Erdos335.Loeb.loeb_critical_coset_masses_positive
#print axioms Erdos335.Loeb.loeb_critical_coset_masses_positive
#check @Erdos335.Loeb.loeb_solid_translate_absorption
#print axioms Erdos335.Loeb.loeb_solid_translate_absorption
#check @Erdos335.Loeb.loeb_critical_translate_maximal
#print axioms Erdos335.Loeb.loeb_critical_translate_maximal
#check @Erdos335.Loeb.loeb_critical_extension_left_subset
#print axioms Erdos335.Loeb.loeb_critical_extension_left_subset
#check @Erdos335.Loeb.loeb_critical_extensions_eq
#print axioms Erdos335.Loeb.loeb_critical_extensions_eq
#check @Erdos335.Loeb.loeb_critical_null_extensions_sum_eq
#print axioms Erdos335.Loeb.loeb_critical_null_extensions_sum_eq
#check @Erdos335.Loeb.sdiff_coset_add_subgroup
#print axioms Erdos335.Loeb.sdiff_coset_add_subgroup
#check @Erdos335.Loeb.loeb_critical_background_periodic
#print axioms Erdos335.Loeb.loeb_critical_background_periodic
#check @Erdos335.Loeb.loeb_equality_extension_extra_outputs_same_coset
#print axioms Erdos335.Loeb.loeb_equality_extension_extra_outputs_same_coset
#check @Erdos335.Loeb.loeb_equality_extension_extra_coset
#print axioms Erdos335.Loeb.loeb_equality_extension_extra_coset
#check @Erdos335.Loeb.loeb_equality_extension_periodic_backgrounds
#print axioms Erdos335.Loeb.loeb_equality_extension_periodic_backgrounds
#check @Erdos335.Loeb.internalInnerMeasure_eq_add_sdiff
#print axioms Erdos335.Loeb.internalInnerMeasure_eq_add_sdiff
#check @Erdos335.Loeb.loeb_measure_section_eq_of_essential_period
#print axioms Erdos335.Loeb.loeb_measure_section_eq_of_essential_period
#check @Erdos335.Loeb.loeb_nonperiodic_equality_extension_active_section
#print axioms Erdos335.Loeb.loeb_nonperiodic_equality_extension_active_section
#check @Erdos335.Loeb.loeb_equality_extension_background_add_subset
#print axioms Erdos335.Loeb.loeb_equality_extension_background_add_subset
#check @Erdos335.Loeb.measurable_saturation_of_positive_subgroup
#print axioms Erdos335.Loeb.measurable_saturation_of_positive_subgroup
#check @Erdos335.Loeb.loeb_equality_extension_sparse_subset_coset
#print axioms Erdos335.Loeb.loeb_equality_extension_sparse_subset_coset
#check @Erdos335.Loeb.active_sparse_of_sum_not_mem
#print axioms Erdos335.Loeb.active_sparse_of_sum_not_mem
#check @Erdos335.Loeb.sum_sdiff_eq_active_sparse
#print axioms Erdos335.Loeb.sum_sdiff_eq_active_sparse
#check @Erdos335.Loeb.unique_expression_of_background_and_sparse
#print axioms Erdos335.Loeb.unique_expression_of_background_and_sparse
#check @Erdos335.Loeb.loeb_equality_extension_active_inner
#print axioms Erdos335.Loeb.loeb_equality_extension_active_inner
#check @Erdos335.Loeb.loeb_sparse_complement_measure_zero
#print axioms Erdos335.Loeb.loeb_sparse_complement_measure_zero
#check @Erdos335.Loeb.loeb_inter_saturation_background_periodic
#print axioms Erdos335.Loeb.loeb_inter_saturation_background_periodic
#check @Erdos335.Loeb.loeb_one_sided_equality_reduction
#print axioms Erdos335.Loeb.loeb_one_sided_equality_reduction
#check @Erdos335.Loeb.loeb_completion_at_most_one_coset
#print axioms Erdos335.Loeb.loeb_completion_at_most_one_coset
#check @Erdos335.Loeb.QuasiPeriodicPairData.swap
#print axioms Erdos335.Loeb.QuasiPeriodicPairData.swap
#check @Erdos335.Loeb.exists_quasiPeriodicPairData_of_one_sided_equality
#print axioms Erdos335.Loeb.exists_quasiPeriodicPairData_of_one_sided_equality
#check @Erdos335.Loeb.loeb_reducible_left_cross_strict
#print axioms Erdos335.Loeb.loeb_reducible_left_cross_strict
#check @Erdos335.Loeb.loeb_reducible_cross_strict
#print axioms Erdos335.Loeb.loeb_reducible_cross_strict
#check @Erdos335.Loeb.loeb_measure_sdiff_zero_of_full_inner
#print axioms Erdos335.Loeb.loeb_measure_sdiff_zero_of_full_inner
#check @Erdos335.Loeb.loeb_solid_extension_add_subset
#print axioms Erdos335.Loeb.loeb_solid_extension_add_subset
#check @Erdos335.Loeb.loeb_measure_saturation_eq_of_essential_period
#print axioms Erdos335.Loeb.loeb_measure_saturation_eq_of_essential_period
#check @Erdos335.Loeb.loeb_add_eq_add_saturations_of_essential_periods
#print axioms Erdos335.Loeb.loeb_add_eq_add_saturations_of_essential_periods
#check @Erdos335.Loeb.loeb_essential_period_of_full_inner_subset
#print axioms Erdos335.Loeb.loeb_essential_period_of_full_inner_subset
#check @Erdos335.Loeb.loeb_periodic_core_extensions_absorbed
#print axioms Erdos335.Loeb.loeb_periodic_core_extensions_absorbed
#check @Erdos335.Loeb.loeb_periodic_completion_one_coset
#print axioms Erdos335.Loeb.loeb_periodic_completion_one_coset
#check @Erdos335.Loeb.exists_quasiPeriodicDecomposition_of_sparse_extension
#print axioms Erdos335.Loeb.exists_quasiPeriodicDecomposition_of_sparse_extension
#check @Erdos335.Loeb.loeb_full_periodic_core_reduction
#print axioms Erdos335.Loeb.loeb_full_periodic_core_reduction
#check @Erdos335.Loeb.loeb_solid_extension_into_periodic_superset
#print axioms Erdos335.Loeb.loeb_solid_extension_into_periodic_superset
#check @Erdos335.Loeb.loeb_solid_periodic_core_lift
#print axioms Erdos335.Loeb.loeb_solid_periodic_core_lift
#check @Erdos335.Loeb.exists_finite_coset_cover
#print axioms Erdos335.Loeb.exists_finite_coset_cover
#check @Erdos335.Loeb.loeb_exists_finite_coset_cover
#print axioms Erdos335.Loeb.loeb_exists_finite_coset_cover
#check @Erdos335.Loeb.loeb_sum_with_essentially_periodic_summand
#print axioms Erdos335.Loeb.loeb_sum_with_essentially_periodic_summand
#check @Erdos335.Loeb.loeb_periodic_subset_of_measure_sdiff_zero
#print axioms Erdos335.Loeb.loeb_periodic_subset_of_measure_sdiff_zero
#check @Erdos335.Loeb.loeb_periodic_sets_eq_of_ae
#print axioms Erdos335.Loeb.loeb_periodic_sets_eq_of_ae
#check @Erdos335.Loeb.loeb_periodic_extension_by_one_coset
#print axioms Erdos335.Loeb.loeb_periodic_extension_by_one_coset
#check @Erdos335.Loeb.loeb_reducible_equal_cross_core_periods
#print axioms Erdos335.Loeb.loeb_reducible_equal_cross_core_periods
#check @Erdos335.Loeb.loeb_reducible_equal_cross_sum_periods
#print axioms Erdos335.Loeb.loeb_reducible_equal_cross_sum_periods
#check @Erdos335.Loeb.loeb_periodic_saturations_eq_of_common_full_inner
#print axioms Erdos335.Loeb.loeb_periodic_saturations_eq_of_common_full_inner
#check @Erdos335.Loeb.loeb_cross_equality_periodic_envelope
#print axioms Erdos335.Loeb.loeb_cross_equality_periodic_envelope
#check @Erdos335.Loeb.subgroup_le_stabilizer_of_add_eq
#print axioms Erdos335.Loeb.subgroup_le_stabilizer_of_add_eq
#check @Erdos335.Loeb.single_coset_extension_add_larger_subgroup
#print axioms Erdos335.Loeb.single_coset_extension_add_larger_subgroup
#check @Erdos335.Loeb.loeb_stabilizer_of_single_coset_envelope
#print axioms Erdos335.Loeb.loeb_stabilizer_of_single_coset_envelope
#check @Erdos335.Loeb.loeb_equality_completion_single_coset
#print axioms Erdos335.Loeb.loeb_equality_completion_single_coset
#check @Erdos335.Loeb.loeb_reducible_cross_equal
#print axioms Erdos335.Loeb.loeb_reducible_cross_equal
#check @Erdos335.Loeb.loeb_reducible_equality_dichotomy
#print axioms Erdos335.Loeb.loeb_reducible_equality_dichotomy
#check @Erdos335.Loeb.exists_loeb_solid_full_measure_subset
#print axioms Erdos335.Loeb.exists_loeb_solid_full_measure_subset
#check @Erdos335.Loeb.MeasureIrreducible
#print axioms Erdos335.Loeb.MeasureIrreducible
#check @Erdos335.Loeb.loeb_irreducible_or_reducible
#print axioms Erdos335.Loeb.loeb_irreducible_or_reducible
#check @Erdos335.Loeb.loeb_irreducible_periodic_core_lift
#print axioms Erdos335.Loeb.loeb_irreducible_periodic_core_lift
#check @Erdos335.Loeb.exists_internal_upper_bound_exact
#print axioms Erdos335.Loeb.exists_internal_upper_bound_exact
#check @Erdos335.Loeb.exists_internal_ae_representative
#print axioms Erdos335.Loeb.exists_internal_ae_representative
#check @Erdos335.Loeb.loeb_inner_measure_ge_of_ae_subset
#print axioms Erdos335.Loeb.loeb_inner_measure_ge_of_ae_subset
#check @Erdos335.Loeb.exists_compact_measurable_set_model
#print axioms Erdos335.Loeb.exists_compact_measurable_set_model
#check @Erdos335.Loeb.loeb_irreducible_pair_in_critical_container
#print axioms Erdos335.Loeb.loeb_irreducible_pair_in_critical_container
#check @Erdos335.Loeb.preimage_add_of_surjective_addHom
#print axioms Erdos335.Loeb.preimage_add_of_surjective_addHom
#check @Erdos335.Loeb.HasCompactEqualityModel
#print axioms Erdos335.Loeb.HasCompactEqualityModel
#check @Erdos335.Loeb.loeb_irreducible_equality_compact_or_decomposed
#print axioms Erdos335.Loeb.loeb_irreducible_equality_compact_or_decomposed
#check @Erdos335.Loeb.loeb_equality_compact_or_decomposed
#print axioms Erdos335.Loeb.loeb_equality_compact_or_decomposed
#check @Erdos335.Loeb.internalInnerMeasure_le_of_ae_subset
#print axioms Erdos335.Loeb.internalInnerMeasure_le_of_ae_subset
#check @Erdos335.Loeb.internalInnerMeasure_congr_ae
#print axioms Erdos335.Loeb.internalInnerMeasure_congr_ae
#check @Erdos335.Loeb.MeasureNonextendible
#print axioms Erdos335.Loeb.MeasureNonextendible
#check @Erdos335.Loeb.loeb_nonextendible_left_extension_eq
#print axioms Erdos335.Loeb.loeb_nonextendible_left_extension_eq
#check @Erdos335.Loeb.loeb_nonextendible_absorbed_coset
#print axioms Erdos335.Loeb.loeb_nonextendible_absorbed_coset
#check @Erdos335.Loeb.QuasiPeriodicDecomposition.active_add_period
#print axioms Erdos335.Loeb.QuasiPeriodicDecomposition.active_add_period
#check @Erdos335.Loeb.QuasiPeriodicDecomposition.active_eq_inter_coset
#print axioms Erdos335.Loeb.QuasiPeriodicDecomposition.active_eq_inter_coset
#check @Erdos335.Loeb.QuasiPeriodicDecomposition.background_eq_sdiff_coset
#print axioms Erdos335.Loeb.QuasiPeriodicDecomposition.background_eq_sdiff_coset
#check @Erdos335.Loeb.QuasiPeriodicPairData.sum_partition
#print axioms Erdos335.Loeb.QuasiPeriodicPairData.sum_partition
#check @Erdos335.Loeb.QuasiPeriodicPairData.background_disjoint_active_coset
#print axioms Erdos335.Loeb.QuasiPeriodicPairData.background_disjoint_active_coset
#check @Erdos335.Loeb.loeb_quasiPeriodic_decomposition_solid
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_decomposition_solid
#check @Erdos335.Loeb.loeb_quasiPeriodic_background
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_background
#check @Erdos335.Loeb.loeb_quasiPeriodic_essential_period_of_full_coset
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_essential_period_of_full_coset
#check @Erdos335.Loeb.QuasiPeriodicPairData.active_sum_subset_coset
#print axioms Erdos335.Loeb.QuasiPeriodicPairData.active_sum_subset_coset
#check @Erdos335.Loeb.loeb_quasiPeriodic_translate_avoids_active_coset
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_translate_avoids_active_coset
#check @Erdos335.Loeb.loeb_quasiPeriodic_translate_saturated_subset
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_translate_saturated_subset
#check @Erdos335.Loeb.loeb_nonextendible_quasiPeriodic_translate
#print axioms Erdos335.Loeb.loeb_nonextendible_quasiPeriodic_translate
#check @Erdos335.Loeb.loeb_essential_period_of_full_cosets
#print axioms Erdos335.Loeb.loeb_essential_period_of_full_cosets
#check @Erdos335.Loeb.MeasureNonextendible.swap
#print axioms Erdos335.Loeb.MeasureNonextendible.swap
#check @Erdos335.Loeb.loeb_quasiPeriodic_extension_background
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_extension_background
#check @Erdos335.Loeb.measurable_loeb_translate
#print axioms Erdos335.Loeb.measurable_loeb_translate
#check @Erdos335.Loeb.loeb_translation_sdiff_zero_of_full_inner
#print axioms Erdos335.Loeb.loeb_translation_sdiff_zero_of_full_inner
#check @Erdos335.Loeb.loeb_quasiPeriodic_null_extension_backgrounds
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_null_extension_backgrounds
#check @Erdos335.Loeb.exists_quasiPeriodicDecomposition_of_null_extension
#print axioms Erdos335.Loeb.exists_quasiPeriodicDecomposition_of_null_extension
#check @Erdos335.Loeb.left_coset_of_sum_right_cosets
#print axioms Erdos335.Loeb.left_coset_of_sum_right_cosets
#check @Erdos335.Loeb.loeb_quasiPeriodic_null_extension_unique_expression
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_null_extension_unique_expression
#check @Erdos335.Loeb.loeb_quasiPeriodic_extension_active_inner
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_extension_active_inner
#check @Erdos335.Loeb.loeb_positive_quasiPeriodic_core_lift
#print axioms Erdos335.Loeb.loeb_positive_quasiPeriodic_core_lift
#check @Erdos335.Loeb.loeb_saturation_stabilizer
#print axioms Erdos335.Loeb.loeb_saturation_stabilizer
#check @Erdos335.Loeb.MeasureIrreducible.swap
#print axioms Erdos335.Loeb.MeasureIrreducible.swap
#check @Erdos335.Loeb.loeb_zero_left_active_core_lift
#print axioms Erdos335.Loeb.loeb_zero_left_active_core_lift
#check @Erdos335.Loeb.loeb_null_active_core_lift
#print axioms Erdos335.Loeb.loeb_null_active_core_lift
#check @Erdos335.Loeb.loeb_irreducible_extension_of_periodic_core
#print axioms Erdos335.Loeb.loeb_irreducible_extension_of_periodic_core
#check @Erdos335.Loeb.loeb_irreducible_extension_of_quasiPeriodic_core
#print axioms Erdos335.Loeb.loeb_irreducible_extension_of_quasiPeriodic_core
#check @Erdos335.Loeb.preimage_vadd_subgroup
#print axioms Erdos335.Loeb.preimage_vadd_subgroup
#check @Erdos335.Loeb.QuasiPeriodicDecomposition.comap
#print axioms Erdos335.Loeb.QuasiPeriodicDecomposition.comap
#check @Erdos335.Loeb.exists_quasiPeriodicPairData_comap
#print axioms Erdos335.Loeb.exists_quasiPeriodicPairData_comap
#check @Erdos335.Loeb.loeb_quasiPeriodic_comap
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_comap
#check @Erdos335.Loeb.essential_sum_period_comap
#print axioms Erdos335.Loeb.essential_sum_period_comap
#check @Erdos335.Loeb.QuasiPeriodicPairData.active_sum_eq_inter
#print axioms Erdos335.Loeb.QuasiPeriodicPairData.active_sum_eq_inter
#check @Erdos335.Loeb.QuasiPeriodicDecomposition.restrict
#print axioms Erdos335.Loeb.QuasiPeriodicDecomposition.restrict
#check @Erdos335.Loeb.loeb_quasiPeriodic_background_positive
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_background_positive
#check @Erdos335.Loeb.loeb_quasiPeriodic_full_restriction
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_full_restriction
#check @Erdos335.Loeb.essential_periodic_subset_of_null_difference
#print axioms Erdos335.Loeb.essential_periodic_subset_of_null_difference
#check @Erdos335.Loeb.QuasiPeriodicDecomposition.empty_active_restriction_period
#print axioms Erdos335.Loeb.QuasiPeriodicDecomposition.empty_active_restriction_period
#check @Erdos335.Loeb.loeb_irreducible_quasiPeriodic_ae_transfer
#print axioms Erdos335.Loeb.loeb_irreducible_quasiPeriodic_ae_transfer
#check @Erdos335.Loeb.loeb_irreducible_periodic_ae_transfer
#print axioms Erdos335.Loeb.loeb_irreducible_periodic_ae_transfer
#check @Erdos335.Loeb.dysonGroupLeft
#print axioms Erdos335.Loeb.dysonGroupLeft
#check @Erdos335.Loeb.dysonGroupRight
#print axioms Erdos335.Loeb.dysonGroupRight
#check @Erdos335.Loeb.dysonGroup_sum_subset
#print axioms Erdos335.Loeb.dysonGroup_sum_subset
#check @Erdos335.Loeb.dysonGroup_translate_right
#print axioms Erdos335.Loeb.dysonGroup_translate_right
#check @Erdos335.Loeb.vadd_set_eq_neg_preimage
#print axioms Erdos335.Loeb.vadd_set_eq_neg_preimage
#check @Erdos335.Loeb.measurableSet_dysonGroup
#print axioms Erdos335.Loeb.measurableSet_dysonGroup
#check @Erdos335.Loeb.dysonGroup_measure_identity
#print axioms Erdos335.Loeb.dysonGroup_measure_identity
#check @Erdos335.Loeb.shrinking_measure_le_reciprocal
#print axioms Erdos335.Loeb.shrinking_measure_le_reciprocal
#check @Erdos335.Loeb.shrinking_measure_tendsto_zero
#print axioms Erdos335.Loeb.shrinking_measure_tendsto_zero
#check @Erdos335.Loeb.eventually_difference_subset_of_unique_maximum
#print axioms Erdos335.Loeb.eventually_difference_subset_of_unique_maximum
#check @Erdos335.Loeb.haarOverlap
#print axioms Erdos335.Loeb.haarOverlap
#check @Erdos335.Loeb.continuous_haarOverlap
#print axioms Erdos335.Loeb.continuous_haarOverlap
#check @Erdos335.Loeb.haarOverlap_eq_full_iff
#print axioms Erdos335.Loeb.haarOverlap_eq_full_iff
#check @Erdos335.Loeb.haarOverlap_strict_maximum
#print axioms Erdos335.Loeb.haarOverlap_strict_maximum
#check @Erdos335.Loeb.haarOverlap_ge_of_sumset_ae_subset
#print axioms Erdos335.Loeb.haarOverlap_ge_of_sumset_ae_subset
#check @Erdos335.Loeb.shrinking_sumsets_localize
#print axioms Erdos335.Loeb.shrinking_sumsets_localize
#check @Erdos335.Loeb.QuasiPeriodicDecomposition.refinement_anchor_mem
#print axioms Erdos335.Loeb.QuasiPeriodicDecomposition.refinement_anchor_mem
#check @Erdos335.Loeb.QuasiPeriodicDecomposition.refine
#print axioms Erdos335.Loeb.QuasiPeriodicDecomposition.refine
#check @Erdos335.Loeb.QuasiPeriodicPairData.refine
#print axioms Erdos335.Loeb.QuasiPeriodicPairData.refine
#check @Erdos335.Loeb.loeb_period_le_of_positive_coset_subset
#print axioms Erdos335.Loeb.loeb_period_le_of_positive_coset_subset
#check @Erdos335.Loeb.loeb_quasiPeriodic_refinement_period_le
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_refinement_period_le
#check @Erdos335.Loeb.QuasiPeriodicDecomposition.period_ne_of_coset_containment
#print axioms Erdos335.Loeb.QuasiPeriodicDecomposition.period_ne_of_coset_containment
#check @Erdos335.Loeb.loeb_quasiPeriodic_refinement_period_ne
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_refinement_period_ne
#check @Erdos335.Loeb.loeb_proper_subgroup_measure_double_le
#print axioms Erdos335.Loeb.loeb_proper_subgroup_measure_double_le
#check @Erdos335.Loeb.loeb_quasiPeriodic_refinement
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_refinement
#check @Erdos335.Loeb.loeb_quasiPeriodic_arbitrarily_small_of_refinable
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_arbitrarily_small_of_refinable
#check @Erdos335.Loeb.measurable_loeb_neg
#print axioms Erdos335.Loeb.measurable_loeb_neg
#check @Erdos335.Loeb.loebMeasure_neg
#print axioms Erdos335.Loeb.loebMeasure_neg
#check @Erdos335.Loeb.neg_add_subgroup
#print axioms Erdos335.Loeb.neg_add_subgroup
#check @Erdos335.Loeb.loeb_difference_deficit_periodizes_sum
#print axioms Erdos335.Loeb.loeb_difference_deficit_periodizes_sum
#check @Erdos335.Loeb.compactIntersectionProfile
#print axioms Erdos335.Loeb.compactIntersectionProfile
#check @Erdos335.Loeb.indicator_convolution_eq_intersectionProfile
#print axioms Erdos335.Loeb.indicator_convolution_eq_intersectionProfile
#check @Erdos335.Loeb.continuous_compactIntersectionProfile
#print axioms Erdos335.Loeb.continuous_compactIntersectionProfile
#check @Erdos335.Loeb.integral_compactIntersectionProfile
#print axioms Erdos335.Loeb.integral_compactIntersectionProfile
#check @Erdos335.Loeb.compactIntersectionProfile_positive_support_subset
#print axioms Erdos335.Loeb.compactIntersectionProfile_positive_support_subset
#check @Erdos335.Loeb.exists_positive_le_support_average
#print axioms Erdos335.Loeb.exists_positive_le_support_average
#check @Erdos335.Loeb.small_intersection_average_bound
#print axioms Erdos335.Loeb.small_intersection_average_bound
#check @Erdos335.Loeb.exists_small_positive_intersection
#print axioms Erdos335.Loeb.exists_small_positive_intersection
#check @Erdos335.Loeb.compactIntersectionProfile_congr_ae
#print axioms Erdos335.Loeb.compactIntersectionProfile_congr_ae
#check @Erdos335.Loeb.exists_full_measure_positive_intersection_cores
#print axioms Erdos335.Loeb.exists_full_measure_positive_intersection_cores
#check @Erdos335.Loeb.preimage_neg_addHom
#print axioms Erdos335.Loeb.preimage_neg_addHom
#check @Erdos335.Loeb.loebMeasure_map_hom_isNegInvariant
#print axioms Erdos335.Loeb.loebMeasure_map_hom_isNegInvariant
#check @Erdos335.Loeb.loeb_quotient_difference_measure_bound
#print axioms Erdos335.Loeb.loeb_quotient_difference_measure_bound
#check @Erdos335.Loeb.compactIntersectionProfile_eq_dysonMeasure
#print axioms Erdos335.Loeb.compactIntersectionProfile_eq_dysonMeasure
#check @Erdos335.Loeb.exists_shrinking_step_in_loeb_compact_quotient
#print axioms Erdos335.Loeb.exists_shrinking_step_in_loeb_compact_quotient
#check @Erdos335.Loeb.loeb_nonextendible_complement_duality
#print axioms Erdos335.Loeb.loeb_nonextendible_complement_duality
#check @Erdos335.Loeb.loeb_finite_hom_kernel_outer_positive
#print axioms Erdos335.Loeb.loeb_finite_hom_kernel_outer_positive
#check @Erdos335.Loeb.loeb_positive_finite_index_subgroup
#print axioms Erdos335.Loeb.loeb_positive_finite_index_subgroup
#check @Erdos335.Loeb.loeb_positive_subgroup_intersection
#print axioms Erdos335.Loeb.loeb_positive_subgroup_intersection
#check @Erdos335.Loeb.loeb_finset_period_intersection
#print axioms Erdos335.Loeb.loeb_finset_period_intersection
#check @Erdos335.Loeb.loeb_finite_union_has_positive_period
#print axioms Erdos335.Loeb.loeb_finite_union_has_positive_period
#check @Erdos335.Loeb.loeb_finite_union_of_critical_sums_periodic
#print axioms Erdos335.Loeb.loeb_finite_union_of_critical_sums_periodic
#check @Erdos335.Loeb.loeb_nonperiodic_finite_union_has_noncritical_component
#print axioms Erdos335.Loeb.loeb_nonperiodic_finite_union_has_noncritical_component
#check @Erdos335.Loeb.dysonMixedPart
#print axioms Erdos335.Loeb.dysonMixedPart
#check @Erdos335.Loeb.dysonMixedPart_saturation_subset
#print axioms Erdos335.Loeb.dysonMixedPart_saturation_subset
#check @Erdos335.Loeb.dysonMixedPart_saturation_eq
#print axioms Erdos335.Loeb.dysonMixedPart_saturation_eq
#check @Erdos335.Loeb.dysonMixedPart_disjoint
#print axioms Erdos335.Loeb.dysonMixedPart_disjoint
#check @Erdos335.Loeb.dyson_coset_partition
#print axioms Erdos335.Loeb.dyson_coset_partition
#check @Erdos335.Loeb.loeb_nonextendible_dyson_overlap_periodic
#print axioms Erdos335.Loeb.loeb_nonextendible_dyson_overlap_periodic
#check @Erdos335.Loeb.complement_add_period
#print axioms Erdos335.Loeb.complement_add_period
#check @Erdos335.Loeb.loeb_nonextendible_part_periodic
#print axioms Erdos335.Loeb.loeb_nonextendible_part_periodic
#check @Erdos335.Loeb.dysonMixedPart_coset_partition
#print axioms Erdos335.Loeb.dysonMixedPart_coset_partition
#check @Erdos335.Loeb.loeb_dyson_mixed_coset_bound
#print axioms Erdos335.Loeb.loeb_dyson_mixed_coset_bound
#check @Erdos335.Loeb.dyson_sum_eq_periodic_union_mixed
#print axioms Erdos335.Loeb.dyson_sum_eq_periodic_union_mixed
#check @Erdos335.Loeb.exists_ultralimit_in_internal_of_approximation
#print axioms Erdos335.Loeb.exists_ultralimit_in_internal_of_approximation
#check @Erdos335.Loeb.isCompact_image_internalSet_ultralimitFunction
#print axioms Erdos335.Loeb.isCompact_image_internalSet_ultralimitFunction
#check @Erdos335.Loeb.isCompact_image_internalAddSubgroup
#print axioms Erdos335.Loeb.isCompact_image_internalAddSubgroup
#check @Erdos335.Loeb.isCompact_image_positive_loeb_subgroup
#print axioms Erdos335.Loeb.isCompact_image_positive_loeb_subgroup
#check @Erdos335.Loeb.isCompact_image_positive_loeb_subgroup_rangeRestrict
#print axioms Erdos335.Loeb.isCompact_image_positive_loeb_subgroup_rangeRestrict
#check @Erdos335.Loeb.isOpen_map_positive_loeb_subgroup_rangeRestrict
#print axioms Erdos335.Loeb.isOpen_map_positive_loeb_subgroup_rangeRestrict
#check @Erdos335.Loeb.preimage_vadd_addHom
#print axioms Erdos335.Loeb.preimage_vadd_addHom
#check @Erdos335.Loeb.stabilizer_preimage_comap
#print axioms Erdos335.Loeb.stabilizer_preimage_comap
#check @Erdos335.Loeb.map_stabilizer_preimage
#print axioms Erdos335.Loeb.map_stabilizer_preimage
#check @Erdos335.Loeb.compact_factor_kneser_from_pullback
#print axioms Erdos335.Loeb.compact_factor_kneser_from_pullback
#check @Erdos335.Loeb.compact_factor_kneser_identity
#print axioms Erdos335.Loeb.compact_factor_kneser_identity
#check @Erdos335.Loeb.loeb_nonextendible_left_ae_period
#print axioms Erdos335.Loeb.loeb_nonextendible_left_ae_period
#check @Erdos335.Loeb.loeb_nonextendible_inputs_ae_period
#print axioms Erdos335.Loeb.loeb_nonextendible_inputs_ae_period
#check @Erdos335.Loeb.loeb_nonextendible_of_no_essential_period
#print axioms Erdos335.Loeb.loeb_nonextendible_of_no_essential_period
#check @Erdos335.Loeb.coset_section_sum_subset
#print axioms Erdos335.Loeb.coset_section_sum_subset
#check @Erdos335.Loeb.coset_section_nonempty_of_saturation_eq
#print axioms Erdos335.Loeb.coset_section_nonempty_of_saturation_eq
#check @Erdos335.Loeb.disjoint_periodic_set_coset
#print axioms Erdos335.Loeb.disjoint_periodic_set_coset
#check @Erdos335.Loeb.disjoint_cosets_of_not_mem
#print axioms Erdos335.Loeb.disjoint_cosets_of_not_mem
#check @Erdos335.Loeb.loeb_section_measures_le_sum_section
#print axioms Erdos335.Loeb.loeb_section_measures_le_sum_section
#check @Erdos335.Loeb.loeb_single_outside_coset_of_noncritical_section
#print axioms Erdos335.Loeb.loeb_single_outside_coset_of_noncritical_section
#check @Erdos335.Loeb.exists_quasiPeriodicDecomposition_of_single_coset_remainder
#print axioms Erdos335.Loeb.exists_quasiPeriodicDecomposition_of_single_coset_remainder
#check @Erdos335.Loeb.loeb_left_measure_le_sum_inner
#print axioms Erdos335.Loeb.loeb_left_measure_le_sum_inner
#check @Erdos335.Loeb.loeb_positive_of_strict_sum_deficit
#print axioms Erdos335.Loeb.loeb_positive_of_strict_sum_deficit
#check @Erdos335.Loeb.loeb_nonperiodic_union_base_has_noncritical_component
#print axioms Erdos335.Loeb.loeb_nonperiodic_union_base_has_noncritical_component
#check @Erdos335.Loeb.loeb_mixed_sum_quasiPeriodic_decomposition
#print axioms Erdos335.Loeb.loeb_mixed_sum_quasiPeriodic_decomposition
#check @Erdos335.Loeb.loeb_dyson_mixed_case_quasiPeriodic_output
#print axioms Erdos335.Loeb.loeb_dyson_mixed_case_quasiPeriodic_output
#check @Erdos335.Loeb.loeb_dyson_exclusive_case_quasiPeriodic_model
#print axioms Erdos335.Loeb.loeb_dyson_exclusive_case_quasiPeriodic_model
#check @Erdos335.Loeb.loeb_strict_dyson_quasiPeriodic_output_model
#print axioms Erdos335.Loeb.loeb_strict_dyson_quasiPeriodic_output_model
#check @Erdos335.Loeb.connectedSpace_of_no_proper_open_addSubgroup
#print axioms Erdos335.Loeb.connectedSpace_of_no_proper_open_addSubgroup
#check @Erdos335.Loeb.exists_minimal_open_addSubgroup_of_bounded_index
#print axioms Erdos335.Loeb.exists_minimal_open_addSubgroup_of_bounded_index
#check @Erdos335.Loeb.connectedSpace_of_minimal_open_addSubgroup
#print axioms Erdos335.Loeb.connectedSpace_of_minimal_open_addSubgroup
#check @Erdos335.Loeb.open_addSubgroup_indices_unbounded_or_connected
#print axioms Erdos335.Loeb.open_addSubgroup_indices_unbounded_or_connected
#check @Erdos335.Loeb.haar_measure_open_addSubgroup
#print axioms Erdos335.Loeb.haar_measure_open_addSubgroup
#check @Erdos335.Loeb.compact_open_subgroups_small_or_connected
#print axioms Erdos335.Loeb.compact_open_subgroups_small_or_connected
#check @Erdos335.Loeb.loeb_zero_growth_generated_period
#print axioms Erdos335.Loeb.loeb_zero_growth_generated_period
#check @Erdos335.Loeb.finite_growth_concentrates
#print axioms Erdos335.Loeb.finite_growth_concentrates
#check @Erdos335.Loeb.loeb_zero_growth_family_periodic
#print axioms Erdos335.Loeb.loeb_zero_growth_family_periodic
#check @Erdos335.Loeb.loeb_one_generated_coset_input_quasiPeriodic
#print axioms Erdos335.Loeb.loeb_one_generated_coset_input_quasiPeriodic
#check @Erdos335.Loeb.vadd_set_add_eq
#print axioms Erdos335.Loeb.vadd_set_add_eq
#check @Erdos335.Loeb.add_vadd_set_eq
#print axioms Erdos335.Loeb.add_vadd_set_eq
#check @Erdos335.Loeb.internalInnerMeasure_le_vadd
#print axioms Erdos335.Loeb.internalInnerMeasure_le_vadd
#check @Erdos335.Loeb.internalInnerMeasure_vadd
#print axioms Erdos335.Loeb.internalInnerMeasure_vadd
#check @Erdos335.Loeb.loeb_vadd_congr_ae
#print axioms Erdos335.Loeb.loeb_vadd_congr_ae
#check @Erdos335.Loeb.QuasiPeriodicDecomposition.loebTranslate
#print axioms Erdos335.Loeb.QuasiPeriodicDecomposition.loebTranslate
#check @Erdos335.Loeb.loeb_general_strict_dyson_output_model
#print axioms Erdos335.Loeb.loeb_general_strict_dyson_output_model
#check @Erdos335.Loeb.loeb_noncritical_section_outside_periodic_background
#print axioms Erdos335.Loeb.loeb_noncritical_section_outside_periodic_background
#check @Erdos335.Loeb.loeb_quasiPeriodic_pair_of_strict_background
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_pair_of_strict_background
#check @Erdos335.Loeb.loeb_background_stabilizer_eq_of_maximal_period
#print axioms Erdos335.Loeb.loeb_background_stabilizer_eq_of_maximal_period
#check @Erdos335.Loeb.loeb_background_sum_strict_of_irreducible
#print axioms Erdos335.Loeb.loeb_background_sum_strict_of_irreducible
#check @Erdos335.Loeb.loeb_translate_ae_of_essential_period
#print axioms Erdos335.Loeb.loeb_translate_ae_of_essential_period
#check @Erdos335.Loeb.loeb_exists_maximal_essential_period
#print axioms Erdos335.Loeb.loeb_exists_maximal_essential_period
#check @Erdos335.Loeb.QuasiPeriodicDecomposition.loebEnlargePeriod
#print axioms Erdos335.Loeb.QuasiPeriodicDecomposition.loebEnlargePeriod
#check @Erdos335.Loeb.loeb_quasiPeriodic_pair_of_positive_background
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_pair_of_positive_background
#check @Erdos335.Loeb.exists_positive_internal_subgroup_of_inner
#print axioms Erdos335.Loeb.exists_positive_internal_subgroup_of_inner
#check @Erdos335.Loeb.measurable_loeb_subgroup_of_positive_inner
#print axioms Erdos335.Loeb.measurable_loeb_subgroup_of_positive_inner
#check @Erdos335.Loeb.measurable_loeb_generated_subgroup
#print axioms Erdos335.Loeb.measurable_loeb_generated_subgroup
#check @Erdos335.Loeb.loeb_one_coset_input_reduction
#print axioms Erdos335.Loeb.loeb_one_coset_input_reduction
#check @Erdos335.Loeb.loeb_quasiPeriodic_pair_of_nonnull_background
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_pair_of_nonnull_background
#check @Erdos335.Loeb.loeb_quasiPeriodic_pair_of_one_coset_and_large_sum
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_pair_of_one_coset_and_large_sum
#check @Erdos335.Loeb.loeb_integral_indicator_convolution
#print axioms Erdos335.Loeb.loeb_integral_indicator_convolution
#check @Erdos335.Loeb.loeb_exists_positive_indicator_convolution
#print axioms Erdos335.Loeb.loeb_exists_positive_indicator_convolution
#check @Erdos335.Loeb.loeb_section_zero_or_full_of_ae_periods
#print axioms Erdos335.Loeb.loeb_section_zero_or_full_of_ae_periods
#check @Erdos335.Loeb.loeb_essential_periodic_core_of_ae_periods
#print axioms Erdos335.Loeb.loeb_essential_periodic_core_of_ae_periods
#check @Erdos335.Loeb.loeb_irreducible_sum_ae_periods_of_input
#print axioms Erdos335.Loeb.loeb_irreducible_sum_ae_periods_of_input
#check @Erdos335.Loeb.loeb_ae_periodic_sum_core_classification
#print axioms Erdos335.Loeb.loeb_ae_periodic_sum_core_classification
#check @Erdos335.Loeb.loeb_neg_congr_ae
#print axioms Erdos335.Loeb.loeb_neg_congr_ae
#check @Erdos335.Loeb.loeb_ae_period_compl
#print axioms Erdos335.Loeb.loeb_ae_period_compl
#check @Erdos335.Loeb.loeb_ae_period_of_neg
#print axioms Erdos335.Loeb.loeb_ae_period_of_neg
#check @Erdos335.Loeb.loeb_quasiPeriodic_null_active_ae_periods
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_null_active_ae_periods
#check @Erdos335.Loeb.loeb_irreducible_of_no_positive_ae_periods
#print axioms Erdos335.Loeb.loeb_irreducible_of_no_positive_ae_periods
#check @Erdos335.Loeb.loeb_complement_dual_structure
#print axioms Erdos335.Loeb.loeb_complement_dual_structure
#check @Erdos335.Loeb.MeasureIrreducible.full_measure_restriction
#print axioms Erdos335.Loeb.MeasureIrreducible.full_measure_restriction
#check @Erdos335.Loeb.loeb_irreducible_full_measure_restriction
#print axioms Erdos335.Loeb.loeb_irreducible_full_measure_restriction
#check @Erdos335.Loeb.loeb_aperiodic_full_measure_restriction
#print axioms Erdos335.Loeb.loeb_aperiodic_full_measure_restriction
#check @Erdos335.Loeb.loeb_quasiPeriodic_complement_core
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_complement_core
#check @Erdos335.Loeb.loeb_quasiPeriodic_active_mass_bounds
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_active_mass_bounds
#check @Erdos335.Loeb.loeb_strict_dyson_complement_core
#print axioms Erdos335.Loeb.loeb_strict_dyson_complement_core
#check @Erdos335.Loeb.QuasiPeriodicDecomposition.loebNeg
#print axioms Erdos335.Loeb.QuasiPeriodicDecomposition.loebNeg
#check @Erdos335.Loeb.loeb_strict_dyson_positive_background_model
#print axioms Erdos335.Loeb.loeb_strict_dyson_positive_background_model
#check @Erdos335.Loeb.loeb_quasiPeriodic_pair_of_strict_background_data
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_pair_of_strict_background_data
#check @Erdos335.Loeb.loeb_quasiPeriodic_pair_of_positive_background_data
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_pair_of_positive_background_data
#check @Erdos335.Loeb.loeb_quasiPeriodic_active_irreducible
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_active_irreducible
#check @Erdos335.Loeb.loeb_quasiPeriodic_active_structure
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_active_structure
#check @Erdos335.Loeb.loeb_quasiPeriodic_pair_of_full_measure_partner
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_pair_of_full_measure_partner
#check @Erdos335.Loeb.loeb_quasiPeriodic_active_positive_of_irreducible
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_active_positive_of_irreducible
#check @Erdos335.Loeb.loeb_pair_of_negative_full_measure_partner
#print axioms Erdos335.Loeb.loeb_pair_of_negative_full_measure_partner
#check @Erdos335.Loeb.loeb_pair_of_negative_positive_background
#print axioms Erdos335.Loeb.loeb_pair_of_negative_positive_background
#check @Erdos335.Loeb.loeb_quasiPeriodic_pair_of_large_output_model
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_pair_of_large_output_model
#check @Erdos335.Loeb.loeb_strict_dyson_quasiPeriodic_pair
#print axioms Erdos335.Loeb.loeb_strict_dyson_quasiPeriodic_pair
#check @Erdos335.Loeb.loeb_irreducible_translate_right
#print axioms Erdos335.Loeb.loeb_irreducible_translate_right
#check @Erdos335.Loeb.loeb_nonextendible_translate_right
#print axioms Erdos335.Loeb.loeb_nonextendible_translate_right
#check @Erdos335.Loeb.QuasiPeriodicPairData.loebTranslateRight
#print axioms Erdos335.Loeb.QuasiPeriodicPairData.loebTranslateRight
#check @Erdos335.Loeb.loeb_general_strict_dyson_quasiPeriodic_pair
#print axioms Erdos335.Loeb.loeb_general_strict_dyson_quasiPeriodic_pair
#check @Erdos335.Loeb.exists_shrinking_parameter_in_irreducible_compact_factor
#print axioms Erdos335.Loeb.exists_shrinking_parameter_in_irreducible_compact_factor
#check @Erdos335.Loeb.dyson_mass_tendsto_zero
#print axioms Erdos335.Loeb.dyson_mass_tendsto_zero
#check @Erdos335.Loeb.preimage_dysonGroupLeft
#print axioms Erdos335.Loeb.preimage_dysonGroupLeft
#check @Erdos335.Loeb.preimage_dysonGroupRight
#print axioms Erdos335.Loeb.preimage_dysonGroupRight
#check @Erdos335.Loeb.loeb_compact_dyson_step_or_quasiPeriodic
#print axioms Erdos335.Loeb.loeb_compact_dyson_step_or_quasiPeriodic
#check @Erdos335.Loeb.QuasiPeriodicPairData.loebSum
#print axioms Erdos335.Loeb.QuasiPeriodicPairData.loebSum
#check @Erdos335.Loeb.loeb_quasiPeriodic_pair_of_equal_sum_model
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_pair_of_equal_sum_model
#check @Erdos335.Loeb.loeb_equal_sum_model_structure
#print axioms Erdos335.Loeb.loeb_equal_sum_model_structure
#check @Erdos335.Loeb.measurableSet_of_sigmaCompact
#print axioms Erdos335.Loeb.measurableSet_of_sigmaCompact
#check @Erdos335.Loeb.isSigmaCompact_add_sets
#print axioms Erdos335.Loeb.isSigmaCompact_add_sets
#check @Erdos335.Loeb.isSigmaCompact_dysonGroup
#print axioms Erdos335.Loeb.isSigmaCompact_dysonGroup
#check @Erdos335.Loeb.loeb_compact_dyson_sequence_or_quasiPeriodic
#print axioms Erdos335.Loeb.loeb_compact_dyson_sequence_or_quasiPeriodic
#check @Erdos335.Loeb.ae_map_set_eq_of_preimage
#print axioms Erdos335.Loeb.ae_map_set_eq_of_preimage
#check @Erdos335.Loeb.compact_factor_shrinking_sumsets_localize
#print axioms Erdos335.Loeb.compact_factor_shrinking_sumsets_localize
#check @Erdos335.Loeb.dyson_chain_coset_ancestry
#print axioms Erdos335.Loeb.dyson_chain_coset_ancestry
#check @Erdos335.Loeb.loeb_quasiPeriodic_pair_of_one_coset_and_nonconcentration
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_pair_of_one_coset_and_nonconcentration
#check @Erdos335.Loeb.loeb_compact_small_open_subgroup_quasiPeriodic
#print axioms Erdos335.Loeb.loeb_compact_small_open_subgroup_quasiPeriodic
#check @Erdos335.Loeb.loeb_compact_quasiPeriodic_or_open_connected
#print axioms Erdos335.Loeb.loeb_compact_quasiPeriodic_or_open_connected
#check @Erdos335.tendsto_of_separated_approximants
#print axioms Erdos335.tendsto_of_separated_approximants
#check @Erdos335.tendsto_of_finite_approximants
#print axioms Erdos335.tendsto_of_finite_approximants
#check @Erdos335.tendsto_of_finite_template_approximation
#print axioms Erdos335.tendsto_of_finite_template_approximation
#check @Erdos335.Loeb.exists_exact_invariant_ae_average
#print axioms Erdos335.Loeb.exists_exact_invariant_ae_average
#check @Erdos335.Loeb.exists_exact_invariant_ae_set
#print axioms Erdos335.Loeb.exists_exact_invariant_ae_set
#check @Erdos335.Loeb.exists_compact_addHaar_probability
#print axioms Erdos335.Loeb.exists_compact_addHaar_probability
#check @Erdos335.Loeb.exists_sigmaCompact_quotient_representative
#print axioms Erdos335.Loeb.exists_sigmaCompact_quotient_representative
#check @Erdos335.Loeb.quotient_representative_has_trivial_ae_stabilizer
#print axioms Erdos335.Loeb.quotient_representative_has_trivial_ae_stabilizer
#check @Erdos335.Loeb.exists_aperiodic_quotient_representative
#print axioms Erdos335.Loeb.exists_aperiodic_quotient_representative
#check @Erdos335.Loeb.exists_aestabilizer_quotient_representative
#print axioms Erdos335.Loeb.exists_aestabilizer_quotient_representative
#check @Erdos335.Loeb.MeasureIrreducible.of_ae_pair
#print axioms Erdos335.Loeb.MeasureIrreducible.of_ae_pair
#check @Erdos335.Loeb.compact_factor_nonextendible_inputs_ae_period
#print axioms Erdos335.Loeb.compact_factor_nonextendible_inputs_ae_period
#check @Erdos335.Loeb.exists_sigmaCompact_positive_intersection_cores
#print axioms Erdos335.Loeb.exists_sigmaCompact_positive_intersection_cores
#check @Erdos335.Loeb.compactIntersectionProfile_translate_left
#print axioms Erdos335.Loeb.compactIntersectionProfile_translate_left
#check @Erdos335.Loeb.compactIntersectionProfile_period_of_ae
#print axioms Erdos335.Loeb.compactIntersectionProfile_period_of_ae
#check @Erdos335.Loeb.positive_intersection_support_periodic
#print axioms Erdos335.Loeb.positive_intersection_support_periodic
#check @Erdos335.Loeb.preimage_image_subset_of_ker_invariant
#print axioms Erdos335.Loeb.preimage_image_subset_of_ker_invariant
#check @Erdos335.Loeb.preimage_image_eq_of_ker_invariant
#print axioms Erdos335.Loeb.preimage_image_eq_of_ker_invariant
#check @Erdos335.Loeb.preimage_image_add_eq_of_ker_invariant
#print axioms Erdos335.Loeb.preimage_image_add_eq_of_ker_invariant
#check @Erdos335.Loeb.exists_quotient_pair_cores
#print axioms Erdos335.Loeb.exists_quotient_pair_cores
#check @Erdos335.Loeb.loeb_compact_aperiodic_quotient_pair
#print axioms Erdos335.Loeb.loeb_compact_aperiodic_quotient_pair
#check @Erdos335.Loeb.loeb_compact_pair_in_open_cosets_or_quasiPeriodic
#print axioms Erdos335.Loeb.loeb_compact_pair_in_open_cosets_or_quasiPeriodic
#check @Erdos335.Loeb.loeb_compact_quasiPeriodic_or_connected_cosets
#print axioms Erdos335.Loeb.loeb_compact_quasiPeriodic_or_connected_cosets
#check @Erdos335.Loeb.loeb_ae_pair_model_structure
#print axioms Erdos335.Loeb.loeb_ae_pair_model_structure
#check @Erdos335.Loeb.integral_translate_character
#print axioms Erdos335.Loeb.integral_translate_character
#check @Erdos335.Loeb.character_eq_one_of_period_and_nonzero_coefficient
#print axioms Erdos335.Loeb.character_eq_one_of_period_and_nonzero_coefficient
#check @Erdos335.Loeb.fourier_character_trivial_on_ae_stabilizer
#print axioms Erdos335.Loeb.fourier_character_trivial_on_ae_stabilizer
#check @Erdos335.Loeb.haarOverlap_add_lower_bound
#print axioms Erdos335.Loeb.haarOverlap_add_lower_bound
#check @Erdos335.Loeb.haarOverlap_nsmul_loss_le
#print axioms Erdos335.Loeb.haarOverlap_nsmul_loss_le
#check @Erdos335.Loeb.haarOverlap_nsmul_loss_le_of_sumset
#print axioms Erdos335.Loeb.haarOverlap_nsmul_loss_le_of_sumset
#check @Erdos335.Loeb.loeb_quotient_quasiPeriodic_or_connected_cosets
#print axioms Erdos335.Loeb.loeb_quotient_quasiPeriodic_or_connected_cosets
#check @Erdos335.Loeb.exists_nontrivial_internal_period_character
#print axioms Erdos335.Loeb.exists_nontrivial_internal_period_character
#check @Erdos335.Loeb.exists_continuous_quotient_character
#print axioms Erdos335.Loeb.exists_continuous_quotient_character
#check @Erdos335.Loeb.exists_nontrivial_quotient_character_of_essential_periods
#print axioms Erdos335.Loeb.exists_nontrivial_quotient_character_of_essential_periods
#check @Erdos335.Loeb.exists_positive_haarOverlap_loss_on_compact
#print axioms Erdos335.Loeb.exists_positive_haarOverlap_loss_on_compact
#check @Erdos335.Loeb.exists_uniform_scaled_difference_mass_lower_bound
#print axioms Erdos335.Loeb.exists_uniform_scaled_difference_mass_lower_bound
#check @Erdos335.Loeb.continuous_circle_hom_surjective_of_ne_zero
#print axioms Erdos335.Loeb.continuous_circle_hom_surjective_of_ne_zero
#check @Erdos335.Loeb.exists_unitCircle_addEquiv
#print axioms Erdos335.Loeb.exists_unitCircle_addEquiv
#check @Erdos335.Loeb.continuous_additiveCircle_hom_surjective_of_ne_zero
#print axioms Erdos335.Loeb.continuous_additiveCircle_hom_surjective_of_ne_zero
#check @Erdos335.Loeb.exists_circle_power_nonpositive_real
#print axioms Erdos335.Loeb.exists_circle_power_nonpositive_real
#check @Erdos335.Loeb.exists_character_width_mass_bound
#print axioms Erdos335.Loeb.exists_character_width_mass_bound
#check @Erdos335.Loeb.integral_subgroup_average
#print axioms Erdos335.Loeb.integral_subgroup_average
#check @Erdos335.Loeb.subgroup_fiber_measure_bound
#print axioms Erdos335.Loeb.subgroup_fiber_measure_bound
#check @Erdos335.Loeb.measure_le_invariant_container_mul_fiber_diameter
#print axioms Erdos335.Loeb.measure_le_invariant_container_mul_fiber_diameter
#check @Erdos335.Loeb.singleton_measure_zero_of_infinite_invariant
#print axioms Erdos335.Loeb.singleton_measure_zero_of_infinite_invariant
#check @Erdos335.Loeb.exists_small_open_identity_neighborhood
#print axioms Erdos335.Loeb.exists_small_open_identity_neighborhood
#check @Erdos335.Loeb.finite_fiber_group_of_localized_containers
#print axioms Erdos335.Loeb.finite_fiber_group_of_localized_containers
#check @Erdos335.Loeb.norm_unitAddCircle_eq_arg
#print axioms Erdos335.Loeb.norm_unitAddCircle_eq_arg
#check @Erdos335.Loeb.map_haar_unitAddCircle_eq_volume
#print axioms Erdos335.Loeb.map_haar_unitAddCircle_eq_volume
#check @Erdos335.Loeb.measure_character_closedBall_preimage_le
#print axioms Erdos335.Loeb.measure_character_closedBall_preimage_le
#check @Erdos335.Loeb.exists_character_invariant_containers
#print axioms Erdos335.Loeb.exists_character_invariant_containers
#check @Erdos335.Loeb.finite_character_kernel_of_localized_critical_pairs
#print axioms Erdos335.Loeb.finite_character_kernel_of_localized_critical_pairs
#check @Erdos335.Loeb.loeb_compact_quasiPeriodic_or_finite_character_kernel
#print axioms Erdos335.Loeb.loeb_compact_quasiPeriodic_or_finite_character_kernel
#check @Erdos335.Loeb.isCoveringMap_of_finite_circle_kernel
#print axioms Erdos335.Loeb.isCoveringMap_of_finite_circle_kernel
#check @Erdos335.Loeb.exists_real_hom_lift_of_circle_cover
#print axioms Erdos335.Loeb.exists_real_hom_lift_of_circle_cover
#check @Erdos335.Loeb.real_hom_lift_of_circle_cover_surjective
#print axioms Erdos335.Loeb.real_hom_lift_of_circle_cover_surjective
#check @Erdos335.Loeb.exists_positive_integer_period_of_real_lift
#print axioms Erdos335.Loeb.exists_positive_integer_period_of_real_lift
#check @Erdos335.Loeb.exists_circle_addEquiv_of_finite_character_kernel
#print axioms Erdos335.Loeb.exists_circle_addEquiv_of_finite_character_kernel
#check @Erdos335.Loeb.loeb_compact_quasiPeriodic_or_circle_model
#print axioms Erdos335.Loeb.loeb_compact_quasiPeriodic_or_circle_model
#check @Erdos335.Loeb.exists_internal_character_detecting_nonperiod
#print axioms Erdos335.Loeb.exists_internal_character_detecting_nonperiod
#check @Erdos335.Loeb.exists_quotient_character_detecting_nonperiod
#print axioms Erdos335.Loeb.exists_quotient_character_detecting_nonperiod
#check @Erdos335.Loeb.exists_quotient_character_separating_zero
#print axioms Erdos335.Loeb.exists_quotient_character_separating_zero
#check @Erdos335.Loeb.exists_nontrivial_character_on_quotient_subgroup
#print axioms Erdos335.Loeb.exists_nontrivial_character_on_quotient_subgroup
#check @Erdos335.Loeb.dysonGroup_preserves_cosets
#print axioms Erdos335.Loeb.dysonGroup_preserves_cosets
#check @Erdos335.Loeb.dyson_chain_preserves_cosets
#print axioms Erdos335.Loeb.dyson_chain_preserves_cosets
#check @Erdos335.Loeb.exists_normalized_open_subgroup_measure
#print axioms Erdos335.Loeb.exists_normalized_open_subgroup_measure
#check @Erdos335.Loeb.subgroup_measure_preimage
#print axioms Erdos335.Loeb.subgroup_measure_preimage
#check @Erdos335.Loeb.subgroup_preimage_add
#print axioms Erdos335.Loeb.subgroup_preimage_add
#check @Erdos335.Loeb.ae_eq_subgroup_iff
#print axioms Erdos335.Loeb.ae_eq_subgroup_iff
#check @Erdos335.Loeb.ae_period_subgroup_iff
#print axioms Erdos335.Loeb.ae_period_subgroup_iff
#check @Erdos335.Loeb.finite_character_kernel_on_connected_open_subgroup
#print axioms Erdos335.Loeb.finite_character_kernel_on_connected_open_subgroup
#check @Erdos335.Loeb.loeb_compact_quasiPeriodic_or_finite_open_character_kernel
#print axioms Erdos335.Loeb.loeb_compact_quasiPeriodic_or_finite_open_character_kernel
#check @Erdos335.Loeb.loeb_compact_quasiPeriodic_or_open_circle_model
#print axioms Erdos335.Loeb.loeb_compact_quasiPeriodic_or_open_circle_model
#check @Erdos335.Loeb.translate_pair_sum
#print axioms Erdos335.Loeb.translate_pair_sum
#check @Erdos335.Loeb.translate_set_difference
#print axioms Erdos335.Loeb.translate_set_difference
#check @Erdos335.Loeb.ae_period_translate_iff
#print axioms Erdos335.Loeb.ae_period_translate_iff
#check @Erdos335.Loeb.finite_character_kernel_on_connected_cosets
#print axioms Erdos335.Loeb.finite_character_kernel_on_connected_cosets
#check @Erdos335.Loeb.loeb_compact_quasiPeriodic_or_coset_circle_model
#print axioms Erdos335.Loeb.loeb_compact_quasiPeriodic_or_coset_circle_model
#check @Erdos335.Loeb.nontrivial_subgroup_of_positive_critical_cosets
#print axioms Erdos335.Loeb.nontrivial_subgroup_of_positive_critical_cosets
#check @Erdos335.Loeb.loeb_compact_quasiPeriodic_or_circle_cosets
#print axioms Erdos335.Loeb.loeb_compact_quasiPeriodic_or_circle_cosets
#check @Erdos335.Loeb.loeb_essential_quotient_quasiPeriodic_or_circle_cosets
#print axioms Erdos335.Loeb.loeb_essential_quotient_quasiPeriodic_or_circle_cosets
#check @Erdos335.Loeb.derivative_alternating_sum_le_of_varying_increment_bounds
#print axioms Erdos335.Loeb.derivative_alternating_sum_le_of_varying_increment_bounds
#check @Erdos335.Loeb.derivative_alternating_sum_le_of_increment_bounds
#print axioms Erdos335.Loeb.derivative_alternating_sum_le_of_increment_bounds
#check @Erdos335.Loeb.interval_integral_translation_endpoints
#print axioms Erdos335.Loeb.interval_integral_translation_endpoints
#check @Erdos335.Loeb.derivative_alternating_sum_le_of_translation_integrals
#print axioms Erdos335.Loeb.derivative_alternating_sum_le_of_translation_integrals
#check @Erdos335.Loeb.derivative_alternating_sum_le_of_varying_translation_integrals
#print axioms Erdos335.Loeb.derivative_alternating_sum_le_of_varying_translation_integrals
#check @Erdos335.Loeb.ae_interval_of_order_convex_on_full_measure_set
#print axioms Erdos335.Loeb.ae_interval_of_order_convex_on_full_measure_set
#check @Erdos335.Loeb.two_interval_integrals_le_positive_part
#print axioms Erdos335.Loeb.two_interval_integrals_le_positive_part
#check @Erdos335.Loeb.two_interval_translation_integrals_le
#print axioms Erdos335.Loeb.two_interval_translation_integrals_le
#check @Erdos335.Loeb.ae_interval_of_sharp_translation_bound
#print axioms Erdos335.Loeb.ae_interval_of_sharp_translation_bound
#check @Erdos335.Loeb.exists_endpoints_cover_measure
#print axioms Erdos335.Loeb.exists_endpoints_cover_measure
#check @Erdos335.Loeb.exists_localized_endpoint_sequence
#print axioms Erdos335.Loeb.exists_localized_endpoint_sequence
#check @Erdos335.Loeb.exists_zero_derivative_indicator_point
#print axioms Erdos335.Loeb.exists_zero_derivative_indicator_point
#check @Erdos335.Loeb.haarOverlap_neg_eq
#print axioms Erdos335.Loeb.haarOverlap_neg_eq
#check @Erdos335.Loeb.haarOverlap_loss_eq_positive_part_integral
#print axioms Erdos335.Loeb.haarOverlap_loss_eq_positive_part_integral
#check @Erdos335.Loeb.unitCircle_overlap_loss_eq_interval_integral
#print axioms Erdos335.Loeb.unitCircle_overlap_loss_eq_interval_integral
#check @Erdos335.Loeb.hasDerivAt_left_constant_extension
#print axioms Erdos335.Loeb.hasDerivAt_left_constant_extension
#check @Erdos335.Loeb.primitive_upper_cutoff
#print axioms Erdos335.Loeb.primitive_upper_cutoff
#check @Erdos335.Loeb.hasDerivAt_upper_cutoff_primitive
#print axioms Erdos335.Loeb.hasDerivAt_upper_cutoff_primitive
#check @Erdos335.Loeb.periodic_cutoff_translation_loss_le
#print axioms Erdos335.Loeb.periodic_cutoff_translation_loss_le
#check @Erdos335.Loeb.periodic_primitive_add_one
#print axioms Erdos335.Loeb.periodic_primitive_add_one
#check @Erdos335.Loeb.periodic_primitive_derivative_zero_one
#print axioms Erdos335.Loeb.periodic_primitive_derivative_zero_one
#check @Erdos335.Loeb.unit_interval_cutoff_derivative_zero
#print axioms Erdos335.Loeb.unit_interval_cutoff_derivative_zero
#check @Erdos335.Loeb.periodic_unit_cutoff_derivative_zero
#print axioms Erdos335.Loeb.periodic_unit_cutoff_derivative_zero
#check @Erdos335.Loeb.periodic_indicator_ae_interval_of_translation_bound
#print axioms Erdos335.Loeb.periodic_indicator_ae_interval_of_translation_bound
#check @Erdos335.Loeb.shifted_primitive_derivative_zero
#print axioms Erdos335.Loeb.shifted_primitive_derivative_zero
#check @Erdos335.Loeb.volume_centered_circle_lift
#print axioms Erdos335.Loeb.volume_centered_circle_lift
#check @Erdos335.Loeb.centered_circle_lift_in_small_interval
#print axioms Erdos335.Loeb.centered_circle_lift_in_small_interval
#check @Erdos335.Loeb.haarOverlap_translate_eq
#print axioms Erdos335.Loeb.haarOverlap_translate_eq
#check @Erdos335.Loeb.volume_unitCircle_lift_openInterval
#print axioms Erdos335.Loeb.volume_unitCircle_lift_openInterval
#check @Erdos335.Loeb.exists_unitCircle_regular_cut
#print axioms Erdos335.Loeb.exists_unitCircle_regular_cut
#check @Erdos335.Loeb.exists_unitCircle_localized_endpoints
#print axioms Erdos335.Loeb.exists_unitCircle_localized_endpoints
#check @Erdos335.Loeb.exists_unitCircle_difference_sequence
#print axioms Erdos335.Loeb.exists_unitCircle_difference_sequence
#check @Erdos335.Loeb.unitCircle_critical_overlap_loss_le
#print axioms Erdos335.Loeb.unitCircle_critical_overlap_loss_le
#check @Erdos335.Loeb.exists_unitCircle_sharp_translation_sequence
#print axioms Erdos335.Loeb.exists_unitCircle_sharp_translation_sequence
#check @Erdos335.Loeb.unitCircle_ae_interval_cut_of_localized_critical_pairs
#print axioms Erdos335.Loeb.unitCircle_ae_interval_cut_of_localized_critical_pairs
#check @Erdos335.Loeb.unitCircle_openArc_preimage
#print axioms Erdos335.Loeb.unitCircle_openArc_preimage
#check @Erdos335.Loeb.unitCircle_ae_eq_openArc_of_cut
#print axioms Erdos335.Loeb.unitCircle_ae_eq_openArc_of_cut
#check @Erdos335.Loeb.volume_unitCircle_openArc
#print axioms Erdos335.Loeb.volume_unitCircle_openArc
#check @Erdos335.Loeb.unitCircle_ae_arc_of_localized_critical_pairs
#print axioms Erdos335.Loeb.unitCircle_ae_arc_of_localized_critical_pairs
#check @Erdos335.Loeb.loeb_unitCircle_sum_ae_arc_or_quasiPeriodic
#print axioms Erdos335.Loeb.loeb_unitCircle_sum_ae_arc_or_quasiPeriodic
#check @Erdos335.Loeb.MeasureIrreducible.sum_ae_period_of_left
#print axioms Erdos335.Loeb.MeasureIrreducible.sum_ae_period_of_left
#check @Erdos335.Loeb.compact_factor_irreducible_sum_ae_period_of_left
#print axioms Erdos335.Loeb.compact_factor_irreducible_sum_ae_period_of_left
#check @Erdos335.Loeb.compact_factor_left_aperiodic_of_sum_aperiodic
#print axioms Erdos335.Loeb.compact_factor_left_aperiodic_of_sum_aperiodic
#check @Erdos335.Loeb.loeb_unitCircle_measurable_sum_ae_arc_or_quasiPeriodic
#print axioms Erdos335.Loeb.loeb_unitCircle_measurable_sum_ae_arc_or_quasiPeriodic
#check @Erdos335.Loeb.surjective_circle_restriction_of_positive_loeb_subgroup
#print axioms Erdos335.Loeb.surjective_circle_restriction_of_positive_loeb_subgroup
#check @Erdos335.Loeb.map_restrict_subgroup_unitCircle
#print axioms Erdos335.Loeb.map_restrict_subgroup_unitCircle
#check @Erdos335.Loeb.loeb_circle_subgroup_intersection_measure
#print axioms Erdos335.Loeb.loeb_circle_subgroup_intersection_measure
#check @Erdos335.Loeb.loeb_circle_coset_intersection_measure
#print axioms Erdos335.Loeb.loeb_circle_coset_intersection_measure
#check @Erdos335.Loeb.circle_pullback_quasiPeriodic_background_empty
#print axioms Erdos335.Loeb.circle_pullback_quasiPeriodic_background_empty
#check @Erdos335.Loeb.not_quasiPeriodic_pair_of_proper_circle_pullbacks
#print axioms Erdos335.Loeb.not_quasiPeriodic_pair_of_proper_circle_pullbacks
#check @Erdos335.Loeb.loeb_unitCircle_critical_inputs_measure_lt_one
#print axioms Erdos335.Loeb.loeb_unitCircle_critical_inputs_measure_lt_one
#check @Erdos335.Loeb.loeb_unitCircle_sum_ae_arc
#print axioms Erdos335.Loeb.loeb_unitCircle_sum_ae_arc
#check @Erdos335.Loeb.unitCircle_compl_openArc
#print axioms Erdos335.Loeb.unitCircle_compl_openArc
#check @Erdos335.Loeb.unitCircle_complement_ae_closedArc
#print axioms Erdos335.Loeb.unitCircle_complement_ae_closedArc
#check @Erdos335.Loeb.loeb_unitCircle_complement_ae_arc
#print axioms Erdos335.Loeb.loeb_unitCircle_complement_ae_arc
#check @Erdos335.Loeb.UnitCircleClosedArcModel
#print axioms Erdos335.Loeb.UnitCircleClosedArcModel
#check @Erdos335.Loeb.unitCircle_closedArcModel_of_complement_arc
#print axioms Erdos335.Loeb.unitCircle_closedArcModel_of_complement_arc
#check @Erdos335.Loeb.loeb_unitCircle_pair_ae_closedArcs
#print axioms Erdos335.Loeb.loeb_unitCircle_pair_ae_closedArcs
#check @Erdos335.Loeb.unitCircle_translate_image
#print axioms Erdos335.Loeb.unitCircle_translate_image
#check @Erdos335.Loeb.volume_unitCircle_openArc_of_width
#print axioms Erdos335.Loeb.volume_unitCircle_openArc_of_width
#check @Erdos335.Loeb.unitCircle_closedArc_ae_openArc
#print axioms Erdos335.Loeb.unitCircle_closedArc_ae_openArc
#check @Erdos335.Loeb.volume_unitCircle_closedArc_of_width
#print axioms Erdos335.Loeb.volume_unitCircle_closedArc_of_width
#check @Erdos335.Loeb.unitCircle_zero_closedArc_add
#print axioms Erdos335.Loeb.unitCircle_zero_closedArc_add
#check @Erdos335.Loeb.unitCircle_translate_closedArc_subset_iff
#print axioms Erdos335.Loeb.unitCircle_translate_closedArc_subset_iff
#check @Erdos335.Loeb.closure_unitCircle_openArc
#print axioms Erdos335.Loeb.closure_unitCircle_openArc
#check @Erdos335.Loeb.support_unitCircle_closedArc
#print axioms Erdos335.Loeb.support_unitCircle_closedArc
#check @Erdos335.Loeb.add_support_subset_of_sum_ae_subset
#print axioms Erdos335.Loeb.add_support_subset_of_sum_ae_subset
#check @Erdos335.Loeb.unitCircle_normalized_closedArcModel
#print axioms Erdos335.Loeb.unitCircle_normalized_closedArcModel
#check @Erdos335.Loeb.volume_unitCircle_normalized_closedArc
#print axioms Erdos335.Loeb.volume_unitCircle_normalized_closedArc
#check @Erdos335.Loeb.MeasureIrreducible.sum_ae_subset_of_ae_containers
#print axioms Erdos335.Loeb.MeasureIrreducible.sum_ae_subset_of_ae_containers
#check @Erdos335.Loeb.support_unitCircle_translated_closedArc
#print axioms Erdos335.Loeb.support_unitCircle_translated_closedArc
#check @Erdos335.Loeb.unitCircle_translated_closedArc_erosion
#print axioms Erdos335.Loeb.unitCircle_translated_closedArc_erosion
#check @Erdos335.Loeb.unitCircle_left_subset_of_ae_sum_container
#print axioms Erdos335.Loeb.unitCircle_left_subset_of_ae_sum_container
#check @Erdos335.Loeb.loeb_unitCircle_literal_containment
#print axioms Erdos335.Loeb.loeb_unitCircle_literal_containment
#check @Erdos335.Loeb.loeb_unitCircle_inverse
#print axioms Erdos335.Loeb.loeb_unitCircle_inverse
#check @Erdos335.Loeb.loeb_connected_compact_quasiPeriodic_or_closedArcs
#print axioms Erdos335.Loeb.loeb_connected_compact_quasiPeriodic_or_closedArcs
#check @Erdos335.Loeb.loebOuterMeasure_map_coordinateEquiv
#print axioms Erdos335.Loeb.loebOuterMeasure_map_coordinateEquiv
#check @Erdos335.Loeb.loebMeasure_preimage_coordinateEquiv
#print axioms Erdos335.Loeb.loebMeasure_preimage_coordinateEquiv
#check @Erdos335.Loeb.measurable_coordinateEquiv
#print axioms Erdos335.Loeb.measurable_coordinateEquiv
#check @Erdos335.Loeb.productMap_injective
#print axioms Erdos335.Loeb.productMap_injective
#check @Erdos335.Loeb.internalSet_image
#print axioms Erdos335.Loeb.internalSet_image
#check @Erdos335.Loeb.range_productMap
#print axioms Erdos335.Loeb.range_productMap
#check @Erdos335.Loeb.loebMeasure_eq_iInf_internal_supersets
#print axioms Erdos335.Loeb.loebMeasure_eq_iInf_internal_supersets
#check @Erdos335.Loeb.countingRatio_image_injection
#print axioms Erdos335.Loeb.countingRatio_image_injection
#check @Erdos335.Loeb.ultraCount_image_injection
#print axioms Erdos335.Loeb.ultraCount_image_injection
#check @Erdos335.Loeb.loebMeasure_internal_image_injection
#print axioms Erdos335.Loeb.loebMeasure_internal_image_injection
#check @Erdos335.Loeb.loebMeasure_image_injection
#print axioms Erdos335.Loeb.loebMeasure_image_injection
#check @Erdos335.Loeb.measurable_positive_internal_injection
#print axioms Erdos335.Loeb.measurable_positive_internal_injection
#check @Erdos335.Loeb.measurableSet_image_positive_internal_injection
#print axioms Erdos335.Loeb.measurableSet_image_positive_internal_injection
#check @Erdos335.Loeb.measurableEmbedding_positive_internal_injection
#print axioms Erdos335.Loeb.measurableEmbedding_positive_internal_injection
#check @Erdos335.Loeb.internalInnerMeasure_image_injection
#print axioms Erdos335.Loeb.internalInnerMeasure_image_injection
#check @Erdos335.Loeb.cyclicSubgroupOrders
#print axioms Erdos335.Loeb.cyclicSubgroupOrders
#check @Erdos335.Loeb.cyclicSubgroupCoordinate
#print axioms Erdos335.Loeb.cyclicSubgroupCoordinate
#check @Erdos335.Loeb.cyclicSubgroupCoordinate_injective
#print axioms Erdos335.Loeb.cyclicSubgroupCoordinate_injective
#check @Erdos335.Loeb.cyclicSubgroupCoordinate_range
#print axioms Erdos335.Loeb.cyclicSubgroupCoordinate_range
#check @Erdos335.Loeb.cyclicSubgroupCoordinates_range
#print axioms Erdos335.Loeb.cyclicSubgroupCoordinates_range
#check @Erdos335.Loeb.positive_measurable_subgroup_has_cyclic_coordinates
#print axioms Erdos335.Loeb.positive_measurable_subgroup_has_cyclic_coordinates
#check @Erdos335.Loeb.loeb_irreducible_of_internal_embedding
#print axioms Erdos335.Loeb.loeb_irreducible_of_internal_embedding
#check @Erdos335.Loeb.loeb_nonextendible_of_internal_embedding
#print axioms Erdos335.Loeb.loeb_nonextendible_of_internal_embedding
#check @Erdos335.Loeb.image_vadd_addHom
#print axioms Erdos335.Loeb.image_vadd_addHom
#check @Erdos335.Loeb.loeb_image_ae_eq_iff
#print axioms Erdos335.Loeb.loeb_image_ae_eq_iff
#check @Erdos335.Loeb.loeb_no_positive_periods_of_internal_embedding
#print axioms Erdos335.Loeb.loeb_no_positive_periods_of_internal_embedding
#check @Erdos335.Loeb.positive_loeb_subgroup_normalized_coordinates
#print axioms Erdos335.Loeb.positive_loeb_subgroup_normalized_coordinates
#check @Erdos335.Loeb.exists_loeb_open_subgroup_coordinates
#print axioms Erdos335.Loeb.exists_loeb_open_subgroup_coordinates
#check @Erdos335.Loeb.loeb_complement_pos_of_no_positive_periods
#print axioms Erdos335.Loeb.loeb_complement_pos_of_no_positive_periods
#check @Erdos335.Loeb.image_preimage_subgroup_factor
#print axioms Erdos335.Loeb.image_preimage_subgroup_factor
#check @Erdos335.Loeb.subgroup_factor_preimage_add
#print axioms Erdos335.Loeb.subgroup_factor_preimage_add
#check @Erdos335.Loeb.normalized_open_subgroup_measure
#print axioms Erdos335.Loeb.normalized_open_subgroup_measure
#check @Erdos335.Loeb.subgroup_circle_aperiodic
#print axioms Erdos335.Loeb.subgroup_circle_aperiodic
#check @Erdos335.Loeb.subgroup_circle_container_transfer
#print axioms Erdos335.Loeb.subgroup_circle_container_transfer
#check @Erdos335.Loeb.loeb_open_circle_inverse
#print axioms Erdos335.Loeb.loeb_open_circle_inverse
#check @Erdos335.Loeb.loeb_irreducible_translate_pair
#print axioms Erdos335.Loeb.loeb_irreducible_translate_pair
#check @Erdos335.Loeb.loeb_nonextendible_translate_pair
#print axioms Erdos335.Loeb.loeb_nonextendible_translate_pair
#check @Erdos335.Loeb.loeb_ae_period_translate_iff
#print axioms Erdos335.Loeb.loeb_ae_period_translate_iff
#check @Erdos335.Loeb.loeb_circle_coset_inverse
#print axioms Erdos335.Loeb.loeb_circle_coset_inverse
#check @Erdos335.Loeb.loeb_compact_quasiPeriodic_or_closedArc_cosets
#print axioms Erdos335.Loeb.loeb_compact_quasiPeriodic_or_closedArc_cosets
#check @Erdos335.Loeb.loeb_quotient_quasiPeriodic_or_closedArc_cosets
#print axioms Erdos335.Loeb.loeb_quotient_quasiPeriodic_or_closedArc_cosets
#check @Erdos335.Loeb.loeb_add_support_subset_of_ae_sum_container
#print axioms Erdos335.Loeb.loeb_add_support_subset_of_ae_sum_container
#check @Erdos335.Loeb.exists_continuous_circle_character_extension
#print axioms Erdos335.Loeb.exists_continuous_circle_character_extension
#check @Erdos335.Loeb.exists_surjective_continuous_circle_character_extension
#print axioms Erdos335.Loeb.exists_surjective_continuous_circle_character_extension
#check @Erdos335.Loeb.subgroup_character_coset_preimage
#print axioms Erdos335.Loeb.subgroup_character_coset_preimage
#check @Erdos335.Loeb.loeb_unitCircle_left_subset_of_ae_sum_container
#print axioms Erdos335.Loeb.loeb_unitCircle_left_subset_of_ae_sum_container
#check @Erdos335.Loeb.loeb_unitCircle_model_literal_containment
#print axioms Erdos335.Loeb.loeb_unitCircle_model_literal_containment
#check @Erdos335.Loeb.continuous_character_on_countable_factor_internal
#print axioms Erdos335.Loeb.continuous_character_on_countable_factor_internal
#check @Erdos335.Loeb.unitCircle_character_on_countable_factor_internal
#print axioms Erdos335.Loeb.unitCircle_character_on_countable_factor_internal
#check @Erdos335.Loeb.support_image_Icc_of_isOpenMap
#print axioms Erdos335.Loeb.support_image_Icc_of_isOpenMap
#check @Erdos335.Loeb.support_open_circle_arc
#print axioms Erdos335.Loeb.support_open_circle_arc
#check @Erdos335.Loeb.subgroup_circle_arc_image
#print axioms Erdos335.Loeb.subgroup_circle_arc_image
#check @Erdos335.Loeb.embedded_closedArc_add
#print axioms Erdos335.Loeb.embedded_closedArc_add
#check @Erdos335.Loeb.embedded_closedArc_erosion
#print axioms Erdos335.Loeb.embedded_closedArc_erosion
#check @Erdos335.Loeb.loeb_open_circle_model_literal_containment
#print axioms Erdos335.Loeb.loeb_open_circle_model_literal_containment
#check @Erdos335.Loeb.loeb_quotient_quasiPeriodic_or_literal_closedArc_cosets
#print axioms Erdos335.Loeb.loeb_quotient_quasiPeriodic_or_literal_closedArc_cosets
#check @Erdos335.Loeb.preimage_subgroup_character_coset
#print axioms Erdos335.Loeb.preimage_subgroup_character_coset
#check @Erdos335.Loeb.exists_internal_character_for_open_circle_cosets
#print axioms Erdos335.Loeb.exists_internal_character_for_open_circle_cosets
#check @Erdos335.Loeb.essential_stabilizer_quotient_polish
#print axioms Erdos335.Loeb.essential_stabilizer_quotient_polish
#check @Erdos335.Loeb.internalBohrCoset
#print axioms Erdos335.Loeb.internalBohrCoset
#check @Erdos335.Loeb.InternalBohrPairData
#print axioms Erdos335.Loeb.InternalBohrPairData
#check @Erdos335.Loeb.exists_internalBohrPairData_of_compact_cosets
#print axioms Erdos335.Loeb.exists_internalBohrPairData_of_compact_cosets
#check @Erdos335.Loeb.loeb_countable_compact_quasiPeriodic_or_internalBohr
#print axioms Erdos335.Loeb.loeb_countable_compact_quasiPeriodic_or_internalBohr
#check @Erdos335.Loeb.loeb_countable_model_quasiPeriodic_or_internalBohr
#print axioms Erdos335.Loeb.loeb_countable_model_quasiPeriodic_or_internalBohr
#check @Erdos335.Loeb.loeb_irreducible_aperiodic_quasiPeriodic_or_internalBohr
#print axioms Erdos335.Loeb.loeb_irreducible_aperiodic_quasiPeriodic_or_internalBohr
#check @Erdos335.Loeb.loeb_aperiodic_equality_quasiPeriodic_or_internalBohr
#print axioms Erdos335.Loeb.loeb_aperiodic_equality_quasiPeriodic_or_internalBohr
#check @Erdos335.Loeb.loeb_quasiPeriodic_active_inverse
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_active_inverse
#check @Erdos335.Loeb.loeb_irreducible_aperiodic_inverse_alternative
#print axioms Erdos335.Loeb.loeb_irreducible_aperiodic_inverse_alternative
#check @Erdos335.Loeb.loeb_quasiPeriodic_input_saturation_bound
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_input_saturation_bound
#check @Erdos335.Loeb.loeb_quasiPeriodic_period_bound_of_saturation_gap
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_period_bound_of_saturation_gap
#check @Erdos335.Loeb.loeb_irreducible_inverse_of_saturation_gap
#print axioms Erdos335.Loeb.loeb_irreducible_inverse_of_saturation_gap
#check @Erdos335.Loeb.loeb_quasiPeriodic_active_aperiodic
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_active_aperiodic
#check @Erdos335.Loeb.loeb_aperiodic_inverse_iteration_alternative
#print axioms Erdos335.Loeb.loeb_aperiodic_inverse_iteration_alternative
#check @Erdos335.Loeb.loeb_aperiodic_inverse_of_saturation_gap
#print axioms Erdos335.Loeb.loeb_aperiodic_inverse_of_saturation_gap
#check @Erdos335.Loeb.addHom_fiber_eq_coset
#print axioms Erdos335.Loeb.addHom_fiber_eq_coset
#check @Erdos335.Loeb.loebMeasure_finiteQuotient_preimage
#print axioms Erdos335.Loeb.loebMeasure_finiteQuotient_preimage
#check @Erdos335.Loeb.addHom_saturation_eq_preimage_image
#print axioms Erdos335.Loeb.addHom_saturation_eq_preimage_image
#check @Erdos335.Loeb.finiteQuotient_image_of_literal_exhaustion
#print axioms Erdos335.Loeb.finiteQuotient_image_of_literal_exhaustion
#check @Erdos335.Loeb.loeb_literal_exhaustion_saturation_measure
#print axioms Erdos335.Loeb.loeb_literal_exhaustion_saturation_measure
#check @Erdos335.Loeb.loeb_literal_exhaustion_saturation_gap
#print axioms Erdos335.Loeb.loeb_literal_exhaustion_saturation_gap
#check @Erdos335.Loeb.loeb_literal_exhaustion_inverse
#print axioms Erdos335.Loeb.loeb_literal_exhaustion_inverse
#check @Erdos335.Loeb.cyclicIntegerPrefix
#print axioms Erdos335.Loeb.cyclicIntegerPrefix
#check @Erdos335.Loeb.cyclicIntegerPrefix_ncard
#print axioms Erdos335.Loeb.cyclicIntegerPrefix_ncard
#check @Erdos335.Loeb.loebMeasure_cyclicIntegerPrefix
#print axioms Erdos335.Loeb.loebMeasure_cyclicIntegerPrefix
#check @Erdos335.Loeb.cyclicIntegerPrefix_exhaustion
#print axioms Erdos335.Loeb.cyclicIntegerPrefix_exhaustion
#check @Erdos335.Loeb.loeb_cyclicIntegerPrefix_inverse
#print axioms Erdos335.Loeb.loeb_cyclicIntegerPrefix_inverse
#check @Erdos335.Loeb.QuasiPeriodicDecomposition.anchor_mem_of_smaller_coset
#print axioms Erdos335.Loeb.QuasiPeriodicDecomposition.anchor_mem_of_smaller_coset
#check @Erdos335.Loeb.QuasiPeriodicDecomposition.restrictPeriod
#print axioms Erdos335.Loeb.QuasiPeriodicDecomposition.restrictPeriod
#check @Erdos335.Loeb.QuasiPeriodicPairData.restrictPeriod
#print axioms Erdos335.Loeb.QuasiPeriodicPairData.restrictPeriod
#check @Erdos335.Loeb.loeb_circle_coset_period_le_of_ae_containment
#print axioms Erdos335.Loeb.loeb_circle_coset_period_le_of_ae_containment
#check @Erdos335.Loeb.loeb_quasiPeriodic_internalBohr_period_alignment
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_internalBohr_period_alignment
#check @Erdos335.Loeb.loeb_quasiPeriodic_saturation_identity
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_saturation_identity
#check @Erdos335.Loeb.loeb_quasiPeriodic_sum_decomposition
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_sum_decomposition
#check @Erdos335.Loeb.loeb_quasiPeriodic_saturated_equality
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_saturated_equality
#check @Erdos335.Loeb.loeb_quasiPeriodic_finite_quotient_cardinality
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_finite_quotient_cardinality
#check @Erdos335.Loeb.loeb_quasiPeriodic_finite_quotient_expression
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_finite_quotient_expression
#check @Erdos335.ArithmeticRemoval.triangleIndices
#print axioms Erdos335.ArithmeticRemoval.triangleIndices
#check @Erdos335.ArithmeticRemoval.mem_triangleIndices
#print axioms Erdos335.ArithmeticRemoval.mem_triangleIndices
#check @Erdos335.ArithmeticRemoval.triangleIndices_closed
#print axioms Erdos335.ArithmeticRemoval.triangleIndices_closed
#check @Erdos335.ArithmeticRemoval.cliqueFinset_eq_map
#print axioms Erdos335.ArithmeticRemoval.cliqueFinset_eq_map
#check @Erdos335.ArithmeticRemoval.card_cliqueFinset
#print axioms Erdos335.ArithmeticRemoval.card_cliqueFinset
#check @Erdos335.ArithmeticRemoval.additiveTriples
#print axioms Erdos335.ArithmeticRemoval.additiveTriples
#check @Erdos335.ArithmeticRemoval.triangleCoordinates
#print axioms Erdos335.ArithmeticRemoval.triangleCoordinates
#check @Erdos335.ArithmeticRemoval.card_triangleIndices
#print axioms Erdos335.ArithmeticRemoval.card_triangleIndices
#check @Erdos335.ArithmeticRemoval.card_arithmetic_triangles
#print axioms Erdos335.ArithmeticRemoval.card_arithmetic_triangles
#check @Erdos335.ArithmeticRemoval.arithmeticRemovalBound
#print axioms Erdos335.ArithmeticRemoval.arithmeticRemovalBound
#check @Erdos335.ArithmeticRemoval.arithmeticRemovalBound_pos
#print axioms Erdos335.ArithmeticRemoval.arithmeticRemovalBound_pos
#check @Erdos335.ArithmeticRemoval.exists_triangle_free_subgraph
#print axioms Erdos335.ArithmeticRemoval.exists_triangle_free_subgraph
#check @Erdos335.ArithmeticRemoval.removedLeft
#print axioms Erdos335.ArithmeticRemoval.removedLeft
#check @Erdos335.ArithmeticRemoval.removedRight
#print axioms Erdos335.ArithmeticRemoval.removedRight
#check @Erdos335.ArithmeticRemoval.removedSum
#print axioms Erdos335.ArithmeticRemoval.removedSum
#check @Erdos335.ArithmeticRemoval.exists_avoiding_three_sets
#print axioms Erdos335.ArithmeticRemoval.exists_avoiding_three_sets
#check @Erdos335.ArithmeticRemoval.no_solution_of_small_removed
#print axioms Erdos335.ArithmeticRemoval.no_solution_of_small_removed
#check @Erdos335.ArithmeticRemoval.sum_fiber_card_le
#print axioms Erdos335.ArithmeticRemoval.sum_fiber_card_le
#check @Erdos335.ArithmeticRemoval.leftEdge
#print axioms Erdos335.ArithmeticRemoval.leftEdge
#check @Erdos335.ArithmeticRemoval.rightEdge
#print axioms Erdos335.ArithmeticRemoval.rightEdge
#check @Erdos335.ArithmeticRemoval.sumEdge
#print axioms Erdos335.ArithmeticRemoval.sumEdge
#check @Erdos335.ArithmeticRemoval.sum_removedLeft_le
#print axioms Erdos335.ArithmeticRemoval.sum_removedLeft_le
#check @Erdos335.ArithmeticRemoval.sum_removedRight_le
#print axioms Erdos335.ArithmeticRemoval.sum_removedRight_le
#check @Erdos335.ArithmeticRemoval.sum_removedSum_le
#print axioms Erdos335.ArithmeticRemoval.sum_removedSum_le
#check @Erdos335.ArithmeticRemoval.large_fiber_card_bound
#print axioms Erdos335.ArithmeticRemoval.large_fiber_card_bound
#check @Erdos335.ArithmeticRemoval.large_fiber_small
#print axioms Erdos335.ArithmeticRemoval.large_fiber_small
#check @Erdos335.ArithmeticRemoval.arithmetic_removal
#print axioms Erdos335.ArithmeticRemoval.arithmetic_removal
#check @Erdos335.ArithmeticRemoval.representationCount
#print axioms Erdos335.ArithmeticRemoval.representationCount
#check @Erdos335.ArithmeticRemoval.popularSum
#print axioms Erdos335.ArithmeticRemoval.popularSum
#check @Erdos335.ArithmeticRemoval.popularRemovalBound
#print axioms Erdos335.ArithmeticRemoval.popularRemovalBound
#check @Erdos335.ArithmeticRemoval.popularRemovalBound_pos
#print axioms Erdos335.ArithmeticRemoval.popularRemovalBound_pos
#check @Erdos335.ArithmeticRemoval.card_additiveTriples_eq_sum
#print axioms Erdos335.ArithmeticRemoval.card_additiveTriples_eq_sum
#check @Erdos335.ArithmeticRemoval.nonpopular_triples_bound
#print axioms Erdos335.ArithmeticRemoval.nonpopular_triples_bound
#check @Erdos335.ArithmeticRemoval.popular_sumset_removal
#print axioms Erdos335.ArithmeticRemoval.popular_sumset_removal
#check @Erdos335.ArithmeticRemoval.popular_sumset_container
#print axioms Erdos335.ArithmeticRemoval.popular_sumset_container
#check @Erdos335.ArithmeticRemoval.exists_slow_index_for_positive_thresholds
#print axioms Erdos335.ArithmeticRemoval.exists_slow_index_for_positive_thresholds
#check @Erdos335.ArithmeticRemoval.exists_vanishing_removal_parameters
#print axioms Erdos335.ArithmeticRemoval.exists_vanishing_removal_parameters
#check @Erdos335.ArithmeticRemoval.popularSum_antitone
#print axioms Erdos335.ArithmeticRemoval.popularSum_antitone
#check @Erdos335.ArithmeticRemoval.asymptotic_sumset_removal
#print axioms Erdos335.ArithmeticRemoval.asymptotic_sumset_removal
#check @Erdos335.IntermediateScale.characterMean
#print axioms Erdos335.IntermediateScale.characterMean
#check @Erdos335.IntermediateScale.unit_pow_sub_one_le
#print axioms Erdos335.IntermediateScale.unit_pow_sub_one_le
#check @Erdos335.IntermediateScale.characterMean_sub_one_le
#print axioms Erdos335.IntermediateScale.characterMean_sub_one_le
#check @Erdos335.IntermediateScale.characterMean_norm_le
#print axioms Erdos335.IntermediateScale.characterMean_norm_le
#check @Erdos335.IntermediateScale.characterMean_separation
#print axioms Erdos335.IntermediateScale.characterMean_separation
#check @Erdos335.IntermediateScale.countable_strict_energy_fibers
#print axioms Erdos335.IntermediateScale.countable_strict_energy_fibers
#check @Erdos335.IntermediateScale.exists_flat_energy_fiber
#print axioms Erdos335.IntermediateScale.exists_flat_energy_fiber
#check @Erdos335.IntermediateScale.unitCharacter
#print axioms Erdos335.IntermediateScale.unitCharacter
#check @Erdos335.IntermediateScale.unitCharacter_norm
#print axioms Erdos335.IntermediateScale.unitCharacter_norm
#check @Erdos335.IntermediateScale.unitCharacter_sub_one_upper
#print axioms Erdos335.IntermediateScale.unitCharacter_sub_one_upper
#check @Erdos335.IntermediateScale.unitCharacter_sub_one_lower
#print axioms Erdos335.IntermediateScale.unitCharacter_sub_one_lower
#check @Erdos335.IntermediateScale.intermediate_frequency_separation
#print axioms Erdos335.IntermediateScale.intermediate_frequency_separation
#check @Erdos335.IntermediateScale.close_character_means_frequency_dichotomy
#print axioms Erdos335.IntermediateScale.close_character_means_frequency_dichotomy
#check @Erdos335.IntermediateScale.lexScale
#print axioms Erdos335.IntermediateScale.lexScale
#check @Erdos335.IntermediateScale.linear_log_tendsto_atTop
#print axioms Erdos335.IntermediateScale.linear_log_tendsto_atTop
#check @Erdos335.IntermediateScale.linear_log_tendsto_atBot
#print axioms Erdos335.IntermediateScale.linear_log_tendsto_atBot
#check @Erdos335.IntermediateScale.lexScale_ratio_tendsto_zero
#print axioms Erdos335.IntermediateScale.lexScale_ratio_tendsto_zero
#check @Erdos335.IntermediateScale.lexScale_tendsto_atTop
#print axioms Erdos335.IntermediateScale.lexScale_tendsto_atTop
#check @Erdos335.IntermediateScale.lexScale_div_exp_tendsto_zero
#print axioms Erdos335.IntermediateScale.lexScale_div_exp_tendsto_zero
#check @Erdos335.IntermediateScale.intermediateScale
#print axioms Erdos335.IntermediateScale.intermediateScale
#check @Erdos335.IntermediateScale.intermediateScale_div_lower_atTop
#print axioms Erdos335.IntermediateScale.intermediateScale_div_lower_atTop
#check @Erdos335.IntermediateScale.intermediateScale_div_upper_zero
#print axioms Erdos335.IntermediateScale.intermediateScale_div_upper_zero
#check @Erdos335.IntermediateScale.intermediateScale_ratio_zero
#print axioms Erdos335.IntermediateScale.intermediateScale_ratio_zero
#check @Erdos335.IntermediateScale.intermediateScale_atTop
#print axioms Erdos335.IntermediateScale.intermediateScale_atTop
#check @Erdos335.IntermediateScale.floor_preserves_vanishing_ratio
#print axioms Erdos335.IntermediateScale.floor_preserves_vanishing_ratio
#check @Erdos335.IntermediateScale.cyclicWindow
#print axioms Erdos335.IntermediateScale.cyclicWindow
#check @Erdos335.IntermediateScale.fixed_shift_window_error_le
#print axioms Erdos335.IntermediateScale.fixed_shift_window_error_le
#check @Erdos335.IntermediateScale.finite_representative_window_error_le
#print axioms Erdos335.IntermediateScale.finite_representative_window_error_le
#check @Erdos335.IntermediateScale.restored_representatives_error_le
#print axioms Erdos335.IntermediateScale.restored_representatives_error_le
#check @Erdos335.IntermediateScale.finitePrefix
#print axioms Erdos335.IntermediateScale.finitePrefix
#check @Erdos335.IntermediateScale.exists_slow_square_prefix
#print axioms Erdos335.IntermediateScale.exists_slow_square_prefix
#check @Erdos335.IntermediateScale.prefix_sum_le_square
#print axioms Erdos335.IntermediateScale.prefix_sum_le_square
#check @Erdos335.IntermediateScale.restore_exhaustive_cyclic_prefix
#print axioms Erdos335.IntermediateScale.restore_exhaustive_cyclic_prefix
#check @Erdos335.IntermediateScale.cyclic_window_removal_with_exhaustion
#print axioms Erdos335.IntermediateScale.cyclic_window_removal_with_exhaustion
#check @Erdos335.IntermediateScale.cyclicLift
#print axioms Erdos335.IntermediateScale.cyclicLift
#check @Erdos335.IntermediateScale.cyclicLift_image
#print axioms Erdos335.IntermediateScale.cyclicLift_image
#check @Erdos335.IntermediateScale.cyclicLift_subset
#print axioms Erdos335.IntermediateScale.cyclicLift_subset
#check @Erdos335.IntermediateScale.cyclicLift_exhaustion
#print axioms Erdos335.IntermediateScale.cyclicLift_exhaustion
#check @Erdos335.IntermediateScale.prefixConvolutionCount
#print axioms Erdos335.IntermediateScale.prefixConvolutionCount
#check @Erdos335.IntermediateScale.prefixConvolutionCount_eq_zero
#print axioms Erdos335.IntermediateScale.prefixConvolutionCount_eq_zero
#check @Erdos335.IntermediateScale.wrapped_representation_count_le
#print axioms Erdos335.IntermediateScale.wrapped_representation_count_le
#check @Erdos335.IntermediateScale.convolutionTranslationError
#print axioms Erdos335.IntermediateScale.convolutionTranslationError
#check @Erdos335.IntermediateScale.convolutionTranslationError_nonneg
#print axioms Erdos335.IntermediateScale.convolutionTranslationError_nonneg
#check @Erdos335.IntermediateScale.popular_window_mass_bound
#print axioms Erdos335.IntermediateScale.popular_window_mass_bound
#check @Erdos335.IntermediateScale.popular_window_count_bound
#print axioms Erdos335.IntermediateScale.popular_window_count_bound
#check @Erdos335.IntermediateScale.exists_positive_vanishing_divisor
#print axioms Erdos335.IntermediateScale.exists_positive_vanishing_divisor
#check @Erdos335.IntermediateScale.popular_window_estimate_of_convolution_periods
#print axioms Erdos335.IntermediateScale.popular_window_estimate_of_convolution_periods
#check @Erdos335.IntermediateScale.cyclic_window_removal_of_convolution_periods
#print axioms Erdos335.IntermediateScale.cyclic_window_removal_of_convolution_periods
#check @Erdos335.IntermediateScale.naturalIntermediateScale
#print axioms Erdos335.IntermediateScale.naturalIntermediateScale
#check @Erdos335.IntermediateScale.naturalIntermediateScale_atTop
#print axioms Erdos335.IntermediateScale.naturalIntermediateScale_atTop
#check @Erdos335.IntermediateScale.naturalIntermediateScale_lower_ratio
#print axioms Erdos335.IntermediateScale.naturalIntermediateScale_lower_ratio
#check @Erdos335.IntermediateScale.naturalIntermediateScale_upper_ratio
#print axioms Erdos335.IntermediateScale.naturalIntermediateScale_upper_ratio
#check @Erdos335.IntermediateScale.naturalIntermediateScale_lexicographic_ratio
#print axioms Erdos335.IntermediateScale.naturalIntermediateScale_lexicographic_ratio
#check @Erdos335.IntermediateScale.prefixConvolutionCount_mono
#print axioms Erdos335.IntermediateScale.prefixConvolutionCount_mono
#check @Erdos335.IntermediateScale.prefixConvolutionCount_length_bound
#print axioms Erdos335.IntermediateScale.prefixConvolutionCount_length_bound
#check @Erdos335.IntermediateScale.prefixConvolutionCount_abs_length_bound
#print axioms Erdos335.IntermediateScale.prefixConvolutionCount_abs_length_bound
#check @Erdos335.IntermediateScale.convolutionTranslationErrorWithLength
#print axioms Erdos335.IntermediateScale.convolutionTranslationErrorWithLength
#check @Erdos335.IntermediateScale.convolutionTranslationError_length_bound
#print axioms Erdos335.IntermediateScale.convolutionTranslationError_length_bound
#check @Erdos335.IntermediateScale.convolution_period_error_of_nearby_length
#print axioms Erdos335.IntermediateScale.convolution_period_error_of_nearby_length
#check @Erdos335.IntermediateScale.cyclic_window_removal_of_nearby_convolution_periods
#print axioms Erdos335.IntermediateScale.cyclic_window_removal_of_nearby_convolution_periods
#check @Erdos335.IntermediateScale.finiteFiber
#print axioms Erdos335.IntermediateScale.finiteFiber
#check @Erdos335.IntermediateScale.finiteFiberMean
#print axioms Erdos335.IntermediateScale.finiteFiberMean
#check @Erdos335.IntermediateScale.finiteConditionalMean
#print axioms Erdos335.IntermediateScale.finiteConditionalMean
#check @Erdos335.IntermediateScale.finiteFiber_residual_sum
#print axioms Erdos335.IntermediateScale.finiteFiber_residual_sum
#check @Erdos335.IntermediateScale.finiteConditionalMean_bounds
#print axioms Erdos335.IntermediateScale.finiteConditionalMean_bounds
#check @Erdos335.IntermediateScale.finiteConditionalMean_orthogonal
#print axioms Erdos335.IntermediateScale.finiteConditionalMean_orthogonal
#check @Erdos335.IntermediateScale.finiteConditionalMean_sum
#print axioms Erdos335.IntermediateScale.finiteConditionalMean_sum
#check @Erdos335.IntermediateScale.finiteConditionalMean_energy_identity
#print axioms Erdos335.IntermediateScale.finiteConditionalMean_energy_identity
#check @Erdos335.IntermediateScale.finiteConditionalMean_energy_le
#print axioms Erdos335.IntermediateScale.finiteConditionalMean_energy_le
#check @Erdos335.IntermediateScale.refinement_residual_orthogonal
#print axioms Erdos335.IntermediateScale.refinement_residual_orthogonal
#check @Erdos335.IntermediateScale.refinement_increment_orthogonal
#print axioms Erdos335.IntermediateScale.refinement_increment_orthogonal
#check @Erdos335.IntermediateScale.refinement_energy_identity
#print axioms Erdos335.IntermediateScale.refinement_energy_identity
#check @Erdos335.IntermediateScale.refinement_energy_mono
#print axioms Erdos335.IntermediateScale.refinement_energy_mono
#check @Erdos335.IntermediateScale.finite_residual_test_bound
#print axioms Erdos335.IntermediateScale.finite_residual_test_bound
#check @Erdos335.IntermediateScale.finite_unit_test_cauchy
#print axioms Erdos335.IntermediateScale.finite_unit_test_cauchy
#check @Erdos335.IntermediateScale.finite_conditional_energy_increment
#print axioms Erdos335.IntermediateScale.finite_conditional_energy_increment
#check @Erdos335.IntermediateScale.quantizedIndex
#print axioms Erdos335.IntermediateScale.quantizedIndex
#check @Erdos335.IntermediateScale.quantizedValue
#print axioms Erdos335.IntermediateScale.quantizedValue
#check @Erdos335.IntermediateScale.quantizedValue_bounds
#print axioms Erdos335.IntermediateScale.quantizedValue_bounds
#check @Erdos335.IntermediateScale.quantizedValue_approx
#print axioms Erdos335.IntermediateScale.quantizedValue_approx
#check @Erdos335.IntermediateScale.quantized_partition_energy_increment
#print axioms Erdos335.IntermediateScale.quantized_partition_energy_increment
#check @Erdos335.IntermediateScale.bounded_energy_selection
#print axioms Erdos335.IntermediateScale.bounded_energy_selection
#check @Erdos335.IntermediateScale.testPartition
#print axioms Erdos335.IntermediateScale.testPartition
#check @Erdos335.IntermediateScale.testEnergy
#print axioms Erdos335.IntermediateScale.testEnergy
#check @Erdos335.IntermediateScale.testEnergy_bounds
#print axioms Erdos335.IntermediateScale.testEnergy_bounds
#check @Erdos335.IntermediateScale.testEnergy_insert_increment
#print axioms Erdos335.IntermediateScale.testEnergy_insert_increment
#check @Erdos335.IntermediateScale.finite_test_regularity
#print axioms Erdos335.IntermediateScale.finite_test_regularity
#check @Erdos335.IntermediateScale.exists_finite_regularity_parameters
#print axioms Erdos335.IntermediateScale.exists_finite_regularity_parameters
#check @Erdos335.IntermediateScale.finite_test_regularity_with_uniform_parameters
#print axioms Erdos335.IntermediateScale.finite_test_regularity_with_uniform_parameters
#check @Erdos335.IntermediateScale.realCharacterTests
#print axioms Erdos335.IntermediateScale.realCharacterTests
#check @Erdos335.IntermediateScale.realCharacterTests_bound
#print axioms Erdos335.IntermediateScale.realCharacterTests_bound
#check @Erdos335.IntermediateScale.coefficient_real_formula
#print axioms Erdos335.IntermediateScale.coefficient_real_formula
#check @Erdos335.IntermediateScale.coefficient_norm_le_of_real_tests
#print axioms Erdos335.IntermediateScale.coefficient_norm_le_of_real_tests
#check @Erdos335.IntermediateScale.finite_fourier_uniform_partition
#print axioms Erdos335.IntermediateScale.finite_fourier_uniform_partition
#check @Erdos335.IntermediateScale.boundaryGrid
#print axioms Erdos335.IntermediateScale.boundaryGrid
#check @Erdos335.IntermediateScale.boundaryGrid_card_le_one
#print axioms Erdos335.IntermediateScale.boundaryGrid_card_le_one
#check @Erdos335.IntermediateScale.exists_sparse_boundary_offset
#print axioms Erdos335.IntermediateScale.exists_sparse_boundary_offset
#check @Erdos335.IntermediateScale.boundaryShift
#print axioms Erdos335.IntermediateScale.boundaryShift
#check @Erdos335.IntermediateScale.shiftedTest
#print axioms Erdos335.IntermediateScale.shiftedTest
#check @Erdos335.IntermediateScale.nearQuantizationBoundary
#print axioms Erdos335.IntermediateScale.nearQuantizationBoundary
#check @Erdos335.IntermediateScale.boundaryShift_bounds
#print axioms Erdos335.IntermediateScale.boundaryShift_bounds
#check @Erdos335.IntermediateScale.shiftedTest_bound
#print axioms Erdos335.IntermediateScale.shiftedTest_bound
#check @Erdos335.IntermediateScale.shiftedTest_boundary_iff
#print axioms Erdos335.IntermediateScale.shiftedTest_boundary_iff
#check @Erdos335.IntermediateScale.exists_boundary_avoiding_shift
#print axioms Erdos335.IntermediateScale.exists_boundary_avoiding_shift
#check @Erdos335.IntermediateScale.shiftedTest_correlation
#print axioms Erdos335.IntermediateScale.shiftedTest_correlation
#check @Erdos335.IntermediateScale.boundary_avoiding_test_regularity
#print axioms Erdos335.IntermediateScale.boundary_avoiding_test_regularity
#check @Erdos335.IntermediateScale.unitRamp
#print axioms Erdos335.IntermediateScale.unitRamp
#check @Erdos335.IntermediateScale.unitRamp_bounds
#print axioms Erdos335.IntermediateScale.unitRamp_bounds
#check @Erdos335.IntermediateScale.unitRamp_zero
#print axioms Erdos335.IntermediateScale.unitRamp_zero
#check @Erdos335.IntermediateScale.unitRamp_one
#print axioms Erdos335.IntermediateScale.unitRamp_one
#check @Erdos335.IntermediateScale.softCell
#print axioms Erdos335.IntermediateScale.softCell
#check @Erdos335.IntermediateScale.softCell_continuous
#print axioms Erdos335.IntermediateScale.softCell_continuous
#check @Erdos335.IntermediateScale.softCell_bounds
#print axioms Erdos335.IntermediateScale.softCell_bounds
#check @Erdos335.IntermediateScale.softCell_zero_of_le
#print axioms Erdos335.IntermediateScale.softCell_zero_of_le
#check @Erdos335.IntermediateScale.softCell_zero_of_ge
#print axioms Erdos335.IntermediateScale.softCell_zero_of_ge
#check @Erdos335.IntermediateScale.softCell_eq_indicator
#print axioms Erdos335.IntermediateScale.softCell_eq_indicator
#check @Erdos335.IntermediateScale.softQuantizedCell
#print axioms Erdos335.IntermediateScale.softQuantizedCell
#check @Erdos335.IntermediateScale.softQuantizedCell_continuous
#print axioms Erdos335.IntermediateScale.softQuantizedCell_continuous
#check @Erdos335.IntermediateScale.softQuantizedCell_exact
#print axioms Erdos335.IntermediateScale.softQuantizedCell_exact
#check @Erdos335.IntermediateScale.softQuantizedCell_error_sum_le
#print axioms Erdos335.IntermediateScale.softQuantizedCell_error_sum_le
#check @Erdos335.IntermediateScale.circleMonomial
#print axioms Erdos335.IntermediateScale.circleMonomial
#check @Erdos335.IntermediateScale.circleMonomial_span_dense
#print axioms Erdos335.IntermediateScale.circleMonomial_span_dense
#check @Erdos335.IntermediateScale.exists_circle_polynomial_approximation
#print axioms Erdos335.IntermediateScale.exists_circle_polynomial_approximation
#check @Erdos335.IntermediateScale.softPattern
#print axioms Erdos335.IntermediateScale.softPattern
#check @Erdos335.IntermediateScale.softPartitionModel
#print axioms Erdos335.IntermediateScale.softPartitionModel
#check @Erdos335.IntermediateScale.softPattern_bounds
#print axioms Erdos335.IntermediateScale.softPattern_bounds
#check @Erdos335.IntermediateScale.softPattern_exact
#print axioms Erdos335.IntermediateScale.softPattern_exact
#check @Erdos335.IntermediateScale.softPartitionModel_bounds
#print axioms Erdos335.IntermediateScale.softPartitionModel_bounds
#check @Erdos335.IntermediateScale.softPartitionModel_exact
#print axioms Erdos335.IntermediateScale.softPartitionModel_exact
#check @Erdos335.IntermediateScale.softPartitionModel_error_sum_le
#print axioms Erdos335.IntermediateScale.softPartitionModel_error_sum_le
#check @Erdos335.IntermediateScale.finiteFiberMean_bounds
#print axioms Erdos335.IntermediateScale.finiteFiberMean_bounds
#check @Erdos335.IntermediateScale.boundary_union_card_bound
#print axioms Erdos335.IntermediateScale.boundary_union_card_bound
#check @Erdos335.IntermediateScale.softPartitionModel_normalized_error
#print axioms Erdos335.IntermediateScale.softPartitionModel_normalized_error
#check @Erdos335.IntermediateScale.finite_factor_soft_model_error
#print axioms Erdos335.IntermediateScale.finite_factor_soft_model_error
#check @Erdos335.IntermediateScale.finite_factor_soft_model_error_of_card_bound
#print axioms Erdos335.IntermediateScale.finite_factor_soft_model_error_of_card_bound
#check @Erdos335.IntermediateScale.finite_family_circle_approximation
#print axioms Erdos335.IntermediateScale.finite_family_circle_approximation
#check @Erdos335.IntermediateScale.circleCoordinate
#print axioms Erdos335.IntermediateScale.circleCoordinate
#check @Erdos335.IntermediateScale.circleCoordinate_continuous
#print axioms Erdos335.IntermediateScale.circleCoordinate_continuous
#check @Erdos335.IntermediateScale.shiftedTest_continuous
#print axioms Erdos335.IntermediateScale.shiftedTest_continuous
#check @Erdos335.IntermediateScale.circleCell
#print axioms Erdos335.IntermediateScale.circleCell
#check @Erdos335.IntermediateScale.circleCell_norm_le_one
#print axioms Erdos335.IntermediateScale.circleCell_norm_le_one
#check @Erdos335.IntermediateScale.uniform_circleCell_polynomials
#print axioms Erdos335.IntermediateScale.uniform_circleCell_polynomials
#check @Erdos335.IntermediateScale.norm_prod_le_two_pow
#print axioms Erdos335.IntermediateScale.norm_prod_le_two_pow
#check @Erdos335.IntermediateScale.norm_prod_approximation
#print axioms Erdos335.IntermediateScale.norm_prod_approximation
#check @Erdos335.IntermediateScale.pad_indexed_character_sum
#print axioms Erdos335.IntermediateScale.pad_indexed_character_sum
#check @Erdos335.IntermediateScale.split_and_pad_character_sum
#print axioms Erdos335.IntermediateScale.split_and_pad_character_sum
#check @Erdos335.IntermediateScale.productCharacter
#print axioms Erdos335.IntermediateScale.productCharacter
#check @Erdos335.IntermediateScale.productCharacter_apply
#print axioms Erdos335.IntermediateScale.productCharacter_apply
#check @Erdos335.IntermediateScale.character_polynomial_product
#print axioms Erdos335.IntermediateScale.character_polynomial_product
#check @Erdos335.IntermediateScale.polynomial_product_card_bound
#print axioms Erdos335.IntermediateScale.polynomial_product_card_bound
#check @Erdos335.IntermediateScale.polynomial_product_coefficient_bound
#print axioms Erdos335.IntermediateScale.polynomial_product_coefficient_bound
#check @Erdos335.IntermediateScale.weighted_polynomial_product_expansion
#print axioms Erdos335.IntermediateScale.weighted_polynomial_product_expansion
#check @Erdos335.IntermediateScale.weighted_polynomial_product_card_bound
#print axioms Erdos335.IntermediateScale.weighted_polynomial_product_card_bound
#check @Erdos335.IntermediateScale.weighted_polynomial_product_coefficient_bound
#print axioms Erdos335.IntermediateScale.weighted_polynomial_product_coefficient_bound
#check @Erdos335.IntermediateScale.pad_weighted_polynomial_products
#print axioms Erdos335.IntermediateScale.pad_weighted_polynomial_products
#check @Erdos335.IntermediateScale.weighted_product_approximation
#print axioms Erdos335.IntermediateScale.weighted_product_approximation
#check @Erdos335.IntermediateScale.softCharacterModel
#print axioms Erdos335.IntermediateScale.softCharacterModel
#check @Erdos335.IntermediateScale.softCharacterModel_eq
#print axioms Erdos335.IntermediateScale.softCharacterModel_eq
#check @Erdos335.IntermediateScale.softCharacterModel_polynomial_approximation
#print axioms Erdos335.IntermediateScale.softCharacterModel_polynomial_approximation
#check @Erdos335.IntermediateScale.pad_circle_character_sum
#print axioms Erdos335.IntermediateScale.pad_circle_character_sum
#check @Erdos335.IntermediateScale.split_and_pad_circle_character_sum
#print axioms Erdos335.IntermediateScale.split_and_pad_circle_character_sum
#check @Erdos335.IntermediateScale.pad_circle_weighted_polynomial_products
#print axioms Erdos335.IntermediateScale.pad_circle_weighted_polynomial_products
#check @Erdos335.IntermediateScale.softCharacterModel_unit_polynomial_approximation
#print axioms Erdos335.IntermediateScale.softCharacterModel_unit_polynomial_approximation
#check @Erdos335.IntermediateScale.pulledCharacterTests
#print axioms Erdos335.IntermediateScale.pulledCharacterTests
#check @Erdos335.IntermediateScale.circleCoordinate_bound
#print axioms Erdos335.IntermediateScale.circleCoordinate_bound
#check @Erdos335.IntermediateScale.pulledCharacterTests_bound
#print axioms Erdos335.IntermediateScale.pulledCharacterTests_bound
#check @Erdos335.IntermediateScale.selected_character_factor
#print axioms Erdos335.IntermediateScale.selected_character_factor
#check @Erdos335.IntermediateScale.pulled_character_sum_norm_le
#print axioms Erdos335.IntermediateScale.pulled_character_sum_norm_le
#check @Erdos335.IntermediateScale.finite_l2_uniform_triangle
#print axioms Erdos335.IntermediateScale.finite_l2_uniform_triangle
#check @Erdos335.IntermediateScale.quantized_label_card
#print axioms Erdos335.IntermediateScale.quantized_label_card
#check @Erdos335.IntermediateScale.bounded_softCharacter_polynomial_approximation
#print axioms Erdos335.IntermediateScale.bounded_softCharacter_polynomial_approximation
#check @Erdos335.IntermediateScale.conditional_character_approximation
#print axioms Erdos335.IntermediateScale.conditional_character_approximation
#check @Erdos335.IntermediateScale.exists_continuous_model_parameters
#print axioms Erdos335.IntermediateScale.exists_continuous_model_parameters
#check @Erdos335.IntermediateScale.exists_cell_polynomial_parameters
#print axioms Erdos335.IntermediateScale.exists_cell_polynomial_parameters
#check @Erdos335.IntermediateScale.finite_character_regularity
#print axioms Erdos335.IntermediateScale.finite_character_regularity
#check @Erdos335.IntermediateScale.integerCircleCharacter
#print axioms Erdos335.IntermediateScale.integerCircleCharacter
#check @Erdos335.IntermediateScale.integerCircleCharacter_coe
#print axioms Erdos335.IntermediateScale.integerCircleCharacter_coe
#check @Erdos335.IntermediateScale.integerCircleCharacter_representation
#print axioms Erdos335.IntermediateScale.integerCircleCharacter_representation
#check @Erdos335.IntermediateScale.integer_character_inverse_test
#print axioms Erdos335.IntermediateScale.integer_character_inverse_test
#check @Erdos335.IntermediateScale.integer_sample_regularity
#print axioms Erdos335.IntermediateScale.integer_sample_regularity
#check @Erdos335.IntermediateScale.finite_l1_of_mean_square
#print axioms Erdos335.IntermediateScale.finite_l1_of_mean_square
#check @Erdos335.IntermediateScale.finite_polynomial_correlation_bound
#print axioms Erdos335.IntermediateScale.finite_polynomial_correlation_bound
#check @Erdos335.IntermediateScale.intervalFourierNorm
#print axioms Erdos335.IntermediateScale.intervalFourierNorm
#check @Erdos335.IntermediateScale.intervalFourierNorm_le
#print axioms Erdos335.IntermediateScale.intervalFourierNorm_le
#check @Erdos335.IntermediateScale.interval_arithmetic_regularity
#print axioms Erdos335.IntermediateScale.interval_arithmetic_regularity
#check @Erdos335.IntermediateScale.regularityAccuracy
#print axioms Erdos335.IntermediateScale.regularityAccuracy
#check @Erdos335.IntermediateScale.regularityAccuracy_pos
#print axioms Erdos335.IntermediateScale.regularityAccuracy_pos
#check @Erdos335.IntermediateScale.regularityAccuracy_step_le
#print axioms Erdos335.IntermediateScale.regularityAccuracy_step_le
#check @Erdos335.IntermediateScale.regularityAccuracy_geometric_bound
#print axioms Erdos335.IntermediateScale.regularityAccuracy_geometric_bound
#check @Erdos335.IntermediateScale.regularityAccuracy_tendsto_zero
#print axioms Erdos335.IntermediateScale.regularityAccuracy_tendsto_zero
#check @Erdos335.IntermediateScale.regularityAccuracy_complexity_bound
#print axioms Erdos335.IntermediateScale.regularityAccuracy_complexity_bound
#check @Erdos335.IntermediateScale.exists_slow_index_for_eventual_property
#print axioms Erdos335.IntermediateScale.exists_slow_index_for_eventual_property
#check @Erdos335.IntermediateScale.exists_slow_diagonal_for_finite_requirements
#print axioms Erdos335.IntermediateScale.exists_slow_diagonal_for_finite_requirements
#check @Erdos335.IntermediateScale.prefix_patching_energy_bound
#print axioms Erdos335.IntermediateScale.prefix_patching_energy_bound
#check @Erdos335.IntermediateScale.firstCutIndex
#print axioms Erdos335.IntermediateScale.firstCutIndex
#check @Erdos335.IntermediateScale.firstCutIndex_spec
#print axioms Erdos335.IntermediateScale.firstCutIndex_spec
#check @Erdos335.IntermediateScale.firstCutIndex_eq
#print axioms Erdos335.IntermediateScale.firstCutIndex_eq
#check @Erdos335.IntermediateScale.prefixStitch
#print axioms Erdos335.IntermediateScale.prefixStitch
#check @Erdos335.IntermediateScale.prefixStitch_bounds
#print axioms Erdos335.IntermediateScale.prefixStitch_bounds
#check @Erdos335.IntermediateScale.prefixStitch_energy_bound
#print axioms Erdos335.IntermediateScale.prefixStitch_energy_bound
#check @Erdos335.IntermediateScale.exists_prefix_stitched_approximation
#print axioms Erdos335.IntermediateScale.exists_prefix_stitched_approximation
#check @Erdos335.IntermediateScale.cauchy_of_almost_monotone
#print axioms Erdos335.IntermediateScale.cauchy_of_almost_monotone
#check @Erdos335.IntermediateScale.tendsto_of_almost_monotone
#print axioms Erdos335.IntermediateScale.tendsto_of_almost_monotone
#check @Erdos335.IntermediateScale.exists_prefix_mean_square_limit
#print axioms Erdos335.IntermediateScale.exists_prefix_mean_square_limit
#check @Erdos335.IntermediateScale.prefixEnergy
#print axioms Erdos335.IntermediateScale.prefixEnergy
#check @Erdos335.IntermediateScale.prefixCorrelation
#print axioms Erdos335.IntermediateScale.prefixCorrelation
#check @Erdos335.IntermediateScale.prefixEnergy_nonneg
#print axioms Erdos335.IntermediateScale.prefixEnergy_nonneg
#check @Erdos335.IntermediateScale.prefixEnergy_le_one
#print axioms Erdos335.IntermediateScale.prefixEnergy_le_one
#check @Erdos335.IntermediateScale.prefix_distance_energy_identity
#print axioms Erdos335.IntermediateScale.prefix_distance_energy_identity
#check @Erdos335.IntermediateScale.prefix_distance_tendsto
#print axioms Erdos335.IntermediateScale.prefix_distance_tendsto
#check @Erdos335.IntermediateScale.prefix_energy_cauchy_of_approximate_orthogonality
#print axioms Erdos335.IntermediateScale.prefix_energy_cauchy_of_approximate_orthogonality
#check @Erdos335.IntermediateScale.exists_vanishing_prefix_cauchy_bound
#print axioms Erdos335.IntermediateScale.exists_vanishing_prefix_cauchy_bound
#check @Erdos335.IntermediateScale.prefix_orthogonality_difference_sq_le
#print axioms Erdos335.IntermediateScale.prefix_orthogonality_difference_sq_le
#check @Erdos335.IntermediateScale.prefix_orthogonality_limit
#print axioms Erdos335.IntermediateScale.prefix_orthogonality_limit
#check @Erdos335.IntermediateScale.prefix_mean_sq_le_energy
#print axioms Erdos335.IntermediateScale.prefix_mean_sq_le_energy
#check @Erdos335.IntermediateScale.prefix_mean_preservation_limit
#print axioms Erdos335.IntermediateScale.prefix_mean_preservation_limit
#check @Erdos335.IntermediateScale.exists_bounded_prefix_decomposition_limit
#print axioms Erdos335.IntermediateScale.exists_bounded_prefix_decomposition_limit
#check @Erdos335.IntermediateScale.exists_mean_preserving_prefix_decomposition_limit
#print axioms Erdos335.IntermediateScale.exists_mean_preserving_prefix_decomposition_limit
#check @Erdos335.IntermediateScale.exists_sparse_prefix_subsequence
#print axioms Erdos335.IntermediateScale.exists_sparse_prefix_subsequence
#check @Erdos335.IntermediateScale.sum_full_blocks
#print axioms Erdos335.IntermediateScale.sum_full_blocks
#check @Erdos335.IntermediateScale.sum_full_blocks_eq_zero
#print axioms Erdos335.IntermediateScale.sum_full_blocks_eq_zero
#check @Erdos335.IntermediateScale.sum_full_blocks_le
#print axioms Erdos335.IntermediateScale.sum_full_blocks_le
#check @Erdos335.IntermediateScale.blockLift
#print axioms Erdos335.IntermediateScale.blockLift
#check @Erdos335.IntermediateScale.blockLift_apply
#print axioms Erdos335.IntermediateScale.blockLift_apply
#check @Erdos335.IntermediateScale.blockwise_arithmetic_regularity
#print axioms Erdos335.IntermediateScale.blockwise_arithmetic_regularity
#check @Erdos335.IntermediateScale.block_crossing_remainder
#print axioms Erdos335.IntermediateScale.block_crossing_remainder
#check @Erdos335.IntermediateScale.block_crossing_window_card
#print axioms Erdos335.IntermediateScale.block_crossing_window_card
#check @Erdos335.IntermediateScale.block_crossing_density_bound
#print axioms Erdos335.IntermediateScale.block_crossing_density_bound
#check @Erdos335.IntermediateScale.block_crossing_density_tendsto_zero
#print axioms Erdos335.IntermediateScale.block_crossing_density_tendsto_zero
#check @Erdos335.IntermediateScale.block_quotient_constant
#print axioms Erdos335.IntermediateScale.block_quotient_constant
#check @Erdos335.IntermediateScale.block_function_constant
#print axioms Erdos335.IntermediateScale.block_function_constant
#check @Erdos335.IntermediateScale.prefix_block_remainder_norm
#print axioms Erdos335.IntermediateScale.prefix_block_remainder_norm
#check @Erdos335.IntermediateScale.aligned_blocks_norm_bound
#print axioms Erdos335.IntermediateScale.aligned_blocks_norm_bound
#check @Erdos335.IntermediateScale.window_norm_bound_of_blocks
#print axioms Erdos335.IntermediateScale.window_norm_bound_of_blocks
#check @Erdos335.IntermediateScale.unitCharacter_add
#print axioms Erdos335.IntermediateScale.unitCharacter_add
#check @Erdos335.IntermediateScale.window_fourier_shift_norm
#print axioms Erdos335.IntermediateScale.window_fourier_shift_norm
#check @Erdos335.IntermediateScale.window_fourier_bound_of_blocks
#print axioms Erdos335.IntermediateScale.window_fourier_bound_of_blocks
#check @Erdos335.IntermediateScale.exists_common_bounded_correlation_subsequence
#print axioms Erdos335.IntermediateScale.exists_common_bounded_correlation_subsequence
#check @Erdos335.IntermediateScale.exists_common_filtered_correlation_subsequence
#print axioms Erdos335.IntermediateScale.exists_common_filtered_correlation_subsequence
#check @Erdos335.IntermediateScale.prefix_zero_block_norm
#print axioms Erdos335.IntermediateScale.prefix_zero_block_norm
#check @Erdos335.IntermediateScale.prefix_sum_le_of_block_bounds
#print axioms Erdos335.IntermediateScale.prefix_sum_le_of_block_bounds
#check @Erdos335.IntermediateScale.prefix_average_le_of_block_bounds
#print axioms Erdos335.IntermediateScale.prefix_average_le_of_block_bounds
#check @Erdos335.IntermediateScale.prefix_zero_block_real_average
#print axioms Erdos335.IntermediateScale.prefix_zero_block_real_average
#check @Erdos335.IntermediateScale.real_frequency_polynomial_norm_le
#print axioms Erdos335.IntermediateScale.real_frequency_polynomial_norm_le
#check @Erdos335.IntermediateScale.prefix_polynomial_model_error
#print axioms Erdos335.IntermediateScale.prefix_polynomial_model_error
#check @Erdos335.IntermediateScale.tendsto_zero_of_square_bound
#print axioms Erdos335.IntermediateScale.tendsto_zero_of_square_bound
#check @Erdos335.IntermediateScale.sparse_prefix_stitch_energy
#print axioms Erdos335.IntermediateScale.sparse_prefix_stitch_energy
#check @Erdos335.IntermediateScale.sparse_prefix_stitch_orthogonality
#print axioms Erdos335.IntermediateScale.sparse_prefix_stitch_orthogonality
#check @Erdos335.IntermediateScale.sparse_prefix_stitch_mean
#print axioms Erdos335.IntermediateScale.sparse_prefix_stitch_mean
#check @Erdos335.IntermediateScale.filtered_prefix_energy_cauchy
#print axioms Erdos335.IntermediateScale.filtered_prefix_energy_cauchy
#check @Erdos335.IntermediateScale.exists_filtered_prefix_decomposition
#print axioms Erdos335.IntermediateScale.exists_filtered_prefix_decomposition
#check @Erdos335.IntermediateScale.nested_projection_norm_identity
#print axioms Erdos335.IntermediateScale.nested_projection_norm_identity
#check @Erdos335.IntermediateScale.nested_projection_norm_le
#print axioms Erdos335.IntermediateScale.nested_projection_norm_le
#check @Erdos335.IntermediateScale.nested_projection_eq_of_norm_eq
#print axioms Erdos335.IntermediateScale.nested_projection_eq_of_norm_eq
#check @Erdos335.IntermediateScale.exists_flat_structured_fiber
#print axioms Erdos335.IntermediateScale.exists_flat_structured_fiber
#check @Erdos335.IntermediateScale.hilbert_approximation_distance_identity
#print axioms Erdos335.IntermediateScale.hilbert_approximation_distance_identity
#check @Erdos335.IntermediateScale.hilbert_approximation_energy_cauchy
#print axioms Erdos335.IntermediateScale.hilbert_approximation_energy_cauchy
#check @Erdos335.IntermediateScale.hilbert_approximation_cauchy
#print axioms Erdos335.IntermediateScale.hilbert_approximation_cauchy
#check @Erdos335.IntermediateScale.exists_hilbert_approximation_limit
#print axioms Erdos335.IntermediateScale.exists_hilbert_approximation_limit
#check @Erdos335.IntermediateScale.hilbert_cross_limit
#print axioms Erdos335.IntermediateScale.hilbert_cross_limit
#check @Erdos335.IntermediateScale.exists_hilbert_structured_family
#print axioms Erdos335.IntermediateScale.exists_hilbert_structured_family
#check @Erdos335.Loeb.realLoebFunction
#print axioms Erdos335.Loeb.realLoebFunction
#check @Erdos335.Loeb.realLoebFunction_mem
#print axioms Erdos335.Loeb.realLoebFunction_mem
#check @Erdos335.Loeb.measurable_realLoebFunction
#print axioms Erdos335.Loeb.measurable_realLoebFunction
#check @Erdos335.Loeb.realLoebFunction_memLp
#print axioms Erdos335.Loeb.realLoebFunction_memLp
#check @Erdos335.Loeb.realLoebVector
#print axioms Erdos335.Loeb.realLoebVector
#check @Erdos335.Loeb.realLoebVector_norm_sq
#print axioms Erdos335.Loeb.realLoebVector_norm_sq
#check @Erdos335.Loeb.tendsto_realLoebVector_energy
#print axioms Erdos335.Loeb.tendsto_realLoebVector_energy
#check @Erdos335.Loeb.tendsto_realLoebFunction
#print axioms Erdos335.Loeb.tendsto_realLoebFunction
#check @Erdos335.Loeb.realLoebFunction_mul
#print axioms Erdos335.Loeb.realLoebFunction_mul
#check @Erdos335.Loeb.tendsto_realLoebFunction_averages
#print axioms Erdos335.Loeb.tendsto_realLoebFunction_averages
#check @Erdos335.Loeb.realLoebVector_inner
#print axioms Erdos335.Loeb.realLoebVector_inner
#check @Erdos335.Loeb.tendsto_realLoebVector_inner
#print axioms Erdos335.Loeb.tendsto_realLoebVector_inner
#check @Erdos335.Loeb.tendsto_realLoebVector_residual_correlation
#print axioms Erdos335.Loeb.tendsto_realLoebVector_residual_correlation
#check @Erdos335.Loeb.realLoebVector_norm_le_one
#print axioms Erdos335.Loeb.realLoebVector_norm_le_one
#check @Erdos335.Loeb.realLoebVector_residual_inner_eq_zero
#print axioms Erdos335.Loeb.realLoebVector_residual_inner_eq_zero
#check @Erdos335.Loeb.realLoebVector_residual_inner_bound
#print axioms Erdos335.Loeb.realLoebVector_residual_inner_bound
#check @Erdos335.Loeb.exists_loeb_structured_family
#print axioms Erdos335.Loeb.exists_loeb_structured_family
#check @Erdos335.IntermediateScale.prefix_norm_bound_of_block_norm_bound
#print axioms Erdos335.IntermediateScale.prefix_norm_bound_of_block_norm_bound
#check @Erdos335.IntermediateScale.coarse_block_correlation_bound
#print axioms Erdos335.IntermediateScale.coarse_block_correlation_bound
#check @Erdos335.IntermediateScale.cross_scale_prefix_correlation_bound
#print axioms Erdos335.IntermediateScale.cross_scale_prefix_correlation_bound
#check @Erdos335.IntermediateScale.prefix_supported_abs_sum_bound
#print axioms Erdos335.IntermediateScale.prefix_supported_abs_sum_bound
#check @Erdos335.IntermediateScale.prefix_patch_correlation_bound
#print axioms Erdos335.IntermediateScale.prefix_patch_correlation_bound
#check @Erdos335.IntermediateScale.sparse_stitch_cross_correlation
#print axioms Erdos335.IntermediateScale.sparse_stitch_cross_correlation
#check @Erdos335.IntermediateScale.filtered_stitched_correlation_bound
#print axioms Erdos335.IntermediateScale.filtered_stitched_correlation_bound
#check @Erdos335.IntermediateScale.prefix_sum_le_of_patching
#print axioms Erdos335.IntermediateScale.prefix_sum_le_of_patching
#check @Erdos335.IntermediateScale.BlockRegularModel
#print axioms Erdos335.IntermediateScale.BlockRegularModel
#check @Erdos335.IntermediateScale.exists_block_regular_model
#print axioms Erdos335.IntermediateScale.exists_block_regular_model
#check @Erdos335.IntermediateScale.BlockRegularModel.polynomial
#print axioms Erdos335.IntermediateScale.BlockRegularModel.polynomial
#check @Erdos335.IntermediateScale.BlockRegularModel.polynomial_norm_le
#print axioms Erdos335.IntermediateScale.BlockRegularModel.polynomial_norm_le
#check @Erdos335.IntermediateScale.BlockRegularModel.error_sq_bound
#print axioms Erdos335.IntermediateScale.BlockRegularModel.error_sq_bound
#check @Erdos335.IntermediateScale.BlockRegularModel.prefix_approximation
#print axioms Erdos335.IntermediateScale.BlockRegularModel.prefix_approximation
#check @Erdos335.IntermediateScale.BlockRegularModel.residual_abs_le_one
#print axioms Erdos335.IntermediateScale.BlockRegularModel.residual_abs_le_one
#check @Erdos335.IntermediateScale.BlockRegularModel.prefix_mean
#print axioms Erdos335.IntermediateScale.BlockRegularModel.prefix_mean
#check @Erdos335.IntermediateScale.BlockRegularModel.prefix_orthogonality
#print axioms Erdos335.IntermediateScale.BlockRegularModel.prefix_orthogonality
#check @Erdos335.IntermediateScale.stitchedBlockValue
#print axioms Erdos335.IntermediateScale.stitchedBlockValue
#check @Erdos335.IntermediateScale.stitchedBlockPolynomial
#print axioms Erdos335.IntermediateScale.stitchedBlockPolynomial
#check @Erdos335.IntermediateScale.stitchedBlockValue_mem
#print axioms Erdos335.IntermediateScale.stitchedBlockValue_mem
#check @Erdos335.IntermediateScale.stitchedBlockPolynomial_norm_le
#print axioms Erdos335.IntermediateScale.stitchedBlockPolynomial_norm_le
#check @Erdos335.IntermediateScale.stitchedBlock_prefix_approximation
#print axioms Erdos335.IntermediateScale.stitchedBlock_prefix_approximation
#check @Erdos335.IntermediateScale.stitchedBlock_orthogonality
#print axioms Erdos335.IntermediateScale.stitchedBlock_orthogonality
#check @Erdos335.IntermediateScale.stitchedBlock_mean_preservation
#print axioms Erdos335.IntermediateScale.stitchedBlock_mean_preservation
#check @Erdos335.IntermediateScale.stitchedBlockCoefficient
#print axioms Erdos335.IntermediateScale.stitchedBlockCoefficient
#check @Erdos335.IntermediateScale.stitchedBlockFrequency
#print axioms Erdos335.IntermediateScale.stitchedBlockFrequency
#check @Erdos335.IntermediateScale.stitchedBlockPolynomial_representation
#print axioms Erdos335.IntermediateScale.stitchedBlockPolynomial_representation
#check @Erdos335.IntermediateScale.stitchedBlockCoefficient_bound
#print axioms Erdos335.IntermediateScale.stitchedBlockCoefficient_bound
#check @Erdos335.IntermediateScale.stitchedBlockParameters_constant_on_window
#print axioms Erdos335.IntermediateScale.stitchedBlockParameters_constant_on_window
#check @Erdos335.IntermediateScale.terminal_window_count
#print axioms Erdos335.IntermediateScale.terminal_window_count
#check @Erdos335.IntermediateScale.varyingParameterWindows
#print axioms Erdos335.IntermediateScale.varyingParameterWindows
#check @Erdos335.IntermediateScale.varyingParameterWindows_card
#print axioms Erdos335.IntermediateScale.varyingParameterWindows_card
#check @Erdos335.IntermediateScale.varyingParameterWindows_density_bound
#print axioms Erdos335.IntermediateScale.varyingParameterWindows_density_bound
#check @Erdos335.IntermediateScale.varyingParameterWindows_density_tendsto_zero
#print axioms Erdos335.IntermediateScale.varyingParameterWindows_density_tendsto_zero
#check @Erdos335.IntermediateScale.windowFourierNorm
#print axioms Erdos335.IntermediateScale.windowFourierNorm
#check @Erdos335.IntermediateScale.window_fourier_coefficient_le_abs_average
#print axioms Erdos335.IntermediateScale.window_fourier_coefficient_le_abs_average
#check @Erdos335.IntermediateScale.window_fourier_coefficients_bddAbove
#print axioms Erdos335.IntermediateScale.window_fourier_coefficients_bddAbove
#check @Erdos335.IntermediateScale.windowFourierNorm_nonneg
#print axioms Erdos335.IntermediateScale.windowFourierNorm_nonneg
#check @Erdos335.IntermediateScale.windowFourierNorm_le_of_coefficients
#print axioms Erdos335.IntermediateScale.windowFourierNorm_le_of_coefficients
#check @Erdos335.IntermediateScale.windowFourierNorm_le_one
#print axioms Erdos335.IntermediateScale.windowFourierNorm_le_one
#check @Erdos335.IntermediateScale.windowFourierNorm_of_blocks
#print axioms Erdos335.IntermediateScale.windowFourierNorm_of_blocks
#check @Erdos335.IntermediateScale.exceptional_average_bound
#print axioms Erdos335.IntermediateScale.exceptional_average_bound
#check @Erdos335.IntermediateScale.edge_window_count
#print axioms Erdos335.IntermediateScale.edge_window_count
#check @Erdos335.IntermediateScale.windowFourierNorm_congr
#print axioms Erdos335.IntermediateScale.windowFourierNorm_congr
#check @Erdos335.IntermediateScale.stitched_residual_abs_le_one
#print axioms Erdos335.IntermediateScale.stitched_residual_abs_le_one
#check @Erdos335.IntermediateScale.stitched_residual_fourier_average_bound
#print axioms Erdos335.IntermediateScale.stitched_residual_fourier_average_bound
#check @Erdos335.IntermediateScale.stitched_residual_fourier_average_asymptotic
#print axioms Erdos335.IntermediateScale.stitched_residual_fourier_average_asymptotic
#check @Erdos335.IntermediateScale.hilbert_cross_limit_of_lt
#print axioms Erdos335.IntermediateScale.hilbert_cross_limit_of_lt
#check @Erdos335.IntermediateScale.exists_hilbert_strict_structured_family
#print axioms Erdos335.IntermediateScale.exists_hilbert_strict_structured_family
#check @Erdos335.IntermediateScale.BlockRegularModel.same_scale_block_correlation
#print axioms Erdos335.IntermediateScale.BlockRegularModel.same_scale_block_correlation
#check @Erdos335.IntermediateScale.BlockRegularModel.same_scale_prefix_correlation
#print axioms Erdos335.IntermediateScale.BlockRegularModel.same_scale_prefix_correlation
#check @Erdos335.IntermediateScale.BlockRegularModel.cross_scale_prefix_correlation
#print axioms Erdos335.IntermediateScale.BlockRegularModel.cross_scale_prefix_correlation
#check @Erdos335.IntermediateScale.stitched_models_correlation_bound
#print axioms Erdos335.IntermediateScale.stitched_models_correlation_bound
#check @Erdos335.IntermediateScale.exists_block_regularity_sequence
#print axioms Erdos335.IntermediateScale.exists_block_regularity_sequence
#check @Erdos335.Loeb.prefixLoebVector
#print axioms Erdos335.Loeb.prefixLoebVector
#check @Erdos335.Loeb.tendsto_prefixLoebVector_energy
#print axioms Erdos335.Loeb.tendsto_prefixLoebVector_energy
#check @Erdos335.Loeb.tendsto_prefixLoebVector_residual_correlation
#print axioms Erdos335.Loeb.tendsto_prefixLoebVector_residual_correlation
#check @Erdos335.Loeb.exists_loeb_block_structured_family
#print axioms Erdos335.Loeb.exists_loeb_block_structured_family
#check @Erdos335.Loeb.exists_loeb_regular_structured_family
#print axioms Erdos335.Loeb.exists_loeb_regular_structured_family
#check @Erdos335.IntermediateScale.positiveIntermediateScale
#print axioms Erdos335.IntermediateScale.positiveIntermediateScale
#check @Erdos335.IntermediateScale.positiveIntermediateScale_pos
#print axioms Erdos335.IntermediateScale.positiveIntermediateScale_pos
#check @Erdos335.IntermediateScale.positiveIntermediateScale_eventually_eq
#print axioms Erdos335.IntermediateScale.positiveIntermediateScale_eventually_eq
#check @Erdos335.IntermediateScale.positiveIntermediateScale_atTop
#print axioms Erdos335.IntermediateScale.positiveIntermediateScale_atTop
#check @Erdos335.IntermediateScale.positiveIntermediateScale_lower_ratio
#print axioms Erdos335.IntermediateScale.positiveIntermediateScale_lower_ratio
#check @Erdos335.IntermediateScale.positiveIntermediateScale_ambient_ratio
#print axioms Erdos335.IntermediateScale.positiveIntermediateScale_ambient_ratio
#check @Erdos335.IntermediateScale.positiveIntermediateScale_lexicographic_ratio
#print axioms Erdos335.IntermediateScale.positiveIntermediateScale_lexicographic_ratio
#check @Erdos335.IntermediateScale.BlockScaleParameter
#print axioms Erdos335.IntermediateScale.BlockScaleParameter
#check @Erdos335.IntermediateScale.blockScaleExponent
#print axioms Erdos335.IntermediateScale.blockScaleExponent
#check @Erdos335.IntermediateScale.blockScaleFamily
#print axioms Erdos335.IntermediateScale.blockScaleFamily
#check @Erdos335.IntermediateScale.blockScaleExponent_mem
#print axioms Erdos335.IntermediateScale.blockScaleExponent_mem
#check @Erdos335.IntermediateScale.blockScaleFamily_pos
#print axioms Erdos335.IntermediateScale.blockScaleFamily_pos
#check @Erdos335.IntermediateScale.blockScaleFamily_ambient_ratio
#print axioms Erdos335.IntermediateScale.blockScaleFamily_ambient_ratio
#check @Erdos335.IntermediateScale.blockScaleFamily_separated
#print axioms Erdos335.IntermediateScale.blockScaleFamily_separated
#check @Erdos335.IntermediateScale.exists_flat_unitInterval_structured_fiber
#print axioms Erdos335.IntermediateScale.exists_flat_unitInterval_structured_fiber
#check @Erdos335.Loeb.exists_loeb_flat_scale_family
#print axioms Erdos335.Loeb.exists_loeb_flat_scale_family
#check @Erdos335.IntermediateScale.exists_filtered_prefix_decomposition_with_tests
#print axioms Erdos335.IntermediateScale.exists_filtered_prefix_decomposition_with_tests
#check @Erdos335.Loeb.tendsto_prefixLoebVector_correlation
#print axioms Erdos335.Loeb.tendsto_prefixLoebVector_correlation
#check @Erdos335.Loeb.tendsto_prefixLoebVector_distance
#print axioms Erdos335.Loeb.tendsto_prefixLoebVector_distance
#check @Erdos335.IntermediateScale.prefixEnergy_triangle
#print axioms Erdos335.IntermediateScale.prefixEnergy_triangle
#check @Erdos335.IntermediateScale.exists_filtered_two_prefix_decomposition
#print axioms Erdos335.IntermediateScale.exists_filtered_two_prefix_decomposition
#check @Erdos335.Loeb.exists_ordinary_realization_of_equal_loeb_limits
#print axioms Erdos335.Loeb.exists_ordinary_realization_of_equal_loeb_limits
#check @Erdos335.IntermediateScale.exists_ordinary_flat_scale_decomposition
#print axioms Erdos335.IntermediateScale.exists_ordinary_flat_scale_decomposition
#check @Erdos335.IntermediateScale.shifted_prefix_sum_le
#print axioms Erdos335.IntermediateScale.shifted_prefix_sum_le
#check @Erdos335.IntermediateScale.averaged_window_sum_le
#print axioms Erdos335.IntermediateScale.averaged_window_sum_le
#check @Erdos335.IntermediateScale.windowFourierNorm_difference_bound
#print axioms Erdos335.IntermediateScale.windowFourierNorm_difference_bound
#check @Erdos335.IntermediateScale.averaged_windowFourierNorm_difference_bound
#print axioms Erdos335.IntermediateScale.averaged_windowFourierNorm_difference_bound
#check @Erdos335.IntermediateScale.averaged_windowFourierNorm_tendsto_zero
#print axioms Erdos335.IntermediateScale.averaged_windowFourierNorm_tendsto_zero
#check @Erdos335.IntermediateScale.prefix_polynomial_triangle
#print axioms Erdos335.IntermediateScale.prefix_polynomial_triangle
#check @Erdos335.IntermediateScale.stitched_polynomial_approximation_of_limit
#print axioms Erdos335.IntermediateScale.stitched_polynomial_approximation_of_limit
#check @Erdos335.IntermediateScale.stitched_residual_uniformity_of_limit
#print axioms Erdos335.IntermediateScale.stitched_residual_uniformity_of_limit
#check @Erdos335.IntermediateScale.varyingParameterWindows_density_along_subsequence
#print axioms Erdos335.IntermediateScale.varyingParameterWindows_density_along_subsequence
#check @Erdos335.IntermediateScale.window_ratio_tendsto_zero_of_intermediate
#print axioms Erdos335.IntermediateScale.window_ratio_tendsto_zero_of_intermediate
#check @Erdos335.IntermediateScale.exists_intermediate_block_decomposition
#print axioms Erdos335.IntermediateScale.exists_intermediate_block_decomposition
#check @Erdos335.IntermediateScale.exists_common_flat_energy_fiber
#print axioms Erdos335.IntermediateScale.exists_common_flat_energy_fiber
#check @Erdos335.IntermediateScale.exists_common_flat_unitInterval_family
#print axioms Erdos335.IntermediateScale.exists_common_flat_unitInterval_family
#check @Erdos335.IntermediateScale.frequencyThresholdAverage
#print axioms Erdos335.IntermediateScale.frequencyThresholdAverage
#check @Erdos335.IntermediateScale.frequencyThresholdAverage_mem
#print axioms Erdos335.IntermediateScale.frequencyThresholdAverage_mem
#check @Erdos335.IntermediateScale.frequencyThresholdAverage_antitone
#print axioms Erdos335.IntermediateScale.frequencyThresholdAverage_antitone
#check @Erdos335.IntermediateScale.frequencyThresholdLimit
#print axioms Erdos335.IntermediateScale.frequencyThresholdLimit
#check @Erdos335.IntermediateScale.tendsto_frequencyThresholdLimit
#print axioms Erdos335.IntermediateScale.tendsto_frequencyThresholdLimit
#check @Erdos335.IntermediateScale.frequencyThresholdLimit_antitone
#print axioms Erdos335.IntermediateScale.frequencyThresholdLimit_antitone
#check @Erdos335.IntermediateScale.eventually_scale_le_of_ratio_zero
#print axioms Erdos335.IntermediateScale.eventually_scale_le_of_ratio_zero
#check @Erdos335.IntermediateScale.exists_common_flat_frequency_profile
#print axioms Erdos335.IntermediateScale.exists_common_flat_frequency_profile
#check @Erdos335.IntermediateScale.frequencyBandDensity
#print axioms Erdos335.IntermediateScale.frequencyBandDensity
#check @Erdos335.IntermediateScale.frequencyBandDensity_le_threshold_difference
#print axioms Erdos335.IntermediateScale.frequencyBandDensity_le_threshold_difference
#check @Erdos335.IntermediateScale.frequencyBandDensity_tendsto_zero
#print axioms Erdos335.IntermediateScale.frequencyBandDensity_tendsto_zero
#check @Erdos335.IntermediateScale.exists_frequency_scale_selection
#print axioms Erdos335.IntermediateScale.exists_frequency_scale_selection
#check @Erdos335.IntermediateScale.reciprocal_scale_ratio_tendsto_atTop
#print axioms Erdos335.IntermediateScale.reciprocal_scale_ratio_tendsto_atTop
#check @Erdos335.IntermediateScale.scale_tendsto_atTop_of_smaller
#print axioms Erdos335.IntermediateScale.scale_tendsto_atTop_of_smaller
#check @Erdos335.IntermediateScale.finite_union_density_tendsto_zero
#print axioms Erdos335.IntermediateScale.finite_union_density_tendsto_zero
#check @Erdos335.IntermediateScale.principalFrequency
#print axioms Erdos335.IntermediateScale.principalFrequency
#check @Erdos335.IntermediateScale.principalFrequency_mem
#print axioms Erdos335.IntermediateScale.principalFrequency_mem
#check @Erdos335.IntermediateScale.unitCharacter_int
#print axioms Erdos335.IntermediateScale.unitCharacter_int
#check @Erdos335.IntermediateScale.unitCharacter_principalFrequency
#print axioms Erdos335.IntermediateScale.unitCharacter_principalFrequency
#check @Erdos335.IntermediateScale.circleFrequencyDistance
#print axioms Erdos335.IntermediateScale.circleFrequencyDistance
#check @Erdos335.IntermediateScale.circleFrequencyDistance_mem
#print axioms Erdos335.IntermediateScale.circleFrequencyDistance_mem
#check @Erdos335.IntermediateScale.circleFrequencyDistance_le_abs_sub_int
#print axioms Erdos335.IntermediateScale.circleFrequencyDistance_le_abs_sub_int
#check @Erdos335.IntermediateScale.BoundedFrequencyWeights
#print axioms Erdos335.IntermediateScale.BoundedFrequencyWeights
#check @Erdos335.IntermediateScale.frequencyCombination
#print axioms Erdos335.IntermediateScale.frequencyCombination
#check @Erdos335.IntermediateScale.badFrequencyCombinationWindows
#print axioms Erdos335.IntermediateScale.badFrequencyCombinationWindows
#check @Erdos335.IntermediateScale.badFrequencyCombinationWindows_density_tendsto_zero
#print axioms Erdos335.IntermediateScale.badFrequencyCombinationWindows_density_tendsto_zero
#check @Erdos335.IntermediateScale.boundedFrequencyWeights_represent
#print axioms Erdos335.IntermediateScale.boundedFrequencyWeights_represent
#check @Erdos335.IntermediateScale.exists_polynomial_frequency_scale_selection
#print axioms Erdos335.IntermediateScale.exists_polynomial_frequency_scale_selection
#check @Erdos335.IntermediateScale.variableFrequencyPolynomial
#print axioms Erdos335.IntermediateScale.variableFrequencyPolynomial
#check @Erdos335.IntermediateScale.varyingPolynomialParameters
#print axioms Erdos335.IntermediateScale.varyingPolynomialParameters
#check @Erdos335.IntermediateScale.variableFrequencyPolynomial_stitched
#print axioms Erdos335.IntermediateScale.variableFrequencyPolynomial_stitched
#check @Erdos335.IntermediateScale.varyingPolynomialParameters_stitched
#print axioms Erdos335.IntermediateScale.varyingPolynomialParameters_stitched
#check @Erdos335.IntermediateScale.sparse_prefix_ratio_subsequence
#print axioms Erdos335.IntermediateScale.sparse_prefix_ratio_subsequence
#check @Erdos335.IntermediateScale.exists_intermediate_fourier_decomposition
#print axioms Erdos335.IntermediateScale.exists_intermediate_fourier_decomposition
#check @Erdos335.IntermediateScale.polynomial_translation_norm_le
#print axioms Erdos335.IntermediateScale.polynomial_translation_norm_le
#check @Erdos335.IntermediateScale.polynomial_parameters_constant_of_not_mem
#print axioms Erdos335.IntermediateScale.polynomial_parameters_constant_of_not_mem
#check @Erdos335.IntermediateScale.variable_polynomial_translation_norm_le
#print axioms Erdos335.IntermediateScale.variable_polynomial_translation_norm_le
#check @Erdos335.IntermediateScale.variable_polynomial_translation_of_not_mem
#print axioms Erdos335.IntermediateScale.variable_polynomial_translation_of_not_mem
#check @Erdos335.IntermediateScale.shifted_window_sum_le_extended_window
#print axioms Erdos335.IntermediateScale.shifted_window_sum_le_extended_window
#check @Erdos335.IntermediateScale.variable_shifted_window_average_le
#print axioms Erdos335.IntermediateScale.variable_shifted_window_average_le
#check @Erdos335.IntermediateScale.variable_shifted_error_average_le
#print axioms Erdos335.IntermediateScale.variable_shifted_error_average_le
#check @Erdos335.FiniteFourier.convolution_energy_le_of_coefficients
#print axioms Erdos335.FiniteFourier.convolution_energy_le_of_coefficients
#check @Erdos335.FiniteFourier.convolution_l1_le_of_coefficients
#print axioms Erdos335.FiniteFourier.convolution_l1_le_of_coefficients
#check @Erdos335.IntermediateScale.finite_character_integer_frequency
#print axioms Erdos335.IntermediateScale.finite_character_integer_frequency
#check @Erdos335.IntermediateScale.sum_zmod_eq_range
#print axioms Erdos335.IntermediateScale.sum_zmod_eq_range
#check @Erdos335.IntermediateScale.cyclicFourierWindow
#print axioms Erdos335.IntermediateScale.cyclicFourierWindow
#check @Erdos335.IntermediateScale.cyclicFourierWindow_coefficient_le
#print axioms Erdos335.IntermediateScale.cyclicFourierWindow_coefficient_le
#check @Erdos335.IntermediateScale.cyclicFourierWindow_convolution_l1_le
#print axioms Erdos335.IntermediateScale.cyclicFourierWindow_convolution_l1_le
#check @Erdos335.IntermediateScale.unitCharacter_nat_mul
#print axioms Erdos335.IntermediateScale.unitCharacter_nat_mul
#check @Erdos335.IntermediateScale.intervalCharacterMean
#print axioms Erdos335.IntermediateScale.intervalCharacterMean
#check @Erdos335.IntermediateScale.intervalCharacterMean_norm_le
#print axioms Erdos335.IntermediateScale.intervalCharacterMean_norm_le
#check @Erdos335.IntermediateScale.orbit_polynomial_mean_bound
#print axioms Erdos335.IntermediateScale.orbit_polynomial_mean_bound
#check @Erdos335.IntermediateScale.exists_large_orbit_polynomial_value
#print axioms Erdos335.IntermediateScale.exists_large_orbit_polynomial_value
#check @Erdos335.IntermediateScale.exists_torus_polynomial_approximation
#print axioms Erdos335.IntermediateScale.exists_torus_polynomial_approximation
#check @Erdos335.IntermediateScale.integral_torus_monomial
#print axioms Erdos335.IntermediateScale.integral_torus_monomial
#check @Erdos335.IntermediateScale.integrable_torus_monomial
#print axioms Erdos335.IntermediateScale.integrable_torus_monomial
#check @Erdos335.IntermediateScale.integral_torus_polynomial
#print axioms Erdos335.IntermediateScale.integral_torus_polynomial
#check @Erdos335.IntermediateScale.torus_polynomial_integral_error
#print axioms Erdos335.IntermediateScale.torus_polynomial_integral_error
#check @Erdos335.IntermediateScale.exists_torus_polynomial_with_constant
#print axioms Erdos335.IntermediateScale.exists_torus_polynomial_with_constant
#check @Erdos335.IntermediateScale.torusPhaseBump
#print axioms Erdos335.IntermediateScale.torusPhaseBump
#check @Erdos335.IntermediateScale.torusPhaseBump_nonneg
#print axioms Erdos335.IntermediateScale.torusPhaseBump_nonneg
#check @Erdos335.IntermediateScale.torusPhaseBump_zero
#print axioms Erdos335.IntermediateScale.torusPhaseBump_zero
#check @Erdos335.IntermediateScale.torusPhaseBump_positive_phases
#print axioms Erdos335.IntermediateScale.torusPhaseBump_positive_phases
#check @Erdos335.IntermediateScale.torusPhaseBump_integral_pos
#print axioms Erdos335.IntermediateScale.torusPhaseBump_integral_pos
#check @Erdos335.IntermediateScale.unitCharacter_sum
#print axioms Erdos335.IntermediateScale.unitCharacter_sum
#check @Erdos335.IntermediateScale.fourier_coe_eq_unitCharacter
#print axioms Erdos335.IntermediateScale.fourier_coe_eq_unitCharacter
#check @Erdos335.IntermediateScale.integerTorusOrbit
#print axioms Erdos335.IntermediateScale.integerTorusOrbit
#check @Erdos335.IntermediateScale.mFourier_integerTorusOrbit
#print axioms Erdos335.IntermediateScale.mFourier_integerTorusOrbit
#check @Erdos335.IntermediateScale.fourier_integerTorusOrbit
#print axioms Erdos335.IntermediateScale.fourier_integerTorusOrbit
#check @Erdos335.IntermediateScale.exists_torus_phase_test
#print axioms Erdos335.IntermediateScale.exists_torus_phase_test
#check @Erdos335.IntermediateScale.fourier_add_points
#print axioms Erdos335.IntermediateScale.fourier_add_points
#check @Erdos335.IntermediateScale.mFourier_add_points
#print axioms Erdos335.IntermediateScale.mFourier_add_points
#check @Erdos335.IntermediateScale.mFourier_sub_indices
#print axioms Erdos335.IntermediateScale.mFourier_sub_indices
#check @Erdos335.IntermediateScale.torus_polynomial_self_correlation
#print axioms Erdos335.IntermediateScale.torus_polynomial_self_correlation
#check @Erdos335.IntermediateScale.intervalCharacterMean_sub_one_le
#print axioms Erdos335.IntermediateScale.intervalCharacterMean_sub_one_le
#check @Erdos335.IntermediateScale.unitCharacter_distance_bounds
#print axioms Erdos335.IntermediateScale.unitCharacter_distance_bounds
#check @Erdos335.IntermediateScale.positive_weighted_real_sum_lower
#print axioms Erdos335.IntermediateScale.positive_weighted_real_sum_lower
#check @Erdos335.IntermediateScale.intervalCharacterMean_real_lower
#print axioms Erdos335.IntermediateScale.intervalCharacterMean_real_lower
#check @Erdos335.IntermediateScale.unit_mul_sub_one_triangle
#print axioms Erdos335.IntermediateScale.unit_mul_sub_one_triangle
#check @Erdos335.IntermediateScale.torusPhaseBump_le
#print axioms Erdos335.IntermediateScale.torusPhaseBump_le
#check @Erdos335.IntermediateScale.torusPhaseBump_product_zero
#print axioms Erdos335.IntermediateScale.torusPhaseBump_product_zero
#check @Erdos335.IntermediateScale.correlation_product_error
#print axioms Erdos335.IntermediateScale.correlation_product_error
#check @Erdos335.IntermediateScale.torus_bump_correlation_small
#print axioms Erdos335.IntermediateScale.torus_bump_correlation_small
#check @Erdos335.IntermediateScale.exists_positive_phase_polynomial
#print axioms Erdos335.IntermediateScale.exists_positive_phase_polynomial
#check @Erdos335.IntermediateScale.polynomial_orbit_mean
#print axioms Erdos335.IntermediateScale.polynomial_orbit_mean
#check @Erdos335.IntermediateScale.positive_polynomial_orbit_mean_lower
#print axioms Erdos335.IntermediateScale.positive_polynomial_orbit_mean_lower
#check @Erdos335.IntermediateScale.positive_polynomial_phase_hit
#print axioms Erdos335.IntermediateScale.positive_polynomial_phase_hit
#check @Erdos335.IntermediateScale.phase_orbit_error_bound
#print axioms Erdos335.IntermediateScale.phase_orbit_error_bound
#check @Erdos335.IntermediateScale.exists_simultaneous_approximate_period_constant
#print axioms Erdos335.IntermediateScale.exists_simultaneous_approximate_period_constant
#check @Erdos335.IntermediateScale.frequency_gap_of_not_mem_bad_windows
#print axioms Erdos335.IntermediateScale.frequency_gap_of_not_mem_bad_windows
#check @Erdos335.IntermediateScale.exists_polynomial_period_constant
#print axioms Erdos335.IntermediateScale.exists_polynomial_period_constant
#check @Erdos335.IntermediateScale.exceptional_average_bound_scaled
#print axioms Erdos335.IntermediateScale.exceptional_average_bound_scaled
#check @Erdos335.IntermediateScale.approximation_translation_triangle
#print axioms Erdos335.IntermediateScale.approximation_translation_triangle
#check @Erdos335.IntermediateScale.averagedWindowTranslationError
#print axioms Erdos335.IntermediateScale.averagedWindowTranslationError
#check @Erdos335.IntermediateScale.window_translation_error_transfer
#print axioms Erdos335.IntermediateScale.window_translation_error_transfer
#check @Erdos335.IntermediateScale.variableFrequencyPolynomial_norm_le
#print axioms Erdos335.IntermediateScale.variableFrequencyPolynomial_norm_le
#check @Erdos335.IntermediateScale.exists_polynomial_window_periods
#print axioms Erdos335.IntermediateScale.exists_polynomial_window_periods
#check @Erdos335.IntermediateScale.frequency_gap_after_integer_dilation
#print axioms Erdos335.IntermediateScale.frequency_gap_after_integer_dilation
#check @Erdos335.IntermediateScale.exists_divisible_phase_period_constant
#print axioms Erdos335.IntermediateScale.exists_divisible_phase_period_constant
#check @Erdos335.IntermediateScale.ceiling_division_bounds
#print axioms Erdos335.IntermediateScale.ceiling_division_bounds
#check @Erdos335.IntermediateScale.exists_short_divisible_window
#print axioms Erdos335.IntermediateScale.exists_short_divisible_window
#check @Erdos335.IntermediateScale.exists_short_divisible_phase_period_constant
#print axioms Erdos335.IntermediateScale.exists_short_divisible_phase_period_constant
#check @Erdos335.IntermediateScale.linearWindowConvolution
#print axioms Erdos335.IntermediateScale.linearWindowConvolution
#check @Erdos335.IntermediateScale.cyclicInput
#print axioms Erdos335.IntermediateScale.cyclicInput
#check @Erdos335.IntermediateScale.cyclicInput_norm_le
#print axioms Erdos335.IntermediateScale.cyclicInput_norm_le
#check @Erdos335.IntermediateScale.linearWindowConvolution_cyclic
#print axioms Erdos335.IntermediateScale.linearWindowConvolution_cyclic
#check @Erdos335.IntermediateScale.sum_zmod_eq_range_real
#print axioms Erdos335.IntermediateScale.sum_zmod_eq_range_real
#check @Erdos335.IntermediateScale.linear_window_convolution_average_le
#print axioms Erdos335.IntermediateScale.linear_window_convolution_average_le
#check @Erdos335.IntermediateScale.prefix_sum_le_shifted_prefix
#print axioms Erdos335.IntermediateScale.prefix_sum_le_shifted_prefix
#check @Erdos335.IntermediateScale.prefix_average_le_shifted_windows
#print axioms Erdos335.IntermediateScale.prefix_average_le_shifted_windows
#check @Erdos335.IntermediateScale.linearWindowConvolution_norm_le_one
#print axioms Erdos335.IntermediateScale.linearWindowConvolution_norm_le_one
#check @Erdos335.IntermediateScale.linear_convolution_prefix_bound
#print axioms Erdos335.IntermediateScale.linear_convolution_prefix_bound
#check @Erdos335.IntermediateScale.linear_convolution_l1_tendsto_zero
#print axioms Erdos335.IntermediateScale.linear_convolution_l1_tendsto_zero
#check @Erdos335.IntermediateScale.linear_convolution_energy_tendsto_zero
#print axioms Erdos335.IntermediateScale.linear_convolution_energy_tendsto_zero
#check @Erdos335.IntermediateScale.linearWindowConvolution_sub
#print axioms Erdos335.IntermediateScale.linearWindowConvolution_sub
#check @Erdos335.IntermediateScale.structured_convolution_energy_tendsto_zero
#print axioms Erdos335.IntermediateScale.structured_convolution_energy_tendsto_zero
#check @Erdos335.IntermediateScale.exists_divisible_polynomial_window_periods
#print axioms Erdos335.IntermediateScale.exists_divisible_polynomial_window_periods
#check @Erdos335.IntermediateScale.eventually_exists_structured_periods
#print axioms Erdos335.IntermediateScale.eventually_exists_structured_periods
#check @Erdos335.IntermediateScale.exists_asymptotic_structured_periods
#print axioms Erdos335.IntermediateScale.exists_asymptotic_structured_periods
#check @Erdos335.IntermediateScale.intermediate_fourier_convolution_and_periods
#print axioms Erdos335.IntermediateScale.intermediate_fourier_convolution_and_periods
#check @Erdos335.IntermediateScale.positiveWindowConvolution
#print axioms Erdos335.IntermediateScale.positiveWindowConvolution
#check @Erdos335.IntermediateScale.positiveWindowConvolution_succ
#print axioms Erdos335.IntermediateScale.positiveWindowConvolution_succ
#check @Erdos335.IntermediateScale.positive_structured_convolution_energy_tendsto_zero
#print axioms Erdos335.IntermediateScale.positive_structured_convolution_energy_tendsto_zero
#check @Erdos335.IntermediateScale.exists_intermediate_analytic_decomposition
#print axioms Erdos335.IntermediateScale.exists_intermediate_analytic_decomposition
#check @Erdos335.IntermediateScale.windowFourierNorm_extend
#print axioms Erdos335.IntermediateScale.windowFourierNorm_extend
#check @Erdos335.IntermediateScale.windowFourierNorm_extend_ratio
#print axioms Erdos335.IntermediateScale.windowFourierNorm_extend_ratio
#check @Erdos335.IntermediateScale.variableConvolutionAverage
#print axioms Erdos335.IntermediateScale.variableConvolutionAverage
#check @Erdos335.IntermediateScale.variable_convolution_average_bound
#print axioms Erdos335.IntermediateScale.variable_convolution_average_bound
#check @Erdos335.IntermediateScale.variable_convolution_average_tendsto_zero
#print axioms Erdos335.IntermediateScale.variable_convolution_average_tendsto_zero
#check @Erdos335.IntermediateScale.truncatedConvolutionInput
#print axioms Erdos335.IntermediateScale.truncatedConvolutionInput
#check @Erdos335.IntermediateScale.truncatedConvolutionInput_norm_le
#print axioms Erdos335.IntermediateScale.truncatedConvolutionInput_norm_le
#check @Erdos335.IntermediateScale.linearWindowConvolution_padding
#print axioms Erdos335.IntermediateScale.linearWindowConvolution_padding
#check @Erdos335.IntermediateScale.convolution_two_blocks_bound
#print axioms Erdos335.IntermediateScale.convolution_two_blocks_bound
#check @Erdos335.IntermediateScale.backward_window_sum_le
#print axioms Erdos335.IntermediateScale.backward_window_sum_le
#check @Erdos335.IntermediateScale.linearWindowConvolution_norm_le_abs_average
#print axioms Erdos335.IntermediateScale.linearWindowConvolution_norm_le_abs_average
#check @Erdos335.IntermediateScale.linear_convolution_translation_difference
#print axioms Erdos335.IntermediateScale.linear_convolution_translation_difference
#check @Erdos335.IntermediateScale.linearConvolutionPeriodError
#print axioms Erdos335.IntermediateScale.linearConvolutionPeriodError
#check @Erdos335.IntermediateScale.structured_convolution_period_bound
#print axioms Erdos335.IntermediateScale.structured_convolution_period_bound
#check @Erdos335.IntermediateScale.prefixConvolutionCount_linear
#print axioms Erdos335.IntermediateScale.prefixConvolutionCount_linear
#check @Erdos335.IntermediateScale.convolutionTranslationError_eq_linear
#print axioms Erdos335.IntermediateScale.convolutionTranslationError_eq_linear
#check @Erdos335.IntermediateScale.linear_convolution_period_approximation
#print axioms Erdos335.IntermediateScale.linear_convolution_period_approximation
#check @Erdos335.IntermediateScale.full_convolution_period_bound
#print axioms Erdos335.IntermediateScale.full_convolution_period_bound
#check @Erdos335.IntermediateScale.convolution_period_average_tendsto_zero
#print axioms Erdos335.IntermediateScale.convolution_period_average_tendsto_zero
#check @Erdos335.IntermediateScale.indicator_convolution_period_error_bound
#print axioms Erdos335.IntermediateScale.indicator_convolution_period_error_bound
#check @Erdos335.IntermediateScale.exists_small_before_tail
#print axioms Erdos335.IntermediateScale.exists_small_before_tail
#check @Erdos335.IntermediateScale.exists_small_interior_positions
#print axioms Erdos335.IntermediateScale.exists_small_interior_positions
#check @Erdos335.IntermediateScale.exists_selected_convolution_windows
#print axioms Erdos335.IntermediateScale.exists_selected_convolution_windows
#check @Erdos335.IntermediateScale.cyclicWindow_card_eq_prefixCount
#print axioms Erdos335.IntermediateScale.cyclicWindow_card_eq_prefixCount
#check @Erdos335.IntermediateScale.cyclic_window_density_of_prefix_error
#print axioms Erdos335.IntermediateScale.cyclic_window_density_of_prefix_error
#check @Erdos335.IntermediateScale.density_of_small_removed_subset
#print axioms Erdos335.IntermediateScale.density_of_small_removed_subset
#check @Erdos335.IntermediateScale.exists_dense_cyclic_removal
#print axioms Erdos335.IntermediateScale.exists_dense_cyclic_removal
#check @Erdos335.IntermediateScale.exists_intermediate_cyclic_models
#print axioms Erdos335.IntermediateScale.exists_intermediate_cyclic_models
#check @Erdos335.Loeb.loeb_finset_measure_tendsto
#print axioms Erdos335.Loeb.loeb_finset_measure_tendsto
#check @Erdos335.Loeb.loeb_finset_measure_eq
#print axioms Erdos335.Loeb.loeb_finset_measure_eq
#check @Erdos335.Loeb.finset_sum_card_le_container
#print axioms Erdos335.Loeb.finset_sum_card_le_container
#check @Erdos335.Loeb.loeb_cyclic_sum_measure_le
#print axioms Erdos335.Loeb.loeb_cyclic_sum_measure_le
#check @Erdos335.IntermediateScale.cyclicWindow_count_error_le
#print axioms Erdos335.IntermediateScale.cyclicWindow_count_error_le
#check @Erdos335.IntermediateScale.cyclic_window_density_of_general_prefix_error
#print axioms Erdos335.IntermediateScale.cyclic_window_density_of_general_prefix_error
#check @Erdos335.Loeb.loeb_finset_ae_eq_of_same_density
#print axioms Erdos335.Loeb.loeb_finset_ae_eq_of_same_density
#check @Erdos335.Loeb.loeb_cyclic_sum_ae_subset
#print axioms Erdos335.Loeb.loeb_cyclic_sum_ae_subset
#check @Erdos335.Loeb.loeb_literal_translate_ae_subset
#print axioms Erdos335.Loeb.loeb_literal_translate_ae_subset
#check @Erdos335.IntermediateScale.exists_intermediate_loeb_models
#print axioms Erdos335.IntermediateScale.exists_intermediate_loeb_models
#check @Erdos335.Loeb.loeb_literal_model_inverse
#print axioms Erdos335.Loeb.loeb_literal_model_inverse
#check @Erdos335.IntermediateScale.strictSubsequenceExtension
#print axioms Erdos335.IntermediateScale.strictSubsequenceExtension
#check @Erdos335.IntermediateScale.strictSubsequenceExtension_on
#print axioms Erdos335.IntermediateScale.strictSubsequenceExtension_on
#check @Erdos335.IntermediateScale.eventually_strictSubsequenceExtension
#print axioms Erdos335.IntermediateScale.eventually_strictSubsequenceExtension
#check @Erdos335.IntermediateScale.tendsto_strictSubsequenceExtension
#print axioms Erdos335.IntermediateScale.tendsto_strictSubsequenceExtension
#check @Erdos335.IntermediateScale.tendsto_subsequence_of_intermediate_control
#print axioms Erdos335.IntermediateScale.tendsto_subsequence_of_intermediate_control
#check @Erdos335.IntermediateScale.IntermediateFourierModel
#print axioms Erdos335.IntermediateScale.IntermediateFourierModel
#check @Erdos335.IntermediateScale.exists_intermediate_fourier_model
#print axioms Erdos335.IntermediateScale.exists_intermediate_fourier_model
#check @Erdos335.IntermediateScale.IntermediateFourierModel.restrict
#print axioms Erdos335.IntermediateScale.IntermediateFourierModel.restrict
#check @Erdos335.IntermediateScale.exists_joint_intermediate_fourier_models
#print axioms Erdos335.IntermediateScale.exists_joint_intermediate_fourier_models
#check @Erdos335.IntermediateScale.exists_common_small_interior_positions
#print axioms Erdos335.IntermediateScale.exists_common_small_interior_positions
#check @Erdos335.IntermediateScale.exists_normalized_selected_period
#print axioms Erdos335.IntermediateScale.exists_normalized_selected_period
#check @Erdos335.IntermediateScale.exists_joint_convolution_windows
#print axioms Erdos335.IntermediateScale.exists_joint_convolution_windows
#check @Erdos335.IntermediateScale.exists_joint_fourier_convolution_windows
#print axioms Erdos335.IntermediateScale.exists_joint_fourier_convolution_windows
#check @Erdos335.IntermediateScale.exists_joint_cyclic_models
#print axioms Erdos335.IntermediateScale.exists_joint_cyclic_models
#check @Erdos335.IntermediateScale.exists_two_orientation_cyclic_models
#print axioms Erdos335.IntermediateScale.exists_two_orientation_cyclic_models
#check @Erdos335.IntermediateScale.prefix_average_nested_length_error
#print axioms Erdos335.IntermediateScale.prefix_average_nested_length_error
#check @Erdos335.IntermediateScale.prefix_average_length_error
#print axioms Erdos335.IntermediateScale.prefix_average_length_error
#check @Erdos335.IntermediateScale.cyclic_window_length_comparison
#print axioms Erdos335.IntermediateScale.cyclic_window_length_comparison
#check @Erdos335.IntermediateScale.selected_length_excess_tendsto_zero
#print axioms Erdos335.IntermediateScale.selected_length_excess_tendsto_zero
#check @Erdos335.IntermediateScale.selected_lengths_tendsto_near
#print axioms Erdos335.IntermediateScale.selected_lengths_tendsto_near
#check @Erdos335.IntermediateScale.selected_cyclic_profiles_agree
#print axioms Erdos335.IntermediateScale.selected_cyclic_profiles_agree
#check @Erdos335.IntermediateScale.prefixError_mono
#print axioms Erdos335.IntermediateScale.prefixError_mono
#check @Erdos335.IntermediateScale.exists_density_window_scales
#print axioms Erdos335.IntermediateScale.exists_density_window_scales
#check @Erdos335.IntermediateScale.exists_two_orientation_models_of_density
#print axioms Erdos335.IntermediateScale.exists_two_orientation_models_of_density
#check @Erdos335.Loeb.naturalCyclicProjection
#print axioms Erdos335.Loeb.naturalCyclicProjection
#check @Erdos335.Loeb.naturalCyclicProjection_natCast
#print axioms Erdos335.Loeb.naturalCyclicProjection_natCast
#check @Erdos335.Loeb.naturalCyclicProjection_surjective
#print axioms Erdos335.Loeb.naturalCyclicProjection_surjective
#check @Erdos335.Loeb.naturalCyclicProjection_val
#print axioms Erdos335.Loeb.naturalCyclicProjection_val
#check @Erdos335.Loeb.finiteQuotient_eq_finiteFunction
#print axioms Erdos335.Loeb.finiteQuotient_eq_finiteFunction
#check @Erdos335.Loeb.finiteQuotient_preimage_internal
#print axioms Erdos335.Loeb.finiteQuotient_preimage_internal
#check @Erdos335.Loeb.naturalCyclicProjection_kernel
#print axioms Erdos335.Loeb.naturalCyclicProjection_kernel
#check @Erdos335.Loeb.loebMeasure_naturalCyclicProjection_preimage
#print axioms Erdos335.Loeb.loebMeasure_naturalCyclicProjection_preimage
#check @Erdos335.Loeb.loeb_finset_quotient_fiber_tendsto
#print axioms Erdos335.Loeb.loeb_finset_quotient_fiber_tendsto
#check @Erdos335.Loeb.naturalCyclicProjection_window_filter
#print axioms Erdos335.Loeb.naturalCyclicProjection_window_filter
#check @Erdos335.Loeb.loeb_window_residue_measure_tendsto
#print axioms Erdos335.Loeb.loeb_window_residue_measure_tendsto
#check @Erdos335.Loeb.loeb_window_residue_measure_agreement
#print axioms Erdos335.Loeb.loeb_window_residue_measure_agreement
#check @Erdos335.ae_eq_finite_preimage_of_fiber_measures
#print axioms Erdos335.ae_eq_finite_preimage_of_fiber_measures
#check @Erdos335.Loeb.loeb_ae_eq_residue_mask_of_profile
#print axioms Erdos335.Loeb.loeb_ae_eq_residue_mask_of_profile
#check @Erdos335.Loeb.loeb_residue_mask_profile
#print axioms Erdos335.Loeb.loeb_residue_mask_profile
#check @Erdos335.Loeb.loeb_window_residue_mask_transfer
#print axioms Erdos335.Loeb.loeb_window_residue_mask_transfer
#check @Erdos335.IntermediateScale.card_initial_filter_lower
#print axioms Erdos335.IntermediateScale.card_initial_filter_lower
#check @Erdos335.IntermediateScale.exists_small_on_dense_finset
#print axioms Erdos335.IntermediateScale.exists_small_on_dense_finset
#check @Erdos335.IntermediateScale.exists_small_interior_positions_in_dense_sets
#print axioms Erdos335.IntermediateScale.exists_small_interior_positions_in_dense_sets
#check @Erdos335.IntermediateScale.exists_common_small_interior_positions_in_dense_sets
#print axioms Erdos335.IntermediateScale.exists_common_small_interior_positions_in_dense_sets
#check @Erdos335.IntermediateScale.joint_convolution_windows_from_selected_errors
#print axioms Erdos335.IntermediateScale.joint_convolution_windows_from_selected_errors
#check @Erdos335.IntermediateScale.exists_joint_convolution_windows_in_dense_sets
#print axioms Erdos335.IntermediateScale.exists_joint_convolution_windows_in_dense_sets
#check @Erdos335.IntermediateScale.exists_fourier_model_period_data
#print axioms Erdos335.IntermediateScale.exists_fourier_model_period_data
#check @Erdos335.IntermediateScale.exists_constrained_fourier_windows
#print axioms Erdos335.IntermediateScale.exists_constrained_fourier_windows
#check @Erdos335.IntermediateScale.exists_constrained_cyclic_models
#print axioms Erdos335.IntermediateScale.exists_constrained_cyclic_models
#check @Erdos335.sum_measure_inter_fibers
#print axioms Erdos335.sum_measure_inter_fibers
#check @Erdos335.sum_real_measure_inter_fibers
#print axioms Erdos335.sum_real_measure_inter_fibers
#check @Erdos335.Loeb.loebResidueProfile
#print axioms Erdos335.Loeb.loebResidueProfile
#check @Erdos335.Loeb.loebResidueProfile_nonneg
#print axioms Erdos335.Loeb.loebResidueProfile_nonneg
#check @Erdos335.Loeb.loebResidueProfile_le_one
#print axioms Erdos335.Loeb.loebResidueProfile_le_one
#check @Erdos335.Loeb.sum_loebResidueProfile
#print axioms Erdos335.Loeb.sum_loebResidueProfile
#check @Erdos335.Loeb.loebResidueProfile_translate_le
#print axioms Erdos335.Loeb.loebResidueProfile_translate_le
#check @Erdos335.FiniteProfiles.positiveProfileSupport
#print axioms Erdos335.FiniteProfiles.positiveProfileSupport
#check @Erdos335.FiniteProfiles.sum_positiveProfileSupport
#print axioms Erdos335.FiniteProfiles.sum_positiveProfileSupport
#check @Erdos335.FiniteProfiles.positiveProfileSupport_nonempty
#print axioms Erdos335.FiniteProfiles.positiveProfileSupport_nonempty
#check @Erdos335.FiniteProfiles.positiveProfileSupport_subset
#print axioms Erdos335.FiniteProfiles.positiveProfileSupport_subset
#check @Erdos335.FiniteProfiles.periodic_output_forces_indicator_profiles
#print axioms Erdos335.FiniteProfiles.periodic_output_forces_indicator_profiles
#check @Erdos335.Loeb.actual_residue_of_internal_cyclic_window
#print axioms Erdos335.Loeb.actual_residue_of_internal_cyclic_window
#check @Erdos335.Loeb.actual_window_profile_zero_outside_residues
#print axioms Erdos335.Loeb.actual_window_profile_zero_outside_residues
#check @Erdos335.Loeb.sum_shifted_loebResidueProfile
#print axioms Erdos335.Loeb.sum_shifted_loebResidueProfile
#check @Erdos335.Loeb.loeb_cyclic_window_literal_translate_ae
#print axioms Erdos335.Loeb.loeb_cyclic_window_literal_translate_ae
#check @Erdos335.Loeb.actual_window_profile_translate_le
#print axioms Erdos335.Loeb.actual_window_profile_translate_le
#check @Erdos335.Loeb.loebResidueProfile_eq_of_ae
#print axioms Erdos335.Loeb.loebResidueProfile_eq_of_ae
#check @Erdos335.Loeb.loebResidueProfile_zero_of_subset
#print axioms Erdos335.Loeb.loebResidueProfile_zero_of_subset
#check @Erdos335.Loeb.loebResidueProfile_one_of_fiber_ae_subset
#print axioms Erdos335.Loeb.loebResidueProfile_one_of_fiber_ae_subset
#check @Erdos335.Loeb.actualWindowProfile
#print axioms Erdos335.Loeb.actualWindowProfile
#check @Erdos335.Loeb.periodic_output_window_profiles
#print axioms Erdos335.Loeb.periodic_output_window_profiles
#check @Erdos335.Loeb.actual_window_local_deficit_template
#print axioms Erdos335.Loeb.actual_window_local_deficit_template
#check @Erdos335.Loeb.finset_translate_add
#print axioms Erdos335.Loeb.finset_translate_add
#check @Erdos335.Loeb.actual_window_core_image_subset
#print axioms Erdos335.Loeb.actual_window_core_image_subset
#check @Erdos335.Loeb.actual_window_profile_zero_of_core
#print axioms Erdos335.Loeb.actual_window_profile_zero_of_core
#check @Erdos335.Loeb.actual_window_profile_full_of_core
#print axioms Erdos335.Loeb.actual_window_profile_full_of_core
#check @Erdos335.Loeb.loeb_ae_eq_shifted_mask_of_full_profile
#print axioms Erdos335.Loeb.loeb_ae_eq_shifted_mask_of_full_profile
#check @Erdos335.Loeb.actual_window_profile_of_residue_mask
#print axioms Erdos335.Loeb.actual_window_profile_of_residue_mask
#check @Erdos335.Loeb.periodic_output_window_forces_periodic_inputs
#print axioms Erdos335.Loeb.periodic_output_window_forces_periodic_inputs
#check @Erdos335.Loeb.loeb_saturated_critical_cardinality
#print axioms Erdos335.Loeb.loeb_saturated_critical_cardinality
#check @Erdos335.Loeb.exists_loeb_subcritical_quotient_core
#print axioms Erdos335.Loeb.exists_loeb_subcritical_quotient_core
#check @Erdos335.Loeb.subcritical_window_is_periodic
#print axioms Erdos335.Loeb.subcritical_window_is_periodic
#check @Erdos335.Loeb.loeb_equal_translate_difference_period
#print axioms Erdos335.Loeb.loeb_equal_translate_difference_period
#check @Erdos335.Loeb.loeb_quasiPeriodic_period_of_active_period
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_period_of_active_period
#check @Erdos335.Loeb.loeb_null_right_active_difference_periods
#print axioms Erdos335.Loeb.loeb_null_right_active_difference_periods
#check @Erdos335.Loeb.loeb_literal_null_active_difference_periods
#print axioms Erdos335.Loeb.loeb_literal_null_active_difference_periods
#check @Erdos335.Loeb.naturalCyclicProjection_comp
#print axioms Erdos335.Loeb.naturalCyclicProjection_comp
#check @Erdos335.Loeb.finiteQuotient_natural_refinement
#print axioms Erdos335.Loeb.finiteQuotient_natural_refinement
#check @Erdos335.Loeb.natural_quotient_preimage_composition
#print axioms Erdos335.Loeb.natural_quotient_preimage_composition
#check @Erdos335.Loeb.exists_finite_natural_critical_core
#print axioms Erdos335.Loeb.exists_finite_natural_critical_core
#check @Erdos335.Loeb.loeb_fiber_ae_subset_of_full_profile
#print axioms Erdos335.Loeb.loeb_fiber_ae_subset_of_full_profile
#check @Erdos335.Loeb.loeb_mask_ae_subset_of_full_profiles
#print axioms Erdos335.Loeb.loeb_mask_ae_subset_of_full_profiles
#check @Erdos335.Loeb.windowResidueMap
#print axioms Erdos335.Loeb.windowResidueMap
#check @Erdos335.Loeb.windowResidueMap_fiber
#print axioms Erdos335.Loeb.windowResidueMap_fiber
#check @Erdos335.Loeb.windowResidueMap_preimage
#print axioms Erdos335.Loeb.windowResidueMap_preimage
#check @Erdos335.Loeb.windowResidueMap_refinement
#print axioms Erdos335.Loeb.windowResidueMap_refinement
#check @Erdos335.Loeb.actual_window_full_mask_subset
#print axioms Erdos335.Loeb.actual_window_full_mask_subset
#check @Erdos335.Loeb.actual_window_full_on_mask
#print axioms Erdos335.Loeb.actual_window_full_on_mask
#check @Erdos335.Loeb.loebMeasure_windowResidueMap_preimage
#print axioms Erdos335.Loeb.loebMeasure_windowResidueMap_preimage
#check @Erdos335.Loeb.actual_window_zero_off_mask
#print axioms Erdos335.Loeb.actual_window_zero_off_mask
#check @Erdos335.Loeb.actual_window_residue_subset
#print axioms Erdos335.Loeb.actual_window_residue_subset
#check @Erdos335.Loeb.actual_window_residue_capacity
#print axioms Erdos335.Loeb.actual_window_residue_capacity
#check @Erdos335.Loeb.actual_window_mask_of_indicator_profile
#print axioms Erdos335.Loeb.actual_window_mask_of_indicator_profile
#check @Erdos335.Loeb.actual_window_indicator_mass
#print axioms Erdos335.Loeb.actual_window_indicator_mass
#check @Erdos335.Loeb.actual_periodic_input_baseline
#print axioms Erdos335.Loeb.actual_periodic_input_baseline
#check @Erdos335.Loeb.actual_periodic_input_baseline_mass_le
#print axioms Erdos335.Loeb.actual_periodic_input_baseline_mass_le
#check @Erdos335.Loeb.saturated_periodic_input_baseline
#print axioms Erdos335.Loeb.saturated_periodic_input_baseline
#check @Erdos335.Loeb.exists_strict_periodic_window_core
#print axioms Erdos335.Loeb.exists_strict_periodic_window_core
#check @Erdos335.Loeb.loeb_nested_finite_circle_fiber_measure
#print axioms Erdos335.Loeb.loeb_nested_finite_circle_fiber_measure
#check @Erdos335.Loeb.loeb_natural_bohr_residue_profile
#print axioms Erdos335.Loeb.loeb_natural_bohr_residue_profile
#check @Erdos335.Loeb.InternalBohrPairData.residue_profiles
#print axioms Erdos335.Loeb.InternalBohrPairData.residue_profiles
#check @Erdos335.IntermediateScale.prefix_sum_le_shifted_sum
#print axioms Erdos335.IntermediateScale.prefix_sum_le_shifted_sum
#check @Erdos335.IntermediateScale.prefix_mean_le_offset_window_mean
#print axioms Erdos335.IntermediateScale.prefix_mean_le_offset_window_mean
#check @Erdos335.IntermediateScale.prefix_mean_tendsto_zero_of_window_means
#print axioms Erdos335.IntermediateScale.prefix_mean_tendsto_zero_of_window_means
#check @Erdos335.Loeb.loeb_ae_periods_have_natural_mask
#print axioms Erdos335.Loeb.loeb_ae_periods_have_natural_mask
#check @Erdos335.Loeb.loeb_actual_window_inverse
#print axioms Erdos335.Loeb.loeb_actual_window_inverse
#check @Erdos335.residue_capacity_mono_of_dvd
#print axioms Erdos335.residue_capacity_mono_of_dvd
#check @Erdos335.residue_capacity_approximants_at_multiples
#print axioms Erdos335.residue_capacity_approximants_at_multiples
#check @Erdos335.residue_capacity_ge_of_full_coarse_fiber
#print axioms Erdos335.residue_capacity_ge_of_full_coarse_fiber
#check @Erdos335.Loeb.internalBohrPair_right_window_gap
#print axioms Erdos335.Loeb.internalBohrPair_right_window_gap
#check @Erdos335.Loeb.InternalBohrPairData.swap
#print axioms Erdos335.Loeb.InternalBohrPairData.swap
#check @Erdos335.Loeb.loeb_quasiBohr_right_residue_profile
#print axioms Erdos335.Loeb.loeb_quasiBohr_right_residue_profile
#check @Erdos335.Loeb.loeb_quasiBohr_left_residue_profile
#print axioms Erdos335.Loeb.loeb_quasiBohr_left_residue_profile
#check @Erdos335.Loeb.loeb_quasiBohr_right_mass
#print axioms Erdos335.Loeb.loeb_quasiBohr_right_mass
#check @Erdos335.residue_capacity_ge_of_full_coarse_mask
#print axioms Erdos335.residue_capacity_ge_of_full_coarse_mask
#check @Erdos335.Loeb.quasiPeriodicBohr_right_window_gap
#print axioms Erdos335.Loeb.quasiPeriodicBohr_right_window_gap
#check @Erdos335.Loeb.naturalCyclicProjection_zero_iff_multiple
#print axioms Erdos335.Loeb.naturalCyclicProjection_zero_iff_multiple
#check @Erdos335.Loeb.naturalCyclicProjection_eq_iff_add_multiple
#print axioms Erdos335.Loeb.naturalCyclicProjection_eq_iff_add_multiple
#check @Erdos335.kernelCore
#print axioms Erdos335.kernelCore
#check @Erdos335.mem_kernelCore
#print axioms Erdos335.mem_kernelCore
#check @Erdos335.kernelCore_subset
#print axioms Erdos335.kernelCore_subset
#check @Erdos335.kernelCore_preimage_image
#print axioms Erdos335.kernelCore_preimage_image
#check @Erdos335.Loeb.loeb_period_nsmul
#print axioms Erdos335.Loeb.loeb_period_nsmul
#check @Erdos335.Loeb.loeb_translate_membership_ae
#print axioms Erdos335.Loeb.loeb_translate_membership_ae
#check @Erdos335.Loeb.productProjection_nat_mul
#print axioms Erdos335.Loeb.productProjection_nat_mul
#check @Erdos335.Loeb.loeb_integer_period_cover_core
#print axioms Erdos335.Loeb.loeb_integer_period_cover_core
#check @Erdos335.Loeb.loeb_periodic_mask_of_residue_approximation
#print axioms Erdos335.Loeb.loeb_periodic_mask_of_residue_approximation
#check @Erdos335.Loeb.loeb_regular_window_period_is_mask
#print axioms Erdos335.Loeb.loeb_regular_window_period_is_mask
#check @Erdos335.Loeb.InternalBohrPairData.congr
#print axioms Erdos335.Loeb.InternalBohrPairData.congr
#check @Erdos335.Loeb.exists_aligned_quasiPeriodicBohrPair
#print axioms Erdos335.Loeb.exists_aligned_quasiPeriodicBohrPair
#check @Erdos335.Loeb.loeb_regular_window_no_positive_terminal
#print axioms Erdos335.Loeb.loeb_regular_window_no_positive_terminal
#check @Erdos335.Loeb.loeb_literal_active_not_subsingleton
#print axioms Erdos335.Loeb.loeb_literal_active_not_subsingleton
#check @Erdos335.Loeb.internal_literal_fiber_subsingleton
#print axioms Erdos335.Loeb.internal_literal_fiber_subsingleton
#check @Erdos335.Loeb.literal_active_has_two_integers
#print axioms Erdos335.Loeb.literal_active_has_two_integers
#check @Erdos335.Loeb.loeb_regular_actual_window_is_periodic
#print axioms Erdos335.Loeb.loeb_regular_actual_window_is_periodic
#check @Erdos335.ae_eq_of_common_approximate_covers
#print axioms Erdos335.ae_eq_of_common_approximate_covers
#check @Erdos335.Loeb.loeb_regular_prefix_window_agreement
#print axioms Erdos335.Loeb.loeb_regular_prefix_window_agreement
#check @Erdos335.Loeb.loebResidueProfile_vadd
#print axioms Erdos335.Loeb.loebResidueProfile_vadd
#check @Erdos335.Loeb.loeb_regular_prefix_profile_eq_window
#print axioms Erdos335.Loeb.loeb_regular_prefix_profile_eq_window
#check @Erdos335.FiniteProfiles.carrier_eq_of_positive_partner
#print axioms Erdos335.FiniteProfiles.carrier_eq_of_positive_partner
#check @Erdos335.Loeb.loeb_quasiPeriodic_residue_profile
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_residue_profile
#check @Erdos335.Loeb.actual_window_carrier_eq_of_positive_partner
#print axioms Erdos335.Loeb.actual_window_carrier_eq_of_positive_partner
#check @Erdos335.Loeb.actual_window_gamma_bound_of_critical_profiles
#print axioms Erdos335.Loeb.actual_window_gamma_bound_of_critical_profiles
#check @Erdos335.Loeb.loeb_regular_prefix_quasi_period_bound
#print axioms Erdos335.Loeb.loeb_regular_prefix_quasi_period_bound
#check @Erdos335.Loeb.loeb_regular_prefix_aperiodic_inverse
#print axioms Erdos335.Loeb.loeb_regular_prefix_aperiodic_inverse
#check @Erdos335.Loeb.loeb_periods_of_translated_ae
#print axioms Erdos335.Loeb.loeb_periods_of_translated_ae
#check @Erdos335.Loeb.loeb_regular_prefix_periodic_window
#print axioms Erdos335.Loeb.loeb_regular_prefix_periodic_window
#check @Erdos335.Loeb.loeb_regular_pair_window_inverse
#print axioms Erdos335.Loeb.loeb_regular_pair_window_inverse
#check @Erdos335.densityEquivalent_of_common_approximate_covers
#print axioms Erdos335.densityEquivalent_of_common_approximate_covers
#check @Erdos335.Loeb.actual_window_profile_full_of_coarse_mask
#print axioms Erdos335.Loeb.actual_window_profile_full_of_coarse_mask
#check @Erdos335.Loeb.periodic_mask_subset_residue_cover_of_window
#print axioms Erdos335.Loeb.periodic_mask_subset_residue_cover_of_window
#check @Erdos335.Loeb.loeb_regular_window_global_mask
#print axioms Erdos335.Loeb.loeb_regular_window_global_mask
#check @Erdos335.Loeb.loeb_regular_natural_window_global_mask
#print axioms Erdos335.Loeb.loeb_regular_natural_window_global_mask
#check @Erdos335.IntermediateScale.exists_ordinary_density_loeb_models
#print axioms Erdos335.IntermediateScale.exists_ordinary_density_loeb_models
#check @Erdos335.exists_periodic_summand_of_regular_capacity
#print axioms Erdos335.exists_periodic_summand_of_regular_capacity
#check @Erdos335.Loeb.loeb_strict_periodic_input_frame
#print axioms Erdos335.Loeb.loeb_strict_periodic_input_frame
#check @Erdos335.Loeb.periodic_template_residue_density
#print axioms Erdos335.Loeb.periodic_template_residue_density
#check @Erdos335.Loeb.loeb_prefix_residue_measure_of_density
#print axioms Erdos335.Loeb.loeb_prefix_residue_measure_of_density
#check @Erdos335.Loeb.loeb_prefix_mask_of_density_equivalence
#print axioms Erdos335.Loeb.loeb_prefix_mask_of_density_equivalence
#check @Erdos335.Loeb.loeb_fixed_periodic_core_profiles
#print axioms Erdos335.Loeb.loeb_fixed_periodic_core_profiles
#check @Erdos335.Loeb.positiveMultipleSequence
#print axioms Erdos335.Loeb.positiveMultipleSequence
#check @Erdos335.Loeb.positiveMultipleSequence_tendsto
#print axioms Erdos335.Loeb.positiveMultipleSequence_tendsto
#check @Erdos335.Loeb.residueFiber_density_of_all_prefix_measures
#print axioms Erdos335.Loeb.residueFiber_density_of_all_prefix_measures
#check @Erdos335.Loeb.periodic_summand_strict_frame
#print axioms Erdos335.Loeb.periodic_summand_strict_frame
#check @Erdos335.Proposed.hasDensity_residueSection_of_fiber
#print axioms Erdos335.Proposed.hasDensity_residueSection_of_fiber
#check @Erdos335.Proposed.periodic_summand_strict_finite_frame
#print axioms Erdos335.Proposed.periodic_summand_strict_finite_frame
#check @Erdos335.densityEquivalent_of_subset_same_density
#print axioms Erdos335.densityEquivalent_of_subset_same_density
#check @Erdos335.active_fiber_density_of_full_background
#print axioms Erdos335.active_fiber_density_of_full_background
#check @Erdos335.shift_shift_eq
#print axioms Erdos335.shift_shift_eq
#check @Erdos335.DensityEquivalent.of_shift
#print axioms Erdos335.DensityEquivalent.of_shift
#check @Erdos335.period_of_equal_translates
#print axioms Erdos335.period_of_equal_translates
#check @Erdos335.Proposed.FiniteFrame.null_left_translate_coverage
#print axioms Erdos335.Proposed.FiniteFrame.null_left_translate_coverage
#check @Erdos335.Proposed.FiniteFrame.null_left_active_difference_period
#print axioms Erdos335.Proposed.FiniteFrame.null_left_active_difference_period
#check @Erdos335.Proposed.missing_fiber_of_full_shift
#print axioms Erdos335.Proposed.missing_fiber_of_full_shift
#check @Erdos335.Proposed.FiniteFrame.null_left_finite_translate_coverage
#print axioms Erdos335.Proposed.FiniteFrame.null_left_finite_translate_coverage
#check @Erdos335.equivalent_periodic_background_and_fiber
#print axioms Erdos335.equivalent_periodic_background_and_fiber
#check @Erdos335.periodic_mask_shift_of_dvd
#print axioms Erdos335.periodic_mask_shift_of_dvd
#check @Erdos335.period_from_exceptional_fiber
#print axioms Erdos335.period_from_exceptional_fiber
#check @Erdos335.Proposed.FiniteFrame.null_left_common_difference_period
#print axioms Erdos335.Proposed.FiniteFrame.null_left_common_difference_period
#check @Erdos335.Proposed.FiniteFrame.null_left_classified
#print axioms Erdos335.Proposed.FiniteFrame.null_left_classified
#check @Erdos335.Proposed.periodic_inputs_maskBranch
#print axioms Erdos335.Proposed.periodic_inputs_maskBranch
#check @Erdos335.Proposed.periodic_summand_saturated_maskBranch
#print axioms Erdos335.Proposed.periodic_summand_saturated_maskBranch
#check @Erdos335.Proposed.periodic_summand_classified
#print axioms Erdos335.Proposed.periodic_summand_classified
#check @Erdos335.Proposed.SingletonBranch.swap
#print axioms Erdos335.Proposed.SingletonBranch.swap
#check @Erdos335.Proposed.MaskBranch.swap
#print axioms Erdos335.Proposed.MaskBranch.swap
#check @Erdos335.Proposed.regular_summand_strict_classification
#print axioms Erdos335.Proposed.regular_summand_strict_classification
#check @Erdos335.Proposed.classification_iff_of_regular_capacity
#print axioms Erdos335.Proposed.classification_iff_of_regular_capacity
#check @Erdos335.Proposed.PositiveGapNecessity
#print axioms Erdos335.Proposed.PositiveGapNecessity
#check @Erdos335.Proposed.fullSolution_of_positive_gap_necessity
#print axioms Erdos335.Proposed.fullSolution_of_positive_gap_necessity
#check @Erdos335.Loeb.loeb_literal_quasi_period_index_le
#print axioms Erdos335.Loeb.loeb_literal_quasi_period_index_le
#check @Erdos335.finite_family_difference_representatives
#print axioms Erdos335.finite_family_difference_representatives
#check @Erdos335.finite_residue_difference_representatives
#print axioms Erdos335.finite_residue_difference_representatives
#check @Erdos335.Loeb.exists_uniform_literal_null_periods
#print axioms Erdos335.Loeb.exists_uniform_literal_null_periods
#check @Erdos335.Loeb.internalBohrCoset_add_subset
#print axioms Erdos335.Loeb.internalBohrCoset_add_subset
#check @Erdos335.Loeb.internalBohrCoset_measure_toReal
#print axioms Erdos335.Loeb.internalBohrCoset_measure_toReal
#check @Erdos335.Loeb.InternalBohrPairData.sum_model
#print axioms Erdos335.Loeb.InternalBohrPairData.sum_model
#check @Erdos335.Loeb.loeb_quasiPeriodic_refined_profile
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_refined_profile
#check @Erdos335.Loeb.loeb_quasiBohr_output_residue_profile
#print axioms Erdos335.Loeb.loeb_quasiBohr_output_residue_profile
#check @Erdos335.partial_residue_profile_alignment
#print axioms Erdos335.partial_residue_profile_alignment
#check @Erdos335.Loeb.loeb_physical_bohr_output_profile
#print axioms Erdos335.Loeb.loeb_physical_bohr_output_profile
#check @Erdos335.Loeb.positive_terminal_output_moduli_agree
#print axioms Erdos335.Loeb.positive_terminal_output_moduli_agree
#check @Erdos335.FiniteProfiles.coordinate_ge_total_sub_card
#print axioms Erdos335.FiniteProfiles.coordinate_ge_total_sub_card
#check @Erdos335.Loeb.actual_window_profile_ge_total_sub_card
#print axioms Erdos335.Loeb.actual_window_profile_ge_total_sub_card
#check @Erdos335.Loeb.actual_window_capacity_ge_of_positive_refinements
#print axioms Erdos335.Loeb.actual_window_capacity_ge_of_positive_refinements
#check @Erdos335.Loeb.literal_prefix_profile_zero_outside_residues
#print axioms Erdos335.Loeb.literal_prefix_profile_zero_outside_residues
#check @Erdos335.Loeb.literal_prefix_capacity_ge_of_positive_refinements
#print axioms Erdos335.Loeb.literal_prefix_capacity_ge_of_positive_refinements
#check @Erdos335.Loeb.loeb_physical_bohr_right_profile
#print axioms Erdos335.Loeb.loeb_physical_bohr_right_profile
#check @Erdos335.Loeb.loeb_physical_bohr_left_profile
#print axioms Erdos335.Loeb.loeb_physical_bohr_left_profile
#check @Erdos335.Loeb.actual_output_literal_carrier
#print axioms Erdos335.Loeb.actual_output_literal_carrier
#check @Erdos335.Loeb.gamma_eq_of_positive_window_refinements
#print axioms Erdos335.Loeb.gamma_eq_of_positive_window_refinements
#check @Erdos335.Loeb.loeb_positive_terminal_gap_formulas
#print axioms Erdos335.Loeb.loeb_positive_terminal_gap_formulas
#check @Erdos335.FiniteProfiles.support_eq_of_partial_mass
#print axioms Erdos335.FiniteProfiles.support_eq_of_partial_mass
#check @Erdos335.Loeb.loeb_positive_window_literal_support_of_mass
#print axioms Erdos335.Loeb.loeb_positive_window_literal_support_of_mass
#check @Erdos335.natural_preimage_capacity
#print axioms Erdos335.natural_preimage_capacity
#check @Erdos335.exceptional_fiber_card_bound
#print axioms Erdos335.exceptional_fiber_card_bound
#check @Erdos335.input_gap_le_output_gap_of_full_background
#print axioms Erdos335.input_gap_le_output_gap_of_full_background
#check @Erdos335.Loeb.actual_window_full_coarse_residues_refine
#print axioms Erdos335.Loeb.actual_window_full_coarse_residues_refine
#check @Erdos335.Loeb.actual_window_nonactive_output_full
#print axioms Erdos335.Loeb.actual_window_nonactive_output_full
#check @Erdos335.Loeb.local_periodic_input_strict_gap_comparison
#print axioms Erdos335.Loeb.local_periodic_input_strict_gap_comparison
#check @Erdos335.FiniteKneser.saturated_cross_single_extra
#print axioms Erdos335.FiniteKneser.saturated_cross_single_extra
#check @Erdos335.FiniteKneser.saturated_cross_aperiodic_frame
#print axioms Erdos335.FiniteKneser.saturated_cross_aperiodic_frame
#check @Erdos335.FiniteKneser.saturated_cross_stabilizer_invariance
#print axioms Erdos335.FiniteKneser.saturated_cross_stabilizer_invariance
#check @Erdos335.Loeb.exists_saturated_natural_frame
#print axioms Erdos335.Loeb.exists_saturated_natural_frame
#check @Erdos335.Loeb.actual_indicator_profile_coarsen
#print axioms Erdos335.Loeb.actual_indicator_profile_coarsen
#check @Erdos335.Loeb.local_saturated_output_gap_comparison
#print axioms Erdos335.Loeb.local_saturated_output_gap_comparison
#check @Erdos335.Loeb.periodic_output_gap_alternative
#print axioms Erdos335.Loeb.periodic_output_gap_alternative
#check @Erdos335.Loeb.periodic_input_gap_alternative
#print axioms Erdos335.Loeb.periodic_input_gap_alternative
#check @Erdos335.modulus_dvd_of_fiber_inclusion
#print axioms Erdos335.modulus_dvd_of_fiber_inclusion
#check @Erdos335.modulus_dvd_of_partial_profile
#print axioms Erdos335.modulus_dvd_of_partial_profile
#check @Erdos335.no_integer_and_partial_mass
#print axioms Erdos335.no_integer_and_partial_mass
#check @Erdos335.Loeb.loeb_quasiPeriodic_refined_off_active
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_refined_off_active
#check @Erdos335.Loeb.loeb_quasiPeriodic_null_mass_integer
#print axioms Erdos335.Loeb.loeb_quasiPeriodic_null_mass_integer
#check @Erdos335.Loeb.loeb_physical_quasi_off_active
#print axioms Erdos335.Loeb.loeb_physical_quasi_off_active
#check @Erdos335.Loeb.no_mixed_positive_null_terminal
#print axioms Erdos335.Loeb.no_mixed_positive_null_terminal
#check @Erdos335.Loeb.actualWindowFiber
#print axioms Erdos335.Loeb.actualWindowFiber
#check @Erdos335.Loeb.measurable_actualWindowFiber
#print axioms Erdos335.Loeb.measurable_actualWindowFiber
#check @Erdos335.Loeb.windowResidueMap_nat_translate
#print axioms Erdos335.Loeb.windowResidueMap_nat_translate
#check @Erdos335.Loeb.actual_window_fiber_translate_subset
#print axioms Erdos335.Loeb.actual_window_fiber_translate_subset
#check @Erdos335.Loeb.actual_window_fiber_equal_translate
#print axioms Erdos335.Loeb.actual_window_fiber_equal_translate
#check @Erdos335.Loeb.actual_window_fiber_difference_period
#print axioms Erdos335.Loeb.actual_window_fiber_difference_period
#check @Erdos335.FiniteProfiles.sum_profile_with_one_exception
#print axioms Erdos335.FiniteProfiles.sum_profile_with_one_exception
#check @Erdos335.Loeb.actual_window_exceptional_profile
#print axioms Erdos335.Loeb.actual_window_exceptional_profile
#check @Erdos335.Loeb.null_frame_active_measures_equal
#print axioms Erdos335.Loeb.null_frame_active_measures_equal
#check @Erdos335.Loeb.window_mask_period_of_kernel
#print axioms Erdos335.Loeb.window_mask_period_of_kernel
#check @Erdos335.Loeb.actual_window_active_background
#print axioms Erdos335.Loeb.actual_window_active_background
#check @Erdos335.Loeb.actual_window_period_of_active_fiber
#print axioms Erdos335.Loeb.actual_window_period_of_active_fiber
#check @Erdos335.Loeb.null_frame_integer_difference_periods
#print axioms Erdos335.Loeb.null_frame_integer_difference_periods
#check @Erdos335.capacity_bound_of_singleton_residue
#print axioms Erdos335.capacity_bound_of_singleton_residue
#check @Erdos335.positive_gap_null_class_has_two_points
#print axioms Erdos335.positive_gap_null_class_has_two_points
#check @Erdos335.Loeb.exists_uniform_actual_null_periods
#print axioms Erdos335.Loeb.exists_uniform_actual_null_periods
#check @Erdos335.IntermediateScale.fixed_shift_window_membership
#print axioms Erdos335.IntermediateScale.fixed_shift_window_membership
#check @Erdos335.IntermediateScale.fixed_shift_window_discrepancy_le
#print axioms Erdos335.IntermediateScale.fixed_shift_window_discrepancy_le
#check @Erdos335.Loeb.loeb_finset_ae_eq_of_discrepancy
#print axioms Erdos335.Loeb.loeb_finset_ae_eq_of_discrepancy
#check @Erdos335.Loeb.loeb_fixed_shift_window_eq
#print axioms Erdos335.Loeb.loeb_fixed_shift_window_eq
#check @Erdos335.FiniteKneser.one_baseline_eq_output
#print axioms Erdos335.FiniteKneser.one_baseline_eq_output
#check @Erdos335.Loeb.whole_bohr_right_physical_profile
#print axioms Erdos335.Loeb.whole_bohr_right_physical_profile
#check @Erdos335.Loeb.whole_bohr_left_physical_profile
#print axioms Erdos335.Loeb.whole_bohr_left_physical_profile
#check @Erdos335.Loeb.whole_bohr_output_physical_profile
#print axioms Erdos335.Loeb.whole_bohr_output_physical_profile
#check @Erdos335.Loeb.whole_bohr_prefix_carrier
#print axioms Erdos335.Loeb.whole_bohr_prefix_carrier
#check @Erdos335.Loeb.whole_bohr_gap_formulas
#print axioms Erdos335.Loeb.whole_bohr_gap_formulas
#check @Erdos335.IntermediateScale.offset_window_mean_le_prefix_mean
#print axioms Erdos335.IntermediateScale.offset_window_mean_le_prefix_mean
#check @Erdos335.IntermediateScale.abs_prefix_mean_sub_offset_window_mean_le
#print axioms Erdos335.IntermediateScale.abs_prefix_mean_sub_offset_window_mean_le
#check @Erdos335.IntermediateScale.prefix_mean_tendsto_of_offset_window_means
#print axioms Erdos335.IntermediateScale.prefix_mean_tendsto_of_offset_window_means
#check @Erdos335.IntermediateScale.finite_mean_le_threshold_add_bad_fraction
#print axioms Erdos335.IntermediateScale.finite_mean_le_threshold_add_bad_fraction
#check @Erdos335.IntermediateScale.finite_mean_tendsto_zero_of_bad_fractions
#print axioms Erdos335.IntermediateScale.finite_mean_tendsto_zero_of_bad_fractions
#check @Erdos335.Loeb.loeb_vadd_subset_ae
#print axioms Erdos335.Loeb.loeb_vadd_subset_ae
#check @Erdos335.Loeb.window_residue_fiber_nat_translate
#print axioms Erdos335.Loeb.window_residue_fiber_nat_translate
#check @Erdos335.Loeb.actual_full_fiber_translate_subset
#print axioms Erdos335.Loeb.actual_full_fiber_translate_subset
#check @Erdos335.Loeb.actual_null_frame_finite_coverage
#print axioms Erdos335.Loeb.actual_null_frame_finite_coverage
#check @Erdos335.IntermediateScale.exists_fixed_scale_fourier_models_of_density
#print axioms Erdos335.IntermediateScale.exists_fixed_scale_fourier_models_of_density
#check @Erdos335.IntermediateScale.IntermediateFourierModel.subsequence
#print axioms Erdos335.IntermediateScale.IntermediateFourierModel.subsequence
#check @Erdos335.Loeb.loeb_zero_window_mass_of_density
#print axioms Erdos335.Loeb.loeb_zero_window_mass_of_density
#check @Erdos335.Loeb.loeb_finite_prefix_agreement
#print axioms Erdos335.Loeb.loeb_finite_prefix_agreement
#check @Erdos335.Loeb.loeb_null_prefix_indicator
#print axioms Erdos335.Loeb.loeb_null_prefix_indicator
#check @Erdos335.Loeb.loeb_finset_ae_eq_of_ultrafilter_discrepancy
#print axioms Erdos335.Loeb.loeb_finset_ae_eq_of_ultrafilter_discrepancy
#check @Erdos335.Loeb.loeb_sublinear_shift_window_eq
#print axioms Erdos335.Loeb.loeb_sublinear_shift_window_eq
#check @Erdos335.Loeb.actual_sublinear_translate_subset_sum_window
#print axioms Erdos335.Loeb.actual_sublinear_translate_subset_sum_window
#check @Erdos335.positive_density_multiplicative_gap
#print axioms Erdos335.positive_density_multiplicative_gap
#check @Erdos335.exists_next_point_ratio_tendsto_one
#print axioms Erdos335.exists_next_point_ratio_tendsto_one
#check @Erdos335.exists_positive_density_scale_selection
#print axioms Erdos335.exists_positive_density_scale_selection
#check @Erdos335.Loeb.loeb_high_gap_positive_terminal
#print axioms Erdos335.Loeb.loeb_high_gap_positive_terminal
#check @Erdos335.Loeb.standard_character_nat
#print axioms Erdos335.Loeb.standard_character_nat
#check @Erdos335.Loeb.prefix_arc_of_non_torsion_character
#print axioms Erdos335.Loeb.prefix_arc_of_non_torsion_character
#check @Erdos335.Loeb.loeb_full_of_all_phase_translates
#print axioms Erdos335.Loeb.loeb_full_of_all_phase_translates
#check @Erdos335.Loeb.sum_density_one_of_sublinear_phase_surjectivity
#print axioms Erdos335.Loeb.sum_density_one_of_sublinear_phase_surjectivity
#check @Erdos335.Loeb.exists_circle_lifts_tendsto_zero
#print axioms Erdos335.Loeb.exists_circle_lifts_tendsto_zero
#check @Erdos335.Loeb.cyclic_character_integral_drift
#print axioms Erdos335.Loeb.cyclic_character_integral_drift
#check @Erdos335.Loeb.integer_drift_constant_or_diverges
#print axioms Erdos335.Loeb.integer_drift_constant_or_diverges
#check @Erdos335.HasDensity.prefixCount_floor_real_tendsto
#print axioms Erdos335.HasDensity.prefixCount_floor_real_tendsto
#check @Erdos335.HasDensity.macroscopic_interval_real_tendsto
#print axioms Erdos335.HasDensity.macroscopic_interval_real_tendsto
#check @Erdos335.HasDensity.prefixCount_floor_pnat_tendsto
#print axioms Erdos335.HasDensity.prefixCount_floor_pnat_tendsto
#check @Erdos335.HasDensity.macroscopic_interval_pnat_tendsto
#print axioms Erdos335.HasDensity.macroscopic_interval_pnat_tendsto
#check @Erdos335.Loeb.ultralimit_character_nsmul_eq_zero_of_eventually
#print axioms Erdos335.Loeb.ultralimit_character_nsmul_eq_zero_of_eventually
#check @Erdos335.Loeb.loeb_character_not_eventually_fixed_torsion
#print axioms Erdos335.Loeb.loeb_character_not_eventually_fixed_torsion
#check @Erdos335.Loeb.loeb_character_eventually_not_fixed_torsion
#print axioms Erdos335.Loeb.loeb_character_eventually_not_fixed_torsion
#check @Erdos335.Loeb.loeb_character_addOrder_tendsto_atTop
#print axioms Erdos335.Loeb.loeb_character_addOrder_tendsto_atTop
#check @Erdos335.Loeb.exists_sublinear_character_phase_of_unbounded_drift
#print axioms Erdos335.Loeb.exists_sublinear_character_phase_of_unbounded_drift
#check @Erdos335.Loeb.loeb_bounded_drift_exclusion_of_separated_interval
#print axioms Erdos335.Loeb.loeb_bounded_drift_exclusion_of_separated_interval
#check @Erdos335.Loeb.loeb_low_gap_periodic_or_null_prefix
#print axioms Erdos335.Loeb.loeb_low_gap_periodic_or_null_prefix
#check @Erdos335.Loeb.exists_circle_drift_separated_interval
#print axioms Erdos335.Loeb.exists_circle_drift_separated_interval
#check @Erdos335.Loeb.standard_character_non_torsion_of_prefix_model
#print axioms Erdos335.Loeb.standard_character_non_torsion_of_prefix_model
#check @Erdos335.Loeb.short_circle_arc_properties
#print axioms Erdos335.Loeb.short_circle_arc_properties
#check @Erdos335.Loeb.global_prefix_irrational_arc
#print axioms Erdos335.Loeb.global_prefix_irrational_arc
#check @Erdos335.exists_joint_residue_prefix_subsequence
#print axioms Erdos335.exists_joint_residue_prefix_subsequence
#check @Erdos335.Loeb.constrained_cyclic_to_loeb
#print axioms Erdos335.Loeb.constrained_cyclic_to_loeb
#check @Erdos335.Loeb.NaturalResidueProfile
#print axioms Erdos335.Loeb.NaturalResidueProfile
#check @Erdos335.Loeb.positiveResiduePattern
#print axioms Erdos335.Loeb.positiveResiduePattern
#check @Erdos335.Loeb.LocalPositiveResidueProfile
#print axioms Erdos335.Loeb.LocalPositiveResidueProfile
#check @Erdos335.Loeb.paired_positive_profiles_match
#print axioms Erdos335.Loeb.paired_positive_profiles_match
#check @Erdos335.Loeb.exists_local_positive_profile_of_quasi_terminal
#print axioms Erdos335.Loeb.exists_local_positive_profile_of_quasi_terminal
#check @Erdos335.Loeb.exists_local_positive_profile_of_whole_bohr
#print axioms Erdos335.Loeb.exists_local_positive_profile_of_whole_bohr
#check @Erdos335.Loeb.exists_local_positive_profile_of_high_gaps
#print axioms Erdos335.Loeb.exists_local_positive_profile_of_high_gaps
#check @Erdos335.Loeb.exists_high_gap_paired_profiles
#print axioms Erdos335.Loeb.exists_high_gap_paired_profiles
#check @Erdos335.Loeb.constrained_length_gap_of_ratio
#print axioms Erdos335.Loeb.constrained_length_gap_of_ratio
#check @Erdos335.Loeb.constrained_actual_window_profiles_agree
#print axioms Erdos335.Loeb.constrained_actual_window_profiles_agree
#check @Erdos335.Loeb.constrained_prefix_profile_eq_limit
#print axioms Erdos335.Loeb.constrained_prefix_profile_eq_limit
#check @Erdos335.Loeb.constrained_prefix_model_profile_eq_limit
#print axioms Erdos335.Loeb.constrained_prefix_model_profile_eq_limit
#check @Erdos335.Loeb.actual_window_profile_tendsto_absolute_counts
#print axioms Erdos335.Loeb.actual_window_profile_tendsto_absolute_counts
#check @Erdos335.Loeb.reference_window_profile_tendsto_of_actual_profile
#print axioms Erdos335.Loeb.reference_window_profile_tendsto_of_actual_profile
#check @Erdos335.Loeb.high_gap_fixed_scale_window_profiles
#print axioms Erdos335.Loeb.high_gap_fixed_scale_window_profiles
#check @Erdos335.Loeb.not_eventually_separated_of_tendsto
#print axioms Erdos335.Loeb.not_eventually_separated_of_tendsto
#check @Erdos335.Loeb.high_gap_dense_start_exclusion
#print axioms Erdos335.Loeb.high_gap_dense_start_exclusion
#check @Erdos335.Loeb.high_gap_bad_start_fraction_tendsto_zero
#print axioms Erdos335.Loeb.high_gap_bad_start_fraction_tendsto_zero
#check @Erdos335.Loeb.high_gap_macro_prefix_profiles
#print axioms Erdos335.Loeb.high_gap_macro_prefix_profiles
#check @Erdos335.Loeb.positiveProfileScalarValues
#print axioms Erdos335.Loeb.positiveProfileScalarValues
#check @Erdos335.Loeb.positiveResiduePattern_mem_scalarValues
#print axioms Erdos335.Loeb.positiveResiduePattern_mem_scalarValues
#check @Erdos335.Loeb.LocalPositiveResidueProfile.total_output
#print axioms Erdos335.Loeb.LocalPositiveResidueProfile.total_output
#check @Erdos335.Loeb.LocalPositiveResidueProfile.scalar_values
#print axioms Erdos335.Loeb.LocalPositiveResidueProfile.scalar_values
#check @Erdos335.Loeb.high_gap_prefix_scalar_values
#print axioms Erdos335.Loeb.high_gap_prefix_scalar_values
#check @Erdos335.Loeb.exists_high_gap_convergent_macro_subsequence
#print axioms Erdos335.Loeb.exists_high_gap_convergent_macro_subsequence
#check @Erdos335.finite_template_close_of_diverging_subsequence_limits
#print axioms Erdos335.finite_template_close_of_diverging_subsequence_limits
#check @Erdos335.tendsto_of_finite_diverging_subsequence_limits
#print axioms Erdos335.tendsto_of_finite_diverging_subsequence_limits
#check @Erdos335.normalized_prefix_step_tendsto_zero
#print axioms Erdos335.normalized_prefix_step_tendsto_zero
#check @Erdos335.normalized_prefix_limit_of_finite_subsequence_limits
#print axioms Erdos335.normalized_prefix_limit_of_finite_subsequence_limits
#check @Erdos335.hasDensity_of_normalized_prefix_limit
#print axioms Erdos335.hasDensity_of_normalized_prefix_limit
#check @Erdos335.Loeb.exists_high_gap_ordinary_prefix_profiles
#print axioms Erdos335.Loeb.exists_high_gap_ordinary_prefix_profiles
#check @Erdos335.hasDensity_finset_iUnion_of_disjoint
#print axioms Erdos335.hasDensity_finset_iUnion_of_disjoint
#check @Erdos335.Loeb.literal_residue_density_coarsening
#print axioms Erdos335.Loeb.literal_residue_density_coarsening
#check @Erdos335.Loeb.exists_high_gap_all_residue_densities
#print axioms Erdos335.Loeb.exists_high_gap_all_residue_densities
#check @Erdos335.Loeb.actual_zero_prefix_profile_of_density
#print axioms Erdos335.Loeb.actual_zero_prefix_profile_of_density
#check @Erdos335.Loeb.exists_high_gap_profile_of_ordinary_residue_densities
#print axioms Erdos335.Loeb.exists_high_gap_profile_of_ordinary_residue_densities
#check @Erdos335.Loeb.exists_high_gap_global_positive_profile
#print axioms Erdos335.Loeb.exists_high_gap_global_positive_profile
#check @Erdos335.Proposed.section_sum_hasDensity_of_fiber_sum
#print axioms Erdos335.Proposed.section_sum_hasDensity_of_fiber_sum
#check @Erdos335.Proposed.ordinary_positive_finite_frame
#print axioms Erdos335.Proposed.ordinary_positive_finite_frame
#check @Erdos335.Proposed.FiniteFrame.active_sections_sum_hasDensity
#print axioms Erdos335.Proposed.FiniteFrame.active_sections_sum_hasDensity
#check @Erdos335.Proposed.FiniteFrame.sum_density_iff_active_sections
#print axioms Erdos335.Proposed.FiniteFrame.sum_density_iff_active_sections
#check @Erdos335.Proposed.refinedSectionResidue
#print axioms Erdos335.Proposed.refinedSectionResidue
#check @Erdos335.Proposed.refinedSectionResidue_projection
#print axioms Erdos335.Proposed.refinedSectionResidue_projection
#check @Erdos335.Proposed.residueSection_compose
#print axioms Erdos335.Proposed.residueSection_compose
#check @Erdos335.Proposed.residueSection_uniform_residue_density
#print axioms Erdos335.Proposed.residueSection_uniform_residue_density
#check @Erdos335.IntermediateScale.exists_ordinary_density_loeb_models_with_prefix
#print axioms Erdos335.IntermediateScale.exists_ordinary_density_loeb_models_with_prefix
#check @Erdos335.Loeb.uniform_prefix_loeb_profiles
#print axioms Erdos335.Loeb.uniform_prefix_loeb_profiles
#check @Erdos335.Loeb.whole_bohr_modulus_one_of_uniform_profiles
#print axioms Erdos335.Loeb.whole_bohr_modulus_one_of_uniform_profiles
#check @Erdos335.Loeb.not_quasiPeriodic_of_uniform_profiles
#print axioms Erdos335.Loeb.not_quasiPeriodic_of_uniform_profiles
#check @Erdos335.Loeb.whole_bohr_of_uniform_prefix_terminal
#print axioms Erdos335.Loeb.whole_bohr_of_uniform_prefix_terminal
#check @Erdos335.positiveOrbitPullback
#print axioms Erdos335.positiveOrbitPullback
#check @Erdos335.shift_positiveOrbitPullback_subset
#print axioms Erdos335.shift_positiveOrbitPullback_subset
#check @Erdos335.mem_positiveOrbitPullback_translate_iff
#print axioms Erdos335.mem_positiveOrbitPullback_translate_iff
#check @Erdos335.positiveOrbitPullback_translate_densityEquivalent
#print axioms Erdos335.positiveOrbitPullback_translate_densityEquivalent
#check @Erdos335.positiveOrbitPullback_translate_sdiff_sum_negligible
#print axioms Erdos335.positiveOrbitPullback_translate_sdiff_sum_negligible
#check @Erdos335.positiveOrbitPullback_finite_translates_sdiff_sum_negligible
#print axioms Erdos335.positiveOrbitPullback_finite_translates_sdiff_sum_negligible
#check @Erdos335.Proposed.closedArcPullback_eq_positiveOrbitPullback
#print axioms Erdos335.Proposed.closedArcPullback_eq_positiveOrbitPullback
#check @Erdos335.Proposed.closedArcPullback_openOrbit_equivalent
#print axioms Erdos335.Proposed.closedArcPullback_openOrbit_equivalent
#check @Erdos335.Proposed.filled_arc_openOrbit_equivalent
#print axioms Erdos335.Proposed.filled_arc_openOrbit_equivalent
#check @Erdos335.Proposed.density_le_closed_orbit_carrier_measure
#print axioms Erdos335.Proposed.density_le_closed_orbit_carrier_measure
#check @Erdos335.Proposed.open_orbit_measure_le_density_of_negligible_excess
#print axioms Erdos335.Proposed.open_orbit_measure_le_density_of_negligible_excess
#check @Erdos335.Proposed.open_orbit_measure_le_of_hasDensity
#print axioms Erdos335.Proposed.open_orbit_measure_le_of_hasDensity
#check @Erdos335.closure_image_add_open_eq_iUnion
#print axioms Erdos335.closure_image_add_open_eq_iUnion
#check @Erdos335.measure_biUnion_le_of_finset_bounds
#print axioms Erdos335.measure_biUnion_le_of_finset_bounds
#check @Erdos335.orbit_closure_add_open_eq_iUnion
#print axioms Erdos335.orbit_closure_add_open_eq_iUnion
#check @Erdos335.volume_orbit_closure_add_open_le
#print axioms Erdos335.volume_orbit_closure_add_open_le
#check @Erdos335.volume_orbit_closure_add_open_toReal_le
#print axioms Erdos335.volume_orbit_closure_add_open_toReal_le
#check @Erdos335.Loeb.unitCircle_sum_measure_lower_bound
#print axioms Erdos335.Loeb.unitCircle_sum_measure_lower_bound
#check @Erdos335.Loeb.unitCircle_sum_measure_toReal_lower_bound
#print axioms Erdos335.Loeb.unitCircle_sum_measure_toReal_lower_bound
#check @Erdos335.Loeb.circle_closed_arc_differences_shrink
#print axioms Erdos335.Loeb.circle_closed_arc_differences_shrink
#check @Erdos335.Loeb.circle_open_arc_add_closed_arc
#print axioms Erdos335.Loeb.circle_open_arc_add_closed_arc
#check @Erdos335.Loeb.unitCircle_compact_openArc_companion
#print axioms Erdos335.Loeb.unitCircle_compact_openArc_companion
#check @Erdos335.Proposed.filled_arc_companion_measure_bounds
#print axioms Erdos335.Proposed.filled_arc_companion_measure_bounds
#check @Erdos335.Proposed.ordinary_filled_arc_companion
#print axioms Erdos335.Proposed.ordinary_filled_arc_companion
#check @Erdos335.Proposed.full_support_of_uniform_residue_densities
#print axioms Erdos335.Proposed.full_support_of_uniform_residue_densities
#check @Erdos335.Proposed.gamma_eq_one_of_full_support
#print axioms Erdos335.Proposed.gamma_eq_one_of_full_support
#check @Erdos335.Proposed.positive_multiples_density_of_uniform_residue_densities
#print axioms Erdos335.Proposed.positive_multiples_density_of_uniform_residue_densities
#check @Erdos335.Proposed.parallel_irrational_arcs_of_uniform_residue_densities
#print axioms Erdos335.Proposed.parallel_irrational_arcs_of_uniform_residue_densities
#check @Erdos335.Proposed.high_gap_bohr_branch
#print axioms Erdos335.Proposed.high_gap_bohr_branch
#check @Erdos335.Proposed.LowResidueCapacityGap
#print axioms Erdos335.Proposed.LowResidueCapacityGap
#check @Erdos335.Proposed.LowPositiveGapNecessity
#print axioms Erdos335.Proposed.LowPositiveGapNecessity
#check @Erdos335.Proposed.not_low_residue_capacity_gap
#print axioms Erdos335.Proposed.not_low_residue_capacity_gap
#check @Erdos335.Proposed.positiveGapNecessity_of_low_positive_gap_necessity
#print axioms Erdos335.Proposed.positiveGapNecessity_of_low_positive_gap_necessity
#check @Erdos335.Proposed.fullSolution_of_low_positive_gap_necessity
#print axioms Erdos335.Proposed.fullSolution_of_low_positive_gap_necessity
#check @Erdos335.Loeb.baseline_strict_of_fractional_total
#print axioms Erdos335.Loeb.baseline_strict_of_fractional_total
#check @Erdos335.Loeb.finite_prefix_masks_one_saturated_baseline
#print axioms Erdos335.Loeb.finite_prefix_masks_one_saturated_baseline
#check @Erdos335.Loeb.loeb_two_prefix_masks_one_saturated_baseline
#print axioms Erdos335.Loeb.loeb_two_prefix_masks_one_saturated_baseline
#check @Erdos335.Loeb.loeb_two_null_prefix_frames_impossible
#print axioms Erdos335.Loeb.loeb_two_null_prefix_frames_impossible
#check @Erdos335.Loeb.positive_subgroup_natural_quotient_data
#print axioms Erdos335.Loeb.positive_subgroup_natural_quotient_data
#check @Erdos335.Loeb.loeb_quasi_periodic_mass_with_active
#print axioms Erdos335.Loeb.loeb_quasi_periodic_mass_with_active
#check @Erdos335.Loeb.loeb_null_prefix_fractional_data
#print axioms Erdos335.Loeb.loeb_null_prefix_fractional_data
#check @Erdos335.Loeb.finite_full_preimage_add_image
#print axioms Erdos335.Loeb.finite_full_preimage_add_image
#check @Erdos335.Loeb.natural_refined_baseline_capacity
#print axioms Erdos335.Loeb.natural_refined_baseline_capacity
#check @Erdos335.Loeb.actual_zero_prefix_indicator_refines
#print axioms Erdos335.Loeb.actual_zero_prefix_indicator_refines
#check @Erdos335.Loeb.loeb_two_coarse_null_prefixes_impossible
#print axioms Erdos335.Loeb.loeb_two_coarse_null_prefixes_impossible
#check @Erdos335.Loeb.loeb_two_null_prefix_models_force_periodic
#print axioms Erdos335.Loeb.loeb_two_null_prefix_models_force_periodic
#check @Erdos335.Loeb.loeb_low_prefix_gap_periodic_or_null_prefix
#print axioms Erdos335.Loeb.loeb_low_prefix_gap_periodic_or_null_prefix
#check @Erdos335.Loeb.ActualWindowNullFrame
#print axioms Erdos335.Loeb.ActualWindowNullFrame
#check @Erdos335.Loeb.strict_periodic_input_has_bounded_null_frame
#print axioms Erdos335.Loeb.strict_periodic_input_has_bounded_null_frame
#check @Erdos335.Loeb.saturated_output_has_bounded_null_frames
#print axioms Erdos335.Loeb.saturated_output_has_bounded_null_frames
#check @Erdos335.Loeb.periodic_input_has_bounded_null_frame
#print axioms Erdos335.Loeb.periodic_input_has_bounded_null_frame
#check @Erdos335.Loeb.ActualWindowNullFrame.integer_multiple_period
#print axioms Erdos335.Loeb.ActualWindowNullFrame.integer_multiple_period
#check @Erdos335.Loeb.exists_uniform_common_null_periods
#print axioms Erdos335.Loeb.exists_uniform_common_null_periods
#check @Erdos335.Loeb.ActualWindowNullFrame.finite_coverage
#print axioms Erdos335.Loeb.ActualWindowNullFrame.finite_coverage
#check @Erdos335.exists_finite_bounded_residue_representatives
#print axioms Erdos335.exists_finite_bounded_residue_representatives
#check @Erdos335.Loeb.exists_uniform_periodic_input_witnesses
#print axioms Erdos335.Loeb.exists_uniform_periodic_input_witnesses
#check @Erdos335.Loeb.loeb_low_gap_paired_periodic
#print axioms Erdos335.Loeb.loeb_low_gap_paired_periodic
#check @Erdos335.Loeb.exists_uniform_low_gap_window_witnesses
#print axioms Erdos335.Loeb.exists_uniform_low_gap_window_witnesses
#check @Erdos335.IntermediateScale.indicator_prefix_sum
#print axioms Erdos335.IntermediateScale.indicator_prefix_sum
#check @Erdos335.IntermediateScale.indicator_window_sum
#print axioms Erdos335.IntermediateScale.indicator_window_sum
#check @Erdos335.IntermediateScale.prefix_density_le_bad_window_fraction
#print axioms Erdos335.IntermediateScale.prefix_density_le_bad_window_fraction
#check @Erdos335.IntermediateScale.loeb_window_null_tendsto_common_length
#print axioms Erdos335.IntermediateScale.loeb_window_null_tendsto_common_length
#check @Erdos335.IntermediateScale.negligible_of_constrained_window_null
#print axioms Erdos335.IntermediateScale.negligible_of_constrained_window_null
#check @Erdos335.Loeb.low_gap_ordinary_equivalences
#print axioms Erdos335.Loeb.low_gap_ordinary_equivalences
#check @Erdos335.Proposed.low_gap_mask_branch
#print axioms Erdos335.Proposed.low_gap_mask_branch
#check @Erdos335.Proposed.low_gap_classified
#print axioms Erdos335.Proposed.low_gap_classified
#check @Erdos335.Proposed.low_gap_classified_of_either
#print axioms Erdos335.Proposed.low_gap_classified_of_either
#check @Erdos335.Proposed.low_positive_gap_necessity
#print axioms Erdos335.Proposed.low_positive_gap_necessity
#check @Erdos335.Proposed.positive_gap_necessity
#print axioms Erdos335.Proposed.positive_gap_necessity
#check @Erdos335.Proposed.full_classification
#print axioms Erdos335.Proposed.full_classification
#check @Erdos335.Proposed.full_classification_original_positive_counts
#print axioms Erdos335.Proposed.full_classification_original_positive_counts
#check @Erdos335.PeriodicRefinement.prefixCount_dist_le
#print axioms Erdos335.PeriodicRefinement.prefixCount_dist_le
#check @Erdos335.PeriodicRefinement.exists_continuous_prefix_count
#print axioms Erdos335.PeriodicRefinement.exists_continuous_prefix_count
#check @Erdos335.PeriodicRefinement.continuous_prefix_count_error
#print axioms Erdos335.PeriodicRefinement.continuous_prefix_count_error
#check @Erdos335.PeriodicRefinement.rescaled_prefix_count_error
#print axioms Erdos335.PeriodicRefinement.rescaled_prefix_count_error
#check @Erdos335.PeriodicRefinement.rescaled_prefix_count_lipschitz
#print axioms Erdos335.PeriodicRefinement.rescaled_prefix_count_lipschitz
#check @Erdos335.PeriodicRefinement.cumulativeProfileSpace
#print axioms Erdos335.PeriodicRefinement.cumulativeProfileSpace
#check @Erdos335.PeriodicRefinement.cumulativeProfileSpace_compact
#print axioms Erdos335.PeriodicRefinement.cumulativeProfileSpace_compact
#check @Erdos335.PeriodicRefinement.exists_cumulative_profile_subsequence
#print axioms Erdos335.PeriodicRefinement.exists_cumulative_profile_subsequence
#check @Erdos335.PeriodicRefinement.exists_joint_cumulative_limits
#print axioms Erdos335.PeriodicRefinement.exists_joint_cumulative_limits
#check @Erdos335.PeriodicRefinement.exists_compact_uniform_error
#print axioms Erdos335.PeriodicRefinement.exists_compact_uniform_error
#check @Erdos335.PeriodicRefinement.macroInput
#print axioms Erdos335.PeriodicRefinement.macroInput
#check @Erdos335.PeriodicRefinement.CompactCumulativeData
#print axioms Erdos335.PeriodicRefinement.CompactCumulativeData
#check @Erdos335.PeriodicRefinement.CompactCumulativeData.subsequence
#print axioms Erdos335.PeriodicRefinement.CompactCumulativeData.subsequence
#check @Erdos335.PeriodicRefinement.exists_compact_cumulative_data
#print axioms Erdos335.PeriodicRefinement.exists_compact_cumulative_data
#check @Erdos335.PeriodicRefinement.normalized_derivative_remainder
#print axioms Erdos335.PeriodicRefinement.normalized_derivative_remainder
#check @Erdos335.PeriodicRefinement.moving_derivative_window_tendsto
#print axioms Erdos335.PeriodicRefinement.moving_derivative_window_tendsto
#check @Erdos335.PeriodicRefinement.moving_approximate_derivative_window_tendsto
#print axioms Erdos335.PeriodicRefinement.moving_approximate_derivative_window_tendsto
#check @Erdos335.PeriodicRefinement.UniformCumulativeApproximation
#print axioms Erdos335.PeriodicRefinement.UniformCumulativeApproximation
#check @Erdos335.PeriodicRefinement.macro_start_normalized_bound
#print axioms Erdos335.PeriodicRefinement.macro_start_normalized_bound
#check @Erdos335.PeriodicRefinement.actual_macro_window_density
#print axioms Erdos335.PeriodicRefinement.actual_macro_window_density
#check @Erdos335.PeriodicRefinement.macro_floor_shift_bound
#print axioms Erdos335.PeriodicRefinement.macro_floor_shift_bound
#check @Erdos335.PeriodicRefinement.actual_macro_floor_window_density
#print axioms Erdos335.PeriodicRefinement.actual_macro_floor_window_density
#check @Erdos335.PeriodicRefinement.actual_macro_floor_density
#print axioms Erdos335.PeriodicRefinement.actual_macro_floor_density
#check @Erdos335.PeriodicRefinement.macro_cross_start_bound
#print axioms Erdos335.PeriodicRefinement.macro_cross_start_bound
#check @Erdos335.PeriodicRefinement.cumulativeErrorBudget
#print axioms Erdos335.PeriodicRefinement.cumulativeErrorBudget
#check @Erdos335.PeriodicRefinement.cumulativeErrorBudget_nonnegative
#print axioms Erdos335.PeriodicRefinement.cumulativeErrorBudget_nonnegative
#check @Erdos335.PeriodicRefinement.cumulativeErrorBudget_sublinear
#print axioms Erdos335.PeriodicRefinement.cumulativeErrorBudget_sublinear
#check @Erdos335.PeriodicRefinement.cumulative_error_small_of_budget_small
#print axioms Erdos335.PeriodicRefinement.cumulative_error_small_of_budget_small
#check @Erdos335.PeriodicRefinement.prefix_errors_small_of_budget_small
#print axioms Erdos335.PeriodicRefinement.prefix_errors_small_of_budget_small
#check @Erdos335.PeriodicRefinement.cumulativeApproximationOfBudget
#print axioms Erdos335.PeriodicRefinement.cumulativeApproximationOfBudget
#check @Erdos335.IntermediateScale.exists_countable_sublinear_error_scale
#print axioms Erdos335.IntermediateScale.exists_countable_sublinear_error_scale
#check @Erdos335.IntermediateScale.refinementIndex
#print axioms Erdos335.IntermediateScale.refinementIndex
#check @Erdos335.IntermediateScale.refinementIndex_strictMono
#print axioms Erdos335.IntermediateScale.refinementIndex_strictMono
#check @Erdos335.IntermediateScale.refinementIndex_factor
#print axioms Erdos335.IntermediateScale.refinementIndex_factor
#check @Erdos335.IntermediateScale.exists_nested_interval_diagonal
#print axioms Erdos335.IntermediateScale.exists_nested_interval_diagonal
#check @Erdos335.IntermediateScale.IntermediateFourierModel.ambientCongr
#print axioms Erdos335.IntermediateScale.IntermediateFourierModel.ambientCongr
#check @Erdos335.IntermediateScale.exists_periodic_refinement_common_scales
#print axioms Erdos335.IntermediateScale.exists_periodic_refinement_common_scales
#check @Erdos335.PeriodicRefinement.modelEnlargement
#print axioms Erdos335.PeriodicRefinement.modelEnlargement
#check @Erdos335.PeriodicRefinement.modelMoving
#print axioms Erdos335.PeriodicRefinement.modelMoving
#check @Erdos335.PeriodicRefinement.modelOther
#print axioms Erdos335.PeriodicRefinement.modelOther
#check @Erdos335.PeriodicRefinement.PreparedMacroScales
#print axioms Erdos335.PeriodicRefinement.PreparedMacroScales
#check @Erdos335.PeriodicRefinement.exists_prepared_macro_scales
#print axioms Erdos335.PeriodicRefinement.exists_prepared_macro_scales
#check @Erdos335.PeriodicRefinement.floorBadStartSet
#print axioms Erdos335.PeriodicRefinement.floorBadStartSet
#check @Erdos335.PeriodicRefinement.measurableSet_floorBadStartSet
#print axioms Erdos335.PeriodicRefinement.measurableSet_floorBadStartSet
#check @Erdos335.PeriodicRefinement.floorBadStartSet_subset_grid
#print axioms Erdos335.PeriodicRefinement.floorBadStartSet_subset_grid
#check @Erdos335.PeriodicRefinement.volume_floorBadStartSet_le
#print axioms Erdos335.PeriodicRefinement.volume_floorBadStartSet_le
#check @Erdos335.PeriodicRefinement.exists_geometric_bad_start_subsequence
#print axioms Erdos335.PeriodicRefinement.exists_geometric_bad_start_subsequence
#check @Erdos335.PeriodicRefinement.exists_ae_good_floor_subsequence
#print axioms Erdos335.PeriodicRefinement.exists_ae_good_floor_subsequence
#check @Erdos335.PeriodicRefinement.exists_prescribed_window_error_data
#print axioms Erdos335.PeriodicRefinement.exists_prescribed_window_error_data
#check @Erdos335.PeriodicRefinement.threshold_fraction_tendsto_zero
#print axioms Erdos335.PeriodicRefinement.threshold_fraction_tendsto_zero
#check @Erdos335.PeriodicRefinement.threshold_fraction_tendsto_zero_of_eventually_pos
#print axioms Erdos335.PeriodicRefinement.threshold_fraction_tendsto_zero_of_eventually_pos
#check @Erdos335.PeriodicRefinement.floor_mul_mem_enlarged_range
#print axioms Erdos335.PeriodicRefinement.floor_mul_mem_enlarged_range
#check @Erdos335.PeriodicRefinement.exists_ae_sampled_error_subsequence
#print axioms Erdos335.PeriodicRefinement.exists_ae_sampled_error_subsequence
#check @Erdos335.PeriodicRefinement.exists_ae_prescribed_window_error_data
#print axioms Erdos335.PeriodicRefinement.exists_ae_prescribed_window_error_data
#check @Erdos335.PeriodicRefinement.sampled_start_add_six_windows_le
#print axioms Erdos335.PeriodicRefinement.sampled_start_add_six_windows_le
#check @Erdos335.PeriodicRefinement.exists_ae_sampled_convolution_windows
#print axioms Erdos335.PeriodicRefinement.exists_ae_sampled_convolution_windows
#check @Erdos335.PeriodicRefinement.residue_window_translate_subset
#print axioms Erdos335.PeriodicRefinement.residue_window_translate_subset
#check @Erdos335.PeriodicRefinement.residue_window_translate_card_le
#print axioms Erdos335.PeriodicRefinement.residue_window_translate_card_le
#check @Erdos335.PeriodicRefinement.exists_literal_window_element
#print axioms Erdos335.PeriodicRefinement.exists_literal_window_element
#check @Erdos335.PeriodicRefinement.residue_cross_profile_le
#print axioms Erdos335.PeriodicRefinement.residue_cross_profile_le
#check @Erdos335.PeriodicRefinement.exists_literal_residue_window_sequence
#print axioms Erdos335.PeriodicRefinement.exists_literal_residue_window_sequence
#check @Erdos335.PeriodicRefinement.derivative_residue_cross_le
#print axioms Erdos335.PeriodicRefinement.derivative_residue_cross_le
#check @Erdos335.PeriodicRefinement.derivative_residue_cross_max
#print axioms Erdos335.PeriodicRefinement.derivative_residue_cross_max
#check @Erdos335.FiniteKneser.critical_cross_union_has_full_baseline
#print axioms Erdos335.FiniteKneser.critical_cross_union_has_full_baseline
#check @Erdos335.critical_residue_union_has_full_baseline
#print axioms Erdos335.critical_residue_union_has_full_baseline
#check @Erdos335.strict_card_ratio_of_fractional_mass
#print axioms Erdos335.strict_card_ratio_of_fractional_mass
#check @Erdos335.PeriodicRefinementLabels.compatible_partner_card_bound
#print axioms Erdos335.PeriodicRefinementLabels.compatible_partner_card_bound
#check @Erdos335.PeriodicRefinementLabels.completionMask
#print axioms Erdos335.PeriodicRefinementLabels.completionMask
#check @Erdos335.PeriodicRefinementLabels.mem_completionMask
#print axioms Erdos335.PeriodicRefinementLabels.mem_completionMask
#check @Erdos335.PeriodicRefinementLabels.saturated_partner_eq_completion
#print axioms Erdos335.PeriodicRefinementLabels.saturated_partner_eq_completion
#check @Erdos335.PeriodicRefinementLabels.saturated_partner_profile
#print axioms Erdos335.PeriodicRefinementLabels.saturated_partner_profile
#check @Erdos335.PeriodicRefinementLabels.saturated_partner_profiles_unique
#print axioms Erdos335.PeriodicRefinementLabels.saturated_partner_profiles_unique
#check @Erdos335.PeriodicRefinementLabels.both_periodic_profiles_have_saturated_baseline
#print axioms Erdos335.PeriodicRefinementLabels.both_periodic_profiles_have_saturated_baseline
#check @Erdos335.PeriodicRefinementLabelClosure.IsIndicator
#print axioms Erdos335.PeriodicRefinementLabelClosure.IsIndicator
#check @Erdos335.PeriodicRefinementLabelClosure.LocalProfile
#print axioms Erdos335.PeriodicRefinementLabelClosure.LocalProfile
#check @Erdos335.PeriodicRefinementLabelClosure.LocalLabel
#print axioms Erdos335.PeriodicRefinementLabelClosure.LocalLabel
#check @Erdos335.PeriodicRefinementLabelClosure.localLabelFinite
#print axioms Erdos335.PeriodicRefinementLabelClosure.localLabelFinite
#check @Erdos335.PeriodicRefinementLabelClosure.HasLabel
#print axioms Erdos335.PeriodicRefinementLabelClosure.HasLabel
#check @Erdos335.PeriodicRefinementLabelClosure.LocalLabel.swap
#print axioms Erdos335.PeriodicRefinementLabelClosure.LocalLabel.swap
#check @Erdos335.PeriodicRefinementLabelClosure.LocalLabel.swap_swap
#print axioms Erdos335.PeriodicRefinementLabelClosure.LocalLabel.swap_swap
#check @Erdos335.PeriodicRefinementLabelClosure.LocalProfile.swap
#print axioms Erdos335.PeriodicRefinementLabelClosure.LocalProfile.swap
#check @Erdos335.PeriodicRefinementLabelClosure.HasLabel.swap
#print axioms Erdos335.PeriodicRefinementLabelClosure.HasLabel.swap
#check @Erdos335.PeriodicRefinementLabelClosure.indicator_sum
#print axioms Erdos335.PeriodicRefinementLabelClosure.indicator_sum
#check @Erdos335.PeriodicRefinementLabelClosure.indicator_masks_eq
#print axioms Erdos335.PeriodicRefinementLabelClosure.indicator_masks_eq
#check @Erdos335.PeriodicRefinementLabelClosure.indicator_zero_or_one
#print axioms Erdos335.PeriodicRefinementLabelClosure.indicator_zero_or_one
#check @Erdos335.PeriodicRefinementLabelClosure.indicator_of_zero_or_one
#print axioms Erdos335.PeriodicRefinementLabelClosure.indicator_of_zero_or_one
#check @Erdos335.PeriodicRefinementLabelClosure.eq_of_pointwise_le_of_sum_eq
#print axioms Erdos335.PeriodicRefinementLabelClosure.eq_of_pointwise_le_of_sum_eq
#check @Erdos335.PeriodicRefinementLabelClosure.indicator_of_supported_mass
#print axioms Erdos335.PeriodicRefinementLabelClosure.indicator_of_supported_mass
#check @Erdos335.PeriodicRefinementLabelClosure.left_mask_card
#print axioms Erdos335.PeriodicRefinementLabelClosure.left_mask_card
#check @Erdos335.PeriodicRefinementLabelClosure.right_mask_card
#print axioms Erdos335.PeriodicRefinementLabelClosure.right_mask_card
#check @Erdos335.PeriodicRefinementLabelClosure.left_mask_subset
#print axioms Erdos335.PeriodicRefinementLabelClosure.left_mask_subset
#check @Erdos335.PeriodicRefinementLabelClosure.right_mask_subset
#print axioms Erdos335.PeriodicRefinementLabelClosure.right_mask_subset
#check @Erdos335.PeriodicRefinementLabelClosure.left_baseline_full
#print axioms Erdos335.PeriodicRefinementLabelClosure.left_baseline_full
#check @Erdos335.PeriodicRefinementLabelClosure.right_baseline_full
#print axioms Erdos335.PeriodicRefinementLabelClosure.right_baseline_full
#check @Erdos335.PeriodicRefinementLabelClosure.full_mask_card_le_mass
#print axioms Erdos335.PeriodicRefinementLabelClosure.full_mask_card_le_mass
#check @Erdos335.PeriodicRefinementLabelClosure.both_periodic_baseline_saturated
#print axioms Erdos335.PeriodicRefinementLabelClosure.both_periodic_baseline_saturated
#check @Erdos335.PeriodicRefinementLabelClosure.saturated_left_partner_indicator
#print axioms Erdos335.PeriodicRefinementLabelClosure.saturated_left_partner_indicator
#check @Erdos335.PeriodicRefinementLabelClosure.partner_eq_of_saturated_left
#print axioms Erdos335.PeriodicRefinementLabelClosure.partner_eq_of_saturated_left
#check @Erdos335.PeriodicRefinementLabelClosure.partner_eq_of_saturated_right
#print axioms Erdos335.PeriodicRefinementLabelClosure.partner_eq_of_saturated_right
#check @Erdos335.PeriodicRefinementLabelClosure.label_eq_right_of_indicator
#print axioms Erdos335.PeriodicRefinementLabelClosure.label_eq_right_of_indicator
#check @Erdos335.PeriodicRefinementLabelClosure.label_eq_both_of_indicators
#print axioms Erdos335.PeriodicRefinementLabelClosure.label_eq_both_of_indicators
#check @Erdos335.PeriodicRefinementLabelClosure.StrictRightFrame
#print axioms Erdos335.PeriodicRefinementLabelClosure.StrictRightFrame
#check @Erdos335.PeriodicRefinementLabelClosure.LabelFrame
#print axioms Erdos335.PeriodicRefinementLabelClosure.LabelFrame
#check @Erdos335.PeriodicRefinementLabelClosure.CrossInequality
#print axioms Erdos335.PeriodicRefinementLabelClosure.CrossInequality
#check @Erdos335.PeriodicRefinementLabelClosure.positive_outside_mask_of_not_indicator
#print axioms Erdos335.PeriodicRefinementLabelClosure.positive_outside_mask_of_not_indicator
#check @Erdos335.PeriodicRefinementLabelClosure.same_label_one_indicator
#print axioms Erdos335.PeriodicRefinementLabelClosure.same_label_one_indicator
#check @Erdos335.PeriodicRefinementLabelClosure.strict_right_label_closed
#print axioms Erdos335.PeriodicRefinementLabelClosure.strict_right_label_closed
#check @Erdos335.PeriodicRefinementLabelClosure.saturated_label_closed
#print axioms Erdos335.PeriodicRefinementLabelClosure.saturated_label_closed
#check @Erdos335.PeriodicRefinementLabelClosure.same_label_sum_has_same_label
#print axioms Erdos335.PeriodicRefinementLabelClosure.same_label_sum_has_same_label
#check @Erdos335.Loeb.saturated_periodic_mask_determines_partner
#print axioms Erdos335.Loeb.saturated_periodic_mask_determines_partner
#check @Erdos335.Loeb.periodic_input_masks_have_saturated_baseline
#print axioms Erdos335.Loeb.periodic_input_masks_have_saturated_baseline
#check @Erdos335.Loeb.actualLocalLabelProfile
#print axioms Erdos335.Loeb.actualLocalLabelProfile
#check @Erdos335.Loeb.literal_card_gap_at_modulus
#print axioms Erdos335.Loeb.literal_card_gap_at_modulus
#check @Erdos335.Loeb.actual_physical_indicator_refines
#print axioms Erdos335.Loeb.actual_physical_indicator_refines
#check @Erdos335.Loeb.actual_full_profile_refines
#print axioms Erdos335.Loeb.actual_full_profile_refines
#check @Erdos335.Loeb.fine_fiber_translate_of_coarse
#print axioms Erdos335.Loeb.fine_fiber_translate_of_coarse
#check @Erdos335.Loeb.fine_profile_eq_of_coarse_fiber_translate
#print axioms Erdos335.Loeb.fine_profile_eq_of_coarse_fiber_translate
#check @Erdos335.Loeb.actual_null_frame_indicator_at_multiple
#print axioms Erdos335.Loeb.actual_null_frame_indicator_at_multiple
#check @Erdos335.Loeb.actual_bounded_null_frame_indicator
#print axioms Erdos335.Loeb.actual_bounded_null_frame_indicator
#check @Erdos335.Loeb.actual_strict_right_coarse_frame
#print axioms Erdos335.Loeb.actual_strict_right_coarse_frame
#check @Erdos335.Loeb.saturated_fine_extras_outside
#print axioms Erdos335.Loeb.saturated_fine_extras_outside
#check @Erdos335.Loeb.actual_saturated_label_frame
#print axioms Erdos335.Loeb.actual_saturated_label_frame
#check @Erdos335.Loeb.actual_strict_right_label_frame
#print axioms Erdos335.Loeb.actual_strict_right_label_frame
#check @Erdos335.Loeb.actual_strict_left_label_frame
#print axioms Erdos335.Loeb.actual_strict_left_label_frame
#check @Erdos335.Loeb.actual_periodic_profile_has_label
#print axioms Erdos335.Loeb.actual_periodic_profile_has_label
#check @Erdos335.Loeb.actual_bounded_null_frame_has_label
#print axioms Erdos335.Loeb.actual_bounded_null_frame_has_label
#check @Erdos335.PeriodicRefinementLabelClosure.hasLabel_unique
#print axioms Erdos335.PeriodicRefinementLabelClosure.hasLabel_unique
#check @Erdos335.Loeb.factorial_neZero
#print axioms Erdos335.Loeb.factorial_neZero
#check @Erdos335.Loeb.prescribed_window_profile_eq_limit
#print axioms Erdos335.Loeb.prescribed_window_profile_eq_limit
#check @Erdos335.Loeb.prescribed_small_error_window_has_label
#print axioms Erdos335.Loeb.prescribed_small_error_window_has_label
#check @Erdos335.PeriodicRefinementGlobal.AEAddClosed
#print axioms Erdos335.PeriodicRefinementGlobal.AEAddClosed
#check @Erdos335.PeriodicRefinementGlobal.selfIntegral
#print axioms Erdos335.PeriodicRefinementGlobal.selfIntegral
#check @Erdos335.PeriodicRefinementGlobal.continuous_selfIntegral
#print axioms Erdos335.PeriodicRefinementGlobal.continuous_selfIntegral
#check @Erdos335.PeriodicRefinementGlobal.ae_add_closed_fiber
#print axioms Erdos335.PeriodicRefinementGlobal.ae_add_closed_fiber
#check @Erdos335.PeriodicRefinementGlobal.selfIntegral_indicator_zero_off
#print axioms Erdos335.PeriodicRefinementGlobal.selfIntegral_indicator_zero_off
#check @Erdos335.PeriodicRefinementGlobal.exists_positive_interval_ae_subset_of_ae_add_closed
#print axioms Erdos335.PeriodicRefinementGlobal.exists_positive_interval_ae_subset_of_ae_add_closed
#check @Erdos335.PeriodicRefinementGlobal.ae_interval_add_subset
#print axioms Erdos335.PeriodicRefinementGlobal.ae_interval_add_subset
#check @Erdos335.PeriodicRefinementGlobal.exists_tail_ae_subset_of_ae_add_closed
#print axioms Erdos335.PeriodicRefinementGlobal.exists_tail_ae_subset_of_ae_add_closed
#check @Erdos335.PeriodicRefinementGlobal.exists_conull_label_of_ae_add_closed_partition
#print axioms Erdos335.PeriodicRefinementGlobal.exists_conull_label_of_ae_add_closed_partition
#check @Erdos335.PeriodicRefinementGlobal.measurable_finite_label_ae_constant
#print axioms Erdos335.PeriodicRefinementGlobal.measurable_finite_label_ae_constant
#check @Erdos335.PeriodicRefinementMacroAssembly.ProfilePair
#print axioms Erdos335.PeriodicRefinementMacroAssembly.ProfilePair
#check @Erdos335.PeriodicRefinementMacroAssembly.maskVector
#print axioms Erdos335.PeriodicRefinementMacroAssembly.maskVector
#check @Erdos335.PeriodicRefinementMacroAssembly.isIndicator_iff_eq_maskVector
#print axioms Erdos335.PeriodicRefinementMacroAssembly.isIndicator_iff_eq_maskVector
#check @Erdos335.PeriodicRefinementMacroAssembly.periodicInputSlice
#print axioms Erdos335.PeriodicRefinementMacroAssembly.periodicInputSlice
#check @Erdos335.PeriodicRefinementMacroAssembly.profile_pair_mem_slice_iff
#print axioms Erdos335.PeriodicRefinementMacroAssembly.profile_pair_mem_slice_iff
#check @Erdos335.PeriodicRefinementMacroAssembly.isClosed_periodicInputSlice
#print axioms Erdos335.PeriodicRefinementMacroAssembly.isClosed_periodicInputSlice
#check @Erdos335.PeriodicRefinementMacroAssembly.measurableSet_isIndicator
#print axioms Erdos335.PeriodicRefinementMacroAssembly.measurableSet_isIndicator
#check @Erdos335.PeriodicRefinementMacroAssembly.measurableSet_hasLabel
#print axioms Erdos335.PeriodicRefinementMacroAssembly.measurableSet_hasLabel
#check @Erdos335.PeriodicRefinementMacroAssembly.hasLabel_unique
#print axioms Erdos335.PeriodicRefinementMacroAssembly.hasLabel_unique
#check @Erdos335.PeriodicRefinementMacroAssembly.label_eq_of_local_profile_slices
#print axioms Erdos335.PeriodicRefinementMacroAssembly.label_eq_of_local_profile_slices
#check @Erdos335.PeriodicRefinementMacroAssembly.exists_ae_profile_label
#print axioms Erdos335.PeriodicRefinementMacroAssembly.exists_ae_profile_label
#check @Erdos335.PeriodicRefinementGlobal.eventually_constant_of_separated_slice_approximants
#print axioms Erdos335.PeriodicRefinementGlobal.eventually_constant_of_separated_slice_approximants
#check @Erdos335.PeriodicRefinementGlobal.compact_disjoint_slices_separated
#print axioms Erdos335.PeriodicRefinementGlobal.compact_disjoint_slices_separated
#check @Erdos335.PeriodicRefinementGlobal.exists_single_compact_cluster_slice
#print axioms Erdos335.PeriodicRefinementGlobal.exists_single_compact_cluster_slice
#check @Erdos335.PeriodicRefinementGlobal.tendsto_of_compact_cluster_slice_constant
#print axioms Erdos335.PeriodicRefinementGlobal.tendsto_of_compact_cluster_slice_constant
#check @Erdos335.PeriodicRefinementGlobal.exists_single_closed_cluster_slice
#print axioms Erdos335.PeriodicRefinementGlobal.exists_single_closed_cluster_slice
#check @Erdos335.PeriodicRefinement.cumulative_limit_of_density
#print axioms Erdos335.PeriodicRefinement.cumulative_limit_of_density
#check @Erdos335.PeriodicRefinement.cumulative_value_of_ae_derivative
#print axioms Erdos335.PeriodicRefinement.cumulative_value_of_ae_derivative
#check @Erdos335.PeriodicRefinementMacroAssembly.MacroProfileData
#print axioms Erdos335.PeriodicRefinementMacroAssembly.MacroProfileData
#check @Erdos335.PeriodicRefinementMacroAssembly.MacroProfileData.endpoint
#print axioms Erdos335.PeriodicRefinementMacroAssembly.MacroProfileData.endpoint
#check @Erdos335.PeriodicRefinementMacroAssembly.cumulative_mask_at_one
#print axioms Erdos335.PeriodicRefinementMacroAssembly.cumulative_mask_at_one
#check @Erdos335.PeriodicRefinementMacroAssembly.MacroProfileData.left_endpoint_of_ae_indicator
#print axioms Erdos335.PeriodicRefinementMacroAssembly.MacroProfileData.left_endpoint_of_ae_indicator
#check @Erdos335.PeriodicRefinementMacroAssembly.MacroProfileData.right_endpoint_of_ae_indicator
#print axioms Erdos335.PeriodicRefinementMacroAssembly.MacroProfileData.right_endpoint_of_ae_indicator
#check @Erdos335.PeriodicRefinementMacroAssembly.MacroProfileData.endpoint_mem_slice_of_ae_label
#print axioms Erdos335.PeriodicRefinementMacroAssembly.MacroProfileData.endpoint_mem_slice_of_ae_label
#check @Erdos335.PeriodicRefinementMacroAssembly.MacroProfileData.exists_endpoint_slice
#print axioms Erdos335.PeriodicRefinementMacroAssembly.MacroProfileData.exists_endpoint_slice
#check @Erdos335.PeriodicRefinementMacroAssembly.exists_single_prefix_cluster_slice
#print axioms Erdos335.PeriodicRefinementMacroAssembly.exists_single_prefix_cluster_slice
#check @Erdos335.PeriodicRefinementMacroAssembly.exists_periodic_coordinate_limit
#print axioms Erdos335.PeriodicRefinementMacroAssembly.exists_periodic_coordinate_limit
#check @Erdos335.PeriodicRefinementMacroAssembly.exists_periodic_coordinate_limit_of_cluster_profiles
#print axioms Erdos335.PeriodicRefinementMacroAssembly.exists_periodic_coordinate_limit_of_cluster_profiles
#check @Erdos335.PeriodicRefinementMacroAssembly.RawProfileValid
#print axioms Erdos335.PeriodicRefinementMacroAssembly.RawProfileValid
#check @Erdos335.PeriodicRefinementMacroAssembly.RawProfileValid.toLocalProfile
#print axioms Erdos335.PeriodicRefinementMacroAssembly.RawProfileValid.toLocalProfile
#check @Erdos335.PeriodicRefinementMacroAssembly.measurableSet_rawProfileValid
#print axioms Erdos335.PeriodicRefinementMacroAssembly.measurableSet_rawProfileValid
#check @Erdos335.PeriodicRefinementMacroAssembly.exists_totalized_profile
#print axioms Erdos335.PeriodicRefinementMacroAssembly.exists_totalized_profile
#check @Erdos335.PeriodicRefinementMacroAssembly.localProfile_ext
#print axioms Erdos335.PeriodicRefinementMacroAssembly.localProfile_ext
#check @Erdos335.PeriodicRefinementMacroAssembly.RawCrossInequality
#print axioms Erdos335.PeriodicRefinementMacroAssembly.RawCrossInequality
#check @Erdos335.PeriodicRefinementMacroAssembly.cross_of_ae_raw_coordinates
#print axioms Erdos335.PeriodicRefinementMacroAssembly.cross_of_ae_raw_coordinates
#check @Erdos335.PeriodicRefinementMacroAssembly.RawFramedAt
#print axioms Erdos335.PeriodicRefinementMacroAssembly.RawFramedAt
#check @Erdos335.PeriodicRefinementMacroAssembly.frames_of_ae_raw_coordinates
#print axioms Erdos335.PeriodicRefinementMacroAssembly.frames_of_ae_raw_coordinates
#check @Erdos335.PeriodicRefinementMacroAssembly.RawMacroProfileData
#print axioms Erdos335.PeriodicRefinementMacroAssembly.RawMacroProfileData
#check @Erdos335.PeriodicRefinementMacroAssembly.RawMacroProfileData.endpoint
#print axioms Erdos335.PeriodicRefinementMacroAssembly.RawMacroProfileData.endpoint
#check @Erdos335.PeriodicRefinementMacroAssembly.RawMacroProfileData.totalize
#print axioms Erdos335.PeriodicRefinementMacroAssembly.RawMacroProfileData.totalize
#check @Erdos335.PeriodicRefinementMacroAssembly.RawMacroProfileData.exists_endpoint_slice
#print axioms Erdos335.PeriodicRefinementMacroAssembly.RawMacroProfileData.exists_endpoint_slice
#check @Erdos335.PeriodicRefinementMacroAssembly.exists_periodic_coordinate_limit_of_raw_cluster_profiles
#print axioms Erdos335.PeriodicRefinementMacroAssembly.exists_periodic_coordinate_limit_of_raw_cluster_profiles
#check @Erdos335.PeriodicRefinement.literalResidue
#print axioms Erdos335.PeriodicRefinement.literalResidue
#check @Erdos335.PeriodicRefinement.normalizedResiduePrefix
#print axioms Erdos335.PeriodicRefinement.normalizedResiduePrefix
#check @Erdos335.PeriodicRefinement.literal_residue_prefix_sum
#print axioms Erdos335.PeriodicRefinement.literal_residue_prefix_sum
#check @Erdos335.PeriodicRefinement.normalized_residue_prefix_sum
#print axioms Erdos335.PeriodicRefinement.normalized_residue_prefix_sum
#check @Erdos335.PeriodicRefinement.normalized_residue_prefix_nonneg
#print axioms Erdos335.PeriodicRefinement.normalized_residue_prefix_nonneg
#check @Erdos335.PeriodicRefinement.normalized_residue_prefix_mono
#print axioms Erdos335.PeriodicRefinement.normalized_residue_prefix_mono
#check @Erdos335.PeriodicRefinement.pure_residue_hasDensity
#print axioms Erdos335.PeriodicRefinement.pure_residue_hasDensity
#check @Erdos335.PeriodicRefinement.normalized_residue_prefix_limit_bounds
#print axioms Erdos335.PeriodicRefinement.normalized_residue_prefix_limit_bounds
#check @Erdos335.PeriodicRefinement.normalized_residue_prefix_limit_zero
#print axioms Erdos335.PeriodicRefinement.normalized_residue_prefix_limit_zero
#check @Erdos335.PeriodicRefinement.normalized_residue_prefix_limit_mass
#print axioms Erdos335.PeriodicRefinement.normalized_residue_prefix_limit_mass
#check @Erdos335.PeriodicRefinement.prefixCount_translate_le
#print axioms Erdos335.PeriodicRefinement.prefixCount_translate_le
#check @Erdos335.PeriodicRefinement.fixed_translate_prefix_limit_le
#print axioms Erdos335.PeriodicRefinement.fixed_translate_prefix_limit_le
#check @Erdos335.PeriodicRefinement.literal_residue_prefix_limit_le
#print axioms Erdos335.PeriodicRefinement.literal_residue_prefix_limit_le
#check @Erdos335.PeriodicRefinement.localProfile_of_residue_prefix_limits
#print axioms Erdos335.PeriodicRefinement.localProfile_of_residue_prefix_limits
#check @Erdos335.PeriodicRefinement.macroStart
#print axioms Erdos335.PeriodicRefinement.macroStart
#check @Erdos335.PeriodicRefinement.selected_length_ratio_of_gap
#print axioms Erdos335.PeriodicRefinement.selected_length_ratio_of_gap
#check @Erdos335.PeriodicRefinement.ScheduledMacroWindow
#print axioms Erdos335.PeriodicRefinement.ScheduledMacroWindow
#check @Erdos335.PeriodicRefinement.MacroWindowSequence
#print axioms Erdos335.PeriodicRefinement.MacroWindowSequence
#check @Erdos335.PeriodicRefinement.MacroWindowSequence.endpoint_prefix_tendsto
#print axioms Erdos335.PeriodicRefinement.MacroWindowSequence.endpoint_prefix_tendsto
#check @Erdos335.PeriodicRefinement.lipschitz_const_mul_unit
#print axioms Erdos335.PeriodicRefinement.lipschitz_const_mul_unit
#check @Erdos335.PeriodicRefinement.macroWindowSequence_rawData
#print axioms Erdos335.PeriodicRefinement.macroWindowSequence_rawData
#check @Erdos335.PeriodicRefinement.pairedModelIndex
#print axioms Erdos335.PeriodicRefinement.pairedModelIndex
#check @Erdos335.PeriodicRefinement.paired_model_enlargement
#print axioms Erdos335.PeriodicRefinement.paired_model_enlargement
#check @Erdos335.PeriodicRefinement.paired_model_moving
#print axioms Erdos335.PeriodicRefinement.paired_model_moving
#check @Erdos335.PeriodicRefinement.paired_model_other
#print axioms Erdos335.PeriodicRefinement.paired_model_other
#check @Erdos335.PeriodicRefinement.PreparedMacroScales.exists_window_sequence
#print axioms Erdos335.PeriodicRefinement.PreparedMacroScales.exists_window_sequence
#check @Erdos335.PeriodicRefinement.residuePrefixPair
#print axioms Erdos335.PeriodicRefinement.residuePrefixPair
#check @Erdos335.PeriodicRefinement.prefixProfileCompact
#print axioms Erdos335.PeriodicRefinement.prefixProfileCompact
#check @Erdos335.PeriodicRefinement.normalized_residue_prefix_bound
#print axioms Erdos335.PeriodicRefinement.normalized_residue_prefix_bound
#check @Erdos335.PeriodicRefinement.isCompact_prefixProfileCompact
#print axioms Erdos335.PeriodicRefinement.isCompact_prefixProfileCompact
#check @Erdos335.PeriodicRefinement.residuePrefixPair_mem_compact
#print axioms Erdos335.PeriodicRefinement.residuePrefixPair_mem_compact
#check @Erdos335.PeriodicRefinement.exists_localProfile_extending_prefix_limits
#print axioms Erdos335.PeriodicRefinement.exists_localProfile_extending_prefix_limits
#check @Erdos335.PeriodicRefinement.normalized_residue_prefix_step
#print axioms Erdos335.PeriodicRefinement.normalized_residue_prefix_step
#check @Erdos335.PeriodicRefinement.normalized_residue_vector_step
#print axioms Erdos335.PeriodicRefinement.normalized_residue_vector_step
#check @Erdos335.PeriodicRefinement.residuePrefixPair_step
#print axioms Erdos335.PeriodicRefinement.residuePrefixPair_step
#check @Erdos335.PeriodicRefinement.prefix_pair_cluster_localProfile
#print axioms Erdos335.PeriodicRefinement.prefix_pair_cluster_localProfile
#check @Erdos335.Proposed.residueSumIntervals
#print axioms Erdos335.Proposed.residueSumIntervals
#check @Erdos335.Proposed.ResidueSumPacking
#print axioms Erdos335.Proposed.ResidueSumPacking
#check @Erdos335.Proposed.mem_residue_sum_intervals_iff
#print axioms Erdos335.Proposed.mem_residue_sum_intervals_iff
#check @Erdos335.Proposed.residue_sum_intervals_bounds
#print axioms Erdos335.Proposed.residue_sum_intervals_bounds
#check @Erdos335.Proposed.residue_sum_intervals_eq_image
#print axioms Erdos335.Proposed.residue_sum_intervals_eq_image
#check @Erdos335.Proposed.residue_sum_intervals_card
#print axioms Erdos335.Proposed.residue_sum_intervals_card
#check @Erdos335.Proposed.residue_sum_packing_at_iff
#print axioms Erdos335.Proposed.residue_sum_packing_at_iff
#check @Erdos335.Proposed.residue_sum_packing_comm
#print axioms Erdos335.Proposed.residue_sum_packing_comm
#check @Erdos335.Proposed.residue_sum_packing_iff
#print axioms Erdos335.Proposed.residue_sum_packing_iff
#check @Erdos335.Proposed.sparse_shift_zero
#print axioms Erdos335.Proposed.sparse_shift_zero
#check @Erdos335.Proposed.sparse_period_add
#print axioms Erdos335.Proposed.sparse_period_add
#check @Erdos335.Proposed.sparse_period_mul
#print axioms Erdos335.Proposed.sparse_period_mul
#check @Erdos335.Proposed.sparse_period_setGcd
#print axioms Erdos335.Proposed.sparse_period_setGcd
#check @Erdos335.Proposed.sparse_subset_sum
#print axioms Erdos335.Proposed.sparse_subset_sum
#check @Erdos335.Proposed.sparse_sum_density_iff_negligible
#print axioms Erdos335.Proposed.sparse_sum_density_iff_negligible
#check @Erdos335.Proposed.sparse_sum_periods
#print axioms Erdos335.Proposed.sparse_sum_periods
#check @Erdos335.Proposed.sparse_sum_setGcd_period
#print axioms Erdos335.Proposed.sparse_sum_setGcd_period
#check @Erdos335.Proposed.sparse_finite_sum_density_of_setGcd_period
#print axioms Erdos335.Proposed.sparse_finite_sum_density_of_setGcd_period
#check @Erdos335.Proposed.sparse_finite_sum_density_iff_setGcd_period
#print axioms Erdos335.Proposed.sparse_finite_sum_density_iff_setGcd_period
#check @Erdos335.Proposed.sparse_minimum_exists
#print axioms Erdos335.Proposed.sparse_minimum_exists
#check @Erdos335.Proposed.sparse_normalized_zero
#print axioms Erdos335.Proposed.sparse_normalized_zero
#check @Erdos335.Proposed.sparse_restore_minimum
#print axioms Erdos335.Proposed.sparse_restore_minimum
#check @Erdos335.Proposed.sparse_normalized_sum
#print axioms Erdos335.Proposed.sparse_normalized_sum
#check @Erdos335.Proposed.sparse_normalized_density_iff
#print axioms Erdos335.Proposed.sparse_normalized_density_iff
#check @Erdos335.Proposed.sparse_normalized_finite
#print axioms Erdos335.Proposed.sparse_normalized_finite
#check @Erdos335.Proposed.sparse_normalized_setGcd_pos
#print axioms Erdos335.Proposed.sparse_normalized_setGcd_pos
#check @Erdos335.Proposed.sparseEscapingIntervals
#print axioms Erdos335.Proposed.sparseEscapingIntervals
#check @Erdos335.Proposed.SparseEscapePacking
#print axioms Erdos335.Proposed.SparseEscapePacking
#check @Erdos335.Proposed.mem_sparse_escaping_intervals_iff
#print axioms Erdos335.Proposed.mem_sparse_escaping_intervals_iff
#check @Erdos335.Proposed.sparse_escaping_intervals_bounds
#print axioms Erdos335.Proposed.sparse_escaping_intervals_bounds
#check @Erdos335.Proposed.sparse_escaping_intervals_eq_image
#print axioms Erdos335.Proposed.sparse_escaping_intervals_eq_image
#check @Erdos335.Proposed.sparse_escaping_intervals_card
#print axioms Erdos335.Proposed.sparse_escaping_intervals_card
#check @Erdos335.Proposed.sparse_escape_packing_iff
#print axioms Erdos335.Proposed.sparse_escape_packing_iff
#check @Erdos335.Proposed.negligible_iff_zero_sections
#print axioms Erdos335.Proposed.negligible_iff_zero_sections
#check @Erdos335.Proposed.zero_section_sum_of_multiples
#print axioms Erdos335.Proposed.zero_section_sum_of_multiples
#check @Erdos335.Proposed.zero_section_sdiff
#print axioms Erdos335.Proposed.zero_section_sdiff
#check @Erdos335.Proposed.SparseResiduePacking
#print axioms Erdos335.Proposed.SparseResiduePacking
#check @Erdos335.Proposed.sparse_residue_packing_iff
#print axioms Erdos335.Proposed.sparse_residue_packing_iff
#check @Erdos335.Proposed.SparseTerminalCondition
#print axioms Erdos335.Proposed.SparseTerminalCondition
#check @Erdos335.Proposed.sparse_terminal_of_sum_density
#print axioms Erdos335.Proposed.sparse_terminal_of_sum_density
#check @Erdos335.Proposed.SparseTerminalCondition.hasDensity
#print axioms Erdos335.Proposed.SparseTerminalCondition.hasDensity
#check @Erdos335.Proposed.sparse_terminal_iff_sum_density
#print axioms Erdos335.Proposed.sparse_terminal_iff_sum_density
#check @Erdos335.Proposed.SparseSectionBranch
#print axioms Erdos335.Proposed.SparseSectionBranch
#check @Erdos335.Proposed.sparse_section_nonempty
#print axioms Erdos335.Proposed.sparse_section_nonempty
#check @Erdos335.Proposed.SparseSectionBranch.swap
#print axioms Erdos335.Proposed.SparseSectionBranch.swap
#check @Erdos335.Proposed.FiniteFrame.null_left_periodic_input
#print axioms Erdos335.Proposed.FiniteFrame.null_left_periodic_input
#check @Erdos335.Proposed.SparseSectionBranch.periodic_input
#print axioms Erdos335.Proposed.SparseSectionBranch.periodic_input
#check @Erdos335.Proposed.FiniteFrame.null_left_sum_iff_sparse_terminal
#print axioms Erdos335.Proposed.FiniteFrame.null_left_sum_iff_sparse_terminal
#check @Erdos335.Proposed.SparseSectionBranch.hasDensity
#print axioms Erdos335.Proposed.SparseSectionBranch.hasDensity
#check @Erdos335.Proposed.FiniteFrame.null_left_sparse_branch
#print axioms Erdos335.Proposed.FiniteFrame.null_left_sparse_branch
#check @Erdos335.Proposed.sparse_branch_of_strict_periodic_summand
#print axioms Erdos335.Proposed.sparse_branch_of_strict_periodic_summand
#check @Erdos335.Proposed.TwoTemplateBranch
#print axioms Erdos335.Proposed.TwoTemplateBranch
#check @Erdos335.Proposed.two_template_baseline_swap
#print axioms Erdos335.Proposed.two_template_baseline_swap
#check @Erdos335.Proposed.TwoTemplateBranch.swap
#print axioms Erdos335.Proposed.TwoTemplateBranch.swap
#check @Erdos335.Proposed.TwoTemplateBranch.hasDensity
#print axioms Erdos335.Proposed.TwoTemplateBranch.hasDensity
#check @Erdos335.Proposed.two_template_branch_of_periodic_inputs
#print axioms Erdos335.Proposed.two_template_branch_of_periodic_inputs
#check @Erdos335.Proposed.two_template_branch_of_saturated_periodic_summand
#print axioms Erdos335.Proposed.two_template_branch_of_saturated_periodic_summand
#check @Erdos335.Proposed.periodic_summand_refinement_iff
#print axioms Erdos335.Proposed.periodic_summand_refinement_iff
#check @Erdos335.Proposed.periodic_summand_refinement_iff_of_either
#print axioms Erdos335.Proposed.periodic_summand_refinement_iff_of_either
#check @Erdos335.Proposed.PeriodicRefinedClassified
#print axioms Erdos335.Proposed.PeriodicRefinedClassified
#check @Erdos335.Proposed.PeriodicRefinedSolution
#print axioms Erdos335.Proposed.PeriodicRefinedSolution
#check @Erdos335.Proposed.PeriodicRefinedClassified.hasDensity
#print axioms Erdos335.Proposed.PeriodicRefinedClassified.hasDensity
#check @Erdos335.Proposed.HasPeriodicSummand
#print axioms Erdos335.Proposed.HasPeriodicSummand
#check @Erdos335.Proposed.HasPeriodicSummand.swap
#print axioms Erdos335.Proposed.HasPeriodicSummand.swap
#check @Erdos335.Proposed.LowPeriodicSummandNecessity
#print axioms Erdos335.Proposed.LowPeriodicSummandNecessity
#check @Erdos335.Proposed.refined_classified_of_periodic_summand
#print axioms Erdos335.Proposed.refined_classified_of_periodic_summand
#check @Erdos335.Proposed.refined_classified_of_regular_capacity
#print axioms Erdos335.Proposed.refined_classified_of_regular_capacity
#check @Erdos335.Proposed.periodicRefinedSolution_of_low_periodic_summand
#print axioms Erdos335.Proposed.periodicRefinedSolution_of_low_periodic_summand
#check @Erdos335.PeriodicRefinement.negligible_of_zero_residue_prefix_limits
#print axioms Erdos335.PeriodicRefinement.negligible_of_zero_residue_prefix_limits
#check @Erdos335.PeriodicRefinement.periodic_of_residue_prefix_mask
#print axioms Erdos335.PeriodicRefinement.periodic_of_residue_prefix_mask
#check @Erdos335.PeriodicRefinement.raw_macro_profile_at_prefix_cluster
#print axioms Erdos335.PeriodicRefinement.raw_macro_profile_at_prefix_cluster
#check @Erdos335.Proposed.low_periodic_summand_necessity
#print axioms Erdos335.Proposed.low_periodic_summand_necessity
#check @Erdos335.Proposed.full_periodic_classification
#print axioms Erdos335.Proposed.full_periodic_classification
#check @Erdos335.Proposed.full_periodic_classification_original_positive_counts
#print axioms Erdos335.Proposed.full_periodic_classification_original_positive_counts
