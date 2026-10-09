import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OpenCore

set_option autoImplicit false

/-!
Scoped HG16 acceptance check. Run with the lakefile options using
`lake build DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OpenCoreAxioms`
or the repository's single-module helper after building its dependencies.
The public declarations below must have no axioms beyond `propext`,
`Classical.choice`, and `Quot.sound`.
-/

namespace GC.LongTime.Ch12

#check openCoreDiffeo_CX1
#check hyperbolicInteriorGeometry_of_truncation_CX1
#print axioms pieceInteriorTopDiffeo_CX1
#print axioms truncationInteriorDiffeo_CX1
#print axioms truncationInteriorMetric_CX1
#print axioms truncationInteriorMetric_properties_CX1
#print axioms truncationInteriorGeometry_CX1
#print axioms hyperbolicInteriorGeometry_of_truncation_CX1
#print axioms hyperbolicAlternative_of_truncation_CX1
#print axioms endChart_unique_CX1
#print axioms globalCompression_CX1
#print axioms globalCompression_on_CX1
#print axioms globalCompression_off_CX1
#print axioms globalCompression_fixed_CX1
#print axioms globalCompression_local_CX1
#print axioms globalCompression_mem_target_CX1
#print axioms globalCompression_injective_CX1
#print axioms globalCompression_core_CX1
#print axioms globalCompression_surjective_core_CX1
#print axioms openCoreImage_CX1
#print axioms compressionDiffeo_CX1
#print axioms coreInclusionDiffeo_CX1
#print axioms openCoreDiffeo_CX1
#print axioms openCoreDiffeo_eq_inclusion_CX1
#print axioms openCoreDiffeo_eq_inclusion_of_count_zero_CX1
#print axioms halfIntervalLift_CX1
#print axioms halfIntervalLift_height_CX1
#print axioms halfIntervalLift_smooth_CX1
#print axioms halfIntervalLift_injective_mfderiv_CX1
#print axioms exists_cusp_bicollar_CX1
#print axioms compressPair_CX1
#print axioms compressPair_source_CX1
#print axioms compressPair_injective_CX1
#print axioms compressPair_local_CX1
#print axioms endCompression_CX1
#print axioms endCompression_on_CX1
#print axioms endCompression_off_CX1
#print axioms endCompression_target_CX1
#print axioms endCompression_core_CX1
#print axioms endCompression_fixed_CX1
#print axioms endCompression_local_CX1
#print axioms endCompression_injective_CX1
#print axioms endCompression_surjective_core_CX1
#print axioms cusp_range_subset_chart_CX1
#print axioms realCuspChart_CX1
#print axioms realCuspChart_apply_CX1
#print axioms realCuspChart_mem_source_CX1
#print axioms extendedCuspMap_CX1
#print axioms extendedCuspMap_eq_collar_CX1
#print axioms extendedCuspMap_eq_cusp_CX1
#print axioms extendedCuspMap_local_CX1
#print axioms extendedCuspMap_negative_CX1
#print axioms extendedCuspMap_injective_CX1
#print axioms CuspEndChart_CX1
#print axioms exists_cuspEndChart_CX1
#print axioms cuspEndChart_CX1
#print axioms hyperbolicInteriorGeometry_of_diffeomorph_CX1
#print axioms hyperbolicAlternative_of_diffeomorph_CX1
#print axioms hyperbolicMetric_pullback_CX1
#print axioms endNeighborhood_CX1
#print axioms endNeighborhood_open_CX1
#print axioms cusp_subset_endNeighborhood_CX1
#print axioms endNeighborhood_subset_CX1
#print axioms endNeighborhood_disjoint_CX1
#print axioms exists_small_bicollar_CX1
#print axioms mem_openCoreImage_iff_CX1
#print axioms exists_core_cusp_bicollar_CX1
#print axioms exists_negative_stretch_CX1
#print axioms negativeStretch_CX1
#print axioms compressHeight_CX1
#print axioms compressHeight_lt_zero_CX1
#print axioms compressHeight_lower_CX1
#print axioms compressHeight_fixed_CX1
#print axioms compressHeight_injective_CX1
#print axioms compressHeight_local_CX1
#print axioms compressHeight_surjective_negative_CX1

end GC.LongTime.Ch12
