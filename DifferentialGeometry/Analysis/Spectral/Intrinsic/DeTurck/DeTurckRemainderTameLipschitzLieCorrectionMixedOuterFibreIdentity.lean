import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionMixedLiftedFibreIdentity
open DifferentialGeometry.Analysis.Spectral


noncomputable section

open Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open LieCorrectionZeroCore
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance instCompleteSpaceE_tame : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma lieCorrectionZeroMixedConnectionOuterField_toSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) :
    (lieCorrectionZeroMixedConnectionOuterField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 4 I x from
        (lieCorrectionZeroTr (I := I) (M := M) g₀ g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne).toSection x).comp
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (lieCorrectionZeroMixedConnectionLiftedField (I := I) (M := M) g₀ g₁ g_bg).toSection x) :=
  operatorFieldComposition_toSection (I := I) (M := M) g₀ 2 6 4
    (lieCorrectionZeroTr (I := I) (M := M) g₀ g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne)
    (lieCorrectionZeroMixedConnectionLiftedField (I := I) (M := M) g₀ g₁ g_bg) x

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma lieCorrectionZerob_amix_outer_fiber (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
      (lieCorrectionZeroMixedConnectionOuterField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D =
    lieCorrectionZeroTraceStep (I := I) g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne x
      ((tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
        (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g_bg x))
        (lieCorrectionZeroTraceStep (I := I) g₁ 3 lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour x
          ((tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
            (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)) D))) := by
  rw [lieCorrectionZeroMixedConnectionOuterField_toSection (I := I) (M := M) g₀ g₁ g_bg x,
    ContinuousLinearMap.comp_apply]
  rw [lieCorrectionZerob_amix_middle_fiber (I := I) (M := M) g₀ g₁ g_bg x D]
  exact lieCorrectionZeroTr_fiber_apply (I := I) (M := M) g₀ g₁ 4 lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne x _

end DifferentialGeometry.Analysis.Spectral

end
