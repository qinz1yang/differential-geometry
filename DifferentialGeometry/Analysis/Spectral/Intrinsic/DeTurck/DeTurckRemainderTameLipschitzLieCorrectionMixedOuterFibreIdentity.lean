import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionMixedLiftedFibreIdentity
open DifferentialGeometry.Analysis.Spectral


noncomputable section

open Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open LieCorr0Core
open DifferentialGeometry
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
lemma lc0AMixOuterField_toSection (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) :
    (lc0AMixOuterField (I := I) (M := M) g₀ g₁ g_bg).toSection x =
      (show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 4 I x from
        (lc0Tr (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1).toSection x).comp
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (lc0AMixLiftedField (I := I) (M := M) g₀ g₁ g_bg).toSection x) :=
  appCcRS_toSection (I := I) (M := M) g₀ 2 6 4
    (lc0Tr (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1)
    (lc0AMixLiftedField (I := I) (M := M) g₀ g₁ g_bg) x

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma lc0b_amix_outer_fiber (g₀ g₁ g_bg : SmoothRiemannianMetric I M)
    (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
      (lc0AMixOuterField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D =
    lieCorr0TraceStep (I := I) g₁ 4 lieCorr0AMixPerm1 x
      ((tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
        (metricConnDiffLoweredFib (I := I) g₁ g₁ g_bg x))
        (lieCorr0TraceStep (I := I) g₁ 3 lieCorr0AMixPermQ x
          ((tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
            (metricConnDiffLoweredFib (I := I) g₁ g₁ g₀ x)) D))) := by
  rw [lc0AMixOuterField_toSection (I := I) (M := M) g₀ g₁ g_bg x,
    ContinuousLinearMap.comp_apply]
  rw [lc0b_amix_middle_fiber (I := I) (M := M) g₀ g₁ g_bg x D]
  exact lc0Tr_fiber_apply (I := I) (M := M) g₀ g₁ 4 lieCorr0AMixPerm1 x _

end DifferentialGeometry.Analysis.Spectral

end
