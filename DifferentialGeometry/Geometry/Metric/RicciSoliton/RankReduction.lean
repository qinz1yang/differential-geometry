import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankReduction
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CompactAnisotropy
import DifferentialGeometry.Geometry.Metric.RicciSoliton.GaussianModelCover
import DifferentialGeometry.Geometry.Metric.RicciSoliton.GaussianRigidity
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverCurvatureRank

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature
open Curvature.DimensionThree

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

theorem normalizedGradientRicciSoliton_metricCurvatureOperatorRankAt_eq_zero_or_one_or_three_of_compact_of_finrank_eq_three_of_nonnegative_of_not_isGaussian
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 3)
    (hnot : ¬ isGaussianGradientRicciSoliton (E := E) g f 1)
    (hcone : ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∀ x : M,
      metricCurvatureOperatorRankAt (I := I) g x (by
        rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
        exact hdim) = 0 ∨
        metricCurvatureOperatorRankAt (I := I) g x (by
          rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
          exact hdim) = 1 ∨
      metricCurvatureOperatorRankAt (I := I) g x (by
          rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
          exact hdim) = 3 := by
  let _ : NeZero (Module.finrank Real E) := ⟨by
    rw [hdim]
    norm_num⟩
  have hscalar : ∀ y : M, 0 < metricScalarAt (I := I) (M := M) g y := by
    intro y
    exact normalizedGradientRicciSoliton_scalar_pos_of_not_isGaussian
      (I := I) h hnot y
  have hdefect : ∀ x : M, ricciReactionDefectAt (I := I) g x = 0 :=
    gradientRicciSoliton_ricciReactionDefectAt_eq_zero_of_compact_of_finrank_eq_three
      (I := I) (M := M) h.2.1 hscalar hdim
  intro x
  exact metricCurvatureOperatorRankAt_eq_zero_or_one_or_three_of_nonnegative_of_ricciReactionDefectAt_eq_zero
    (I := I) (M := M) g x
      (by
        rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
        exact hdim)
      (hcone x) (hdefect x)

theorem normalizedGradientRicciSoliton_metricCurvatureOperatorRankAt_eq_one_or_three_of_compact_of_finrank_eq_three_of_nonnegative_of_not_isGaussian
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 3)
    (hnot : ¬ isGaussianGradientRicciSoliton (E := E) g f 1)
    (hcone : ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∀ x : M,
      metricCurvatureOperatorRankAt (I := I) g x (by
        rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
        exact hdim) = 1 ∨
      metricCurvatureOperatorRankAt (I := I) g x (by
        rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
        exact hdim) = 3 := by
  let _ : NeZero (Module.finrank Real E) := ⟨by
    rw [hdim]
    norm_num⟩
  intro x
  rcases normalizedGradientRicciSoliton_metricCurvatureOperatorRankAt_eq_zero_or_one_or_three_of_compact_of_finrank_eq_three_of_nonnegative_of_not_isGaussian
      (I := I) (M := M) h hdim hnot hcone x with hzero | hone | hthree
  · exact False.elim (hnot
      (normalizedGradientRicciSoliton_isGaussian_of_curvatureOperatorRankAt_eq_zero
        (I := I) (M := M) h hdim x hzero))
  · exact Or.inl hone
  · exact Or.inr hthree

theorem normalizedGradientRicciSoliton_metricCurvatureOperatorRankAt_eq_zero_of_isGaussian
    [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 3)
    (hGaussian : isGaussianGradientRicciSoliton (E := E) g f 1) :
    ∀ x : M,
      metricCurvatureOperatorRankAt (I := I) g x (by
        rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
        exact hdim) = 0 := by
  let _ : NeZero (Module.finrank Real E) := ⟨by
    rw [hdim]
    norm_num⟩
  obtain ⟨cover, hcover⟩ :=
    exists_solitonModelCovering_of_isGaussianGradientRicciSoliton
      (I := I) h hGaussian
  intro y
  obtain ⟨x, hxy⟩ := solitonModelCovering_surjective hcover y
  have hrank := solitonModelCovering_metricCurvatureOperatorRankAt_eq
    (I := I) (J := modelWithCornersSelf Real E)
    (N := E) hcover x (by
      change Module.finrank Real E = 3
      exact hdim)
  have hsource := euclideanMetric_curvatureOperatorRankAt x hdim
  rw [hxy] at hrank
  rw [← hrank]
  exact hsource

end DifferentialGeometry.Geometry
