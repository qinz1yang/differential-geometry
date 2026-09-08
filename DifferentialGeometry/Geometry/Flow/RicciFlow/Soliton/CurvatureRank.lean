import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankScaling
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankNaturality
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureRank
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.Complete
import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Solution

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

namespace DifferentialGeometry.PDE.RicciFlow.Soliton

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree

theorem canonicalMetric_metricCurvatureOperatorRankAt
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    (sigma : ℝ) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : ℝ} (ht : t ∈ canonicalTimeDomain sigma) (x : M)
    (hdim : Module.finrank ℝ E = 3) :
    metricCurvatureOperatorRankAt
        (canonicalMetric g f sigma hcomplete hsol ht) x hdim =
      metricCurvatureOperatorRankAt g
        (canonicalFlowDiffeomorph g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) x) hdim := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Φ := canonicalFlowDiffeomorph g f sigma hcomplete hsol
    (canonicalFlowParameter sigma t)
  have hdim' (y : M) : Module.finrank ℝ (TangentSpace I y) = 3 := by
    rw [show Module.finrank ℝ (TangentSpace I y) = Module.finrank ℝ E from rfl]
    exact hdim
  rw [canonicalMetric, ← Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    Diffeomorph.pullbackMetricCross_eq_localPullMetric,
    metricCurvatureOperatorRankAt_localPull _ _ _ _ (hdim' x) (hdim' (Φ x)),
    metricCurvatureOperatorRankAt_scaleMetric _ _ _ _ (hdim' (Φ x))]

end DifferentialGeometry.PDE.RicciFlow.Soliton

namespace DifferentialGeometry.Geometry

open Curvature Curvature.DimensionThree
open DifferentialGeometry.PDE.RicciFlow
  (IsSolutionOn curvatureOperator_nonnegative_of_complete_ancient
    curvatureOperatorImageAt_finrank_eq_at_later_time)
open DifferentialGeometry.PDE.RicciFlow.Soliton
  (canonicalTimeDomain canonicalSolutionOn canonicalSolutionOn_metric_zero
    canonicalSolutionOn_isSolutionOn canonicalSolutionOn_complete)

theorem gradientRicciSoliton_curvatureOperatorImageAt_finrank_eq
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) {σ : ℝ} (hσ : 0 ≤ σ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    (x y : M) :
    Module.finrank ℝ (curvatureOperatorImageAt g x
      ⟨metricRm04At g x, metricRm04At_mem_algebraicCurvatureTensorSubmodule g x⟩) =
      Module.finrank ℝ (curvatureOperatorImageAt g y
        ⟨metricRm04At g y, metricRm04At_mem_algebraicCurvatureTensorSubmodule g y⟩) := by
  let b : ℝ := (σ + 1)⁻¹
  have hden : 0 < σ + 1 := by linarith
  have hb : 0 < b := inv_pos.mpr hden
  have hσb : σ * b < 1 := by
    have hdiv : σ * b = σ / (σ + 1) := by
      dsimp [b]
      rw [div_eq_mul_inv]
    rw [hdiv]
    exact (div_lt_iff₀ hden).2 (by linarith)
  let D := RealTimeInterval.infiniteOpen b 0 hb
  have hD : D.carrier ⊆ canonicalTimeDomain σ := by
    intro t ht
    change 0 < 1 - σ * t
    have ht' : t < b := ht
    have hmul : σ * t ≤ σ * b := mul_le_mul_of_nonneg_left ht'.le hσ
    linarith
  let S := canonicalSolutionOn (I := I) g f σ hcomplete hsol D
  have hS : IsSolutionOn S := canonicalSolutionOn_isSolutionOn g f σ hcomplete hsol D hD
  have hreg : Icc (-1 : ℝ) 0 ⊆ D.regular := by
    intro t ht
    change t < b
    exact ht.2.trans_lt hb
  have hR : ∀ r ∈ Icc (-1 : ℝ) 0, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
    intro r hr x
    exact curvatureOperator_nonnegative_of_complete_ancient S hS
      (fun t ht => ht.trans_lt (hr.2.trans_lt hb))
      (fun t ht => ht.trans (hr.2.trans_lt hb))
      (fun t ht => canonicalSolutionOn_complete g f σ hcomplete hsol D hD
        (ht.trans_lt (hr.2.trans_lt hb))) hdim x
  have heq := curvatureOperatorImageAt_finrank_eq_at_later_time S hS hdim
    (show (-1 : ℝ) < 0 by norm_num) hreg hR x y
  have hzero : S.family.metric 0 = g := by
    exact canonicalSolutionOn_metric_zero g f σ hcomplete hsol D
  rw [hzero] at heq
  exact heq

theorem gradientRicciSoliton_metricCurvatureOperatorRankAt_eq
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) {σ : ℝ} (hσ : 0 ≤ σ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    (x y : M) :
    DimensionThree.metricCurvatureOperatorRankAt g x hdim =
      DimensionThree.metricCurvatureOperatorRankAt g y hdim := by
  rw [metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank g x hdim, metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank g y hdim]
  exact gradientRicciSoliton_curvatureOperatorImageAt_finrank_eq g f hσ hcomplete hsol hdim x y

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.PDE.RicciFlow.Soliton

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree

theorem canonicalMetric_metricCurvatureOperatorRankAt_eq_one_of_rank_one
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) {σ : ℝ} (hσ : 0 ≤ σ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    {x₀ : M} (hrank : DimensionThree.metricCurvatureOperatorRankAt g x₀ hdim = 1)
    {t : ℝ} (ht : t ∈ canonicalTimeDomain σ) (x : M) :
    DimensionThree.metricCurvatureOperatorRankAt
      (canonicalMetric g f σ hcomplete hsol ht) x hdim = 1 := by
  rw [canonicalMetric_metricCurvatureOperatorRankAt]
  exact (gradientRicciSoliton_metricCurvatureOperatorRankAt_eq g f hσ hcomplete hsol hdim _ x₀).trans hrank

theorem canonicalMetric_curvatureOperatorImageAt_finrank_eq_one_of_rank_one
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) {σ : ℝ} (hσ : 0 ≤ σ)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f σ) (hdim : Module.finrank ℝ E = 3)
    {x₀ : M} (hrank : DimensionThree.metricCurvatureOperatorRankAt g x₀ hdim = 1)
    {t : ℝ} (ht : t ∈ canonicalTimeDomain σ) (x : M) :
    Module.finrank ℝ (curvatureOperatorImageAt (canonicalMetric g f σ hcomplete hsol ht) x
      ⟨metricRm04At (canonicalMetric g f σ hcomplete hsol ht) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (canonicalMetric g f σ hcomplete hsol ht) x⟩) = 1 := by
  rw [← metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank]
  exact canonicalMetric_metricCurvatureOperatorRankAt_eq_one_of_rank_one
    g f hσ hcomplete hsol hdim hrank ht x

end DifferentialGeometry.PDE.RicciFlow.Soliton
