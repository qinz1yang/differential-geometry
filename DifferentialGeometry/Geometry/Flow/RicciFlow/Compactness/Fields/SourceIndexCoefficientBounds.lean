import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.SourceCurvatureDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Curvature.IndexCoefficients


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {subseq : ℕ → ℕ}

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem FlowMetricConvergenceData.exists_eventually_source_index_norm_bounds_on_time_interval
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ)
    (htgt : TargetIsSigmaCompact Φ)
    {a b : ℝ} (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt a b)
    (hG : MetricFamilySmoothOn X.D co.gInf)
    (hreg : Icc a b ⊆ X.D.regular)
    (hboundary : BoundarylessManifold I P.M)
    {K : Set P.M} (hK : IsCompact K) :
    ∃ K₀ C N : ℝ, 0 < K₀ ∧ 0 ≤ C ∧ 0 ≤ N ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀,
      let S := (X.term (subseq (co.φ k))).S
      ∀ t ∈ Icc a b, ∀ x ∈ Φ.map (co.φ k) '' K,
        Real.sqrt (normSq0S (S.base.metric t) x 4
          (S.base.rm04 t x)) ≤ K₀ ∧
        Real.sqrt (normSq0S (S.base.metric t) x 2
          (hessianSec (I := I) (S.base.connection t)
            (metricCov_smooth (I := I) (S.base.metric t))
            (S.scalar t) (scalarSmoothOfSolution S t) x)) ≤ C ∧
        Real.sqrt (normSq0S (S.base.metric t) x 3
          (totalNabla0SFun (𝕜 := ℝ) (I := I) 2 (S.base.connection t)
            (S.ricci t) x)) ≤ N := by
  obtain ⟨B₀, hB₀, k₀, hzero⟩ :=
    FlowMetricConvergenceData.exists_eventually_source_curvDerivNorm_bound
      Φ R bf hsrc htgt co hG hreg hboundary hK 0
  obtain ⟨B₁, hB₁, k₁, hone⟩ :=
    FlowMetricConvergenceData.exists_eventually_source_curvDerivNorm_bound
      Φ R bf hsrc htgt co hG hreg hboundary hK 1
  obtain ⟨B₂, hB₂, k₂, htwo⟩ :=
    FlowMetricConvergenceData.exists_eventually_source_curvDerivNorm_bound
      Φ R bf hsrc htgt co hG hreg hboundary hK 2
  refine ⟨B₀, (Module.finrank ℝ E : ℝ) ^ 5 * B₂,
    Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) * B₁,
    hB₀, by positivity, by positivity, max k₀ (max k₁ k₂), ?_⟩
  intro k hk
  dsimp only
  intro t ht x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hk₀ : k₀ ≤ k := (le_max_left _ _).trans hk
  have hk₁ : k₁ ≤ k := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hk
  have hk₂ : k₂ ≤ k := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hk
  refine ⟨sqrt_rm04_le_of_curvDerivNorm _ _ _ B₀ (hzero k hk₀ t ht y hy), ?_, ?_⟩
  · exact sqrt_scalarHess_le_of_curvDerivNorm _ _ _ B₂ (htwo k hk₂ t ht y hy)
  · exact sqrt_nablaRicci_le_of_curvDerivNorm _ _ _ B₁ (hone k hk₁ t ht y hy)


theorem FlowMetricConvergenceData.exists_eventually_source_index_norm_bounds
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ)
    (htgt : TargetIsSigmaCompact Φ)
    (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt (-1) (-1 / 4))
    (hG : MetricFamilySmoothOn X.D co.gInf)
    (hreg : Icc (-1 : ℝ) (-1 / 4) ⊆ X.D.regular)
    (hboundary : BoundarylessManifold I P.M)
    {K : Set P.M} (hK : IsCompact K) :
    ∃ K₀ C N : ℝ, 0 < K₀ ∧ 0 ≤ C ∧ 0 ≤ N ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀,
      let S := (X.term (subseq (co.φ k))).S
      ∀ s ∈ Icc (1 / 2 : ℝ) 1, ∀ x ∈ Φ.map (co.φ k) '' K,
        Real.sqrt (normSq0S (S.base.metric (0 - s ^ 2)) x 4
          (S.base.rm04 (0 - s ^ 2) x)) ≤ K₀ ∧
        Real.sqrt (normSq0S (S.base.metric (0 - s ^ 2)) x 2
          (hessianSec (I := I) (S.base.connection (0 - s ^ 2))
            (metricCov_smooth (I := I) (S.base.metric (0 - s ^ 2)))
            (S.scalar (0 - s ^ 2)) (scalarSmoothOfSolution S (0 - s ^ 2)) x)) ≤ C ∧
        Real.sqrt (normSq0S (S.base.metric (0 - s ^ 2)) x 3
          (totalNabla0SFun (𝕜 := ℝ) (I := I) 2 (S.base.connection (0 - s ^ 2))
            (S.ricci (0 - s ^ 2)) x)) ≤ N := by
  obtain ⟨K₀, C, N, hK₀, hC, hN, k₀, hbound⟩ :=
    FlowMetricConvergenceData.exists_eventually_source_index_norm_bounds_on_time_interval
      Φ R bf hsrc htgt co hG hreg hboundary hK
  refine ⟨K₀, C, N, hK₀, hC, hN, k₀, ?_⟩
  intro k hk
  dsimp only
  intro s hs x hx
  have htime : 0 - s ^ 2 ∈ Icc (-1 : ℝ) (-1 / 4) := by
    have hs0 : 0 ≤ s := by linarith [hs.1]
    have hlow := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2) hs.1
    have hhigh := mul_self_le_mul_self hs0 hs.2
    constructor <;> nlinarith only [hlow, hhigh]
  exact hbound k hk (0 - s ^ 2) htime x hx

end DifferentialGeometry.CheegerGromovCompactness
