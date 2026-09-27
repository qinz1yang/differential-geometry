import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PullbackCurvatureDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedPullbackExtensions
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullback


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
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

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem eventually_curvDerivNorm_gSeqExt_eq
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {K : Set P.M} (hK : IsCompact K) :
    ∀ᶠ i in atTop, ∀ t : ℝ, ∀ j : ℕ, ∀ x ∈ K,
      curvDerivNorm j (gSeqExt Φ R bf hsrc htgt i t) x =
        curvDerivNorm j ((X.term (subseq i)).S.base.metric t) (Φ.map i x) := by
  filter_upwards [eventually_gSeqExt_eq_pullback Φ R bf hsrc htgt K hK] with i hi
  obtain ⟨U, hU, hKU, hUΦ, hmetric⟩ := hi
  intro t j x hx
  have heq := curvDerivNorm_eq_of_local_pullback
    (gSeqExt Φ R bf hsrc htgt i t) ((X.term (subseq i)).S.base.metric t)
    (Φ.partialDiffeomorph i) ⟨U, hU⟩ hUΦ (hmetric t) j ⟨x, hKU hx⟩
  exact heq

theorem FlowMetricConvergenceData.exists_eventually_curvDerivNorm_bound
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {a b : ℝ} (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt a b)
    (hG : MetricFamilySmoothOn X.D co.gInf)
    (hreg : Icc a b ⊆ X.D.regular) (hboundary : BoundarylessManifold I P.M)
    {K : Set P.M} (hK : IsCompact K) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ k ≥ N, ∀ t ∈ Icc a b, ∀ x ∈ K,
      curvDerivNorm j (gSeqExt Φ R bf hsrc htgt (co.φ k) t) x ≤ C := by
  obtain ⟨C, hC, N, hbound⟩ :=
    FlowMetricConvergenceData.exists_eventually_intrinsic_curvature_derivative_bound
      Φ R bf hsrc htgt co hG hreg hboundary hK j
  refine ⟨C, hC, N, ?_⟩
  intro k hk t ht x hx
  rw [curvDerivNorm, curvDerivNormSq, curvCovDeriv_normSq_eq]
  exact hbound k hk t ht x hx

theorem FlowMetricConvergenceData.exists_eventually_source_curvDerivNorm_bound
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {a b : ℝ} (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt a b)
    (hG : MetricFamilySmoothOn X.D co.gInf)
    (hreg : Icc a b ⊆ X.D.regular) (hboundary : BoundarylessManifold I P.M)
    {K : Set P.M} (hK : IsCompact K) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ k ≥ N, ∀ t ∈ Icc a b, ∀ x ∈ K,
      curvDerivNorm j ((X.term (subseq (co.φ k))).S.base.metric t)
        (Φ.map (co.φ k) x) ≤ C := by
  obtain ⟨C, hC, N₁, hbound⟩ :=
    FlowMetricConvergenceData.exists_eventually_curvDerivNorm_bound
      Φ R bf hsrc htgt co hG hreg hboundary hK j
  have heq := co.strictMono.tendsto_atTop.eventually
    (eventually_curvDerivNorm_gSeqExt_eq Φ R bf hsrc htgt hK)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 heq
  refine ⟨C, hC, max N₁ N₂, ?_⟩
  intro k hk t ht x hx
  have hk₁ : N₁ ≤ k := (le_max_left _ _).trans hk
  have hk₂ : N₂ ≤ k := (le_max_right _ _).trans hk
  rw [← hN₂ k hk₂ t j x hx]
  exact hbound k hk₁ t ht x hx

end DifferentialGeometry.CheegerGromovCompactness
