import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Convergence
import DifferentialGeometry.Geometry.Metric.Convergence.Time.CompactBounds

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set
open Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ}

theorem FlowMetricConvergenceData.exists_eventually_metricCovDerivNorm_bound
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    {a b : ℝ} (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt a b)
    (hG : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      MetricFamilySmoothOn X.D co.gInf)
    (hreg : Icc a b ⊆ X.D.regular)
    {K : Set P.M} (hK : letI : TopologicalSpace P.M := P.topology; IsCompact K)
    (p : ℕ) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ k ≥ N, ∀ t ∈ Icc a b,
      ∀ q ≤ p, ∀ x ∈ K,
        metricCovDerivNorm q (gSeqExt Φ R bf hsrc htgt (co.φ k) t) R x ≤ C := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨C, hC, hbound⟩ :=
    exists_metricCovDerivNorm_bound_on_compact_regular co.gInf hG hreg R hK p
  obtain ⟨N, hN⟩ := co.convergencePt K hK p 1 zero_lt_one
  refine ⟨C + 1, by positivity, N, ?_⟩
  intro k hk t ht q hq x hx
  exact (covNorm_le_add q (gSeqExt Φ R bf hsrc htgt (co.φ k) t)
    (co.gInf t) R x).trans
      (add_le_add (hbound q hq t ht x hx) (hN k hk t ht q hq x hx).le)

end DifferentialGeometry.CheegerGromovCompactness
