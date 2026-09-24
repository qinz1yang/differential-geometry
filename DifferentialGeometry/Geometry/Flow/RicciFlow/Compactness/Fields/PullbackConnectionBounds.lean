import DifferentialGeometry.Geometry.Connection.Convergence.ReferenceBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.DerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PullbackMetricEquivalence
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.CompactEquivalence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ}

theorem
  FlowMetricConvergenceData.exists_eventually_connection_difference_norm_bound_of_limit_equivalence
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
    {L : ℝ} (hL : 1 ≤ L)
    (hlimit : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      ∀ t ∈ Icc a b, MetricUniformEquivalentOn K R (co.gInf t) L) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, ∀ k ≥ N, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      ∀ x ∈ K, ∀ u w : TangentSpace I x,
        Real.sqrt ((gSeqExt Φ R bf hsrc htgt (co.φ k) s).inner x
          (CovariantDerivative.difference
            (metricCov (gSeqExt Φ R bf hsrc htgt (co.φ k) t))
            (metricCov (gSeqExt Φ R bf hsrc htgt (co.φ k) s)) x u w)
          (CovariantDerivative.difference
            (metricCov (gSeqExt Φ R bf hsrc htgt (co.φ k) t))
            (metricCov (gSeqExt Φ R bf hsrc htgt (co.φ k) s)) x u w)) ≤
          A * Real.sqrt ((gSeqExt Φ R bf hsrc htgt (co.φ k) s).inner x u u) *
            Real.sqrt ((gSeqExt Φ R bf hsrc htgt (co.φ k) s).inner x w w) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  obtain ⟨J, hJ, N₁, hN₁⟩ :=
    FlowMetricConvergenceData.exists_eventually_metricCovDerivNorm_bound
      Φ R bf hsrc htgt co hG hreg hK 1
  obtain ⟨N₂, hN₂⟩ :=
    FlowMetricConvergenceData.exists_eventually_metricUniformEquivalentOn
      Φ R bf hsrc htgt co hK hL hlimit
  let A : ℝ := Real.sqrt (2 * L) ^ 3 * (3 * (2 * L) ^ 3 * J)
  have hLp : 0 < 2 * L := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, max N₁ N₂, ?_⟩
  intro k hk s hs t ht x hx u w
  have hk₁ : N₁ ≤ k := (le_max_left _ _).trans hk
  have hk₂ : N₂ ≤ k := (le_max_right _ _).trans hk
  have hbound := connectionDifference_norm_le_of_reference_metric_bounds R
    (gSeqExt Φ R bf hsrc htgt (co.φ k) s)
    (gSeqExt Φ R bf hsrc htgt (co.φ k) t)
    (hN₂ k hk₂ s hs) (hN₂ k hk₂ t ht)
    (fun y hy ↦ hN₁ k hk₁ s hs 1 le_rfl y hy)
    (fun y hy ↦ hN₁ k hk₁ t ht 1 le_rfl y hy) hx u w
  refine hbound.trans_eq ?_
  dsimp [A]
  ring

theorem FlowMetricConvergenceData.exists_eventually_connection_difference_norm_bound
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
    {K : Set P.M} (hK : letI : TopologicalSpace P.M := P.topology; IsCompact K) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, ∀ k ≥ N, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      ∀ x ∈ K, ∀ u w : TangentSpace I x,
        Real.sqrt ((gSeqExt Φ R bf hsrc htgt (co.φ k) s).inner x
          (CovariantDerivative.difference
            (metricCov (gSeqExt Φ R bf hsrc htgt (co.φ k) t))
            (metricCov (gSeqExt Φ R bf hsrc htgt (co.φ k) s)) x u w)
          (CovariantDerivative.difference
            (metricCov (gSeqExt Φ R bf hsrc htgt (co.φ k) t))
            (metricCov (gSeqExt Φ R bf hsrc htgt (co.φ k) s)) x u w)) ≤
          A * Real.sqrt ((gSeqExt Φ R bf hsrc htgt (co.φ k) s).inner x u u) *
            Real.sqrt ((gSeqExt Φ R bf hsrc htgt (co.φ k) s).inner x w w) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  have hcarrier : Icc a b ⊆ X.D.carrier := fun _ ht => X.D.regular_subset (hreg ht)
  obtain ⟨L, hL, hlimit⟩ :=
    exists_metric_uniform_equivalent_on_compact_of_metricFamilySmoothOn
      co.gInf hG isCompact_Icc hcarrier hK R
  exact
  FlowMetricConvergenceData.exists_eventually_connection_difference_norm_bound_of_limit_equivalence
    Φ R bf hsrc htgt co hG hreg hK hL hlimit

end DifferentialGeometry.CheegerGromovCompactness
