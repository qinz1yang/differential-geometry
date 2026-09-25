import DifferentialGeometry.Geometry.Curvature.Bounds.MetricDerivatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.DerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PullbackMetricEquivalence
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.CompactEquivalence


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Set
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ}

theorem FlowMetricConvergenceData.exists_eventually_intrinsic_curvature_derivative_bound
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
    (hboundary : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      BoundarylessManifold I P.M)
    {K : Set P.M} (hK : letI : TopologicalSpace P.M := P.topology; IsCompact K)
    (j : ℕ) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ k ≥ N, ∀ t ∈ Icc a b, ∀ x ∈ K,
      Real.sqrt (normSq0S (gSeqExt Φ R bf hsrc htgt (co.φ k) t) x (4 + j)
        (iterCov (gSeqExt Φ R bf hsrc htgt (co.φ k) t) 4
          (metricRm04 (gSeqExt Φ R bf hsrc htgt (co.φ k) t)) j x)) ≤ C := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : BoundarylessManifold I P.M := hboundary
  obtain ⟨J, hJ, N₁, hN₁⟩ :=
    FlowMetricConvergenceData.exists_eventually_metricCovDerivNorm_bound
      Φ R bf hsrc htgt co hG hreg hK (j + 2)
  have hcarrier : Icc a b ⊆ X.D.carrier := fun _ ht => X.D.regular_subset (hreg ht)
  obtain ⟨L, hL, hlimit⟩ :=
    exists_metric_uniform_equivalent_on_compact_of_metricFamilySmoothOn
      co.gInf hG isCompact_Icc hcarrier hK R
  obtain ⟨N₂, hN₂⟩ :=
    FlowMetricConvergenceData.exists_eventually_metricUniformEquivalentOn
      Φ R bf hsrc htgt co hK hL hlimit
  have h2L : 1 ≤ 2 * L := by linarith
  obtain ⟨C, hC, hbound⟩ :=
    exists_pos_bound_intrinsic_curvature_derivative_on_compact_of_metric_jets
      R hK j (2 * L) J h2L hJ.le
  refine ⟨C, hC, max N₁ N₂, ?_⟩
  intro k hk t ht x hx
  have hk₁ : N₁ ≤ k := (le_max_left _ _).trans hk
  have hk₂ : N₂ ≤ k := (le_max_right _ _).trans hk
  exact hbound (gSeqExt Φ R bf hsrc htgt (co.φ k) t) x hx
    ((hN₂ k hk₂ t ht).2 x hx) (fun s hs => hN₁ k hk₁ t ht s hs x hx)

end DifferentialGeometry.CheegerGromovCompactness
