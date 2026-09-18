import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Topology ContDiff Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

local instance pointedInnerManifoldOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] : IsManifold I 1 P :=
  IsManifold.of_le (I := I) (M := P) (n := ∞) (by decide)

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

local instance pointedInnerLimitTopology : TopologicalSpace L.M := L.topology
local instance pointedInnerLimitCharted : ChartedSpace H L.M := L.charted
local instance pointedInnerLimitSmooth : IsManifold I ∞ L.M := L.smooth
local instance pointedInnerLimitT2 : T2Space L.M := L.t2
local instance pointedInnerLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

local instance pointedInnerApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology
local instance pointedInnerApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted
local instance pointedInnerApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
local instance pointedInnerApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2
local instance pointedInnerApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

local instance pointedInnerSourceTopology (k : ℕ) :
    TopologicalSpace (MetricSourceDomain (I := I) Phi k) := metricSourceDomainTopology Phi k
local instance pointedInnerSourceCharted (k : ℕ) :
    ChartedSpace H (MetricSourceDomain (I := I) Phi k) := metricSourceDomainChartedSpace Phi k
local instance pointedInnerSourceSmooth (k : ℕ) :
    IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := metric_source_domain_smooth Phi k
local instance pointedInnerSourceT2 (k : ℕ) :
    T2Space (MetricSourceDomain (I := I) Phi k) := metric_source_domain_t2 Phi k
local instance pointedInnerSourceSigma (k : ℕ) :
    SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
  metric_source_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_source Phi k)

local instance pointedInnerTargetTopology (k : ℕ) :
    TopologicalSpace (MetricTargetDomain (I := I) Phi k) := metricTargetDomainTopology Phi k
local instance pointedInnerTargetCharted (k : ℕ) :
    ChartedSpace H (MetricTargetDomain (I := I) Phi k) := metricTargetDomainChartedSpace Phi k
local instance pointedInnerTargetSmooth (k : ℕ) :
    IsManifold I ∞ (MetricTargetDomain (I := I) Phi k) := metric_target_domain_smooth Phi k
local instance pointedInnerTargetT2 (k : ℕ) :
    T2Space (MetricTargetDomain (I := I) Phi k) := metric_target_domain_t2 Phi k
local instance pointedInnerTargetSigma (k : ℕ) :
    SigmaCompactSpace (MetricTargetDomain (I := I) Phi k) :=
  metric_target_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_target Phi k)

variable {Phi}

omit [I.Boundaryless] in
theorem pointed_metric_inner_tendsto
    (hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Phi
        (CanonicalMetricCompactness.canonicalSourceData Phi) K 0)
    (x : L.M) (v w : TangentSpace I x) :
    Tendsto (fun k => (X.obj (subseq k)).metric.inner (Phi.map k x)
      (mfderiv I I (Phi.map k) x v) (mfderiv I I (Phi.map k) x w))
      atTop (𝓝 (L.metric.inner x v w)) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  let n : ℝ := Module.finrank ℝ E
  let S : ℝ := L.metric.inner x (v + w) (v + w) +
    L.metric.inner x v v + L.metric.inner x w w
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hS : 0 ≤ S := by
    have hnonneg (z : TangentSpace I x) : 0 ≤ L.metric.inner x z z := by
      by_cases hz : z = 0
      · simp [hz]
      · exact (L.metric.pos x z hz).le
    exact add_nonneg (add_nonneg (hnonneg _) (hnonneg _)) (hnonneg _)
  have hden : 0 < n * S + 1 := by positivity
  obtain ⟨k0, hk0⟩ := hconv {x} isCompact_singleton
    (epsilon / (n * S + 1)) (by positivity)
  refine ⟨k0, fun k hk => ?_⟩
  obtain ⟨hsource, hsup⟩ := hk0 k hk
  let xu : MetricSourceDomain (I := I) Phi k := ⟨x, hsource (Set.mem_singleton x)⟩
  let gU := L.metric.restrictOpen (I := I) (metricSourceOpenSubset Phi k)
  let hU := Diffeomorph.pullbackMetric (I := I)
    ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
    (metricSourceTargetDiffeomorph Phi k)
  have hcompact : IsCompact (metricSourceCompactSet (I := I) Phi k {x}) :=
    metric_source_compact_set_is_compact (I := I) Phi k isCompact_singleton hsource
  change metricDerivNormSupOn (I := I)
    (metricSourceCompactSet (I := I) Phi k {x}) 0 hU gU gU < _ at hsup
  have hpoint := (derivNorm_le_sup (I := I) hcompact (le_refl 0)
    hU gU gU (x := xu) (Set.mem_singleton x)).trans_lt hsup
  have hbound := metricInnerApply_diff_le (I := I) hU gU gU xu v w
  have hpull : hU.inner xu v w = (X.obj (subseq k)).metric.inner (Phi.map k x)
      (mfderiv I I (Phi.map k) x v) (mfderiv I I (Phi.map k) x w) := by
    dsimp only [hU]
    erw [Diffeomorph.pullbackMetric_inner]
    change (X.obj (subseq k)).metric.inner _ _ _ = _
    erw [metric_source_target_diffeomorph_mfderiv,
      metric_source_target_diffeomorph_mfderiv]
    rfl
  change |hU.inner xu v w - L.metric.inner x v w| ≤
    n * metricDerivNorm (I := I) 0 hU gU gU xu * S at hbound
  rw [hpull] at hbound
  rw [Real.dist_eq]
  apply hbound.trans_lt
  calc
    _ ≤ n * (epsilon / (n * S + 1)) * S :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoint.le hn) hS
    _ = (n * S) * (epsilon / (n * S + 1)) := by ring
    _ < (n * S + 1) * (epsilon / (n * S + 1)) :=
      mul_lt_mul_of_pos_right (by linarith) (by positivity)
    _ = epsilon := by field_simp

end DifferentialGeometry.CheegerGromovCompactness
end
