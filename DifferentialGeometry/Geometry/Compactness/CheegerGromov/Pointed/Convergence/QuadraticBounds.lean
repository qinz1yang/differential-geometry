import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Inner

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

local instance pointedQuadraticManifoldOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] : IsManifold I 1 P :=
  IsManifold.of_le (I := I) (M := P) (n := ∞) (by decide)

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

local instance pointedQuadraticLimitTopology : TopologicalSpace L.M := L.topology
local instance pointedQuadraticLimitCharted : ChartedSpace H L.M := L.charted
local instance pointedQuadraticLimitSmooth : IsManifold I ∞ L.M := L.smooth
local instance pointedQuadraticLimitT2 : T2Space L.M := L.t2
local instance pointedQuadraticLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

local instance pointedQuadraticApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology
local instance pointedQuadraticApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted
local instance pointedQuadraticApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
local instance pointedQuadraticApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2
local instance pointedQuadraticApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

local instance pointedQuadraticSourceTopology (k : ℕ) :
    TopologicalSpace (MetricSourceDomain (I := I) Phi k) := metricSourceDomainTopology Phi k
local instance pointedQuadraticSourceCharted (k : ℕ) :
    ChartedSpace H (MetricSourceDomain (I := I) Phi k) := metricSourceDomainChartedSpace Phi k
local instance pointedQuadraticSourceSmooth (k : ℕ) :
    IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := metric_source_domain_smooth Phi k
local instance pointedQuadraticSourceT2 (k : ℕ) :
    T2Space (MetricSourceDomain (I := I) Phi k) := metric_source_domain_t2 Phi k
local instance pointedQuadraticSourceSigma (k : ℕ) :
    SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
  metric_source_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_source Phi k)

local instance pointedQuadraticTargetTopology (k : ℕ) :
    TopologicalSpace (MetricTargetDomain (I := I) Phi k) := metricTargetDomainTopology Phi k
local instance pointedQuadraticTargetCharted (k : ℕ) :
    ChartedSpace H (MetricTargetDomain (I := I) Phi k) := metricTargetDomainChartedSpace Phi k
local instance pointedQuadraticTargetSmooth (k : ℕ) :
    IsManifold I ∞ (MetricTargetDomain (I := I) Phi k) := metric_target_domain_smooth Phi k
local instance pointedQuadraticTargetT2 (k : ℕ) :
    T2Space (MetricTargetDomain (I := I) Phi k) := metric_target_domain_t2 Phi k
local instance pointedQuadraticTargetSigma (k : ℕ) :
    SigmaCompactSpace (MetricTargetDomain (I := I) Phi k) :=
  metric_target_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_target Phi k)

variable {Phi}

omit [I.Boundaryless] in
theorem pointed_metric_eventually_quadratic_bounds
    {K : Set L.M} (hK : IsCompact K)
    (hconv : metricSourceConvergesOn (I := I) Phi
      (CanonicalMetricCompactness.canonicalSourceData Phi) K 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ k in atTop, K ⊆ Phi.source k ∧ ∀ x ∈ K, ∀ v : TangentSpace I x,
      (1 - epsilon) * L.metric.inner x v v ≤
        (X.obj (subseq k)).metric.inner (Phi.map k x)
          (mfderiv I I (Phi.map k) x v) (mfderiv I I (Phi.map k) x v) ∧
      (X.obj (subseq k)).metric.inner (Phi.map k x)
          (mfderiv I I (Phi.map k) x v) (mfderiv I I (Phi.map k) x v) ≤
        (1 + epsilon) * L.metric.inner x v v := by
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := Nat.cast_nonneg _
  obtain ⟨k0, hk0⟩ := hconv (epsilon / (n + 1)) (by positivity)
  filter_upwards [eventually_ge_atTop k0] with k hk
  obtain ⟨hsource, hsup⟩ := hk0 k hk
  refine ⟨hsource, fun x hx v => ?_⟩
  let xu : MetricSourceDomain (I := I) Phi k := ⟨x, hsource hx⟩
  let gU := L.metric.restrictOpen (I := I) (metricSourceOpenSubset Phi k)
  let hU := Diffeomorph.pullbackMetric (I := I)
    ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
    (metricSourceTargetDiffeomorph Phi k)
  have hcompact : IsCompact (metricSourceCompactSet (I := I) Phi k K) :=
    metric_source_compact_set_is_compact (I := I) Phi k hK hsource
  change metricDerivNormSupOn (I := I)
    (metricSourceCompactSet (I := I) Phi k K) 0 hU gU gU < _ at hsup
  have hpoint := (derivNorm_le_sup (I := I) hcompact (le_refl 0)
    hU gU gU (x := xu) hx).trans_lt hsup
  have hbound := metricQuadFormDiff_le_metricDerivNorm (I := I) hU gU gU xu v
  have hpull : hU.inner xu v v = (X.obj (subseq k)).metric.inner (Phi.map k x)
      (mfderiv I I (Phi.map k) x v) (mfderiv I I (Phi.map k) x v) := by
    dsimp only [hU]
    erw [Diffeomorph.pullbackMetric_inner]
    change (X.obj (subseq k)).metric.inner _ _ _ = _
    erw [metric_source_target_diffeomorph_mfderiv]
    rfl
  change |hU.inner xu v v - L.metric.inner x v v| ≤
    n * metricDerivNorm (I := I) 0 hU gU gU xu * L.metric.inner x v v at hbound
  rw [hpull] at hbound
  have hnn : 0 ≤ L.metric.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (L.metric.pos x v hv).le
  have hsmall : n * metricDerivNorm (I := I) 0 hU gU gU xu ≤ epsilon := by
    calc
      _ ≤ n * (epsilon / (n + 1)) := mul_le_mul_of_nonneg_left hpoint.le hn
      _ ≤ epsilon := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < n + 1)]
        nlinarith
  have hb := hbound.trans (mul_le_mul_of_nonneg_right hsmall hnn)
  have hbs := abs_le.mp hb
  exact ⟨by nlinarith [hbs.1], by nlinarith [hbs.2]⟩

end DifferentialGeometry.CheegerGromovCompactness
end
