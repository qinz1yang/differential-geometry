import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MetricRicciDifference
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped Topology ContDiff Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

local instance pointedRicciManifoldOne {P : Type*} [TopologicalSpace P]
    [ChartedSpace H P] [IsManifold I ∞ P] : IsManifold I 1 P :=
  IsManifold.of_le (I := I) (M := P) (n := ∞) (by decide)

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

local instance pointedRicciLimitTopology : TopologicalSpace L.M := L.topology
local instance pointedRicciLimitCharted : ChartedSpace H L.M := L.charted
local instance pointedRicciLimitSmooth : IsManifold I ∞ L.M := L.smooth
local instance pointedRicciLimitT2 : T2Space L.M := L.t2
local instance pointedRicciLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

local instance pointedRicciApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology
local instance pointedRicciApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted
local instance pointedRicciApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
local instance pointedRicciApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2
local instance pointedRicciApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

local instance pointedRicciSourceTopology (k : ℕ) :
    TopologicalSpace (MetricSourceDomain (I := I) Phi k) := metricSourceDomainTopology Phi k
local instance pointedRicciSourceCharted (k : ℕ) :
    ChartedSpace H (MetricSourceDomain (I := I) Phi k) := metricSourceDomainChartedSpace Phi k
local instance pointedRicciSourceSmooth (k : ℕ) :
    IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := metric_source_domain_smooth Phi k
local instance pointedRicciSourceT2 (k : ℕ) :
    T2Space (MetricSourceDomain (I := I) Phi k) := metric_source_domain_t2 Phi k
local instance pointedRicciSourceSigma (k : ℕ) :
    SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
  metric_source_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_source Phi k)

local instance pointedRicciTargetTopology (k : ℕ) :
    TopologicalSpace (MetricTargetDomain (I := I) Phi k) := metricTargetDomainTopology Phi k
local instance pointedRicciTargetCharted (k : ℕ) :
    ChartedSpace H (MetricTargetDomain (I := I) Phi k) := metricTargetDomainChartedSpace Phi k
local instance pointedRicciTargetSmooth (k : ℕ) :
    IsManifold I ∞ (MetricTargetDomain (I := I) Phi k) := metric_target_domain_smooth Phi k
local instance pointedRicciTargetT2 (k : ℕ) :
    T2Space (MetricTargetDomain (I := I) Phi k) := metric_target_domain_t2 Phi k
local instance pointedRicciTargetSigma (k : ℕ) :
    SigmaCompactSpace (MetricTargetDomain (I := I) Phi k) :=
  metric_target_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_target Phi k)

variable {Phi}

private theorem canonicalRicci_restrict (k : ℕ)
    (x : MetricSourceDomain (I := I) Phi k) (v : TangentSpace I x) :
    ricciTensor (I := I) (L.metric.restrictOpen (I := I) (metricSourceOpenSubset Phi k)) x v v =
      ricciTensor (I := I) L.metric (x : L.M) v v := by
  have h := ricciTensor_restrictOpen L.metric (metricSourceOpenSubset Phi k) x v v
  erw [mfderiv_subtype_val_apply] at h
  exact h

private theorem canonicalRicci_pullback (k : ℕ)
    (x : MetricSourceDomain (I := I) Phi k) (v : TangentSpace I x) :
    ricciTensor (I := I)
        (Diffeomorph.pullbackMetric (I := I)
          ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
          (metricSourceTargetDiffeomorph Phi k)) x v v =
      ricciTensor (I := I) (X.obj (subseq k)).metric (Phi.map k (x : L.M))
        (mfderiv I I (Phi.map k) (x : L.M) v)
        (mfderiv I I (Phi.map k) (x : L.M) v) := by
  rw [DifferentialGeometry.CheegerGromovCompactness.ricciTensor_pullback]
  erw [ricciTensor_restrictOpen (X.obj (subseq k)).metric
    (metricTargetOpenSubset Phi k) (metricSourceTargetDiffeomorph Phi k x)
    (mfderiv I I (metricSourceTargetDiffeomorph Phi k) x v)
    (mfderiv I I (metricSourceTargetDiffeomorph Phi k) x v)]
  erw [mfderiv_subtype_val_apply, metric_source_target_diffeomorph_apply,
    metric_source_target_diffeomorph_mfderiv (I := I) Phi k x v]

theorem pointedRicci_tendsto_of_canonical_metric_convergence
    (hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Phi
        (CanonicalMetricCompactness.canonicalSourceData Phi) K 2)
    (x : L.M) (v : TangentSpace I x) :
    Tendsto (fun k => ricciTensor (I := I) (X.obj (subseq k)).metric (Phi.map k x)
      (mfderiv I I (Phi.map k) x v) (mfderiv I I (Phi.map k) x v))
      atTop (𝓝 (ricciTensor (I := I) L.metric x v v)) := by
  let n : ℝ := Module.finrank ℝ E
  let A : ℝ := n * 432 * L.metric.inner x v v
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hv : 0 ≤ L.metric.inner x v v :=
    DifferentialGeometry.metric_inner_self_nonneg L.metric x v
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  apply Metric.tendsto_atTop.mpr
  intro epsilon hepsilon
  let delta : ℝ := min 1 (min (1 / (2 * (n + 1))) (epsilon / (A + 1)))
  have hd0 : 0 < delta := by dsimp only [delta]; positivity
  have hd1 : delta ≤ 1 := min_le_left _ _
  have hdn : n * delta ≤ 1 / 2 := by
    have ht : delta ≤ 1 / (2 * (n + 1)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hm := (le_div_iff₀ (by positivity : 0 < 2 * (n + 1))).mp ht
    nlinarith [hd0.le]
  have hdA : A * delta < epsilon := by
    have ht : delta ≤ epsilon / (A + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hm := (le_div_iff₀ (by positivity : 0 < A + 1)).mp ht
    nlinarith
  obtain ⟨k0, hk0⟩ := hconv {x} isCompact_singleton delta hd0
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
    (metricSourceCompactSet (I := I) Phi k {x}) 2 hU gU gU < delta at hsup
  have hjet (a : ℕ) (ha : a ≤ 2) : metricDerivNorm (I := I) a hU gU gU xu ≤ delta := by
    have ht := derivNorm_le_sup (I := I) hcompact ha
      hU gU gU (x := xu) (Set.mem_singleton x)
    exact ht.trans hsup.le
  have hb := metricRicci_difference_le_relative_two_jets gU hU xu hd0.le hd1 hdn hjet v
  have hlim : ricciTensor (I := I) gU xu v v = ricciTensor (I := I) L.metric x v v :=
    canonicalRicci_restrict (Phi := Phi) k xu v
  have hpull : ricciTensor (I := I) hU xu v v =
      ricciTensor (I := I) (X.obj (subseq k)).metric (Phi.map k x)
        (mfderiv I I (Phi.map k) x v) (mfderiv I I (Phi.map k) x v) :=
    canonicalRicci_pullback (Phi := Phi) k xu v
  rw [hpull, hlim] at hb
  have hcoeff : (Module.finrank ℝ E : ℝ) * (432 * delta) * gU.inner xu v v =
      A * delta := by
    change n * (432 * delta) * L.metric.inner x v v =
      (n * 432 * L.metric.inner x v v) * delta
    ring
  rw [hcoeff] at hb
  rw [Real.dist_eq]
  exact hb.trans_lt hdA

theorem pointedRicci_tendsto_of_metricCG_canonical_domains
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (x : L.M) (v : TangentSpace I x) :
    Tendsto (fun k => ricciTensor (I := I) (X.obj (subseq k)).metric (Phi.map k x)
      (mfderiv I I (Phi.map k) x v) (mfderiv I I (Phi.map k) x v))
      atTop (𝓝 (ricciTensor (I := I) L.metric x v v)) := by
  apply pointedRicci_tendsto_of_canonical_metric_convergence
  intro K hK
  have ht := C.converges K hK 2
  have hD : C.domain = CanonicalMetricCompactness.canonicalSourceData Phi := funext hcanonical
  rw [hD] at ht
  exact ht

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
