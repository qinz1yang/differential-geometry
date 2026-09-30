import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Globalization
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

noncomputable section

open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
variable {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
variable {subseq : Nat → Nat}

theorem compactLimit_eventually_source_eq_univ
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)
    (hcompact :
      let : TopologicalSpace L.M := L.topology
      CompactSpace L.M) :
    ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k → Φ.source k = Set.univ := by
  let : TopologicalSpace L.M := L.topology
  let : CompactSpace L.M := hcompact
  obtain ⟨k0, hk0⟩ := Φ.source_subset (K := Set.univ) isCompact_univ
  refine ⟨k0, ?_⟩
  intro k hk
  exact Set.eq_univ_of_univ_subset (hk0 k hk)

theorem compactLimit_eventually_globalizes
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)
    (hcompact :
      let : TopologicalSpace L.M := L.topology
      CompactSpace L.M)
    (hconnected : ∀ k : Nat,
      let : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
      ConnectedSpace (X.obj (subseq k)).M) :
    ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k →
      let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
      let : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
      Φ.source k = Set.univ ∧ Φ.target k = Set.univ ∧
        ∃ e : Diffeomorph I I L.M (X.obj (subseq k)).M (∞ : WithTop ℕ∞),
          (∀ x, e x = Φ.map k x) ∧
          (∀ y, e.symm y = (Φ.partialDiffeomorph k).symm y) ∧
          e L.basepoint = (X.obj (subseq k)).basepoint ∧
          CompactSpace (X.obj (subseq k)).M := by
  obtain ⟨k0, hk0⟩ := compactLimit_eventually_source_eq_univ Φ hcompact
  refine ⟨k0, ?_⟩
  intro k hk
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
  let : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
  let : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
  let : CompactSpace L.M := hcompact
  let : ConnectedSpace (X.obj (subseq k)).M := hconnected k
  have hsource : (Φ.partialDiffeomorph k).source = Set.univ := hk0 k hk
  have hsourceCompact : IsCompact (Φ.partialDiffeomorph k).source := by
    rw [hsource]
    exact isCompact_univ
  have htarget : (Φ.partialDiffeomorph k).target = Set.univ :=
    partialDiffeomorph_target_eq_univ_of_compact_source (Φ.partialDiffeomorph k)
      hsourceCompact ⟨L.basepoint, Φ.base_mem k⟩
  let e := globalDiffeomorphOfUniv (Φ.partialDiffeomorph k) hsource htarget
  refine ⟨hsource, htarget, e, ?_, ?_, ?_, e.toHomeomorph.compactSpace⟩
  · intro x
    rfl
  · intro y
    rfl
  · exact Φ.basepoint_map k

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions (compactLimit_eventually_globalizes)

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle
open CanonicalMetricCompactness
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

local instance globalizedMetricLimitTopology : TopologicalSpace L.M := L.topology
local instance globalizedMetricLimitCharted : ChartedSpace H L.M := L.charted
local instance globalizedMetricLimitSmooth : IsManifold I ∞ L.M := L.smooth
local instance globalizedMetricLimitT2 : T2Space L.M := L.t2
local instance globalizedMetricLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

local instance globalizedMetricApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology
local instance globalizedMetricApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted
local instance globalizedMetricApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
local instance globalizedMetricApproxT2 (k : ℕ) : T2Space (X.obj k).M := (X.obj k).t2
local instance globalizedMetricApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

local instance globalizedMetricSourceTopology (k : ℕ) :
    TopologicalSpace (MetricSourceDomain (I := I) Phi k) := metricSourceDomainTopology Phi k
local instance globalizedMetricSourceCharted (k : ℕ) :
    ChartedSpace H (MetricSourceDomain (I := I) Phi k) := metricSourceDomainChartedSpace Phi k
local instance globalizedMetricSourceSmooth (k : ℕ) :
    IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) := metric_source_domain_smooth Phi k
local instance globalizedMetricSourceT2 (k : ℕ) :
    T2Space (MetricSourceDomain (I := I) Phi k) := metric_source_domain_t2 Phi k
local instance globalizedMetricSourceSigma (k : ℕ) :
    SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
  metric_source_domain_sigma_compact Phi k (PointedRiemannianConvergenceMaps.isSigmaCompact_source Phi k)

local instance globalizedMetricTargetTopology (k : ℕ) :
    TopologicalSpace (MetricTargetDomain (I := I) Phi k) := metricTargetDomainTopology Phi k
local instance globalizedMetricTargetCharted (k : ℕ) :
    ChartedSpace H (MetricTargetDomain (I := I) Phi k) := metricTargetDomainChartedSpace Phi k
local instance globalizedMetricTargetSmooth (k : ℕ) :
    IsManifold I ∞ (MetricTargetDomain (I := I) Phi k) := metric_target_domain_smooth Phi k
local instance globalizedMetricTargetT2 (k : ℕ) :
    T2Space (MetricTargetDomain (I := I) Phi k) := metric_target_domain_t2 Phi k

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem canonicalSource_pullback_eq_global_restrict (k : ℕ)
    (e : Diffeomorph I I L.M (X.obj (subseq k)).M (∞ : WithTop ℕ∞))
    (he : ∀ x : L.M, e x = Phi.map k x) :
    (canonicalSourceData Phi k).pullbackMetric =
      (Diffeomorph.pullbackMetric (I := I) (X.obj (subseq k)).metric e).restrictOpen
        (I := I) (metricSourceOpenSubset Phi k) := by
  change Diffeomorph.pullbackMetric (I := I)
      ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
      (metricSourceTargetDiffeomorph Phi k) =
    (Diffeomorph.pullbackMetric (I := I) (X.obj (subseq k)).metric e).restrictOpen
      (I := I) (metricSourceOpenSubset Phi k)
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  change
    (Diffeomorph.pullbackMetric (I := I)
      ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
      (metricSourceTargetDiffeomorph Phi k)).inner x v w =
      (Diffeomorph.pullbackMetric (I := I) (X.obj (subseq k)).metric e).inner
        (x : L.M) v w
  with_unfolding_all
    erw [Diffeomorph.pullbackMetric_inner, Diffeomorph.pullbackMetric_inner]
    change (X.obj (subseq k)).metric.inner
        ((metricSourceTargetDiffeomorph Phi k x : MetricTargetDomain (I := I) Phi k) :
          (X.obj (subseq k)).M)
        (mfderiv I I (metricSourceTargetDiffeomorph Phi k) x v)
        (mfderiv I I (metricSourceTargetDiffeomorph Phi k) x w) =
      (X.obj (subseq k)).metric.inner (e (x : L.M))
        (mfderiv I I e (x : L.M) v) (mfderiv I I e (x : L.M) w)
    simp only [metric_source_target_diffeomorph_mfderiv]
    have hef : (e : L.M → (X.obj (subseq k)).M) = Phi.map k := funext he
    rw [hef]
    rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] in
private theorem globalizedMetric_sourceCompact_image (k : ℕ) (K : Set L.M)
    (hKsource : K ⊆ Phi.source k) :
    (Subtype.val : MetricSourceDomain (I := I) Phi k → L.M) ''
      metricSourceCompactSet (I := I) Phi k K = K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hKsource hx⟩, hx, rfl⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem canonicalSource_sup_eq_global_pullback (k : ℕ)
    (e : Diffeomorph I I L.M (X.obj (subseq k)).M (∞ : WithTop ℕ∞))
    (he : ∀ x : L.M, e x = Phi.map k x)
    (K : Set L.M) (p : ℕ) (hKsource : K ⊆ Phi.source k) :
    (canonicalSourceData Phi k).derivNormSupOn (I := I) K p =
      metricDerivNormSupOn (I := I) K p
        (Diffeomorph.pullbackMetric (I := I) (X.obj (subseq k)).metric e)
        L.metric L.metric := by
  change metricDerivNormSupOn (I := I) (metricSourceCompactSet (I := I) Phi k K) p
      (Diffeomorph.pullbackMetric (I := I)
        ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
        (metricSourceTargetDiffeomorph Phi k))
      (L.metric.restrictOpen (I := I) (metricSourceOpenSubset Phi k))
      (L.metric.restrictOpen (I := I) (metricSourceOpenSubset Phi k)) = _
  have hpb : Diffeomorph.pullbackMetric (I := I)
      ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Phi k))
      (metricSourceTargetDiffeomorph Phi k) =
      (Diffeomorph.pullbackMetric (I := I) (X.obj (subseq k)).metric e).restrictOpen
        (I := I) (metricSourceOpenSubset Phi k) :=
    canonicalSource_pullback_eq_global_restrict Phi k e he
  rw [hpb,
    metricDerivNormSupOn_restrictOpen,
    globalizedMetric_sourceCompact_image Phi k K hKsource]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem compactLimit_global_pullback_metric_convergence
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k : ℕ, C.domain k = canonicalSourceData Phi k)
    (hcompact : CompactSpace L.M)
    (hconnected : ∀ k : ℕ, ConnectedSpace (X.obj (subseq k)).M) :
    ∃ k0 : ℕ,
      ∃ e : ∀ k : ℕ,
        Diffeomorph I I L.M (X.obj (subseq (k0 + k))).M (∞ : WithTop ℕ∞),
        (∀ k : ℕ, Phi.source (k0 + k) = Set.univ ∧
          Phi.target (k0 + k) = Set.univ ∧
          (∀ x : L.M, e k x = Phi.map (k0 + k) x) ∧
          (∀ y, (e k).symm y = (Phi.partialDiffeomorph (k0 + k)).symm y) ∧
          e k L.basepoint = (X.obj (subseq (k0 + k))).basepoint ∧
          CompactSpace (X.obj (subseq (k0 + k))).M) ∧
        MetricCInfConvergenceOnCompacts (I := I)
          (fun k => Diffeomorph.pullbackMetric (I := I)
            (X.obj (subseq (k0 + k))).metric (e k)) L.metric L.metric := by
  classical
  obtain ⟨k0, hk0⟩ := compactLimit_eventually_globalizes Phi hcompact hconnected
  have hex (k : ℕ) :
      ∃ e : Diffeomorph I I L.M (X.obj (subseq (k0 + k))).M (∞ : WithTop ℕ∞),
        (∀ x : L.M, e x = Phi.map (k0 + k) x) ∧
        (∀ y, e.symm y = (Phi.partialDiffeomorph (k0 + k)).symm y) ∧
        e L.basepoint = (X.obj (subseq (k0 + k))).basepoint ∧
        CompactSpace (X.obj (subseq (k0 + k))).M :=
    (hk0 (k0 + k) (by omega)).2.2
  choose e he hinverse hbase hcompactApprox using hex
  refine ⟨k0, e, ?_, ?_⟩
  · intro k
    exact ⟨(hk0 (k0 + k) (by omega)).1, (hk0 (k0 + k) (by omega)).2.1,
      he k, hinverse k, hbase k, hcompactApprox k⟩
  · intro K hK p eps heps
    obtain ⟨k1, hk1⟩ := C.converges K hK p eps heps
    refine ⟨k1, fun k hk => ?_⟩
    have hc := hk1 (k0 + k) (by omega)
    have hs : (canonicalSourceData Phi (k0 + k)).derivNormSupOn (I := I) K p < eps := by
      rw [← hcanonical (k0 + k)]
      exact hc.2
    rw [canonicalSource_sup_eq_global_pullback Phi (k0 + k) (e k) (he k) K p hc.1] at hs
    exact hs

end DifferentialGeometry.CheegerGromovCompactness

end
