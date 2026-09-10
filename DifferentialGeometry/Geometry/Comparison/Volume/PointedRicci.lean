import DifferentialGeometry.Geometry.Comparison.Volume.PointedConvergence
import DifferentialGeometry.Geometry.Comparison.Volume.LocalRicci
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.RicciFromJets
import DifferentialGeometry.Geometry.Metric.Convergence.Window.AllPoints
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Bounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section NestedSource

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)


def nestedSourceOpen (k₀ k : ℕ) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) :=
      metricSourceDomainTopology (I := I) Phi k
    TopologicalSpace.Opens (MetricSourceDomain (I := I) Phi k) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomainTopology (I := I) Phi k
  exact ⟨Subtype.val ⁻¹' Phi.source k₀,
    (Phi.source_open k₀).preimage continuous_subtype_val⟩

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
noncomputable def nestedSourceDiffeomorph (k₀ k : ℕ) (hkk : k₀ ≤ k) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) :=
      metricSourceDomainTopology (I := I) Phi k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) :=
      metricSourceDomainChartedSpace (I := I) Phi k
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) :=
      metric_source_domain_smooth (I := I) Phi k
    Diffeomorph I I (metricSourceOpenSubset (I := I) Phi k₀)
      (nestedSourceOpen (I := I) Phi k₀ k) ∞ := by
  sorry

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] in
theorem nestedSourceDiffeomorph_mfderiv (k₀ k : ℕ) (hkk : k₀ ≤ k)
    :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) :=
      metricSourceDomainTopology (I := I) Phi k
    letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) :=
      metricSourceDomainChartedSpace (I := I) Phi k
    letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) :=
      metric_source_domain_smooth (I := I) Phi k
    ∀ (x : metricSourceOpenSubset (I := I) Phi k₀) (v : TangentSpace I x),
      mfderiv I I (nestedSourceDiffeomorph (I := I) Phi k₀ k hkk) x v = v := by
  sorry

end NestedSource

section TransportedMetrics

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)


noncomputable def fixedSourceLimitMetric (k₀ : ℕ) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    SmoothRiemannianMetric I (metricSourceOpenSubset (I := I) Phi k₀) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : T2Space (MetricSourceDomain (I := I) Phi k₀) :=
    metric_source_domain_t2 (I := I) Phi k₀
  exact L.metric.restrictOpen (I := I) (metricSourceOpenSubset (I := I) Phi k₀)

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem fixedSourceLimitMetric_eq_restrictOpen (k₀ : ℕ) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : T2Space L.M := L.t2
    fixedSourceLimitMetric (I := I) Phi k₀ =
      L.metric.restrictOpen (I := I) (metricSourceOpenSubset (I := I) Phi k₀) := by
  rfl


noncomputable def transportedSourceMetric (k₀ k : ℕ) (hkk : k₀ ≤ k) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    SmoothRiemannianMetric I (metricSourceOpenSubset (I := I) Phi k₀) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  letI : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
  letI : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
  letI : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
  letI : IsManifold I ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth
  letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomainTopology (I := I) Phi k
  letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomainChartedSpace (I := I) Phi k
  letI : T2Space (MetricSourceDomain (I := I) Phi k) :=
    metric_source_domain_t2 (I := I) Phi k
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) :=
    metric_source_domain_smooth (I := I) Phi k
  letI : TopologicalSpace (MetricTargetDomain (I := I) Phi k) :=
    metricTargetDomainTopology (I := I) Phi k
  letI : ChartedSpace H (MetricTargetDomain (I := I) Phi k) :=
    metricTargetDomainChartedSpace (I := I) Phi k
  letI : T2Space (MetricTargetDomain (I := I) Phi k) :=
    metric_target_domain_t2 (I := I) Phi k
  letI : IsManifold I ∞ (MetricTargetDomain (I := I) Phi k) :=
    metric_target_domain_smooth (I := I) Phi k
  let targetMetric := (X.obj (subseq k)).metric.restrictOpen
    (I := I) (metricTargetOpenSubset (I := I) Phi k)
  let sourceMetric := Diffeomorph.pullbackMetric (I := I) targetMetric
    (metricSourceTargetDiffeomorph (I := I) Phi k)
  let F := nestedSourceDiffeomorph (I := I) Phi k₀ k hkk
  exact Diffeomorph.pullbackMetric (I := I)
    (sourceMetric.restrictOpen (I := I) (nestedSourceOpen (I := I) Phi k₀ k)) F


noncomputable def transportedLimitMetric (k₀ k : ℕ) (hkk : k₀ ≤ k) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    SmoothRiemannianMetric I (metricSourceOpenSubset (I := I) Phi k₀) := by
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  letI : TopologicalSpace (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomainTopology (I := I) Phi k
  letI : ChartedSpace H (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomainChartedSpace (I := I) Phi k
  letI : T2Space (MetricSourceDomain (I := I) Phi k) :=
    metric_source_domain_t2 (I := I) Phi k
  letI : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) :=
    metric_source_domain_smooth (I := I) Phi k
  let sourceLimit := L.metric.restrictOpen (I := I) (metricSourceOpenSubset (I := I) Phi k)
  let F := nestedSourceDiffeomorph (I := I) Phi k₀ k hkk
  exact Diffeomorph.pullbackMetric (I := I)
    (sourceLimit.restrictOpen (I := I) (nestedSourceOpen (I := I) Phi k₀ k)) F

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
theorem transportedLimitMetric_eq (k₀ k : ℕ) (hkk : k₀ ≤ k) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    transportedLimitMetric (I := I) Phi k₀ k hkk =
      fixedSourceLimitMetric (I := I) Phi k₀ := by
  sorry

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem transportedSourceMetric_derivNorm_le
    (k₀ k p a : ℕ) (hkk : k₀ ≤ k) (ha : a ≤ p) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    ∀ x : metricSourceOpenSubset (I := I) Phi k₀,
      metricDerivNorm (I := I) a
        (transportedSourceMetric (I := I) Phi k₀ k hkk)
        (fixedSourceLimitMetric (I := I) Phi k₀)
        (fixedSourceLimitMetric (I := I) Phi k₀) x ≤
          (canonicalMetricSourceData (I := I) Phi k).derivNormSupOn
            (I := I) ({(x : L.M)} : Set L.M) p := by
  sorry

omit [NeZero (Module.finrank ℝ E)] in
theorem transportedSourceMetric_ricci_nonneg
    (hRic : ∀ i : ℕ,
      let Y := X.obj i
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
        (I := I) Y.metric 0)
    (k₀ k : ℕ) (hkk : k₀ ≤ k) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : T2Space L.M := L.t2
    letI : IsManifold I ∞ L.M := L.smooth
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
      (I := I) (transportedSourceMetric (I := I) Phi k₀ k hkk) 0 := by
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : T2Space L.M := L.t2
  let : IsManifold I ∞ L.M := L.smooth
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
  let : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
  let : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
  let : IsManifold I ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth
  let : SigmaCompactSpace (X.obj (subseq k)).M := (X.obj (subseq k)).sigmaCompact
  have hsigS : IsSigmaCompact (Phi.source k) :=
    DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I (Phi.source_open k)
  have hsigT : IsSigmaCompact (Phi.target k) :=
    DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I (Phi.target_open k)
  let : TopologicalSpace (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomainTopology (I := I) Phi k
  let : ChartedSpace H (MetricSourceDomain (I := I) Phi k) :=
    metricSourceDomainChartedSpace (I := I) Phi k
  let : T2Space (MetricSourceDomain (I := I) Phi k) :=
    metric_source_domain_t2 (I := I) Phi k
  let : IsManifold I ∞ (MetricSourceDomain (I := I) Phi k) :=
    metric_source_domain_smooth (I := I) Phi k
  let : SigmaCompactSpace (MetricSourceDomain (I := I) Phi k) :=
    metric_source_domain_sigma_compact (I := I) Phi k hsigS
  let : TopologicalSpace (MetricTargetDomain (I := I) Phi k) :=
    metricTargetDomainTopology (I := I) Phi k
  let : ChartedSpace H (MetricTargetDomain (I := I) Phi k) :=
    metricTargetDomainChartedSpace (I := I) Phi k
  let : T2Space (MetricTargetDomain (I := I) Phi k) :=
    metric_target_domain_t2 (I := I) Phi k
  let : IsManifold I ∞ (MetricTargetDomain (I := I) Phi k) :=
    metric_target_domain_smooth (I := I) Phi k
  let : SigmaCompactSpace (MetricTargetDomain (I := I) Phi k) :=
    metric_target_domain_sigma_compact (I := I) Phi k hsigT
  let : SigmaCompactSpace (nestedSourceOpen (I := I) Phi k₀ k) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I
        (nestedSourceOpen (I := I) Phi k₀ k).isOpen)
  let : SigmaCompactSpace (metricSourceOpenSubset (I := I) Phi k₀) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I
        (metricSourceOpenSubset (I := I) Phi k₀).isOpen)
  intro x v
  simp only [zero_mul]
  let targetMetric := (X.obj (subseq k)).metric.restrictOpen
    (I := I) (metricTargetOpenSubset (I := I) Phi k)
  let sourceMetric := Diffeomorph.pullbackMetric (I := I) targetMetric
    (metricSourceTargetDiffeomorph (I := I) Phi k)
  let F := nestedSourceDiffeomorph (I := I) Phi k₀ k hkk
  change 0 ≤ ricciTensor (I := I)
    (Diffeomorph.pullbackMetric (I := I)
      (sourceMetric.restrictOpen (I := I) (nestedSourceOpen (I := I) Phi k₀ k)) F)
      x v v
  rw [ricciTensor_pullback (I := I), ricciTensor_restrictOpen (I := I),
    ricciTensor_pullback (I := I), ricciTensor_restrictOpen (I := I)]
  simpa only [zero_mul] using (hRic (subseq k) _ _)

end TransportedMetrics

section RicciLimit

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {subseq : ℕ → ℕ}
  {Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq}

theorem ricciTensor_nonneg_of_metricDerivNorm_tendsto
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (gSeq : ℕ → SmoothRiemannianMetric I M) (gInf : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∀ a : ℕ, a ≤ 2 → metricDerivNorm (I := I) a (gSeq k) gInf gInf x < ε)
    (hRic : ∀ k : ℕ, 0 ≤ ricciTensor (I := I) (gSeq k) x v v) :
    0 ≤ ricciTensor (I := I) gInf x v v := by
  sorry

theorem fixedSourceLimitMetric_ricci_nonneg
    (C : CanonicalPointedRiemannianCGConverges (I := I) X L subseq Phi)
    (hRic : ∀ i : ℕ,
      let Y := X.obj i
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
        (I := I) Y.metric 0)
    (kSource : ℕ) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : T2Space L.M := L.t2
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    let U := metricSourceOpenSubset (I := I) Phi kSource
    letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
    DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
      (I := I) (fixedSourceLimitMetric (I := I) Phi kSource) 0 := by
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : T2Space L.M := L.t2
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let U := metricSourceOpenSubset (I := I) Phi kSource
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  change DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
    (I := I) (fixedSourceLimitMetric (I := I) Phi kSource) 0
  intro xU vU
  simp only [zero_mul]
  let x : L.M := xU
  have hxCompact : IsCompact ({x} : Set L.M) := isCompact_singleton
  let gInf := fixedSourceLimitMetric (I := I) Phi kSource
  have hkSource : ∀ k : ℕ, kSource ≤ kSource + k := fun k => Nat.le_add_right _ k
  let gSeq : ℕ → SmoothRiemannianMetric I U := fun k =>
    transportedSourceMetric (I := I) Phi kSource (kSource + k) (hkSource k)
  have hconv : ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∀ a : ℕ, a ≤ 2 → metricDerivNorm (I := I) a (gSeq k) gInf gInf xU < ε := by
    intro ε hε
    obtain ⟨kε, hkε⟩ := C.converges ({x} : Set L.M) hxCompact 2 ε hε
    refine ⟨kε, fun k hk a ha => ?_⟩
    refine lt_of_le_of_lt
      (transportedSourceMetric_derivNorm_le (I := I) Phi kSource (kSource + k) 2 a
        (hkSource k) ha xU) ?_
    exact hkε (kSource + k) (hk.trans (Nat.le_add_left k kSource))
  have hRicSeq : ∀ k : ℕ, 0 ≤ ricciTensor (I := I) (gSeq k) xU vU vU := by
    intro k
    have hkRic := transportedSourceMetric_ricci_nonneg (I := I) Phi hRic
      kSource (kSource + k) (hkSource k)
    simpa only [zero_mul] using hkRic xU vU
  exact ricciTensor_nonneg_of_metricDerivNorm_tendsto
    (I := I) gSeq gInf xU vU hconv hRicSeq

omit [NeZero (Module.finrank ℝ E)] in
theorem ricciBoundedBelow_zero_of_open_restrictions
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (h : ∀ x : M, ∃ (U : TopologicalSpace.Opens M) (_hx : x ∈ U),
      letI : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
        (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
      DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
        (I := I) (g.restrictOpen (I := I) U) 0) :
    DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
      (I := I) g 0 := by
  intro x v
  simp only [zero_mul]
  obtain ⟨U, hx, hRicU⟩ := h x
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let xU : U := ⟨x, hx⟩
  let vU : TangentSpace I xU := v
  have hRic : 0 ≤ ricciTensor (I := I) (g.restrictOpen (I := I) U) xU vU vU := by
    simpa only [zero_mul] using hRicU xU vU
  have hrestrict := ricciTensor_restrictOpen (I := I) g U xU vU vU
  have hRic' : 0 ≤ ricciTensor (I := I) g (xU : M)
      (mfderiv I I (Subtype.val : U → M) xU vU)
      (mfderiv I I (Subtype.val : U → M) xU vU) := hRic.trans_eq hrestrict
  have hv : mfderiv I I (Subtype.val : U → M) xU vU = v := by
    rw [mfderiv_subtype_val_apply]
  rw [hv] at hRic'
  change 0 ≤ ricciTensor (I := I) g x v v at hRic'
  exact hRic'

theorem ricciNonnegative_of_canonicalPointedLimit
    (C : CanonicalPointedRiemannianCGConverges (I := I) X L subseq Phi)
    (hRic : ∀ i : ℕ,
      let Y := X.obj i
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
        (I := I) Y.metric 0) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : T2Space L.M := L.t2
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
      (I := I) L.metric 0 := by
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : T2Space L.M := L.t2
  let : SigmaCompactSpace L.M := L.sigmaCompact
  apply ricciBoundedBelow_zero_of_open_restrictions (I := I) L.metric
  intro x
  have hxCompact : IsCompact ({x} : Set L.M) := isCompact_singleton
  obtain ⟨kSource, hkSource⟩ := Phi.source_subset hxCompact
  have hxSource : x ∈ Phi.source kSource := hkSource kSource le_rfl (Set.mem_singleton x)
  let U := metricSourceOpenSubset (I := I) Phi kSource
  let hU : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  refine ⟨U, hxSource, ?_⟩
  let : SigmaCompactSpace U := hU
  have hRicU := fixedSourceLimitMetric_ricci_nonneg (I := I) C hRic kSource
  rw [fixedSourceLimitMetric_eq_restrictOpen (I := I)] at hRicU
  exact hRicU

end RicciLimit

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
