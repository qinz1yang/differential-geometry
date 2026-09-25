import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.Construction
import DifferentialGeometry.Geometry.Metric.Convergence.Scaling

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

def PointedRiemannianManifold.scaleMetric
    (L : PointedRiemannianManifold.{u, uE, uH} I) (c : ℝ) (hc : 0 < c) :
    PointedRiemannianManifold.{u, uE, uH} I :=
  { L with metric := DifferentialGeometry.scaleMetric c hc L.metric }

@[simp] theorem PointedRiemannianManifold.scaleMetric_carrier
    (L : PointedRiemannianManifold.{u, uE, uH} I) (c : ℝ) (hc : 0 < c) :
    (L.scaleMetric c hc).M = L.M := rfl

@[simp] theorem PointedRiemannianManifold.scaleMetric_basepoint
    (L : PointedRiemannianManifold.{u, uE, uH} I) (c : ℝ) (hc : 0 < c) :
    (L.scaleMetric c hc).basepoint = L.basepoint := rfl

@[simp] theorem PointedRiemannianManifold.scaleMetric_metric
    (L : PointedRiemannianManifold.{u, uE, uH} I) (c : ℝ) (hc : 0 < c) :
    (L.scaleMetric c hc).metric = DifferentialGeometry.scaleMetric c hc L.metric := rfl

def PointedRiemannianSeq.scaleMetric
    (X : PointedRiemannianSeq.{u, uE, uH} I) (c : ℝ) (hc : 0 < c) :
    PointedRiemannianSeq.{u, uE, uH} I where
  obj k := (X.obj k).scaleMetric c hc

@[simp] theorem PointedRiemannianSeq.scaleMetric_obj
    (X : PointedRiemannianSeq.{u, uE, uH} I) (c : ℝ) (hc : 0 < c) (k : ℕ) :
    (X.scaleMetric c hc).obj k = (X.obj k).scaleMetric c hc := rfl

variable {X : PointedRiemannianSeq.{u, uE, uH} I}
  {L : PointedRiemannianManifold.{u, uE, uH} I} {f : ℕ → ℕ}

def PointedRiemannianConvergenceMaps.scaleMetric
    (Phi : PointedRiemannianConvergenceMaps X L f) (c : ℝ) (hc : 0 < c) :
    PointedRiemannianConvergenceMaps (X.scaleMetric c hc) (L.scaleMetric c hc) f where
  partialDiffeomorph := Phi.partialDiffeomorph
  source_exhausts := Phi.source_exhausts
  base_mem := Phi.base_mem
  basepoint_map := Phi.basepoint_map

@[simp] theorem PointedRiemannianConvergenceMaps.scaleMetric_partialDiffeomorph
    (Phi : PointedRiemannianConvergenceMaps X L f) (c : ℝ) (hc : 0 < c) (k : ℕ) :
    (Phi.scaleMetric c hc).partialDiffeomorph k = Phi.partialDiffeomorph k := rfl

@[simp] theorem PointedRiemannianConvergenceMaps.scaleMetric_source
    (Phi : PointedRiemannianConvergenceMaps X L f) (c : ℝ) (hc : 0 < c) (k : ℕ) :
    (Phi.scaleMetric c hc).source k = Phi.source k := rfl

@[simp] theorem PointedRiemannianConvergenceMaps.scaleMetric_target
    (Phi : PointedRiemannianConvergenceMaps X L f) (c : ℝ) (hc : 0 < c) (k : ℕ) :
    (Phi.scaleMetric c hc).target k = Phi.target k := rfl

@[simp] theorem PointedRiemannianConvergenceMaps.scaleMetric_map
    (Phi : PointedRiemannianConvergenceMaps X L f) (c : ℝ) (hc : 0 < c) (k : ℕ) :
    (Phi.scaleMetric c hc).map k = Phi.map k := rfl

variable [FiniteDimensional ℝ E]

def MetricSourceData.scaleMetric
    {Phi : PointedRiemannianConvergenceMaps X L f} {k : ℕ}
    (D : MetricSourceData Phi k) (c : ℝ) (hc : 0 < c) :
    MetricSourceData (Phi.scaleMetric c hc) k where
  topology := D.topology
  charted := D.charted
  t2 := D.t2
  smooth := D.smooth
  sigmaCompact := D.sigmaCompact
  limitMetric := @DifferentialGeometry.scaleMetric E _ _ H _ I (MetricSourceDomain Phi k)
    D.topology D.charted D.smooth c hc D.limitMetric
  pullbackMetric := @DifferentialGeometry.scaleMetric E _ _ H _ I (MetricSourceDomain Phi k)
    D.topology D.charted D.smooth c hc D.pullbackMetric
  referenceMetric := @DifferentialGeometry.scaleMetric E _ _ H _ I (MetricSourceDomain Phi k)
    D.topology D.charted D.smooth c hc D.referenceMetric
  compact_preimage := D.compact_preimage
  limit_inner := by
    intro x v w
    exact congrArg (c * ·) (D.limit_inner x v w)
  pullback_inner := by
    intro x v w
    exact congrArg (c * ·) (D.pullback_inner x v w)

private theorem MetricSourceData.scaleMetric_derivNormSupOn_le
    {Phi : PointedRiemannianConvergenceMaps X L f} {k : ℕ}
    (D : MetricSourceData Phi k) (c : ℝ) (hc : 0 < c)
    {K : Set L.M} (hK : IsCompact K) (hKsrc : K ⊆ Phi.source k) (p : ℕ) :
    (D.scaleMetric c hc).derivNormSupOn K p ≤
      metricJetScaleLoss c p * D.derivNormSupOn K p := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : TopologicalSpace (MetricSourceDomain Phi k) := D.topology
  let : ChartedSpace H (MetricSourceDomain Phi k) := D.charted
  let : IsManifold I ∞ (MetricSourceDomain Phi k) := D.smooth
  let : T2Space (MetricSourceDomain Phi k) := D.t2
  exact @metricDerivNormSupOn_scale_all_le E _ _ _ H _ I (MetricSourceDomain Phi k)
    D.topology D.charted D.smooth D.t2 c hc (metricSourceCompactSet Phi k K)
    (D.compact_preimage K hK hKsrc) p D.pullbackMetric D.limitMetric D.referenceMetric

def MetricConvergenceData.scaleMetric
    {Phi : PointedRiemannianConvergenceMaps X L f}
    (C : MetricConvergenceData Phi) (c : ℝ) (hc : 0 < c) :
    MetricConvergenceData (Phi.scaleMetric c hc) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact {
    domain k := (C.domain k).scaleMetric c hc
    converges := by
      intro K hK p epsilon hepsilon
      have hA := metricJetScaleLoss_pos c p
      obtain ⟨N, hN⟩ := C.converges K hK p (epsilon / metricJetScaleLoss c p)
        (div_pos hepsilon hA)
      refine ⟨N, fun k hk => ?_⟩
      obtain ⟨hsource, hnorm⟩ := hN k hk
      refine ⟨hsource, ?_⟩
      have hbound := (C.domain k).scaleMetric_derivNormSupOn_le c hc hK hsource p
      exact hbound.trans_lt ((mul_lt_mul_of_pos_left hnorm hA).trans_eq
        (mul_div_cancel₀ epsilon hA.ne')) }

def PointedRiemannianConverges.scaleMetric
    {Phi : PointedRiemannianConvergenceMaps X L f}
    (C : PointedRiemannianConverges X L f Phi) (c : ℝ) (hc : 0 < c) :
    PointedRiemannianConverges (X.scaleMetric c hc) (L.scaleMetric c hc) f
      (Phi.scaleMetric c hc) where
  metrics := C.metrics.scaleMetric c hc

theorem CanonicalMetricCompactness.canonicalSourceData_scaleMetric
    (Phi : PointedRiemannianConvergenceMaps X L f) (c : ℝ) (hc : 0 < c) (k : ℕ) :
    (canonicalSourceData Phi k).scaleMetric c hc =
      canonicalSourceData (Phi.scaleMetric c hc) k := by
  unfold canonicalSourceData MetricSourceData.ofRestrictPullback
    MetricSourceData.ofCanonical MetricSourceData.scaleMetric
  congr 1

theorem MetricConvergenceData.scaleMetric_domain_eq_canonical
    {Phi : PointedRiemannianConvergenceMaps X L f}
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (c : ℝ) (hc : 0 < c) (k : ℕ) :
    (C.scaleMetric c hc).domain k =
      CanonicalMetricCompactness.canonicalSourceData (Phi.scaleMetric c hc) k := by
  change (C.domain k).scaleMetric c hc = _
  rw [hcanonical k, CanonicalMetricCompactness.canonicalSourceData_scaleMetric]

end DifferentialGeometry.CheegerGromovCompactness
