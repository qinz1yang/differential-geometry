import DifferentialGeometry.Geometry.Geodesic.Minimizing.TriangleEquality
import DifferentialGeometry.Geometry.Metric.Distance.LocalCompletion
import DifferentialGeometry.Geometry.Geodesic.Naturality.MetricLocality
import DifferentialGeometry.Geometry.Geodesic.EquationGerm
import DifferentialGeometry.Geometry.Comparison.Distance.EndpointRate

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section Complete
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem regularity_of_complete_metric_segment
    (g : SmoothRiemannianMetric I M) (hcomplete : RiemannianMetricComplete g)
    (f : ℝ → M) (t : ℝ) {R : ℝ} (hR : 0 < R)
    (hdist : ∀ s ∈ Icc (-R) R, ∀ v ∈ Icc (-R) R,
      riemannianEDistOf g (f (t + s)) (f (t + v)) = ENNReal.ofReal |s - v|) :
    ContMDiffAt 𝓘(ℝ, ℝ) I ∞ f t ∧ Geodesic.HasGeodesicEquationAt g f t := by
  let : IsManifold I 1 M := IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  let L : ℝ := min R (expDiffeoRadius g hEnorm (f t)) / 2
  have hL : 0 < L := half_pos (lt_min hR (expDiffeoRadius_pos g hEnorm (f t)))
  have hLR : L < R := (half_lt_self
    (lt_min hR (expDiffeoRadius_pos g hEnorm (f t)))).trans_le (min_le_left _ _)
  have hLe : L < expDiffeoRadius g hEnorm (f t) := (half_lt_self
    (lt_min hR (expDiffeoRadius_pos g hEnorm (f t)))).trans_le (min_le_right _ _)
  let segment (s : Icc (-L) L) : M := f (t + s)
  obtain ⟨v, _hv, hsegment⟩ := exists_intrinsicGeodesic_eq_centered_metric_segment g hEnorm
    hL segment (by simpa only [segment, add_zero] using hLe) (by
      intro s v
      rw [← riemannianEDistOf_eq_riemannianEDist g hEnorm]
      exact hdist s ⟨by linarith [s.property.1], by linarith [s.property.2]⟩
        v ⟨by linarith [v.property.1], by linarith [v.property.2]⟩)
  simp only [segment] at hsegment
  let gamma (s : ℝ) : M := intrinsicGeodesic g hEnorm (f (t + 0)) v (s - t)
  have heq : f =ᶠ[𝓝 t] gamma := by
    filter_upwards [Metric.ball_mem_nhds t hL] with s hs
    have habs : |s - t| < L := by simpa only [Metric.mem_ball, Real.dist_eq] using hs
    have h := hsegment ⟨s - t, ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2.le⟩⟩
    simpa only [gamma, add_sub_cancel] using h
  have hsmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma :=
    (intrinsicGeodesic_contMDiff g hEnorm (f (t + 0)) v).comp (contMDiff_id.sub contMDiff_const)
  have hgeo : Geodesic.HasGeodesicEquationAt g gamma t := by
    have h := Geodesic.isGeodesic_comp_add
      (intrinsicGeodesic_isGeodesic g hEnorm (f (t + 0)) v) (-t) t
    simpa only [gamma, sub_eq_add_neg] using h
  exact ⟨hsmooth.contMDiffAt.congr_of_eventuallyEq heq,
    Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at heq.eq_of_nhds heq hgeo⟩

end Complete

section Metric
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem contMDiffAt_and_geodesicEquationAt_of_metric_segment
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (f : ℝ → M) (t : ℝ) {R : ℝ} (hR : 0 < R)
    (hdist : ∀ s ∈ Icc (-R) R, ∀ v ∈ Icc (-R) R,
      dist (f (t + s)) (f (t + v)) = |s - v|) :
    ContMDiffAt 𝓘(ℝ, ℝ) I ∞ f t ∧ Geodesic.HasGeodesicEquationAt g f t ∧
      g.inner (f t) (mfderiv 𝓘(ℝ, ℝ) I f t 1) (mfderiv 𝓘(ℝ, ℝ) I f t 1) = 1 := by
  obtain ⟨g', r, U, hr, hcomplete, hU, hbuffer, heq, _, hlocal⟩ :=
    exists_riemannianMetricComplete_eqOn_ball g hmetric (f t)
  let S := min R r / 2
  have hS : 0 < S := half_pos (lt_min hR hr)
  have hSR : S < R := (half_lt_self (lt_min hR hr)).trans_le (min_le_left _ _)
  have hSr : S < r := (half_lt_self (lt_min hR hr)).trans_le (min_le_right _ _)
  have hparam (s : ℝ) (hs : s ∈ Icc (-S) S) : s ∈ Icc (-R) R :=
    ⟨by linarith only [hs.1, hSR], hs.2.trans hSR.le⟩
  have hball (s : ℝ) (hs : s ∈ Icc (-S) S) : f (t + s) ∈ Metric.ball (f t) r := by
    change dist (f (t + s)) (f t) < r
    have h := hdist s (hparam s hs) 0 ⟨by linarith only [hR], hR.le⟩
    rw [add_zero, sub_zero] at h
    rw [h]
    exact (abs_le.mpr hs).trans_lt hSr
  have hd : ∀ s ∈ Icc (-S) S, ∀ v ∈ Icc (-S) S,
      riemannianEDistOf g' (f (t + s)) (f (t + v)) = ENNReal.ofReal |s - v| := by
    intro s hs v hv
    rw [hlocal _ (hball s hs) _ (hball v hv), hdist s (hparam s hs) v (hparam v hv)]
  obtain ⟨hsmooth, hgeo⟩ := regularity_of_complete_metric_segment g' hcomplete f t hS hd
  have hftU : f t ∈ U := hbuffer (by
    change dist (f t) (f t) ≤ 4 * r
    rw [dist_self]
    positivity)
  have hgeo' : Geodesic.HasGeodesicEquationAt g f t := by
    apply (Geodesic.hasGeodesicEquationAt_iff_of_metric_eventuallyEq g g' ?_).mpr hgeo
    filter_upwards [hU.mem_nhds hftU] with x hx
    intro v w
    rw [heq x hx]
  refine ⟨hsmooth, hgeo', ?_⟩
  have hspeed := riemannianEDistOf_div_tendsto_speed g f t
    (hsmooth.mdifferentiableAt (by decide))
  have hlimit : Tendsto
      (fun h : ℝ => (riemannianEDistOf g (f (t + h)) (f t)).toReal / h)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioc_mem_nhdsGT hR] with h hh
    have hdist' := hdist h ⟨by linarith only [hh.1, hR], hh.2⟩
      0 ⟨by linarith only [hR], hR.le⟩
    rw [add_zero, sub_zero, abs_of_pos hh.1] at hdist'
    rw [← hmetric, edist_dist, ENNReal.toReal_ofReal dist_nonneg, hdist', div_self hh.1.ne']
  have hsqrt := tendsto_nhds_unique hspeed hlimit
  calc
    _ = (Real.sqrt (g.inner (f t) (mfderiv 𝓘(ℝ, ℝ) I f t 1)
        (mfderiv 𝓘(ℝ, ℝ) I f t 1))) ^ 2 := (Real.sq_sqrt (metric_inner_self_nonneg g _ _)).symm
    _ = 1 := (congrArg (fun x : ℝ => x ^ 2) hsqrt).trans (one_pow 2)

section Intrinsic
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem eqOn_intrinsicGeodesic_of_metric_segment
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (f : ℝ → M) {R : ℝ} (hR : 0 < R)
    (hdist : ∀ s ∈ Icc (-R) R, ∀ v ∈ Icc (-R) R, dist (f s) (f v) = |s - v|) :
    EqOn f (intrinsicGeodesic g hEnorm (f 0) (mfderiv 𝓘(ℝ, ℝ) I f 0 1)) (Ioo (-R) R) := by
  have hmetric (x y : M) : edist x y = riemannianEDistOf g x y := by
    rw [riemannianEDistOf_eq_riemannianEDist g hEnorm]
    exact IsRiemannianManifold.out x y
  have hreg (t : ℝ) (ht : t ∈ Ioo (-R) R) :
      ContMDiffAt 𝓘(ℝ, ℝ) I ∞ f t ∧ Geodesic.HasGeodesicEquationAt g f t := by
    let δ := min (R - t) (R + t) / 2
    have hmin : 0 < min (R - t) (R + t) := lt_min (sub_pos.mpr ht.2) (by linarith [ht.1])
    have hδ : 0 < δ := half_pos hmin
    have hδright : δ < R - t := (half_lt_self hmin).trans_le (min_le_left _ _)
    have hδleft : δ < R + t := (half_lt_self hmin).trans_le (min_le_right _ _)
    have hparam (s : ℝ) (hs : s ∈ Icc (-δ) δ) : t + s ∈ Icc (-R) R :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hh := contMDiffAt_and_geodesicEquationAt_of_metric_segment g hmetric f t hδ (by
      intro s hs v hv
      rw [hdist _ (hparam s hs) _ (hparam v hv)]
      congr 1
      ring)
    exact ⟨hh.1, hh.2.1⟩
  let v : TangentSpace I (f 0) := mfderiv 𝓘(ℝ, ℝ) I f 0 1
  apply geo_eqOn_of_initial g isOpen_Ioo (convex_Ioo (-R) R).isPreconnected
    ⟨by linarith, hR⟩ (fun t ht => (hreg t ht).2)
    ((intrinsicGeodesic_isGeodesic g hEnorm (f 0) v).isGeodesicOn _)
    (fun t ht => (hreg t ht).1.continuousAt.continuousWithinAt)
    (intrinsicGeodesic_contMDiff g hEnorm (f 0) v).continuous.continuousOn
    (intrinsicGeodesic_zero g hEnorm (f 0) v).symm
  exact (intrinsicGeodesic_mfderiv_zero g hEnorm (f 0) v).symm

end Intrinsic

end Metric

end DifferentialGeometry.Geometry.Riemannian
