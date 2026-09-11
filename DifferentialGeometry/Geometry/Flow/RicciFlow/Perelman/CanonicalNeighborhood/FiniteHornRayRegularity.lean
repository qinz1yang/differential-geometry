import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornLocalCompletion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompleteTriangleEquality

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
section Local
variable {W : Type u} [TopologicalSpace W] [T2Space W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem regularity_of_complete_metric_segment [ConnectedSpace W]
    (g : SmoothRiemannianMetric I3 W) (hcomplete : RiemannianMetricComplete g)
    (f : ℝ → W) (t : ℝ) {R : ℝ} (hR : 0 < R)
    (hdist : ∀ s ∈ Icc (-R) R, ∀ v ∈ Icc (-R) R,
      riemannianEDistOf g (f (t + s)) (f (t + v)) = ENNReal.ofReal |s - v|) :
    ContMDiffAt 𝓘(ℝ, ℝ) I3 ∞ f t ∧ Geodesic.HasGeodesicEquationAt g f t := by
  let : IsManifold I3 1 W := IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace W := Manifold.metrizableSpace I3 W
  let : T3Space W := inferInstance
  let : RiemannianBundle (fun x : W => TangentSpace I3 x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle ThreeSpace (fun x : W => TangentSpace I3 x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace W := EMetricSpace.ofRiemannianMetric I3 W
  let : CompleteSpace W := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I3) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  let L : ℝ := min R (expDiffeoRadius g hEnorm (f t)) / 2
  have hL : 0 < L := half_pos (lt_min hR (expDiffeoRadius_pos g hEnorm (f t)))
  have hLR : L < R := (half_lt_self
    (lt_min hR (expDiffeoRadius_pos g hEnorm (f t)))).trans_le (min_le_left _ _)
  have hLe : L < expDiffeoRadius g hEnorm (f t) := (half_lt_self
    (lt_min hR (expDiffeoRadius_pos g hEnorm (f t)))).trans_le (min_le_right _ _)
  let segment (s : Icc (-L) L) : W := f (t + s)
  obtain ⟨v, _hv, hsegment⟩ := exists_intrinsicGeodesic_eq_centered_metric_segment g hEnorm
    hL segment (by simpa only [segment, add_zero] using hLe) (by
      intro s v
      rw [← riemannianEDistOf_eq_riemannianEDist g hEnorm]
      exact hdist s ⟨by linarith [s.property.1], by linarith [s.property.2]⟩
        v ⟨by linarith [v.property.1], by linarith [v.property.2]⟩)
  simp only [segment] at hsegment
  let gamma (s : ℝ) : W := intrinsicGeodesic g hEnorm (f (t + 0)) v (s - t)
  have heq : f =ᶠ[𝓝 t] gamma := by
    filter_upwards [Metric.ball_mem_nhds t hL] with s hs
    have habs : |s - t| < L := by simpa only [Metric.mem_ball, Real.dist_eq] using hs
    have h := hsegment ⟨s - t, ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2.le⟩⟩
    simpa only [gamma, add_sub_cancel] using h
  have hsmooth : ContMDiff 𝓘(ℝ, ℝ) I3 ∞ gamma :=
    (intrinsicGeodesic_contMDiff g hEnorm (f (t + 0)) v).comp (contMDiff_id.sub contMDiff_const)
  have hgeo : Geodesic.HasGeodesicEquationAt g gamma t := by
    have h := Geodesic.isGeodesic_comp_add
      (intrinsicGeodesic_isGeodesic g hEnorm (f (t + 0)) v) (-t) t
    simpa only [gamma, sub_eq_add_neg] using h
  exact ⟨hsmooth.contMDiffAt.congr_of_eventuallyEq heq,
    Geodesic.HasGeodesicEquationAt.congr_of_eventuallyEq_at heq.eq_of_nhds heq hgeo⟩

omit [SigmaCompactSpace W] [T2Space W] in
private theorem geodesicEquationAt_of_metric_eqOn
    (g g' : SmoothRiemannianMetric I3 W) {U : Set W} (hU : IsOpen U)
    (heq : ∀ z ∈ U, g'.inner z = g.inner z) {f : ℝ → W} {t : ℝ} (ht : f t ∈ U)
    (hgeo : Geodesic.HasGeodesicEquationAt g' f t) :
    Geodesic.HasGeodesicEquationAt g f t := by
  obtain ⟨v, a, hv, hev, ha, halg⟩ := hgeo
  refine ⟨v, a, hv, hev, ha, ?_⟩
  have hC : Geodesic.chartChristoffelContraction g' (f t) v v (extChartAt I3 (f t) (f t)) =
      Geodesic.chartChristoffelContraction g (f t) v v (extChartAt I3 (f t) (f t)) := by
    simp only [Geodesic.chartChristoffelContraction, chartChristoffel_congr_metric g g' hU heq ht]
  rwa [hC] at halg

end Local

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

theorem finiteHorn_endRay_smooth_geodesic
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : EndRay H.endpoint,
      ContMDiffOn 𝓘(ℝ, ℝ) I3 ∞ a.point (Ioo 0 (min a.length d)) ∧
      Geodesic.IsGeodesicOn g a.point (Ioo 0 (min a.length d)) := by
  obtain ⟨d, hd, hlocal⟩ := finiteHorn_exists_local_complete_metric g H
  let : ConnectedSpace W := connectedSpace_iff_univ.mpr H.tube.isConnected_univ
  refine ⟨d, hd, ?_⟩
  intro a
  have hpoint (t : ℝ) (ht : t ∈ Ioo 0 (min a.length d)) :
      ContMDiffAt 𝓘(ℝ, ℝ) I3 ∞ a.point t ∧
      Geodesic.HasGeodesicEquationAt g a.point t := by
    have htlength : t < a.length := ht.2.trans_le (min_le_left _ _)
    have htd : t < d := ht.2.trans_le (min_le_right _ _)
    have htrad : dist (a.point t : UniformSpace.Completion W) H.endpoint < d := by
      rw [a.radial t ⟨ht.1, htlength.le⟩]
      exact htd
    obtain ⟨g', r, U, hr, hcomplete, hU, hbuffer, heq, _hle, hdist⟩ := hlocal (a.point t) htrad
    let R : ℝ := min t (min (a.length - t) r) / 2
    have hmin : 0 < min t (min (a.length - t) r) :=
      lt_min ht.1 (lt_min (sub_pos.mpr htlength) hr)
    have hR : 0 < R := half_pos hmin
    have hRt : R < t := (half_lt_self hmin).trans_le (min_le_left _ _)
    have hRl : R < a.length - t := (half_lt_self hmin).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
    have hRr : R < r := (half_lt_self hmin).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
    have hparam (s : ℝ) (hs : s ∈ Icc (-R) R) : t + s ∈ Ioc 0 a.length :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hball (s : ℝ) (hs : s ∈ Icc (-R) R) : a.point (t + s) ∈ Metric.ball (a.point t) r := by
      change dist (a.point (t + s)) (a.point t) < r
      rw [a.minimizing (t + s) (hparam s hs) t ⟨ht.1, htlength.le⟩, add_sub_cancel_left]
      exact (abs_le.mpr hs).trans_lt hRr
    have hmetric : ∀ s ∈ Icc (-R) R, ∀ v ∈ Icc (-R) R,
        riemannianEDistOf g' (a.point (t + s)) (a.point (t + v)) = ENNReal.ofReal |s - v| := by
      intro s hs v hv
      rw [hdist _ (hball s hs) _ (hball v hv),
        a.minimizing (t + s) (hparam s hs) (t + v) (hparam v hv)]
      congr 2
      ring
    obtain ⟨hsmooth, hgeo⟩ := regularity_of_complete_metric_segment g' hcomplete a.point t hR hmetric
    have hpU : a.point t ∈ U := hbuffer (by
      change dist (a.point t) (a.point t) ≤ 4 * r
      rw [dist_self]
      positivity)
    exact ⟨hsmooth, geodesicEquationAt_of_metric_eqOn g g' hU heq hpU hgeo⟩
  exact ⟨fun t ht => (hpoint t ht).1.contMDiffWithinAt, fun t ht => (hpoint t ht).2⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
