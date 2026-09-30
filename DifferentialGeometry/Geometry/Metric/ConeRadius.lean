import DifferentialGeometry.Geometry.Comparison.Distance.LocalSmoothness
import DifferentialGeometry.Geometry.Comparison.Distance.Eikonal
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Topology.Order.Real
import DifferentialGeometry.Geometry.Comparison.Distance.LocalSegmentSmoothness
import DifferentialGeometry.Geometry.Metric.ConeDistance
import DifferentialGeometry.Geometry.Metric.Distance.Differential
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import DifferentialGeometry.Geometry.Geodesic.Minimizing.MetricSegmentRegularity

section

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

private theorem exists_radial_anchor
    {M Y : Type*} [TopologicalSpace M] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph M (ℝ × Y)) {x : M} (hx : x ∈ e.source)
    {V : Set M} (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ b : ℝ, (e x).1 < b ∧
      ∃ p : M, p ∈ V ∩ e.source ∧ e p = (b, (e x).2) := by
  have hmem : e '' (V ∩ e.source) ∈ 𝓝 (e x) :=
    e.image_mem_nhds hx ((hV.inter e.open_source).mem_nhds ⟨hxV, hx⟩)
  have hline : ContinuousAt (fun b : ℝ => (b, (e x).2)) (e x).1 :=
    continuousAt_id.prodMk continuousAt_const
  have hpre : (fun b : ℝ => (b, (e x).2)) ⁻¹' (e '' (V ∩ e.source)) ∈
      𝓝 (e x).1 := hline.preimage_mem_nhds hmem
  obtain ⟨c, hrc, hc⟩ := exists_Ico_subset_of_mem_nhds hpre (exists_gt (e x).1)
  obtain ⟨b, hrb, hbc⟩ := exists_between hrc
  obtain ⟨p, hp, hep⟩ := hc ⟨hrb.le, hbc⟩
  exact ⟨b, hrb, p, hp, hep⟩

variable {E H M Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [PseudoMetricSpace Y]

theorem contMDiffOn_radius_of_riemannianEDistOf_cone
    (g : SmoothRiemannianMetric I M) (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpos : ∀ x ∈ e.source, 0 < (e x).1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      (riemannianEDistOf g x y).toReal = Metric.coneDistance (e x) (e y)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => (e x).1) e.source := by
  intro p hp
  obtain ⟨U, hU, hpU, hsmooth⟩ :=
    exists_open_contMDiff_riemannianEDistOf_sq g p
  obtain ⟨b, hab, p1, hp1, hep1⟩ := exists_radial_anchor e hp hU hpU
  have hsq (z : M) (hz : z ∈ U) :
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => (riemannianEDistOf g y z).toReal ^ 2) p := by
    exact (hsmooth.contMDiffAt ((hU.prod hU).mem_nhds ⟨hpU, hz⟩)).comp p
      (contMDiffAt_id.prodMk contMDiffAt_const)
  have hrad : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => (e y).1 ^ 2) p := by
    have hc : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun y => (b * (riemannianEDistOf g y p).toReal ^ 2 -
          (e p).1 * (riemannianEDistOf g y p1).toReal ^ 2) / (b - (e p).1) + (e p).1 * b) p :=
      ((contMDiffAt_const.mul (hsq p hpU)).sub
        (contMDiffAt_const.mul (hsq p1 hp1.1))).div_const (b - (e p).1)
          |>.add contMDiffAt_const
    apply hc.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hp] with y hy
    rw [riemannianEDistOf_comm g y p, hdist p hp y hy,
      hdist y hy p1 hp1.2, hep1]
    rw [Metric.coneDistance_comm (e y) (b, (e p).2)]
    simpa only [add_comm] using
      (Metric.coneDistance_recover_radius_sq (hpos p hp).le
        ((hpos p hp).trans hab).le hab.ne (e p).2 (hpos y hy).le)
  have hroot := (Real.contDiffAt_sqrt (sq_pos_of_pos (hpos p hp)).ne').contMDiffAt.comp p hrad
  apply (hroot.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [e.open_source.mem_nhds hp] with y hy
  exact (Real.sqrt_sq (hpos y hy).le).symm


theorem gradient_radius_normSq_eq_one_of_riemannianEDistOf_cone
    (g : SmoothRiemannianMetric I M) (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpos : ∀ x ∈ e.source, 0 < (e x).1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      (riemannianEDistOf g x y).toReal = Metric.coneDistance (e x) (e y))
    {p : M} (hp : p ∈ e.source) :
    g.inner p (Geometry.Operator.gradientFun g (fun y => (e y).1) p)
      (Geometry.Operator.gradientFun g (fun y => (e y).1) p) = 1 := by
  let r : M → ℝ := fun y => (e y).1
  have hr : MDifferentiableAt I 𝓘(ℝ, ℝ) r p :=
    ((contMDiffOn_radius_of_riemannianEDistOf_cone g e hpos hdist p hp).contMDiffAt
      (e.open_source.mem_nhds hp)).mdifferentiableAt (by simp)
  obtain ⟨U, hU, hpU, hsquared⟩ :=
    exists_open_contMDiff_riemannianEDistOf_sq g p
  obtain ⟨V, hV, hpV, heikonal⟩ :=
    exists_open_gradient_riemannianEDistOf_normSq_eq_one g p
  obtain ⟨b, hab, p1, hp1, hep1⟩ := exists_radial_anchor e hp (hU.inter hV) ⟨hpU, hpV⟩
  have hb : 0 < b := (hpos p hp).trans hab
  have hne : p ≠ p1 := by
    intro heq
    have hf := congrArg Prod.fst hep1
    rw [← heq] at hf
    exact hab.ne hf
  have hbase : (riemannianEDistOf g p p1).toReal = b - (e p).1 := by
    rw [hdist p hp p1 hp1.2, hep1, Metric.coneDistance]
    simp only [dist_self, min_eq_right Real.pi_pos.le, Real.cos_zero, mul_one]
    rw [show (e p).1 ^ 2 + b ^ 2 - 2 * (e p).1 * b = (b - (e p).1) ^ 2 by ring,
      Real.sqrt_sq (sub_pos.mpr hab).le]
  have hdSq : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y => (riemannianEDistOf g y p1).toReal ^ 2) p :=
    (hsquared.contMDiffAt ((hU.prod hU).mem_nhds ⟨hpU, hp1.1.1⟩)).comp p
      (contMDiffAt_id.prodMk contMDiffAt_const)
  have hd : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => (riemannianEDistOf g y p1).toReal) p := by
    have hpositive : 0 < (riemannianEDistOf g p p1).toReal := hbase ▸ sub_pos.mpr hab
    have h := (Real.contDiffAt_sqrt (sq_pos_of_pos hpositive).ne').contMDiffAt.comp p hdSq
    exact (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y =>
      (Real.sqrt_sq ENNReal.toReal_nonneg).symm)).mdifferentiableAt (by simp)
  have hsupport : ∀ᶠ y in 𝓝 p, b - (riemannianEDistOf g y p1).toReal ≤ r y := by
    filter_upwards [e.open_source.mem_nhds hp] with y hy
    have h : b - (e y).1 ≤ Metric.coneDistance (e y) (b, (e p).2) :=
      (le_abs_self (b - (e y).1)).trans (by
        simpa only [abs_sub_comm] using
          (Metric.abs_radius_sub_le_coneDistance (hpos y hy).le hb.le
            (x := e y) (y := (b, (e p).2))))
    rw [← hep1, ← hdist y hy p1 hp1.2] at h
    change b - (riemannianEDistOf g y p1).toReal ≤ (e y).1
    linarith
  have hgrad := Geometry.Topology.gradientFun_eq_of_differentiable_lower_support
    g hr (mdifferentiableAt_const.sub hd)
    (show b - (riemannianEDistOf g p p1).toReal = r p by rw [hbase]; dsimp [r]; ring) hsupport
  rw [hgrad]
  change g.inner p (Geometry.Operator.gradientFun g
    (fun y => b - (riemannianEDistOf g y p1).toReal) p)
    (Geometry.Operator.gradientFun g (fun y => b - (riemannianEDistOf g y p1).toReal) p) = 1
  rw [Geometry.Operator.gradientFun_sub g (f := fun _ => b) mdifferentiableAt_const hd,
    Geometry.Operator.gradientFun_const, zero_sub]
  simp only [map_neg, neg_apply, neg_neg]
  have h := heikonal p1 hp1.1.2 p hpV hne.symm
    (by simpa only [riemannianEDistOf_comm g p1] using hd)
  simpa only [riemannianEDistOf_comm g p1] using h

end DifferentialGeometry.Geometry.Riemannian

end

end

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Analysis.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  {Y : Type*} [PseudoMetricSpace Y]

omit [SigmaCompactSpace M] in
private theorem exists_radial_interval (e : OpenPartialHomeomorph M (ℝ × Y))
    {p : M} (hp : p ∈ e.source) :
    ∃ R : ℝ, 0 < R ∧ ∀ s ∈ Icc (-R) R, ((e p).1 + s, (e p).2) ∈ e.target := by
  have htarget : ∀ᶠ t : ℝ in 𝓝 0, ((e p).1 + t, (e p).2) ∈ e.target := by
    have hcont : Continuous (fun t : ℝ => ((e p).1 + t, (e p).2)) := by fun_prop
    have h0 : ((e p).1 + 0, (e p).2) ∈ e.target := by
      simpa only [add_zero] using e.map_source hp
    exact hcont.continuousAt (e.open_target.mem_nhds h0)
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp htarget
  refine ⟨R / 2, half_pos hR, fun s hs => ?_⟩
  apply hball
  change dist s 0 < R
  rw [Real.dist_eq, sub_zero]
  exact (abs_le.mpr hs).trans_lt (half_lt_self hR)

omit [NeZero (Module.finrank ℝ E)] in
theorem contMDiffOn_radius_of_coneDistance
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpositive : ∀ z ∈ e.target, 0 < z.1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      dist x y = Metric.coneDistance (e x) (e y)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => (e x).1) e.source := by
  apply contMDiffOn_radius_of_riemannianEDistOf_cone g e
    (fun x hx => hpositive (e x) (e.map_source hx))
  intro x hx y hy
  simpa only [← hmetric, edist_dist, ENNReal.toReal_ofReal dist_nonneg] using hdist x hx y hy


private theorem radial_curve_calibration
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpositive : ∀ z ∈ e.target, 0 < z.1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      dist x y = Metric.coneDistance (e x) (e y))
    {p : M} (hp : p ∈ e.source) :
    let f : ℝ → M := fun s => e.symm ((e p).1 + s, (e p).2)
    let v : E := mfderiv 𝓘(ℝ, ℝ) I f 0 1
    ContMDiffAt 𝓘(ℝ, ℝ) I ∞ f 0 ∧ Geodesic.HasGeodesicEquationAt g f 0 ∧
      g.inner p v v = 1 ∧ mvfderiv (I := I) (fun x => (e x).1) p v = 1 := by
  let r := (e p).1
  let u := (e p).2
  let f : ℝ → M := fun s => e.symm (r + s, u)
  let ρ : M → ℝ := fun x => (e x).1
  obtain ⟨R, hR, hradial⟩ := exists_radial_interval e hp
  have hfmem (s : ℝ) (hs : s ∈ Icc (-R) R) : f s ∈ e.source :=
    e.map_target (hradial s hs)
  have hfeq (s : ℝ) (hs : s ∈ Icc (-R) R) : e (f s) = (r + s, u) :=
    e.right_inv (hradial s hs)
  have hf0 : f 0 = p := by
    dsimp only [f]
    rw [add_zero]
    exact e.left_inv hp
  have hfdist : ∀ s ∈ Icc (-R) R, ∀ v ∈ Icc (-R) R,
      dist (f s) (f v) = |s - v| := by
    intro s hs v hv
    rw [hdist _ (hfmem s hs) _ (hfmem v hv), hfeq s hs, hfeq v hv,
      Metric.coneDistance_same_direction]
    congr 1
    ring
  have hreg := contMDiffAt_and_geodesicEquationAt_of_metric_segment g hmetric f 0
    hR (by simpa only [zero_add] using hfdist)
  have hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ p :=
    ((contMDiffOn_radius_of_coneDistance g hmetric e hpositive hdist).contMDiffAt
      (e.open_source.mem_nhds hp)).mdifferentiableAt (by decide)
  let v : TangentSpace I p := (mfderiv 𝓘(ℝ, ℝ) I f 0 1 : E)
  have hv : g.inner p v v = 1 := by
    have hh := hreg.2.2
    change g.inner (f 0) (v : E) (v : E) = 1 at hh
    rwa [hf0] at hh
  have heq : (fun s => ρ (f s)) =ᶠ[𝓝 0] fun s => r + s := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hR] with s hs
    have hm : s ∈ Icc (-R) R := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
      exact ⟨(abs_lt.mp hs).1.le, (abs_lt.mp hs).2.le⟩
    exact congrArg Prod.fst (hfeq s hm)
  have hcomp := hasDerivAt_comp_mfderiv_along I ρ f 0
    (by simpa only [hf0] using hρ) (hreg.1.mdifferentiableAt (by decide))
  change HasDerivAt (fun s => ρ (f s)) (mvfderiv (I := I) ρ (f 0) (v : E)) 0 at hcomp
  rw [hf0] at hcomp
  have hrate : mvfderiv (I := I) ρ p v = 1 :=
    hcomp.unique (((hasDerivAt_id (0 : ℝ)).const_add r).congr_of_eventuallyEq heq)
  exact ⟨hreg.1, hreg.2.1, hv, hrate⟩

theorem gradient_radius_eq_radial_velocity_of_coneDistance
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpositive : ∀ z ∈ e.target, 0 < z.1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      dist x y = Metric.coneDistance (e x) (e y))
    {p : M} (hp : p ∈ e.source) :
    (gradientFun g (fun x => (e x).1) p : E) =
      (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => e.symm ((e p).1 + s, (e p).2)) 0 1 : E) := by
  let ρ : M → ℝ := fun x => (e x).1
  let v : TangentSpace I p :=
    (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => e.symm ((e p).1 + s, (e p).2)) 0 1 : E)
  have hcal := radial_curve_calibration g hmetric e hpositive hdist hp
  have hv : g.inner p v v = 1 := hcal.2.2.1
  have hrate : mvfderiv (I := I) ρ p v = 1 := hcal.2.2.2
  have hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ p :=
    ((contMDiffOn_radius_of_coneDistance g hmetric e hpositive hdist).contMDiffAt
      (e.open_source.mem_nhds hp)).mdifferentiableAt (by decide)
  have hlip : ∀ᶠ x in 𝓝 p, |ρ x - ρ p| ≤
      1 * (riemannianEDistOf g x p).toReal := by
    filter_upwards [e.open_source.mem_nhds hp] with x hx
    have h := Metric.abs_radius_sub_le_coneDistance
      (hpositive (e x) (e.map_source hx)).le (hpositive (e p) (e.map_source hp)).le
    rw [← hdist x hx p hp] at h
    simpa only [one_mul, ← hmetric, edist_dist, ENNReal.toReal_ofReal dist_nonneg] using h
  let G : TangentSpace I p := gradientFun g ρ p
  have hGv : g.inner p G v = 1 := (inner_gradientFun g ρ p v).trans hrate
  have hvG : g.inner p v G = 1 := (g.symm p v G).trans hGv
  have hGGnn : 0 ≤ g.inner p G G := metric_inner_self_nonneg g p G
  have hGG : g.inner p G G ≤ 1 := by
    have h := abs_mvfderiv_le_of_eventually_riemannian_distance_bound g ρ p 1 hρ hlip G
    rw [← inner_gradientFun g ρ p G, abs_of_nonneg hGGnn, one_mul] at h
    have hs := Real.sq_sqrt hGGnn
    have hm := mul_self_le_mul_self hGGnn h
    nlinarith only [h, hs, hm, Real.sqrt_nonneg (g.inner p G G)]
  have hsmall : g.inner p (G - v) (G - v) ≤ 0 := by
    simp only [map_sub, sub_apply, hGv, hvG, hv]
    linarith only [hGG]
  have hzero : G - v = 0 := by
    by_contra hne
    exact (not_lt_of_ge hsmall) (g.pos p (G - v) hne)
  exact sub_eq_zero.mp hzero

theorem mfderiv_radius_ne_zero_of_coneDistance
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpositive : ∀ z ∈ e.target, 0 < z.1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      dist x y = Metric.coneDistance (e x) (e y))
    {p : M} (hp : p ∈ e.source) :
    mfderiv I 𝓘(ℝ, ℝ) (fun x => (e x).1) p ≠ 0 := by
  have hrate := (radial_curve_calibration g hmetric e hpositive hdist hp).2.2.2
  intro hzero
  simp only [mvfderiv, hzero, ContinuousLinearMap.comp_zero] at hrate
  change (0 : ℝ) = 1 at hrate
  exact zero_ne_one hrate

omit [NeZero (Module.finrank ℝ E)] in
theorem gradient_radius_normSq_eq_one_of_coneDistance
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpositive : ∀ z ∈ e.target, 0 < z.1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      dist x y = Metric.coneDistance (e x) (e y))
    {p : M} (hp : p ∈ e.source) :
    g.inner p (gradientFun g (fun x => (e x).1) p)
      (gradientFun g (fun x => (e x).1) p) = 1 := by
  apply gradient_radius_normSq_eq_one_of_riemannianEDistOf_cone g e
    (fun x hx => hpositive (e x) (e.map_source hx)) ?_ hp
  intro x hx y hy
  simpa only [← hmetric, edist_dist, ENNReal.toReal_ofReal dist_nonneg] using hdist x hx y hy

end DifferentialGeometry.Geometry.Riemannian
