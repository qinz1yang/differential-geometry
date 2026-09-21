import DifferentialGeometry.Geometry.Comparison.Distance.LocalSegmentSmoothness
import DifferentialGeometry.Geometry.Metric.ConeDistance
import DifferentialGeometry.Geometry.Metric.Distance.Differential
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import DifferentialGeometry.Geometry.Geodesic.Minimizing.MetricSegmentRegularity

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

theorem contMDiffOn_radius_of_coneDistance
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpositive : ∀ z ∈ e.target, 0 < z.1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      dist x y = Metric.coneDistance (e x) (e y)) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => (e x).1) e.source := by
  intro p hp
  apply ContMDiffAt.contMDiffWithinAt
  let r := (e p).1
  let u := (e p).2
  have hr : 0 < r := hpositive (e p) (e.map_source hp)
  obtain ⟨R, hR, hinterval⟩ := exists_radial_interval e hp
  have hradial (s : ℝ) (hs : s ∈ Icc 0 R) : (r + s, u) ∈ e.target :=
    hinterval s ⟨(neg_nonpos.mpr hR.le).trans hs.1, hs.2⟩
  let f : ℝ → M := fun s => e.symm (r + s, u)
  have hfmem (s : ℝ) (hs : s ∈ Icc 0 R) : f s ∈ e.source :=
    e.map_target (hradial s hs)
  have hfeq (s : ℝ) (hs : s ∈ Icc 0 R) : e (f s) = (r + s, u) :=
    e.right_inv (hradial s hs)
  have hf0 : f 0 = p := by
    dsimp only [f]
    rw [add_zero]
    exact e.left_inv hp
  have hfdist : ∀ s ∈ Icc 0 R, ∀ v ∈ Icc 0 R,
      dist (f s) (f v) = |s - v| := by
    intro s hs v hv
    rw [hdist _ (hfmem s hs) _ (hfmem v hv), hfeq s hs, hfeq v hv,
      Metric.coneDistance_same_direction]
    congr 1
    ring
  obtain ⟨δ, hδ, hδR, hsm⟩ := exists_contMDiffAt_dist_of_metric_segment g hmetric f
    hR hfdist
  let a := r + δ / 3
  let b := r + 2 * δ / 3
  let A := f (δ / 3)
  let B := f (2 * δ / 3)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hb : 0 < b := by dsimp only [b]; positivity
  have hab : a ≠ b := by dsimp only [a, b]; linarith
  have hAs : δ / 3 ∈ Icc 0 R := ⟨by positivity, by linarith⟩
  have hBs : 2 * δ / 3 ∈ Icc 0 R := ⟨by positivity, by linarith⟩
  have hAmem : A ∈ e.source := hfmem _ hAs
  have hBmem : B ∈ e.source := hfmem _ hBs
  have hAe : e A = (a, u) := hfeq _ hAs
  have hBe : e B = (b, u) := hfeq _ hBs
  have hAsm : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => dist x A) p := by
    have h := hsm (δ / 3) ⟨by positivity, by linarith⟩
    rwa [hf0] at h
  have hBsm : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => dist x B) p := by
    have h := hsm (2 * δ / 3) ⟨by positivity, by linarith⟩
    rwa [hf0] at h
  have hidentity (x : M) (hx : x ∈ e.source) : (e x).1 ^ 2 = a * b +
      (b * dist x A ^ 2 - a * dist x B ^ 2) / (b - a) := by
    have h := Metric.coneDistance_recover_radius_sq ha.le hb.le hab u
      (hpositive (e x) (e.map_source hx)).le
    rw [← hAe, ← hBe, ← hdist A hAmem x hx, ← hdist B hBmem x hx,
      dist_comm A x, dist_comm B x] at h
    exact h
  have hsquare : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => (e x).1 ^ 2) p := by
    have h : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun x => a * b +
        (b * dist x A ^ 2 - a * dist x B ^ 2) / (b - a)) p := by
      exact contMDiffAt_const.add
        (((contMDiffAt_const.mul (hAsm.pow 2)).sub
          (contMDiffAt_const.mul (hBsm.pow 2))).div_const (b - a))
    apply h.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hp] with x hx
    exact hidentity x hx
  have hsqrt := (Real.contDiffAt_sqrt (pow_ne_zero 2 hr.ne')).contMDiffAt.comp p hsquare
  apply hsqrt.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hp] with x hx
  exact (Real.sqrt_sq (hpositive (e x) (e.map_source hx)).le).symm

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
  have heq := gradient_radius_eq_radial_velocity_of_coneDistance g hmetric e hpositive hdist hp
  erw [heq]
  exact (radial_curve_calibration g hmetric e hpositive hdist hp).2.2.1

end DifferentialGeometry.Geometry.Riemannian
