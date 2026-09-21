import DifferentialGeometry.Geometry.Comparison.Distance.LocalSegmentSmoothness
import DifferentialGeometry.Geometry.Metric.ConeDistance
import DifferentialGeometry.Geometry.Geodesic.Minimizing.MetricSegmentRegularity

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Riemannian
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

theorem mfderiv_radius_ne_zero_of_coneDistance
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpositive : ∀ z ∈ e.target, 0 < z.1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source,
      dist x y = Metric.coneDistance (e x) (e y))
    {p : M} (hp : p ∈ e.source) :
    mfderiv I 𝓘(ℝ, ℝ) (fun x => (e x).1) p ≠ 0 := by
  let r := (e p).1
  let u := (e p).2
  let f : ℝ → M := fun s => e.symm (r + s, u)
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
  have hfs := (contMDiffAt_and_geodesicEquationAt_of_metric_segment g hmetric f 0
    hR (by simpa only [zero_add] using hfdist)).1
  have hρ := (contMDiffOn_radius_of_coneDistance g hmetric e hpositive hdist).contMDiffAt
    (e.open_source.mem_nhds hp)
  have heq : (fun s => (e (f s)).1) =ᶠ[𝓝 0] fun s => r + s := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hR] with s hs
    have hm : s ∈ Icc (-R) R := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
      exact ⟨(abs_lt.mp hs).1.le, (abs_lt.mp hs).2.le⟩
    exact congrArg Prod.fst (hfeq s hm)
  intro hzero
  have hchain := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := 𝓘(ℝ, ℝ))
    (f := f) (g := fun x => (e x).1) 0
    (by simpa only [hf0] using hρ.mdifferentiableAt (by decide))
    (hfs.mdifferentiableAt (by decide))
  have hzero' : mfderiv I 𝓘(ℝ, ℝ) (fun x => (e x).1) (f 0) = 0 := by
    rw [hf0]
    exact hzero
  rw [hzero', ContinuousLinearMap.zero_comp] at hchain
  have hdf : fderiv ℝ (fun s => (e (f s)).1) 0 = 0 := by
    simpa only [mfderiv_eq_fderiv, Function.comp_def] using! hchain
  rw [heq.fderiv_eq] at hdf
  have hone : fderiv ℝ (fun s : ℝ => r + s) 0 1 = 1 := by
    simpa only [id_eq, ContinuousLinearMap.id_apply] using
      congrArg (fun D : ℝ →L[ℝ] ℝ => D 1)
        (((hasFDerivAt_id (0 : ℝ)).const_add r).fderiv)
  have hz := congrArg (fun D : ℝ →L[ℝ] ℝ => D 1) hdf
  exact one_ne_zero (hone.symm.trans hz)

end DifferentialGeometry.Geometry.Riemannian
