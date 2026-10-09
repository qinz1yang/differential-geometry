import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.PositiveCurvature
import DifferentialGeometry.Geometry.Metric.ConeChart.Coordinates
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Mathlib.Analysis.Normed.Module.RCLike.Real
import DifferentialGeometry.Geometry.Comparison.Toponogov.PuncturedConeConvergence
import DifferentialGeometry.Geometry.Metric.ConeChart.Construction
import DifferentialGeometry.Geometry.Metric.Distance.Topology
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.MapDistance
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.InverseComposition
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphRange

set_option autoImplicit false

noncomputable section

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

universe v

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

attribute [local instance] ConeChart.topology ConeChart.charted ConeChart.smooth
  ConeChart.t2 ConeChart.sigmaCompact

private theorem coneChart_false_of_norm_lt
    (c : ℝ) (hc : 0 < c) {U : Set E3}
    (C : ConeChart.{0, 0, 0, v} 2 (scaleMetric c hc metric) U)
    {x : E3} (hx : x ∈ U) (hL : ‖x‖ < transitionEnd) : False := by
  have hxT : x ∈ C.map.target := C.target_eq.symm ▸ hx
  let z := C.map.symm x
  have hz : z ∈ C.map.source := C.map.map_target hxT
  have hzx : C.map z = x := C.map.right_inv hxT
  let a : TangentSpace (𝓡 2) z.2 := EuclideanSpace.single 0 1
  have ha : a ≠ 0 := by
    intro h
    have h0 := congrArg (fun b : EuclideanSpace ℝ (Fin 2) => b 0) h
    change (1 : ℝ) = 0 at h0
    norm_num at h0
  let u : TangentSpace (𝓡 3) (C.map z) :=
    mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) C.map z (0, a)
  let w : TangentSpace (𝓡 3) (C.map z) :=
    mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) C.map z (1, 0)
  have h00 : C.metric.inner z.2 0 0 = 0 := map_zero _
  have ha0 : C.metric.inner z.2 a 0 = 0 := map_zero _
  have huu : (scaleMetric c hc metric).inner (C.map z) u u =
      z.1 ^ 2 * C.metric.inner z.2 a a := by
    simpa only [u, zero_mul, zero_add] using C.radial_metric z hz (0, a) (0, a)
  have hww : (scaleMetric c hc metric).inner (C.map z) w w = 1 := by
    have h := C.radial_metric z hz (1, 0) (1, 0)
    erw [h00] at h
    simpa only [w, one_mul, mul_zero, add_zero] using h
  have huw : (scaleMetric c hc metric).inner (C.map z) u w = 0 := by
    have h := C.radial_metric z hz (0, a) (1, 0)
    erw [ha0] at h
    simpa only [u, w, zero_mul, mul_zero, add_zero] using h
  have hgram : 0 < (scaleMetric c hc metric).inner (C.map z) u u *
      (scaleMetric c hc metric).inner (C.map z) w w -
        ((scaleMetric c hc metric).inner (C.map z) u w) ^ 2 := by
    rw [huu, hww, huw]
    simpa only [mul_one, zero_pow (by decide : 2 ≠ 0), sub_zero] using
      mul_pos (sq_pos_of_pos (C.positive_radius z hz)) (C.metric.pos z.2 a ha)
  have hgram0 : 0 < metric.inner (C.map z) u u * metric.inner (C.map z) w w -
      (metric.inner (C.map z) u w) ^ 2 := by
    simp only [scaleMetric_inner] at hgram
    have heq : c * metric.inner (C.map z) u u * (c * metric.inner (C.map z) w w) -
        (c * metric.inner (C.map z) u w) ^ 2 =
        c ^ 2 * (metric.inner (C.map z) u u * metric.inner (C.map z) w w -
          (metric.inner (C.map z) u w) ^ 2) := by ring
    rw [heq] at hgram
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hc)).mp hgram
  have hpos : 0 < metricRm04StandardAt (scaleMetric c hc metric) (C.map z) u w w u := by
    rw [metricRmStandard_scale]
    exact mul_pos hc (metricRm04_pos (hzx ▸ hL) u w hgram0)
  have hzero := DifferentialGeometry.Geometry.Riemannian.ConeChart.radial_curvature_zero
    C hz u w u
  exact (ne_of_gt hpos) hzero

theorem norm_gt_transitionEnd_of_coneChart
    (c : ℝ) (hc : 0 < c) {U : Set E3}
    (C : ConeChart.{0, 0, 0, v} 2 (scaleMetric c hc metric) U)
    {x : E3} (hx : x ∈ U) : transitionEnd < ‖x‖ := by
  by_contra h
  have hL : ‖x‖ ≤ transitionEnd := le_of_not_gt h
  have hU : IsOpen U := C.target_eq ▸ C.map.open_target
  have hclosure : x ∈ closure (Metric.ball (0 : E3) transitionEnd) := by
    rw [closure_ball _ transitionEnd_pos.ne']
    simpa only [Metric.mem_closedBall, dist_zero_right] using hL
  obtain ⟨y, hyU, hyball⟩ := mem_closure_iff_nhds.mp hclosure U (hU.mem_nhds hx)
  exact coneChart_false_of_norm_lt c hc C hyU
    (by simpa only [Metric.mem_ball, dist_zero_right] using hyball)

theorem norm_gt_transitionEnd_of_coneChart_restrictOpen
    (W : TopologicalSpace.Opens E3) (c : ℝ) (hc : 0 < c) {U : Set W}
    (C : ConeChart.{0, 0, 0, v} 2 (scaleMetric c hc (metric.restrictOpen W)) U)
    {x : W} (hx : x ∈ U) : transitionEnd < ‖(x : E3)‖ := by
  let j := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := 𝓡 3) W ⟨x⟩
  let Φ := C.map.trans j
  have hj : j.source = Set.univ := W.openPartialHomeomorphSubtypeCoe_source _
  have hderiv (z : ℝ × C.surface) :
      mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) Φ z =
        mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3) C.map z := by
    change mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 3)
      ((Subtype.val : W → E3) ∘ C.map) z = _
    exact DifferentialGeometry.mfderiv_subtypeVal_comp C.map z
  let CA : ConeChart.{0, 0, 0, v} 2 (scaleMetric c hc metric) Φ.target := {
    surface := C.surface
    topology := C.topology
    charted := C.charted
    smooth := C.smooth
    t2 := C.t2
    sigmaCompact := C.sigmaCompact
    metric := C.metric
    map := Φ
    positive_radius := fun z hz => C.positive_radius z hz.1
    target_eq := rfl
    radial_metric := by
      intro z hz u w
      rw [hderiv]
      exact C.radial_metric z hz.1 u w }
  have hxT : x ∈ C.map.target := C.target_eq.symm ▸ hx
  have hz : C.map.symm x ∈ Φ.source := by
    refine ⟨C.map.map_target hxT, ?_⟩
    change C.map (C.map.symm x) ∈ j.source
    rw [hj]
    exact Set.mem_univ _
  have hmem : (x : E3) ∈ Φ.target := by
    have h := Φ.map_source hz
    change ((C.map (C.map.symm x) : W) : E3) ∈ Φ.target at h
    erw [C.map.right_inv hxT] at h
    exact h
  exact norm_gt_transitionEnd_of_coneChart c hc CA hmem


open Set Filter in
open scoped _root_.Topology in
theorem rescaled_cone_limit_exclusion
    (V : TopologicalSpace.Opens E3) (hV : PreconnectedSpace V) (c : ℝ) (hc : 0 < c) :
    let _ : PreconnectedSpace V := hV
    let g := scaleMetric c hc (metric.restrictOpen V)
    let _ : PseudoMetricSpace V := g.toPseudoMetricSpace
    let _ : MetricSpace V := MetricSpace.ofT0PseudoMetricSpace V
    ∀ p : V, ‖p.val‖ ≤ transitionEnd →
    ∀ {W : Type*} [MetricSpace W] {q : UniformSpace.Completion W} {d : ℝ},
    DifferentialGeometry.Toponogov.PuncturedConeApproximation q d →
    ∀ (x : ℕ → W) (maps : ℕ → V → W) (rho : ℕ → ℝ),
    (∀ n, 0 < rho n) → Filter.Tendsto rho Filter.atTop (𝓝 0) →
    Filter.Tendsto (fun n => dist (maps n p) (x n) / rho n) Filter.atTop (𝓝 0) →
    ∀ {R lower B : ℝ}, 0 < R → 0 < lower →
    IsCompact (Metric.closedBall p R) →
    (∀ᶠ n in Filter.atTop, dist (x n : UniformSpace.Completion W) q / rho n ∈ Icc lower B) →
    (∀ᶠ n in Filter.atTop, Metric.closedBall (maps n p) (R / 4 * rho n) ⊆
      maps n '' Metric.closedBall p R) →
    (∀ eps : ℝ, 0 < eps → ∀ᶠ n in Filter.atTop,
      ∀ a ∈ Metric.closedBall p R, ∀ b ∈ Metric.closedBall p R,
        |dist (maps n a) (maps n b) / rho n - dist a b| < eps) → False := by
  let _ : PreconnectedSpace V := hV
  dsimp only
  let g := scaleMetric c hc (metric.restrictOpen V)
  let _ : PseudoMetricSpace V := g.toPseudoMetricSpace
  let _ : MetricSpace V := MetricSpace.ofT0PseudoMetricSpace V
  intro p hp W instW q d cone x maps rho hrho hrho0 hoffset R lower B hR hlower
    hcompact hcenter hcover hdist
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) V.isOpen)
  have hcenter' : ∀ᶠ n in Filter.atTop,
      dist (maps n p : UniformSpace.Completion W) q / rho n ∈ Icc (lower / 2) (B + 1) := by
    filter_upwards [hcenter, hoffset.eventually (Iio_mem_nhds
      (lt_min (half_pos hlower) zero_lt_one))] with n hn hsmall
    have hdist : |dist (maps n p : UniformSpace.Completion W) q -
        dist (x n : UniformSpace.Completion W) q| ≤ dist (maps n p) (x n) := by
      simpa only [UniformSpace.Completion.dist_eq] using
        abs_dist_sub_le (maps n p : UniformSpace.Completion W) (x n) q
    have herror : |dist (maps n p : UniformSpace.Completion W) q / rho n -
        dist (x n : UniformSpace.Completion W) q / rho n| ≤
          dist (maps n p) (x n) / rho n := by
      rw [← sub_div, abs_div, abs_of_pos (hrho n)]
      exact div_le_div_of_nonneg_right hdist (hrho n).le
    have hlo := (abs_le.mp herror).1
    have hup := (abs_le.mp herror).2
    have hhalf := hsmall.trans_le (min_le_left _ _)
    have hone := hsmall.trans_le (min_le_right _ _)
    constructor <;> linarith [hn.1, hn.2]
  let _ := cone.angles.metricSpace
  obtain ⟨e, he, hpositive, hmetric⟩ := cone.exists_cone_coordinates_of_rescaled_convergence
    p (fun n => maps n p) maps rho hrho hrho0 (fun _ => rfl) hR (half_pos hlower)
      hcompact hcenter' hcover hdist
  obtain ⟨U, hpU, _, ⟨chart⟩⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_cone_chart_of_coneDistance g
      (fun _ _ => rfl) e hpositive hmetric (m := 2) (by simp) he
  exact (norm_gt_transitionEnd_of_coneChart_restrictOpen V c hc chart hpU).not_ge hp


open Set Filter in
open scoped _root_.Topology in
theorem rescaled_cone_exclusion_of_metric_cp_convergence
    (V : TopologicalSpace.Opens E3) (hV : PreconnectedSpace V)
    (c : ℝ) (hc : 0 < c) (p : V) (hp : ‖p.val‖ ≤ transitionEnd)
    {W : Type*} [MetricSpace W] [ChartedSpace E3 W] [IsManifold (𝓡 3) ∞ W]
    (h : SmoothRiemannianMetric (𝓡 3) W)
    (hmetric : ∀ x y : W, edist x y = riemannianEDistOf h x y)
    (A : ℕ → ℝ) (hA : ∀ n, 0 < A n) (hAtop : Tendsto A atTop atTop)
    (Phi : ℕ → V → W)
    (hPhi : ∀ n, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (Phi n))
    (hinj : ∀ n, Function.Injective (Phi n))
    {K : Set V} (hK : IsCompact K) (hpK : K ∈ 𝓝 p)
    (hconv : CheegerGromovCompactness.MetricCPConvergenceOn K 0
      (fun n => localPullMetric (scaleMetric (A n) (hA n) h) (Phi n) (hPhi n))
      (scaleMetric c hc (metric.restrictOpen V)) (scaleMetric c hc (metric.restrictOpen V)))
    (u : ℕ → V) (hu : Tendsto u atTop (𝓝 p))
    {q : UniformSpace.Completion W} {d : ℝ}
    (cone : DifferentialGeometry.Toponogov.PuncturedConeApproximation q d)
    {lower B : ℝ} (hlower : 0 < lower)
    (hcenter : ∀ᶠ n in atTop,
      dist (Phi n (u n) : UniformSpace.Completion W) q * Real.sqrt (A n) ∈ Icc lower B) :
    False := by
  classical
  let _ : PreconnectedSpace V := hV
  let gInf := scaleMetric c hc (metric.restrictOpen V)
  let _ : PseudoMetricSpace V := gInf.toPseudoMetricSpace
  let _ : MetricSpace V := MetricSpace.ofT0PseudoMetricSpace V
  let _ : EDist V := (gInf.toPseudoMetricSpace).toEDist
  let gSeq := fun n => localPullMetric (scaleMetric (A n) (hA n) h) (Phi n) (hPhi n)
  let hSeq := fun n => scaleMetric (A n) (hA n) h
  let F (n : ℕ) : PartialDiffeomorph (𝓡 3) (𝓡 3) V W ∞ :=
    let e := DifferentialGeometry.Topology.diffeomorphRangeOfInjective (hPhi n) (hinj n)
    e.toPartialDiffeomorph.trans
      (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := 𝓡 3)
        (hPhi n).image ⟨e p⟩)
  have hF (n : ℕ) (x : V) : F n x = Phi n x := rfl
  have hFs (n : ℕ) : (F n).source = univ := by
    let e := DifferentialGeometry.Topology.diffeomorphRangeOfInjective (hPhi n) (hinj n)
    ext x
    change (x ∈ (univ : Set V) ∧ e x ∈ (univ : Set (hPhi n).image)) ↔ x ∈ univ
    simp only [mem_univ, and_self]
  obtain ⟨R, hR, hKR, hRK⟩ :=
    DifferentialGeometry.Geometry.Metric.exists_pos_isCompact_riemannianClosedBallOf_subset_of_mem_nhds
      gInf p hpK
  have hrestrict (s : ℝ) (hs : s ≤ R) :
      CheegerGromovCompactness.MetricCPConvergenceOn (riemannianClosedBallOf gInf p s) 0
        gSeq gInf gInf := by
    intro eps heps
    obtain ⟨N, hN⟩ := hconv (eps / 2) (half_pos heps)
    refine ⟨N, fun n hn => lt_of_le_of_lt
      (CheegerGromovCompactness.metricDerivNormSupOn_le_of_forall _ 0 _ _ _ (eps / 2)
        (half_pos heps).le ?_) (half_lt_self heps)⟩
    intro j hj x hx
    exact (CheegerGromovCompactness.derivNorm_le_sup hK hj _ _ _
      (hRK (riemannianClosedBallOf_mono _ _ hs hx))).trans (hN n hn).le
  have hsource (s : ℝ) : ∀ᶠ n in atTop,
      riemannianClosedBallOf gInf p s ⊆ (F n).source :=
    Eventually.of_forall fun n => by rw [hFs]; exact subset_univ _
  have hpull (s : ℝ) : ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf gInf p s,
      ∀ v : TangentSpace (𝓡 3) x, (gSeq n).inner x v v =
        (hSeq n).inner (F n x) (mfderiv (𝓡 3) (𝓡 3) (F n) x v)
          (mfderiv (𝓡 3) (𝓡 3) (F n) x v) := by
    apply Eventually.of_forall
    intro n x _ v
    exact localPullMetric_inner _ _ _ x v v
  let r := R / 4
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrR : r ≤ R := by dsimp only [r]; linarith
  have hKr : IsCompact (riemannianClosedBallOf gInf p r) :=
    hKR.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf gInf p r)
      (riemannianClosedBallOf_mono _ _ hrR)
  have hcapture := CheegerGromovCompactness.MetricCPConvergenceOn.eventually_closedBall_subset_image_of_pullback
    hSeq F p hr (r := r / 4) (by linarith) hKr (hrestrict r hrR) (hsource r) (hpull r)
  have hdist := fun (eps : ℝ) (heps : 0 < eps) =>
    CheegerGromovCompactness.MetricCPConvergenceOn.eventually_uniform_edist_toReal_of_pullback
      hSeq F p hr.le (R := R) (by dsimp only [r]; linarith) hKR
      (hrestrict R le_rfl) (hsource R) (hpull R) heps
  have hoff := CheegerGromovCompactness.tendsto_riemannianEDistOf_map_zero_of_metricCPConvergenceOn
    gInf gInf gSeq hSeq F p hR hKR (hrestrict R le_rfl) (hsource R) (hpull R) hu
  let rho := fun n => 1 / Real.sqrt (A n)
  have hrho (n : ℕ) : 0 < rho n := one_div_pos.mpr (Real.sqrt_pos.mpr (hA n))
  have hrho0 : Tendsto rho atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hAtop)
  have hdscale (n : ℕ) (x y : W) : (riemannianEDistOf (hSeq n) x y).toReal =
      dist x y / rho n := by
    rw [show hSeq n = scaleMetric (A n) (hA n) h by rfl, edistOf_scale,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), ← hmetric,
      edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    dsimp only [rho]
    rw [one_div, div_inv_eq_mul, mul_comm]
  have hsrcball : riemannianClosedBallOf gInf p r = Metric.closedBall p r := by
    ext y
    change riemannianEDistOf gInf p y ≤ ENNReal.ofReal r ↔ dist y p ≤ r
    rw [← show edist p y = riemannianEDistOf gInf p y from gInf.toPseudoMetricSpace_edist p y, edist_dist,
      ENNReal.ofReal_le_ofReal_iff hr.le, dist_comm]
  apply rescaled_cone_limit_exclusion V hV c hc p hp cone (fun n => Phi n (u n))
    Phi rho hrho hrho0 ?_ (R := r) (lower := lower) (B := B)
    hr hlower (hsrcball ▸ hKr) ?_ ?_ ?_
  · have hh := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hoff
    simpa only [Function.comp_def, ENNReal.toReal_zero, hdscale, hF] using hh
  · simpa only [rho, one_div, div_inv_eq_mul] using hcenter
  · filter_upwards [hcapture] with n hn
    have heq : riemannianClosedBallOf (hSeq n) (F n p) (r / 4) =
        Metric.closedBall (Phi n p) (r / 4 * rho n) := by
      have hrad : r / 4 = Real.sqrt (A n) * (r / 4 * rho n) := by
        dsimp only [rho]; field_simp [(Real.sqrt_pos.mpr (hA n)).ne']
      change riemannianClosedBallOf (scaleMetric (A n) (hA n) h) (Phi n p) (r / 4) = _
      conv_lhs => rw [hrad]
      rw [riemannianClosedBallOf_scaleMetric]
      ext y
      change riemannianEDistOf h (Phi n p) y ≤ ENNReal.ofReal _ ↔ dist y (Phi n p) ≤ _
      rw [← hmetric, edist_dist, ENNReal.ofReal_le_ofReal_iff (by positivity), dist_comm]
    rw [heq, hsrcball] at hn
    simpa only [hF] using hn
  · intro eps heps
    filter_upwards [hdist eps heps] with n hn
    intro x hx y hy
    have hh := hn x (hsrcball.symm ▸ hx) y (hsrcball.symm ▸ hy)
    rw [hdscale, hF, hF] at hh
    have hgdist : (riemannianEDistOf gInf x y).toReal = dist x y := by
      rw [← show edist x y = riemannianEDistOf gInf x y from gInf.toPseudoMetricSpace_edist x y,
        edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    rwa [hgdist] at hh

universe u w

open Set Filter DifferentialGeometry.CheegerGromovCompactness in
open scoped _root_.Topology in
theorem rescaled_cone_exclusion_of_inverse_comparison
    (V : TopologicalSpace.Opens E3) (hV : PreconnectedSpace V)
    (c : ℝ) (hc : 0 < c) (p : V) (hp : ‖p.val‖ ≤ transitionEnd)
    {W : Type u} [MetricSpace W] [ChartedSpace E3 W] [IsManifold (𝓡 3) ∞ W]
    (gW : SmoothRiemannianMetric (𝓡 3) W)
    (hWmetric : ∀ x y : W, edist x y = riemannianEDistOf gW x y)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (P : ℕ → Type w) [∀ n, TopologicalSpace (P n)] [∀ n, ChartedSpace E3 (P n)]
    [∀ n, IsManifold (𝓡 3) ∞ (P n)]
    (H : ∀ n, SmoothRiemannianMetric (𝓡 3) (P n))
    (A : ∀ n, PartialDiffeomorph (𝓡 3) (𝓡 3) V (P n) ∞)
    (Bmap : ∀ n, PartialDiffeomorph (𝓡 3) (𝓡 3) W (P n) ∞)
    (G : ℕ → SmoothRiemannianMetric (𝓡 3) V)
    {K : Set V} (hK : IsCompact K) (hpK : K ∈ 𝓝 p)
    (hconv : MetricCPConvergenceOn K 0 G
      (scaleMetric c hc (metric.restrictOpen V)) (scaleMetric c hc (metric.restrictOpen V)))
    (hsource : ∀ᶠ n in atTop, K ⊆ (A n).source)
    (hmetric : ∀ᶠ n in atTop, ∀ y ∈ K, ∀ v : TangentSpace (𝓡 3) y,
      (G n).inner y v v = (H n).inner (A n y)
        (mfderiv (𝓡 3) (𝓡 3) (A n) y v) (mfderiv (𝓡 3) (𝓡 3) (A n) y v))
    (x : ℕ → W) (marks : ℕ → V) (hmarks : Tendsto marks atTop (𝓝 p))
    (hmark : ∀ᶠ n in atTop, A n (marks n) = Bmap n (x n))
    {R : ℝ} (hR : 0 < R)
    (hBsource : ∀ᶠ n in atTop,
      riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) R ⊆ (Bmap n).source)
    (hcapture : ∀ᶠ n in atTop,
      riemannianClosedBallOf (H n) (Bmap n (x n)) (R / 4) ⊆
        (Bmap n) '' riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) R)
    (hBconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop,
      ∀ y ∈ riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (x n) R,
      ∀ v : TangentSpace (𝓡 3) y,
        (1 - eta) * (scaleMetric (scale n) (hscale n) gW).inner y v v ≤
          (H n).inner (Bmap n y) (mfderiv (𝓡 3) (𝓡 3) (Bmap n) y v)
            (mfderiv (𝓡 3) (𝓡 3) (Bmap n) y v) ∧
        (H n).inner (Bmap n y) (mfderiv (𝓡 3) (𝓡 3) (Bmap n) y v)
          (mfderiv (𝓡 3) (𝓡 3) (Bmap n) y v) ≤
            (1 + eta) * (scaleMetric (scale n) (hscale n) gW).inner y v v)
    {q : UniformSpace.Completion W} {d : ℝ}
    (cone : DifferentialGeometry.Toponogov.PuncturedConeApproximation q d)
    {lower upper : ℝ} (hlower : 0 < lower)
    (hradial : ∀ᶠ n in atTop,
      dist (x n : UniformSpace.Completion W) q * Real.sqrt (scale n) ∈ Icc lower upper) :
    False := by
  let _ : PreconnectedSpace V := hV
  let gInf := scaleMetric c hc (metric.restrictOpen V)
  let _ : PseudoMetricSpace V := gInf.toPseudoMetricSpace
  let _ : MetricSpace V := MetricSpace.ofT0PseudoMetricSpace V
  let _ : EDist V := gInf.toPseudoMetricSpace.toEDist
  obtain ⟨Rsrc, hRsrc, hKR, hRK⟩ :=
    Geometry.Metric.exists_pos_isCompact_riemannianClosedBallOf_subset_of_mem_nhds gInf p hpK
  have hconv' : MetricCPConvergenceOn (riemannianClosedBallOf gInf p Rsrc) 0 G gInf gInf := by
    intro eps heps
    obtain ⟨N, hN⟩ := hconv (eps / 2) (half_pos heps)
    refine ⟨N, fun n hn => lt_of_le_of_lt
      (metricDerivNormSupOn_le_of_forall _ 0 _ _ _ (eps / 2) (half_pos heps).le ?_)
      (half_lt_self heps)⟩
    intro j hj y hy
    exact (derivNorm_le_sup hK hj _ _ _ (hRK hy)).trans (hN n hn).le
  let Hend := fun n => scaleMetric (scale n) (hscale n) gW
  let Cmap := fun n => (A n).trans (Bmap n).symm
  obtain ⟨r, hr, _, hKr, hcaptureC, hoffset, hdistC⟩ :=
    exists_inverse_composition_distance_comparison_of_tendsto_marks
      gInf gInf G H Hend A Bmap p hRsrc hR hKR hconv'
      (hsource.mono fun n hn => hRK.trans hn)
      (hmetric.mono fun n hn y hy v => hn y (hRK hy) v)
      x hmarks hmark hBsource hcapture hBconv
  let rho := fun n => 1 / Real.sqrt (scale n)
  have hrho (n : ℕ) : 0 < rho n := one_div_pos.mpr (Real.sqrt_pos.mpr (hscale n))
  have hrho0 : Tendsto rho atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hscaleTop)
  have hdscale (n : ℕ) (a b : W) : (riemannianEDistOf (Hend n) a b).toReal =
      dist a b / rho n := by
    rw [show Hend n = scaleMetric (scale n) (hscale n) gW by rfl, edistOf_scale,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), ← hWmetric,
      edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    dsimp only [rho]
    rw [one_div, div_inv_eq_mul, mul_comm]
  have hsrcball : riemannianClosedBallOf gInf p r = Metric.closedBall p r := by
    ext y
    change riemannianEDistOf gInf p y ≤ ENNReal.ofReal r ↔ dist y p ≤ r
    rw [← show edist p y = riemannianEDistOf gInf p y from gInf.toPseudoMetricSpace_edist p y,
      edist_dist, ENNReal.ofReal_le_ofReal_iff hr.le, dist_comm]
  apply rescaled_cone_limit_exclusion V hV c hc p hp cone x (fun n => Cmap n) rho
    hrho hrho0 ?_ (R := r) (lower := lower) (B := upper) hr hlower (hsrcball ▸ hKr) ?_ ?_ ?_
  · have hh := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hoffset
    simpa only [Function.comp_def, ENNReal.toReal_zero, hdscale] using hh
  · simpa only [rho, one_div, div_inv_eq_mul] using hradial
  · filter_upwards [hcaptureC] with n hn
    have hb := hn.2.1
    have heq : riemannianClosedBallOf (Hend n) (Cmap n p) (r / 4) =
        Metric.closedBall (Cmap n p) (r / 4 * rho n) := by
      have hrad : r / 4 = Real.sqrt (scale n) * (r / 4 * rho n) := by
        dsimp only [rho]; field_simp [(Real.sqrt_pos.mpr (hscale n)).ne']
      change riemannianClosedBallOf (scaleMetric (scale n) (hscale n) gW) (Cmap n p) (r / 4) = _
      conv_lhs => rw [hrad]
      rw [riemannianClosedBallOf_scaleMetric]
      ext y
      change riemannianEDistOf gW (Cmap n p) y ≤ ENNReal.ofReal _ ↔ dist y (Cmap n p) ≤ _
      rw [← hWmetric, edist_dist, ENNReal.ofReal_le_ofReal_iff (by positivity), dist_comm]
    rw [heq, hsrcball] at hb
    exact hb
  · intro eps heps
    filter_upwards [hdistC eps heps] with n hn
    intro a ha b hb
    have hh := hn a (hsrcball.symm ▸ ha) b (hsrcball.symm ▸ hb)
    rw [hdscale] at hh
    have hgdist : (riemannianEDistOf gInf a b).toReal = dist a b := by
      rw [← show edist a b = riemannianEDistOf gInf a b from gInf.toPseudoMetricSpace_edist a b,
        edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    rwa [hgdist] at hh


end DifferentialGeometry.PDE.RicciFlow.StandardCap
