import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWindowVolume

set_option autoImplicit false
noncomputable section
open Set Function Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private theorem exists_window_partialDiffeomorph_of_embedding
    {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    {D : ℝ} (f : standardCapWindow D → N)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f) (hinj : Injective f)
    (p : standardCapWindow D) :
    ∃ Φ : PartialDiffeomorph ThreeModel ThreeModel ThreeSpace
        N ∞,
      Φ.source = (standardCapWindow D : Set ThreeSpace) ∧
      Φ.target = range f ∧
      ∀ x : standardCapWindow D, Φ x.val = f x := by
  let U := standardCapWindow D
  have hlocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f :=
    hf
  let V := hlocal.image
  let e : Diffeomorph ThreeModel ThreeModel U V ∞ :=
    DifferentialGeometry.Topology.diffeomorphRangeOfInjective hlocal
      hinj
  let x₀ : U := p
  let iU := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ThreeModel U ⟨x₀⟩
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ThreeModel V ⟨e x₀⟩
  let Φ := (iU.symm.trans e.toPartialDiffeomorph).trans iV
  refine ⟨Φ, ?_, ?_, ?_⟩
  · ext x
    change ((x ∈ iU.target ∧ iU.symm x ∈ (univ : Set U)) ∧
      e (iU.symm x) ∈ (univ : Set V)) ↔ x ∈ U
    simp only [mem_univ, and_true, iU,
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    rfl
  · ext y
    change (y ∈ iV.target ∧ (iV.symm y ∈ (univ : Set V) ∧
      e.symm (iV.symm y) ∈ (univ : Set U))) ↔ y ∈ range f
    simp only [mem_univ, and_self, and_true, iV,
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    rfl
  · intro x
    change (e (iU.symm x.val) : N) = f x
    rw [show iU.symm x.val = x from
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply
        ThreeModel U ⟨x₀⟩ x.property]
    rfl


variable {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold ThreeModel ∞ N] [T2Space N]
  {D : ℝ} (h : SmoothRiemannianMetric ThreeModel N)
  (Φ : standardCapWindow D → N)
  (hΦ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ) (hiΦ : Injective Φ)

omit [T2Space N] in
include hΦ hiΦ in
private theorem image_coordinate_ball_subset_of_metric_upper
    (hupper : ∀ x : standardCapWindow D, ‖x.val‖ < D → ∀ v : TangentSpace ThreeModel x,
      h.inner (Φ x) (mfderiv ThreeModel ThreeModel Φ x v)
        (mfderiv ThreeModel ThreeModel Φ x v) ≤ 4 * metric.inner x.val v v)
    (p : standardCapWindow D) {r : ℝ} (hr : 0 < r) (hmargin : ‖p.val‖ + r < D) :
    Φ '' {x : standardCapWindow D | dist x.val p.val ≤ r / 4} ⊆
      riemannianBallOf h (Φ p) r := by
  let ge := DifferentialGeometry.Geometry.standardEuclideanMetric ThreeSpace
  have hed (x y : ThreeSpace) : riemannianEDistOf ge x y = edist x y :=
    DifferentialGeometry.Geometry.riemannianEDistOf_standardEuclideanMetric x y
  obtain ⟨F, hsource, _, hmap⟩ := exists_window_partialDiffeomorph_of_embedding Φ hΦ hiΦ p
  have hnorm {z : ThreeSpace} (hz : z ∈ riemannianClosedBallOf ge p.val r) : ‖z‖ < D := by
    have hdist : dist z p.val ≤ r := by
      change riemannianEDistOf ge p.val z ≤ ENNReal.ofReal r at hz
      rw [hed, edist_dist, ENNReal.ofReal_le_ofReal_iff hr.le] at hz
      rwa [dist_comm]
    have hn := norm_le_norm_sub_add z p.val
    rw [← dist_eq_norm] at hn
    linarith
  have hsub : riemannianClosedBallOf ge p.val r ⊆ standardCapWindow D := by
    intro z hz
    change ‖z‖ < D + 1
    exact (hnorm hz).trans (by linarith)
  have hu : ∀ z ∈ riemannianClosedBallOf ge p.val r, ∀ v : TangentSpace ThreeModel z,
      h.inner (F z) (mfderiv ThreeModel ThreeModel (F : ThreeSpace → N) z v)
        (mfderiv ThreeModel ThreeModel (F : ThreeSpace → N) z v) ≤
      (2 : ℝ)^2 * ge.inner z v v := by
    intro z hz v
    let q : standardCapWindow D := ⟨z, hsub hz⟩
    have hd : mfderiv ThreeModel ThreeModel Φ q =
        mfderiv ThreeModel ThreeModel (F : ThreeSpace → N) z := by
      have heq : (fun x : standardCapWindow D => F x) = Φ := funext hmap
      rw [← heq]
      exact mfderiv_restrict_open (F : ThreeSpace → N) (standardCapWindow D) q
    have hb := hupper q (hnorm hz) v
    rw [hd, ← hmap q] at hb
    apply hb.trans
    change 4 * metric.inner z v v ≤
      2 ^ 2 * @inner ℝ ThreeSpace _ (show ThreeSpace from v) (show ThreeSpace from v)
    rw [real_inner_self_eq_norm_sq]
    nlinarith [metric_inner_le z v]
  rintro _ ⟨x, hx, rfl⟩
  have hy : riemannianEDistOf ge p.val x.val < ENNReal.ofReal r := by
    rw [hed, edist_dist]
    apply (ENNReal.ofReal_lt_ofReal_iff hr).mpr
    rw [dist_comm]
    exact hx.trans_lt (by linarith)
  have hd := Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
    ge h F p.val x.val hr (by norm_num : (0 : ℝ) < 2)
    (by rw [hsource]; exact hsub) hu hy
  rw [hmap p, hmap x] at hd
  apply hd.trans_lt
  calc
    ENNReal.ofReal 2 * riemannianEDistOf ge p.val x.val ≤
        ENNReal.ofReal 2 * ENNReal.ofReal (r / 4) := by
      rw [hed, edist_dist, dist_comm]
      exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hx)
    _ = ENNReal.ofReal (r / 2) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    _ < ENNReal.ofReal r := (ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith)
private local instance : MeasurableSpace ThreeSpace := borel ThreeSpace
private local instance : BorelSpace ThreeSpace := ⟨rfl⟩
private local instance (V : TopologicalSpace.Opens ThreeSpace) : MeasurableSpace V := borel V
private local instance (V : TopologicalSpace.Opens ThreeSpace) : BorelSpace V := ⟨rfl⟩
private local instance (V : TopologicalSpace.Opens ThreeSpace) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)

variable [SigmaCompactSpace N]

include hΦ hiΦ in
private theorem volume_image_ge_of_metric_lower
    (hlower : ∀ x : standardCapWindow D, ‖x.val‖ < D → ∀ v : TangentSpace ThreeModel x,
      (1 / 4 : ℝ) * metric.inner x.val v v ≤
        h.inner (Φ x) (mfderiv ThreeModel ThreeModel Φ x v)
          (mfderiv ThreeModel ThreeModel Φ x v))
    {S : Set (standardCapWindow D)} (hS : MeasurableSet S)
    (hSD : S ⊆ {x : standardCapWindow D | ‖x.val‖ < D}) :
    ENNReal.ofReal (1 / 8 : ℝ) *
      riemannianVolumeMeasure ThreeModel (standardCapWindow D)
        (metric.restrictOpen (standardCapWindow D)) S ≤
      riemannianVolumeMeasure ThreeModel N h (Φ '' S) := by
  let hp := pullbackMetricOfInjectiveLocalDiffeomorph h Φ hΦ hiΦ
  let g₀ := metric.restrictOpen (standardCapWindow D)
  have hcomp (x : standardCapWindow D) (hx : x ∈ S) (v : TangentSpace ThreeModel x) :
      (scaleMetric (1 / 4 : ℝ) (by norm_num) g₀).inner x v v ≤
        1 * hp.inner x v v := by
    rw [scaleMetric_inner, one_mul, pullbackMetricOfInjectiveLocalDiffeomorph_inner]
    exact hlower x (hSD hx) v
  have hv := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le
    hp (scaleMetric (1 / 4 : ℝ) (by norm_num) g₀) zero_lt_one hS hcomp
  rw [volume_scale_apply] at hv
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hdim] at hv
  norm_num at hv
  have heq := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    hp h Φ hΦ hiΦ (fun x v z => pullbackMetricOfInjectiveLocalDiffeomorph_inner h Φ hΦ hiΦ x v z) hS
  rw [← heq]
  rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hv
  norm_num at hv
  exact hv

include hΦ hiΦ in
theorem window_ball_volume_ge_of_metric_bounds
    (hmetric : ∀ x : standardCapWindow D, ‖x.val‖ < D → ∀ v : TangentSpace ThreeModel x,
      (1 / 4 : ℝ) * metric.inner x.val v v ≤
        h.inner (Φ x) (mfderiv ThreeModel ThreeModel Φ x v)
          (mfderiv ThreeModel ThreeModel Φ x v) ∧
      h.inner (Φ x) (mfderiv ThreeModel ThreeModel Φ x v)
        (mfderiv ThreeModel ThreeModel Φ x v) ≤ 4 * metric.inner x.val v v)
    (p : standardCapWindow D) {r : ℝ} (hr : 0 < r) (hmargin : ‖p.val‖ + r < D) :
    ENNReal.ofReal (1 / 8 : ℝ) *
      riemannianVolumeMeasure ThreeModel ThreeSpace metric (Metric.closedBall p.val (r / 4)) ≤
    riemannianVolumeMeasure ThreeModel N h (riemannianBallOf h (Φ p) r) := by
  let S : Set (standardCapWindow D) := {x | dist x.val p.val ≤ r / 4}
  have hS : MeasurableSet S := (isClosed_le (continuous_subtype_val.dist continuous_const)
    continuous_const).measurableSet
  have hSD : S ⊆ {x : standardCapWindow D | ‖x.val‖ < D} := by
    intro x hx
    have hn := norm_le_norm_sub_add x.val p.val
    change dist x.val p.val ≤ r / 4 at hx
    rw [dist_eq_norm] at hx
    change ‖x.val‖ < D
    linarith
  have himage : Metric.closedBall p.val (r / 4) ⊆ standardCapWindow D := by
    intro x hx
    have hn := norm_le_norm_sub_add x p.val
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    change ‖x‖ < D + 1
    linarith
  have hvol : riemannianVolumeMeasure ThreeModel (standardCapWindow D)
      (metric.restrictOpen (standardCapWindow D)) S =
      riemannianVolumeMeasure ThreeModel ThreeSpace metric (Metric.closedBall p.val (r / 4)) :=
    DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset
      metric (standardCapWindow D) Metric.isClosed_closedBall.measurableSet himage
  rw [← hvol]
  exact (volume_image_ge_of_metric_lower h Φ hΦ hiΦ
    (fun x hx v => (hmetric x hx v).1) hS hSD).trans
      (measure_mono (image_coordinate_ball_subset_of_metric_upper h Φ hΦ hiΦ
        (fun x hx v => (hmetric x hx v).2) p hr hmargin))
theorem exists_uniform_scaled_window_ball_volume_lower (R₀ : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
        [IsManifold ThreeModel ∞ N] [T2Space N] [SigmaCompactSpace N]
        {D : ℝ} (g : SmoothRiemannianMetric ThreeModel N)
        (Φ : standardCapWindow D → N),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Φ →
      ∀ (q : ℝ) (hq : 0 < q),
      (∀ x : standardCapWindow D, ‖x.val‖ < D → ∀ v : TangentSpace ThreeModel x,
        (1 / 4 : ℝ) * metric.inner x.val v v ≤
          (scaleMetric q hq g).inner (Φ x) (mfderiv ThreeModel ThreeModel Φ x v)
            (mfderiv ThreeModel ThreeModel Φ x v) ∧
        (scaleMetric q hq g).inner (Φ x) (mfderiv ThreeModel ThreeModel Φ x v)
          (mfderiv ThreeModel ThreeModel Φ x v) ≤ 4 * metric.inner x.val v v) →
      ∀ p : standardCapWindow D, ‖p.val‖ ≤ R₀ →
      ∀ r : ℝ, 0 < r → r ≤ 1 → ‖p.val‖ + r < D →
        ENNReal.ofReal κ * ENNReal.ofReal (r / Real.sqrt q) ^ 3 ≤
          riemannianVolumeMeasure ThreeModel N g
            (riemannianBallOf g (Φ p) (r / Real.sqrt q)) := by
  obtain ⟨ν, hν, hvol⟩ := exists_uniform_standard_cap_coordinate_ball_volume_lower R₀
  refine ⟨ν / 8, by positivity, ?_⟩
  intro N _ _ _ _ _ D g Φ hemb q hq hmetric p hp r hr hr1 hmargin
  have hlocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv Φ
      hemb.contMDiff (fun x => (hemb.isImmersion.isImmersionAt x).mfderiv_injective (by decide)) rfl
  have hv := (mul_le_mul' (le_rfl : ENNReal.ofReal (1 / 8 : ℝ) ≤ _)
    (hvol p.val hp r hr hr1)).trans
      (window_ball_volume_ge_of_metric_bounds (scaleMetric q hq g) Φ hlocal
        hemb.isEmbedding.injective hmetric p hr hmargin)
  have hv' : ENNReal.ofReal (ν / 8) * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel N (scaleMetric q hq g)
        (riemannianBallOf (scaleMetric q hq g) (Φ p) r) := by
    have he : ENNReal.ofReal (ν / 8) * ENNReal.ofReal r ^ 3 =
        ENNReal.ofReal (1 / 8 : ℝ) * (ENNReal.ofReal ν * ENNReal.ofReal r ^ 3) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 8)]
      congr 2
      ring
    exact he.trans_le hv
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have heq : Real.sqrt q * (r / Real.sqrt q) = r := by field_simp
  have hball := riemannianBallOf_scaleMetric q hq g (Φ p) (r / Real.sqrt q)
  rw [heq] at hball
  rw [hball, volume_scale_apply] at hv'
  rw [show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace]] at hv'
  have hc : ENNReal.ofReal (Real.sqrt q) ^ 3 ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr hs)
  have hct : ENNReal.ofReal (Real.sqrt q) ^ 3 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  apply (ENNReal.mul_le_mul_iff_right hc hct).mp
  calc
    ENNReal.ofReal (Real.sqrt q) ^ 3 *
        (ENNReal.ofReal (ν / 8) * ENNReal.ofReal (r / Real.sqrt q) ^ 3)
      = ENNReal.ofReal (ν / 8) * ENNReal.ofReal r ^ 3 := by
          rw [mul_left_comm, ← mul_pow,
            ← ENNReal.ofReal_mul hs.le, heq]
    _ ≤ _ := hv'

theorem exists_uniform_nearby_scaled_window_ball_volume_lower (R₁ : ℝ) (hR₁ : 0 < R₁) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
        [IsManifold ThreeModel ∞ N] [T2Space N] [SigmaCompactSpace N]
        {D : ℝ} (g : SmoothRiemannianMetric ThreeModel N)
        (Φ : standardCapWindow D → N),
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Φ →
      ∀ (q Q C : ℝ) (hq : 0 < q), 0 < Q → 0 < C → q ≤ C * Q →
      (∀ x : standardCapWindow D, ‖x.val‖ < D → ∀ v : TangentSpace ThreeModel x,
        (1 / 4 : ℝ) * metric.inner x.val v v ≤
          (scaleMetric q hq g).inner (Φ x) (mfderiv ThreeModel ThreeModel Φ x v)
            (mfderiv ThreeModel ThreeModel Φ x v) ∧
        (scaleMetric q hq g).inner (Φ x) (mfderiv ThreeModel ThreeModel Φ x v)
          (mfderiv ThreeModel ThreeModel Φ x v) ≤ 4 * metric.inner x.val v v) →
      R₁ + 1 < D →
      ∀ (u : standardCapWindow D) (y : N) (d : ℝ), 0 ≤ d →
      riemannianEDistOf g (Φ u) y ≤ ENNReal.ofReal (d / Real.sqrt Q) →
      2 * ‖u.val‖ + d * Real.sqrt C < R₁ / 2 →
      ∀ a : ℝ, 0 < a → a * Real.sqrt C ≤ 1 →
        ENNReal.ofReal κ * ENNReal.ofReal (a / Real.sqrt Q) ^ 3 ≤
          riemannianVolumeMeasure ThreeModel N g (riemannianBallOf g y (a / Real.sqrt Q)) := by
  obtain ⟨κ, hκ, hvolume⟩ := exists_uniform_scaled_window_ball_volume_lower R₁
  refine ⟨κ, hκ, ?_⟩
  intro N _ _ _ _ _ D g Φ hemb q Q C hq hQ hC hscale hmetric hmargin u y d hd hnear hreserve a ha hsmall
  have hlocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Φ :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv Φ
      hemb.contMDiff (fun x => (hemb.isImmersion.isImmersionAt x).mfderiv_injective (by decide)) rfl
  have hnorm : ‖u.val‖ < R₁ := by
    nlinarith [norm_nonneg u.val, mul_nonneg hd (Real.sqrt_nonneg C)]
  obtain ⟨⟨v, hv, hvy⟩, _⟩ :=
    window_exists_preimage_and_ball_subset_image_of_scaled_metric_bounds
      g (D := D) (R₀ := ‖u.val‖) (R₁ := R₁) (R₂ := R₁)
      (L := 2) (U := 2) (q := q) (Q := Q) (C := C) (d := d) (r := 0)
      hR₁ le_rfl (by linarith) (by norm_num) (by norm_num) hq hQ hC hscale hd le_rfl
      Φ hlocal hemb.isEmbedding.injective
      (by intro x hx v; have h := (hmetric x (hx.trans_lt (by linarith)) v).1; nlinarith)
      (by intro x hx v; have h := (hmetric x (hx.trans_lt (by linarith)) v).2; nlinarith)
      u le_rfl hnorm y hnear hreserve (by simpa only [add_zero] using hreserve.le)
  let r := a * (Real.sqrt q / Real.sqrt Q)
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hratio : Real.sqrt q / Real.sqrt Q ≤ Real.sqrt C := by
    apply (div_le_iff₀ hsQ).mpr
    calc
      Real.sqrt q ≤ Real.sqrt (C * Q) := Real.sqrt_le_sqrt hscale
      _ = Real.sqrt C * Real.sqrt Q := Real.sqrt_mul hC.le Q
  have hr : 0 < r := mul_pos ha (div_pos hsq hsQ)
  have hr1 : r ≤ 1 := (mul_le_mul_of_nonneg_left hratio ha.le).trans hsmall
  have hrD : ‖v.val‖ + r < D := (add_le_add hv hr1).trans_lt hmargin
  have hphysical : r / Real.sqrt q = a / Real.sqrt Q := by
    dsimp only [r]
    field_simp
  have hvol := hvolume g Φ hemb q hq hmetric v hv r hr hr1 hrD
  simpa only [hvy, hphysical] using hvol

end DifferentialGeometry.PDE.RicciFlow.StandardCap
