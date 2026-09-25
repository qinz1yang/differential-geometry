import DifferentialGeometry.Geometry.Metric.Convergence.Metric.QuadraticBounds
import DifferentialGeometry.Geometry.Comparison.OpenEmbeddingBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Distance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticWindow
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

theorem isCompact_window_norm_le {D r : ℝ} (hfit : r < D + 1) :
    IsCompact {x : standardCapWindow D | ‖x.val‖ ≤ r} := by
  have hc : IsCompact {x : ThreeSpace | ‖x‖ ≤ r} := by
    simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : ThreeSpace) r
  exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
    intro x hx
    exact ⟨⟨x, hx.trans_lt hfit⟩, rfl⟩)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem window_image_closedBall_subset_ball_of_metric_upper
    (g : SmoothRiemannianMetric I M) {D r R : ℝ} (hr : 0 < r) (hrR : r < R) (hRD : R < D)
    (Φ : standardCapWindow D → M) (hΦ : IsLocalDiffeomorph ThreeModel I ∞ Φ)
    (hinj : Injective Φ)
    (hupper : ∀ x : standardCapWindow D, ‖x.val‖ ≤ R → ∀ v : TangentSpace ThreeModel x,
      g.inner (Φ x) (mfderiv ThreeModel I Φ x v) (mfderiv ThreeModel I Φ x v) ≤
        2 * metric.inner x.val v v) :
    ∃ p : standardCapWindow D, p.val = 0 ∧
      Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ r} ⊆
        riemannianBallOf g (Φ p) (2 * r) := by
  have hD : 0 < D := hr.trans (hrR.trans hRD)
  let p : standardCapWindow D := ⟨0, by change ‖(0 : ThreeSpace)‖ < D + 1; simp; linarith⟩
  refine ⟨p, rfl, ?_⟩
  have hnorm (s : ℝ) (hs : 0 ≤ s) (x : ThreeSpace) :
      x ∈ riemannianClosedBallOf metric (0 : ThreeSpace) s ↔ ‖x‖ ≤ s := by
    change riemannianEDistOf metric 0 x ≤ ENNReal.ofReal s ↔ ‖x‖ ≤ s
    rw [edist_zero, ENNReal.ofReal_le_ofReal_iff hs]
  have hsource : riemannianClosedBallOf metric p.val R ⊆ standardCapWindow D := by
    intro x hx
    have hh := (hnorm R (hr.trans hrR).le x).mp hx
    change ‖x‖ < D + 1
    linarith
  have hup : ∀ x : standardCapWindow D, x.val ∈ riemannianClosedBallOf metric p.val R →
      ∀ v : TangentSpace ThreeModel x,
        g.inner (Φ x) (mfderiv ThreeModel I Φ x v) (mfderiv ThreeModel I Φ x v) ≤
          (Real.sqrt 2) ^ 2 * metric.inner x.val v v := by
    intro x hx v
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact hupper x ((hnorm R (hr.trans hrR).le x.val).mp hx) v
  have hL : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hL2 : Real.sqrt 2 < 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have himage := Geometry.Metric.image_closedBall_subset_ball_of_metric_upper_on_opens
    g metric (standardCapWindow D) Φ hΦ hinj p hr hrR hL hL2 hsource hup
  simpa only [show p.val = (0 : ThreeSpace) from rfl, hnorm r hr.le] using himage

theorem window_image_closedBall_subset_ball_of_metric_close
    (g : SmoothRiemannianMetric I M) {D r R : ℝ} (hr : 0 < r) (hrR : r < R) (hRD : R < D)
    (Φ : standardCapWindow D → M) (hΦ : IsLocalDiffeomorph ThreeModel I ∞ Φ)
    (hinj : Injective Φ) (h : SmoothRiemannianMetric ThreeModel (standardCapWindow D))
    (hmetric : ∀ x (v z : TangentSpace ThreeModel x), h.inner x v z =
      g.inner (Φ x) (mfderiv ThreeModel I Φ x v) (mfderiv ThreeModel I Φ x z))
    (hclose : ∀ x : standardCapWindow D, ‖x.val‖ ≤ R →
      metricDerivNorm 0 h (metric.restrictOpen (standardCapWindow D))
        (metric.restrictOpen (standardCapWindow D)) x ≤ 1) :
    ∃ p : standardCapWindow D, p.val = 0 ∧
      Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ r} ⊆
        riemannianBallOf g (Φ p) (2 * r) := by
  apply window_image_closedBall_subset_ball_of_metric_upper g hr hrR hRD Φ hΦ hinj
  intro x hx v
  rw [← hmetric]
  have hb := (inner_bounds_of_metricDerivNorm_le
    (metric.restrictOpen (standardCapWindow D)) h x (hclose x hx) v).2
  simpa only [SmoothRiemannianMetric.restrictOpen_inner, show (1 : ℝ) + 1 = 2 by norm_num] using hb

private theorem window_edist_map_le_of_metric_upper_of_radius_le
    (g : SmoothRiemannianMetric I M) {D R L : ℝ} (hRD : R ≤ D + 1) (hL : 0 < L)
    (Φ : standardCapWindow D → M) (hΦ : IsLocalDiffeomorph ThreeModel I ∞ Φ)
    (hinj : Injective Φ)
    (hupper : ∀ z : standardCapWindow D, ‖z.val‖ < R → ∀ v : TangentSpace ThreeModel z,
      g.inner (Φ z) (mfderiv ThreeModel I Φ z v) (mfderiv ThreeModel I Φ z v) ≤
        L ^ 2 * metric.inner z.val v v)
    (x y : standardCapWindow D) (hx : ‖x.val‖ < R) (hy : ‖y.val‖ < R) :
    riemannianEDistOf g (Φ x) (Φ y) ≤ ENNReal.ofReal (L * (‖x.val‖ + ‖y.val‖)) := by
  have hD : 0 < D + 1 := ((norm_nonneg x.val).trans_lt hx).trans_le hRD
  let p : standardCapWindow D := ⟨0, by
    change ‖(0 : ThreeSpace)‖ < D + 1
    simp only [norm_zero]
    linarith⟩
  have hradial (z : standardCapWindow D) (hz : ‖z.val‖ < R) :
      riemannianEDistOf g (Φ p) (Φ z) ≤ ENNReal.ofReal (L * ‖z.val‖) := by
    obtain ⟨r, hzr, hrR⟩ := exists_between hz
    have hrD : r < D + 1 := hrR.trans_le hRD
    have hr : 0 < r := (norm_nonneg z.val).trans_lt hzr
    have hsource : riemannianClosedBallOf metric p.val r ⊆ standardCapWindow D := by
      intro a ha
      have hn : ‖a‖ ≤ r := by
        change riemannianEDistOf metric 0 a ≤ ENNReal.ofReal r at ha
        rw [edist_zero, ENNReal.ofReal_le_ofReal_iff hr.le] at ha
        exact ha
      change ‖a‖ < D + 1
      linarith
    have hb := Geometry.Metric.edistOf_map_le_of_metric_upper_on_opens
      g metric (standardCapWindow D) Φ hΦ hinj p z hr hL hsource
      (fun a ha v => hupper a (by
        change riemannianEDistOf metric 0 a.val ≤ ENNReal.ofReal r at ha
        rw [edist_zero, ENNReal.ofReal_le_ofReal_iff hr.le] at ha
        exact ha.trans_lt hrR) v) (by
        change riemannianEDistOf metric 0 z.val < ENNReal.ofReal r
        rw [edist_zero]
        exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr hzr)
    simpa only [show p.val = (0 : ThreeSpace) from rfl, edist_zero,
      ← ENNReal.ofReal_mul hL.le] using hb
  have hx' := hradial x hx
  have hy' := hradial y hy
  have hsymm : riemannianEDistOf g (Φ x) (Φ p) = riemannianEDistOf g (Φ p) (Φ x) :=
    riemannianEDistOf_comm g (Φ x) (Φ p)
  calc
    riemannianEDistOf g (Φ x) (Φ y) ≤
        riemannianEDistOf g (Φ x) (Φ p) + riemannianEDistOf g (Φ p) (Φ y) :=
      riemannianEDistOf_triangle g (Φ x) (Φ p) (Φ y)
    _ ≤ ENNReal.ofReal (L * ‖x.val‖) + ENNReal.ofReal (L * ‖y.val‖) := by
      rw [hsymm]
      exact add_le_add hx' hy'
    _ = ENNReal.ofReal (L * (‖x.val‖ + ‖y.val‖)) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hL.le (norm_nonneg _))
        (mul_nonneg hL.le (norm_nonneg _)), mul_add]

theorem window_edist_map_le_of_metric_upper_on_source
    (g : SmoothRiemannianMetric I M) {D L : ℝ} (hL : 0 < L)
    (Φ : standardCapWindow D → M) (hΦ : IsLocalDiffeomorph ThreeModel I ∞ Φ)
    (hinj : Injective Φ)
    (hupper : ∀ z : standardCapWindow D, ∀ v : TangentSpace ThreeModel z,
      g.inner (Φ z) (mfderiv ThreeModel I Φ z v) (mfderiv ThreeModel I Φ z v) ≤
        L ^ 2 * metric.inner z.val v v)
    (x y : standardCapWindow D) :
    riemannianEDistOf g (Φ x) (Φ y) ≤ ENNReal.ofReal (L * (‖x.val‖ + ‖y.val‖)) := by
  exact window_edist_map_le_of_metric_upper_of_radius_le g le_rfl hL
    Φ hΦ hinj (fun z _ => hupper z) x y x.property y.property

theorem window_edist_map_le_of_metric_upper
    (g : SmoothRiemannianMetric I M) {D L : ℝ} (hL : 0 < L)
    (Φ : standardCapWindow D → M) (hΦ : IsLocalDiffeomorph ThreeModel I ∞ Φ)
    (hinj : Injective Φ)
    (hupper : ∀ z : standardCapWindow D, ‖z.val‖ < D → ∀ v : TangentSpace ThreeModel z,
      g.inner (Φ z) (mfderiv ThreeModel I Φ z v) (mfderiv ThreeModel I Φ z v) ≤
        L ^ 2 * metric.inner z.val v v)
    (x y : standardCapWindow D) (hx : ‖x.val‖ < D) (hy : ‖y.val‖ < D) :
    riemannianEDistOf g (Φ x) (Φ y) ≤ ENNReal.ofReal (L * (‖x.val‖ + ‖y.val‖)) := by
  exact window_edist_map_le_of_metric_upper_of_radius_le g (by linarith) hL
    Φ hΦ hinj hupper x y hx hy


variable [T2Space M]

theorem window_tip_ball_subset_image_closedBall_of_metric_lower
    (g : SmoothRiemannianMetric I M) {D R L : ℝ} (hR : 0 < R) (hRD : R < D + 1)
    (hL : 0 < L) (Φ : standardCapWindow D → M)
    (hΦ : IsLocalDiffeomorph ThreeModel I ∞ Φ) (hinj : Injective Φ)
    (p : standardCapWindow D) (hp : p.val = 0)
    (hlower : ∀ x : standardCapWindow D, ‖x.val‖ ≤ R → ∀ v : TangentSpace ThreeModel x,
      metric.inner x.val v v ≤ L ^ 2 *
        g.inner (Φ x) (mfderiv ThreeModel I Φ x v) (mfderiv ThreeModel I Φ x v)) :
    riemannianBallOf g (Φ p) (R / L) ⊆
      Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ R} := by
  have hnorm (z : ThreeSpace) :
      z ∈ riemannianClosedBallOf metric p.val R ↔ ‖z‖ ≤ R := by
    change riemannianEDistOf metric p.val z ≤ ENNReal.ofReal R ↔ ‖z‖ ≤ R
    rw [hp, edist_zero, ENNReal.ofReal_le_ofReal_iff hR.le]
  have heq : riemannianClosedBallOf metric p.val R = Metric.closedBall 0 R := by
    ext z
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm z
  have hcpt : IsCompact (riemannianClosedBallOf metric p.val R) :=
    heq ▸ isCompact_closedBall _ _
  have hsource : riemannianClosedBallOf metric p.val R ⊆ standardCapWindow D := by
    intro z hz
    exact ((hnorm z).mp hz).trans_lt hRD
  have hc := ball_subset_image_of_metric_lower_on_opens g metric
    (standardCapWindow D) Φ hΦ hinj p hR hL hcpt hsource
    (fun x hx => hlower x ((hnorm x.val).mp hx))
  exact hc.trans (image_mono (fun x hx => (hnorm x.val).mp hx))

theorem window_ball_subset_image_closedBall_of_metric_bounds
    (g : SmoothRiemannianMetric I M) {D R L U d r : ℝ} (hR : 0 < R)
    (hRD : R < D + 1) (hL : 0 < L) (hU : 0 < U) (hd : 0 ≤ d)
    (Φ : standardCapWindow D → M) (hΦ : IsLocalDiffeomorph ThreeModel I ∞ Φ)
    (hinj : Injective Φ)
    (hlower : ∀ x : standardCapWindow D, ‖x.val‖ ≤ R → ∀ v : TangentSpace ThreeModel x,
      metric.inner x.val v v ≤ L ^ 2 *
        g.inner (Φ x) (mfderiv ThreeModel I Φ x v) (mfderiv ThreeModel I Φ x v))
    (hupper : ∀ x : standardCapWindow D, ‖x.val‖ ≤ R → ∀ v : TangentSpace ThreeModel x,
      g.inner (Φ x) (mfderiv ThreeModel I Φ x v) (mfderiv ThreeModel I Φ x v) ≤
        U ^ 2 * metric.inner x.val v v)
    (u : standardCapWindow D) (hu : ‖u.val‖ < R) (y : M)
    (hnear : riemannianEDistOf g (Φ u) y ≤ ENNReal.ofReal d)
    (hmargin : U * ‖u.val‖ + d + r ≤ R / L) :
    riemannianBallOf g y r ⊆ Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ R} := by
  let p : standardCapWindow D := ⟨0, by
    change ‖(0 : ThreeSpace)‖ < D + 1
    simpa only [norm_zero] using hR.trans hRD⟩
  have hp : p.val = (0 : ThreeSpace) := rfl
  have htip := window_edist_map_le_of_metric_upper_of_radius_le g hRD.le hU
    Φ hΦ hinj (fun x hx => hupper x hx.le) p u (by simpa only [hp, norm_zero] using hR) hu
  simp only [hp, norm_zero, zero_add] at htip
  have htipy : riemannianEDistOf g (Φ p) y ≤ ENNReal.ofReal (U * ‖u.val‖ + d) := by
    apply (riemannianEDistOf_triangle g (Φ p) (Φ u) y).trans
    rw [ENNReal.ofReal_add (mul_nonneg hU.le (norm_nonneg _)) hd]
    exact add_le_add htip hnear
  apply subset_trans ?_
    (window_tip_ball_subset_image_closedBall_of_metric_lower g hR hRD hL Φ hΦ hinj p hp hlower)
  intro z hz
  have hr : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt (bot_le) hz)
  change riemannianEDistOf g (Φ p) z < ENNReal.ofReal (R / L)
  apply (riemannianEDistOf_triangle g (Φ p) y z).trans_lt
  apply lt_of_lt_of_le (ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top htipy) htipy hz)
  rw [← ENNReal.ofReal_add (add_nonneg (mul_nonneg hU.le (norm_nonneg _)) hd) hr.le]
  exact ENNReal.ofReal_le_ofReal hmargin


theorem window_exists_preimage_and_ball_subset_image_of_scaled_metric_bounds
    (g : SmoothRiemannianMetric I M) {D R₀ R₁ R₂ L U q Q C d r : ℝ}
    (hR₁ : 0 < R₁) (hR₁₂ : R₁ ≤ R₂) (hR₂D : R₂ < D + 1)
    (hL : 0 < L) (hU : 0 < U) (hq : 0 < q) (hQ : 0 < Q) (hC : 0 < C)
    (hscale : q ≤ C * Q) (hd : 0 ≤ d) (hr : 0 ≤ r)
    (Φ : standardCapWindow D → M) (hΦ : IsLocalDiffeomorph ThreeModel I ∞ Φ)
    (hinj : Injective Φ)
    (hlower : ∀ x : standardCapWindow D, ‖x.val‖ ≤ R₂ → ∀ v : TangentSpace ThreeModel x,
      metric.inner x.val v v ≤ L ^ 2 *
        (scaleMetric q hq g).inner (Φ x) (mfderiv ThreeModel I Φ x v) (mfderiv ThreeModel I Φ x v))
    (hupper : ∀ x : standardCapWindow D, ‖x.val‖ ≤ R₂ → ∀ v : TangentSpace ThreeModel x,
      (scaleMetric q hq g).inner (Φ x) (mfderiv ThreeModel I Φ x v) (mfderiv ThreeModel I Φ x v) ≤
        U ^ 2 * metric.inner x.val v v)
    (u : standardCapWindow D) (hu : ‖u.val‖ ≤ R₀) (huR : R₀ < R₁) (y : M)
    (hnear : riemannianEDistOf g (Φ u) y ≤ ENNReal.ofReal (d / Real.sqrt Q))
    (hinner : U * R₀ + d * Real.sqrt C < R₁ / L)
    (houter : U * R₀ + (d + r) * Real.sqrt C ≤ R₂ / L) :
    (∃ x : standardCapWindow D, ‖x.val‖ ≤ R₁ ∧ Φ x = y) ∧
      riemannianBallOf g y (r / Real.sqrt Q) ⊆
        Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ R₂} := by
  have hratio : Real.sqrt q / Real.sqrt Q ≤ Real.sqrt C := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hQ)).mpr
    calc
      Real.sqrt q ≤ Real.sqrt (C * Q) := Real.sqrt_le_sqrt hscale
      _ = Real.sqrt C * Real.sqrt Q := Real.sqrt_mul hC.le Q
  have hlength (a : ℝ) (ha : 0 ≤ a) :
      Real.sqrt q * (a / Real.sqrt Q) ≤ a * Real.sqrt C := by
    calc
      Real.sqrt q * (a / Real.sqrt Q) = a * (Real.sqrt q / Real.sqrt Q) := by ring
      _ ≤ a * Real.sqrt C := mul_le_mul_of_nonneg_left hratio ha
  have hnearq : riemannianEDistOf (scaleMetric q hq g) (Φ u) y ≤
      ENNReal.ofReal (d * Real.sqrt C) := by
    rw [edistOf_scale]
    apply (mul_le_mul (le_refl (ENNReal.ofReal (Real.sqrt q))) hnear bot_le bot_le).trans
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg q)]
    exact ENNReal.ofReal_le_ofReal (hlength d hd)
  have hinner' : U * ‖u.val‖ + d * Real.sqrt C < R₁ / L :=
    (add_le_add (mul_le_mul_of_nonneg_left hu hU.le) le_rfl).trans_lt hinner
  let e := (R₁ / L - (U * ‖u.val‖ + d * Real.sqrt C)) / 2
  have he : 0 < e := half_pos (sub_pos.mpr hinner')
  have hsmall := window_ball_subset_image_closedBall_of_metric_bounds
    (scaleMetric q hq g) hR₁ (hR₁₂.trans_lt hR₂D) hL hU
    (mul_nonneg hd (Real.sqrt_nonneg C)) Φ hΦ hinj
    (fun x hx => hlower x (hx.trans hR₁₂)) (fun x hx => hupper x (hx.trans hR₁₂))
    u (hu.trans_lt huR) y hnearq (r := e) (by dsimp only [e]; linarith)
  have hyy : y ∈ riemannianBallOf (scaleMetric q hq g) y e := by
    change riemannianEDistOf (scaleMetric q hq g) y y < ENNReal.ofReal e
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr he
  obtain ⟨x, hx, hxy⟩ := hsmall hyy
  refine ⟨⟨x, hx, hxy⟩, ?_⟩
  have hlarge := window_ball_subset_image_closedBall_of_metric_bounds
    (scaleMetric q hq g) (hR₁.trans_le hR₁₂) hR₂D hL hU
    (mul_nonneg hd (Real.sqrt_nonneg C)) Φ hΦ hinj hlower hupper
    u ((hu.trans_lt huR).trans_le hR₁₂) y hnearq (r := r * Real.sqrt C) (by
      have hh := mul_le_mul_of_nonneg_left hu hU.le
      nlinarith)
  apply subset_trans ?_ hlarge
  rw [← riemannianBallOf_scaleMetric q hq g y (r / Real.sqrt Q)]
  exact riemannianBallOf_mono _ _ (hlength r hr)

theorem window_ball_subset_image_ball_of_metric_bounds
    (g : SmoothRiemannianMetric I M) {D R L U d r : ℝ}
    (hRD : R < D + 1) (hL : 0 < L) (hU : 0 < U) (hd : 0 ≤ d)
    (Φ : standardCapWindow D → M) (hΦ : IsLocalDiffeomorph ThreeModel I ∞ Φ)
    (hinj : Injective Φ)
    (hlower : ∀ x : standardCapWindow D, ‖x.val‖ < R → ∀ v : TangentSpace ThreeModel x,
      metric.inner x.val v v ≤ L ^ 2 *
        g.inner (Φ x) (mfderiv ThreeModel I Φ x v) (mfderiv ThreeModel I Φ x v))
    (hupper : ∀ x : standardCapWindow D, ‖x.val‖ < R → ∀ v : TangentSpace ThreeModel x,
      g.inner (Φ x) (mfderiv ThreeModel I Φ x v) (mfderiv ThreeModel I Φ x v) ≤
        U ^ 2 * metric.inner x.val v v)
    (u : standardCapWindow D) (hu : ‖u.val‖ < R) (y : M)
    (hnear : riemannianEDistOf g (Φ u) y ≤ ENNReal.ofReal d)
    (hmargin : U * ‖u.val‖ + d + r < R / L) :
    riemannianBallOf g y r ⊆ Φ '' {x : standardCapWindow D | ‖x.val‖ < R} := by
  have hmargin' : L * (U * ‖u.val‖ + d + r) < R := by
    simpa only [mul_comm L] using (lt_div_iff₀ hL).mp hmargin
  obtain ⟨S, hS, hSR⟩ := exists_between (max_lt hu hmargin')
  have huS : ‖u.val‖ < S := (le_max_left _ _).trans_lt hS
  have hSpos : 0 < S := (norm_nonneg _).trans_lt huS
  have hmarginS : U * ‖u.val‖ + d + r ≤ S / L := by
    apply (le_div_iff₀ hL).mpr
    simpa only [mul_comm L] using ((le_max_right _ _).trans_lt hS).le
  have hball := window_ball_subset_image_closedBall_of_metric_bounds g hSpos
    (hSR.trans hRD) hL hU hd Φ hΦ hinj
    (fun x hx => hlower x (hx.trans_lt hSR))
    (fun x hx => hupper x (hx.trans_lt hSR)) u huS y hnear hmarginS
  exact hball.trans (image_mono (fun x hx => hx.trans_lt hSR))

end DifferentialGeometry.PDE.RicciFlow.StandardCap

end

section

set_option autoImplicit false
noncomputable section
open Set Filter
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

universe u

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type u} [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace H (M n)]
  [∀ n, IsManifold I ∞ (M n)]

theorem eventually_window_scaled_metric_bounds_of_metric_cp_convergence
    {D R : ℝ} (hR : R < D + 1)
    (g : ℕ → SmoothRiemannianMetric ThreeModel (standardCapWindow D))
    (gRef : SmoothRiemannianMetric ThreeModel (standardCapWindow D))
    {order : ℕ}
    (hconv : MetricCPConvergenceOn {x : standardCapWindow D | ‖x.val‖ ≤ R} order g
      (metric.restrictOpen (standardCapWindow D)) gRef)
    (h : ∀ n, SmoothRiemannianMetric I (M n)) (q : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (Φ : ∀ n, standardCapWindow D → M n)
    (hmetric : ∀ n (x : standardCapWindow D), ‖x.val‖ ≤ R → ∀ v : TangentSpace ThreeModel x,
      (g n).inner x v v = (scaleMetric (q n) (hq n) (h n)).inner (Φ n x)
        (mfderiv ThreeModel I (Φ n) x v) (mfderiv ThreeModel I (Φ n) x v)) :
    ∀ᶠ n in atTop, ∀ x : standardCapWindow D, ‖x.val‖ ≤ R → ∀ v : TangentSpace ThreeModel x,
      metric.inner x.val v v ≤ (2 : ℝ) ^ 2 *
          (scaleMetric (q n) (hq n) (h n)).inner (Φ n x)
            (mfderiv ThreeModel I (Φ n) x v) (mfderiv ThreeModel I (Φ n) x v) ∧
        (scaleMetric (q n) (hq n) (h n)).inner (Φ n x)
          (mfderiv ThreeModel I (Φ n) x v) (mfderiv ThreeModel I (Φ n) x v) ≤
            (2 : ℝ) ^ 2 * metric.inner x.val v v := by
  have hcompact : IsCompact {x : standardCapWindow D | ‖x.val‖ ≤ R} := by
    have hball : IsCompact {x : ThreeSpace | ‖x‖ ≤ R} := by
      simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : ThreeSpace) R
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hball (by
      intro x hx
      exact ⟨⟨x, show ‖x‖ < D + 1 from hx.trans_lt hR⟩, rfl⟩)
  have hconv0 : MetricCPConvergenceOn {x : standardCapWindow D | ‖x.val‖ ≤ R} 0 g
      (metric.restrictOpen (standardCapWindow D)) gRef := by
    intro ε hε
    obtain ⟨j, hj⟩ := hconv (ε / 2) (by positivity)
    refine ⟨j, fun n hn => ?_⟩
    apply lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall _ 0 _ _ _
      (ε / 2) (by positivity) ?_) (by linarith)
    intro m hm x hx
    exact (derivNorm_le_sup hcompact (hm.trans (Nat.zero_le order)) _ _ _ hx).trans (hj n hn).le
  filter_upwards [hconv0.eventually_quadratic_bounds hcompact (show (0 : ℝ) < 1 / 2 by norm_num)]
    with n hn
  intro x hx v
  have hb := hn x hx v
  simp only [SmoothRiemannianMetric.restrictOpen_inner, hmetric n x hx] at hb
  have hnonneg := metric_inner_self_nonneg metric x.val v
  constructor <;> nlinarith

end DifferentialGeometry.PDE.RicciFlow.StandardCap

end
end
