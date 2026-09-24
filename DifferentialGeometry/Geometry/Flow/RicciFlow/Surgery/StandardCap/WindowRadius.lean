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

theorem window_edist_map_le_of_metric_upper
    (g : SmoothRiemannianMetric I M) {D L : ℝ} (hL : 0 < L)
    (Φ : standardCapWindow D → M) (hΦ : IsLocalDiffeomorph ThreeModel I ∞ Φ)
    (hinj : Injective Φ)
    (hupper : ∀ z : standardCapWindow D, ‖z.val‖ < D → ∀ v : TangentSpace ThreeModel z,
      g.inner (Φ z) (mfderiv ThreeModel I Φ z v) (mfderiv ThreeModel I Φ z v) ≤
        L ^ 2 * metric.inner z.val v v)
    (x y : standardCapWindow D) (hx : ‖x.val‖ < D) (hy : ‖y.val‖ < D) :
    riemannianEDistOf g (Φ x) (Φ y) ≤ ENNReal.ofReal (L * (‖x.val‖ + ‖y.val‖)) := by
  have hD : 0 < D := (norm_nonneg x.val).trans_lt hx
  let p : standardCapWindow D := ⟨0, by
    change ‖(0 : ThreeSpace)‖ < D + 1
    simp only [norm_zero]
    linarith⟩
  have hradial (z : standardCapWindow D) (hz : ‖z.val‖ < D) :
      riemannianEDistOf g (Φ p) (Φ z) ≤ ENNReal.ofReal (L * ‖z.val‖) := by
    obtain ⟨R, hzR, hRD⟩ := exists_between hz
    have hR : 0 < R := (norm_nonneg z.val).trans_lt hzR
    have hsource : riemannianClosedBallOf metric p.val R ⊆ standardCapWindow D := by
      intro a ha
      have hn : ‖a‖ ≤ R := by
        change riemannianEDistOf metric 0 a ≤ ENNReal.ofReal R at ha
        rw [edist_zero, ENNReal.ofReal_le_ofReal_iff hR.le] at ha
        exact ha
      change ‖a‖ < D + 1
      linarith
    have hb := Geometry.Metric.edistOf_map_le_of_metric_upper_on_opens
      g metric (standardCapWindow D) Φ hΦ hinj p z hR hL hsource
      (fun a ha v => hupper a (by
        change riemannianEDistOf metric 0 a.val ≤ ENNReal.ofReal R at ha
        rw [edist_zero, ENNReal.ofReal_le_ofReal_iff hR.le] at ha
        exact ha.trans_lt hRD) v) (by
        change riemannianEDistOf metric 0 z.val < ENNReal.ofReal R
        rw [edist_zero]
        exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr hzR)
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

end DifferentialGeometry.PDE.RicciFlow.StandardCap
