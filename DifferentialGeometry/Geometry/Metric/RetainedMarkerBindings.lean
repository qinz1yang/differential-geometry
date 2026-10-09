import DifferentialGeometry.Geometry.Metric.RetainedMarkerLocality
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false
noncomputable section
open Set Metric
namespace GC.MetricGeometry

theorem retained_marker_image_radius
    {P X A : Type*} [PseudoMetricSpace X]
    (f : P → X) (ρ : P → ℝ) (marker : A → X → ℝ) (R : A → ℝ)
    (hR : ∀ i, 0 < R i) (hmarker : ∀ i, LipschitzWith 1 (marker i))
    (hfull : ∀ p, ∃ i, marker i (f p) = R i)
    (hsupport : ∀ i p, 0 < marker i (f p) → 3 * R i / 4 ≤ ρ p ∧ ρ p ≤ 5 * R i / 4)
    (σ L : ℝ) (hσ : 0 < σ) (hL : 0 ≤ L) (hsmall : L * σ ≤ 1 / 5) :
    let r : Set.range f → ℝ := fun x => σ * ρ (Classical.choose x.property)
    (∀ x, 0 < r x) ∧
      (∀ x y : Set.range f, dist (x : X) (y : X) ≤ L * max (r x) (r y) →
        (3 / 5 : ℝ) * r x ≤ r y ∧ r y ≤ (5 / 3 : ℝ) * r x) ∧
      (∀ (p : P) (x : Set.range f), f p = (x : X) →
        (3 / 5 : ℝ) * (σ * ρ p) ≤ r x ∧ r x ≤ (5 / 3 : ℝ) * (σ * ρ p)) := by
  classical
  dsimp only
  have hx (x : Set.range f) : f (Classical.choose x.property) = (x : X) :=
    Classical.choose_spec x.property
  have hp (p : P) : 0 < ρ p := by
    obtain ⟨i, hi⟩ := hfull p
    have hs := hsupport i p (by rw [hi]; exact hR i)
    linarith [hR i]
  refine ⟨fun x => mul_pos hσ (hp _), ?_, ?_⟩
  · intro x y hd
    have hh := nearby_scale_comparison_of_retained_markers f ρ marker R hR hmarker
      hfull hsupport hσ.le hL hsmall (Classical.choose x.property)
      (Classical.choose y.property) (by simpa only [hx] using hd)
    have hlo := mul_le_mul_of_nonneg_left hh.1 hσ.le
    have hup := mul_le_mul_of_nonneg_left hh.2 hσ.le
    constructor <;> nlinarith
  · intro p x heq
    obtain ⟨i, hi⟩ := hfull p
    have hh := scale_comparison_of_retained_marker f ρ marker R hR hsupport
      (heq.trans (hx x).symm) i hi
    have hlo := mul_le_mul_of_nonneg_left hh.2.1 hσ.le
    have hup := mul_le_mul_of_nonneg_left hh.2.2 hσ.le
    constructor <;> nlinarith

theorem retained_marker_projected_half_buffer
    {P A E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (π : E →L[ℝ] H) (hπ : ‖π‖ ≤ 1) (F f : P → E)
    (ρ : P → ℝ) (marker : A → H → ℝ) (R : A → ℝ)
    (hR : ∀ i, 0 < R i)
    (hsupport : ∀ i p, 0 < marker i (π (F p)) →
      3 * R i / 4 ≤ ρ p ∧ ρ p ≤ 5 * R i / 4)
    (p px : P) (heq : π (F p) = π (F px))
    (i : A) (hfull : marker i (π (F p)) = R i)
    (σ e : ℝ) (hσ : 0 < σ) (he : e ≤ 3 * σ / 10)
    (herror : ‖f p - F p‖ ≤ e * ρ p) :
    let r := σ * ρ px
    0 < r ∧ (3 / 5 : ℝ) * (σ * ρ p) ≤ r ∧
      r ≤ (5 / 3 : ℝ) * (σ * ρ p) ∧
      ‖π (f p) - π (F p)‖ ≤ r / 2 ∧
      ball (π (f p)) (r / 2) ⊆ ball (π (F p)) r ∧
      segment ℝ (π (F p)) (π (f p)) ⊆ ball (π (F p)) r := by
  have hc := scale_comparison_of_retained_marker (fun q => π (F q)) ρ marker R
    hR hsupport heq i hfull
  have hρpx : 0 < ρ px := by linarith [hc.1, hc.2.1]
  have hlo := mul_le_mul_of_nonneg_left hc.2.1 hσ.le
  have hup := mul_le_mul_of_nonneg_left hc.2.2 hσ.le
  have hd : ‖π (f p) - π (F p)‖ ≤ σ * ρ px / 2 := by
    rw [← map_sub]
    have hh := (π.le_opNorm (f p - F p)).trans
      ((mul_le_mul_of_nonneg_right hπ (norm_nonneg _)).trans_eq (one_mul _))
    have heρ := mul_le_mul_of_nonneg_right he hc.1.le
    exact hh.trans (herror.trans (by nlinarith))
  dsimp only
  refine ⟨mul_pos hσ hρpx, by nlinarith, by nlinarith, hd, ?_, ?_⟩
  · intro z hz
    have ht := dist_triangle z (π (f p)) (π (F p))
    rw [dist_eq_norm (π (f p)) (π (F p))] at ht
    change dist z (π (F p)) < σ * ρ px
    have hz' : dist z (π (f p)) < σ * ρ px / 2 := hz
    linarith
  · exact (convex_ball (π (F p)) (σ * ρ px)).segment_subset
      (mem_ball_self (mul_pos hσ hρpx))
      (show π (f p) ∈ ball (π (F p)) (σ * ρ px) from by
        rw [mem_ball, dist_eq_norm]
        exact hd.trans_lt (by nlinarith [mul_pos hσ hρpx]))

theorem retained_marker_selected_cloud_control {MP MI H : Type*} [PseudoMetricSpace H]
    (f : MP → H) (ρ : MP → ℝ) (marker : MI → H → ℝ) (R : MI → ℝ)
    (hR : ∀ i, 0 < R i) (hmarker : ∀ i, LipschitzWith 1 (marker i))
    (hfull : ∀ p, ∃ i, marker i (f p) = R i)
    (hsupport : ∀ i p, 0 < marker i (f p) → 3 * R i / 4 ≤ ρ p ∧ ρ p ≤ 5 * R i / 4)
    (T : Set H) (select : H → MP) (hselect : ∀ x ∈ T, f (select x) = x)
    (r : H → ℝ) {σ L : ℝ} (hr : ∀ x ∈ T, r x = σ * ρ (select x))
    (hσ : 0 ≤ σ) (hL : 0 ≤ L) (hsmall : L * σ ≤ 1 / 5) :
    ∀ x ∈ T, ∀ y ∈ T, dist y x ≤ L * max (r y) (r x) →
      r x / (5 / 3) ≤ r y ∧ r y ≤ (5 / 3) * r x := by
  intro x hx y hy hdist
  have hn := nearby_scale_comparison_of_retained_markers f ρ marker R hR hmarker hfull
    hsupport hσ hL hsmall (select x) (select y) (by
      simpa only [hselect x hx, hselect y hy, ← hr x hx, ← hr y hy, dist_comm,
        max_comm] using hdist)
  rw [hr x hx, hr y hy]
  have hlo := mul_le_mul_of_nonneg_left hn.1 hσ
  have hup := mul_le_mul_of_nonneg_left hn.2 hσ
  constructor <;> nlinarith

end GC.MetricGeometry
