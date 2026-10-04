import DifferentialGeometry.Geometry.Metric.RetainedMarkerLocality
import DifferentialGeometry.Geometry.Metric.AffinePlaneCoherence
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Module.Convex

/-! Actual retained-marker radii and projected half-tubes for the unchanged original cloud. -/

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

variable {MP MI H : Type*}

theorem markerChosenRadius_local_scale_control [PseudoMetricSpace H]
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

theorem markerChosenRadius_coarse_control [PseudoMetricSpace H]
    (f : MP → H) (ρ : MP → ℝ) (marker : MI → H → ℝ) (R : MI → ℝ)
    (hR : ∀ i, 0 < R i) (hmarker : ∀ i, LipschitzWith 1 (marker i))
    (hfull : ∀ p, ∃ i, marker i (f p) = R i)
    (hsupport : ∀ i p, 0 < marker i (f p) → 3 * R i / 4 ≤ ρ p ∧ ρ p ≤ 5 * R i / 4)
    (T : Set H) (select : H → MP) (hselect : ∀ x ∈ T, f (select x) = x)
    (r : H → ℝ) {σ : ℝ} (hr : ∀ x ∈ T, r x = σ * ρ (select x))
    (hσ : 0 ≤ σ) (hσhalf : σ ≤ 1 / 2) :
    ∀ x ∈ T, ∀ y ∈ T, |r y - r x| ≤ 2 * (dist x y + r x) := by
  intro x hx y hy
  have hh := radius_control_of_retained_markers f ρ marker R hR hmarker hfull hsupport
    hσ hσhalf (select x) (select y)
  simpa only [hselect x hx, hselect y hy, ← hr x hx, ← hr y hy] using hh

theorem marker_cloud_plane_coherence [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : MP → H) (ρ : MP → ℝ) (marker : MI → H → ℝ) (R : MI → ℝ)
    (hR : ∀ i, 0 < R i) (hmarker : ∀ i, LipschitzWith 1 (marker i))
    (hfull : ∀ p, ∃ i, marker i (f p) = R i)
    (hsupport : ∀ i p, 0 < marker i (f p) → 3 * R i / 4 ≤ ρ p ∧ ρ p ≤ 5 * R i / 4)
    (T : Set H) (select : H → MP) (hselect : ∀ x ∈ T, f (select x) = x)
    (r : H → ℝ) {σ L : ℝ} (hr : ∀ x ∈ T, r x = σ * ρ (select x))
    (hσ : 0 < σ) (hL : 1 ≤ L) (hsmall : L * σ ≤ 1 / 5)
    (x y : H) (hx : x ∈ T) (hy : y ∈ T)
    (hdist : dist y x ≤ L * max (r y) (r x))
    (P Q : Submodule ℝ H) [FiniteDimensional ℝ P] [FiniteDimensional ℝ Q]
    (hdim : Module.finrank ℝ P = Module.finrank ℝ Q)
    {δ : ℝ} (hδ : 0 < δ)
    (hδsmall : δ < min (1 / (4 * (5 / 3 : ℝ)))
      (min (1 / (2 * (L * (5 / 3) + 3))) (1 / (4 * ((5 / 3 : ℝ) + 1)))))
    (hcloudx : hausdorffEDist (T ∩ ball x (r x / δ))
      ((AffineSubspace.mk' x P : Set H) ∩ ball x (r x / δ)) ≤ ENNReal.ofReal (δ * r x))
    (hcloudy : hausdorffEDist (T ∩ ball y (r y / δ))
      ((AffineSubspace.mk' y Q : Set H) ∩ ball y (r y / δ)) ≤ ENNReal.ofReal (δ * r y)) :
    ‖Pᗮ.starProjection (y - x)‖ ≤ δ * r x ∧
      ‖Pᗮ.starProjection - Qᗮ.starProjection‖ ≤ 16 * δ := by
  have hlocal := markerChosenRadius_local_scale_control f ρ marker R hR hmarker hfull
    hsupport T select hselect r hr hσ.le (by linarith) hsmall x hx y hy hdist
  obtain ⟨i, hi⟩ := hfull (select x)
  have hsupportx := hsupport i (select x) (by rw [hi]; exact hR i)
  have hρx : 0 < ρ (select x) := by linarith [hR i, hsupportx.1]
  have hrx : 0 < r x := by rw [hr x hx]; exact mul_pos hσ hρx
  have hm : max (r y) (r x) ≤ (5 / 3 : ℝ) * r x :=
    max_le hlocal.2 (by nlinarith)
  have hcenter : ‖y - x‖ ≤ (L * (5 / 3)) * r x := by
    rw [← dist_eq_norm]
    exact hdist.trans (by nlinarith [mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ L)])
  have hδbound : δ < 1 / (4 * ((5 / 3 : ℝ) + 1)) :=
    hδsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hinterior : δ * (L * (5 / 3) + 2) < 1 := by
    have hs : δ < 1 / (2 * (L * (5 / 3) + 3)) :=
      hδsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hprod := (lt_div_iff₀ (by positivity : 0 < 2 * (L * (5 / 3) + 3))).mp hs
    nlinarith
  have hh := normal_offset_and_projection_gap_le_of_large_affine_hausdorffEDist
    P Q hdim T x y hy hrx (by norm_num : (1 : ℝ) ≤ 5 / 3)
    hlocal.1 hlocal.2 hcenter hδ hδbound hinterior hcloudx hcloudy
  simpa only [show 6 * ((5 / 3 : ℝ) + 1) = 16 by norm_num] using hh

theorem markerChosenRadius_halfTube [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F g : MP → H) (Q : H →L[ℝ] H) (hQ : ‖Q‖ ≤ 1)
    (ρ : MP → ℝ) (marker : MI → H → ℝ) (R : MI → ℝ)
    (hR : ∀ i, 0 < R i) (hfull : ∀ p, ∃ i, marker i (Q (F p)) = R i)
    (hsupport : ∀ i p, 0 < marker i (Q (F p)) →
      3 * R i / 4 ≤ ρ p ∧ ρ p ≤ 5 * R i / 4)
    (p q : MP) (hpreimage : Q (F q) = Q (F p))
    {σ e : ℝ} (hσ : 0 < σ) (he : e ≤ 3 * σ / 10)
    (herror : ‖g p - F p‖ ≤ e * ρ p) :
    let r := σ * ρ q
    0 < r ∧ (3 / 5 : ℝ) * σ * ρ p ≤ r ∧ r ≤ (5 / 3 : ℝ) * σ * ρ p ∧
      dist (Q (g p)) (Q (F p)) ≤ r / 2 ∧
      ball (Q (g p)) (r / 2) ⊆ ball (Q (F p)) r ∧
      segment ℝ (Q (F p)) (Q (g p)) ⊆ ball (Q (F p)) r := by
  obtain ⟨i, hi⟩ := hfull p
  have hc := scale_comparison_of_retained_marker (fun v => Q (F v)) ρ marker R
    hR hsupport hpreimage.symm i hi
  have hρq : 0 < ρ q := by linarith [hc.1, hc.2.1]
  have hρp : 0 < ρ p := hc.1
  have hlo := mul_le_mul_of_nonneg_left hc.2.1 hσ.le
  have hup := mul_le_mul_of_nonneg_left hc.2.2 hσ.le
  have hd : dist (Q (g p)) (Q (F p)) ≤ σ * ρ q / 2 := by
    have hcontract : ‖Q (g p - F p)‖ ≤ ‖g p - F p‖ :=
      (Q.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hQ (norm_nonneg _)).trans_eq
        (one_mul _))
    have heρ := mul_le_mul_of_nonneg_right he hρp.le
    rw [dist_eq_norm, ← map_sub]
    exact hcontract.trans (herror.trans (by nlinarith))
  dsimp only
  refine ⟨mul_pos hσ hρq, by nlinarith, by nlinarith, hd, ?_, ?_⟩
  · intro z hz
    have ht := dist_triangle z (Q (g p)) (Q (F p))
    have hz' : dist z (Q (g p)) < σ * ρ q / 2 := hz
    change dist z (Q (F p)) < σ * ρ q
    linarith
  · exact (convex_ball (Q (F p)) (σ * ρ q)).segment_subset
      (mem_ball_self (mul_pos hσ hρq))
      (show Q (g p) ∈ ball (Q (F p)) (σ * ρ q) from
        hd.trans_lt (by nlinarith [mul_pos hσ hρq]))

theorem marker_support_scales_on_original_domains
    {M : Type*} [PseudoMetricSpace M] (f : M → H) (ρ : M → ℝ)
    {Λ : NNReal} (hρ : LipschitzWith Λ ρ) (center : MI → M) (U : MI → Set M)
    (marker : MI → H → ℝ) {D : ℝ} (hsmall : (Λ : ℝ) * D ≤ 1 / 4)
    (hpositive : ∀ i, 0 < ρ (center i))
    (hU : ∀ i, U i ⊆ closedBall (center i) (D * ρ (center i)))
    (hsupport : ∀ i p, 0 < marker i (f p) → p ∈ U i) :
    ∀ i p, 0 < marker i (f p) →
      3 * ρ (center i) / 4 ≤ ρ p ∧ ρ p ≤ 5 * ρ (center i) / 4 := by
  intro i p hp
  exact scale_bounds_on_closedBall hρ (hpositive i) hsmall (hU i (hsupport i p hp))

theorem packet_cutoff_support_scales
    {M : Type*} [PseudoMetricSpace M] (f : M → H) (ρ : M → ℝ)
    {Λ : NNReal} (hρ : LipschitzWith Λ ρ) (center : MI → M)
    (ζ : MI → M → ℝ) (marker : MI → H → ℝ) {D : ℝ}
    (hsmall : (Λ : ℝ) * D ≤ 1 / 4) (hpositive : ∀ i, 0 < ρ (center i))
    (hsupport : ∀ i, tsupport (ζ i) ⊆ closedBall (center i) (D * ρ (center i)))
    (hmarker : ∀ i p, marker i (f p) = ρ (center i) * ζ i p) :
    (∀ i p, p ∈ tsupport (ζ i) →
      3 * ρ (center i) / 4 ≤ ρ p ∧ ρ p ≤ 5 * ρ (center i) / 4) ∧
    (∀ i p, 0 < marker i (f p) →
      3 * ρ (center i) / 4 ≤ ρ p ∧ ρ p ≤ 5 * ρ (center i) / 4) ∧
    (∀ p, (∃ i, ζ i p = 1) → ∃ i, marker i (f p) = ρ (center i)) := by
  have hb (i : MI) (p : M) (hp : p ∈ tsupport (ζ i)) :=
    scale_bounds_on_closedBall hρ (hpositive i) hsmall (hsupport i hp)
  refine ⟨hb, ?_, ?_⟩
  · intro i p hp
    have hn : ζ i p ≠ 0 := by
      intro hz
      rw [hmarker i p, hz, mul_zero] at hp
      exact lt_irrefl 0 hp
    exact hb i p (subset_tsupport (ζ i) hn)
  · intro p hp
    obtain ⟨i, hi⟩ := hp
    exact ⟨i, by rw [hmarker i p, hi, mul_one]⟩

theorem constant_marker_halfTube_consumer (p q : ℝ) {σ e : ℝ}
    (hσ : 0 < σ) (he : e ≤ 3 * σ / 10) (hf : |q - p| ≤ e) :
    Metric.ball q (σ / 2) ⊆ Metric.ball p σ ∧
      segment ℝ p q ⊆ Metric.ball p σ := by
  have hh := markerChosenRadius_halfTube (MP := Unit) (MI := Unit)
    (fun v => p) (fun v => q) (ContinuousLinearMap.id ℝ ℝ)
    (by simpa only [ContinuousLinearMap.norm_id] using (le_refl (1 : ℝ)))
    (fun v => 1) (fun i z => 1) (fun i => 1) (fun i => by norm_num)
    (fun v => ⟨(), rfl⟩) (by intro i v h; constructor <;> norm_num)
    () () rfl hσ he (by simpa only [Real.norm_eq_abs, mul_one] using hf)
  simpa only [ContinuousLinearMap.id_apply, mul_one] using hh.2.2.2.2

end GC.MetricGeometry
