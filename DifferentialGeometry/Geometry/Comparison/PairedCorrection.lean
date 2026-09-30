import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.AngleEstimates
import DifferentialGeometry.Geometry.Comparison.AlmostRadialPoint
import DifferentialGeometry.Geometry.Comparison.FourPoint

set_option autoImplicit false

open Set Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem opposite_change_and_angle {δ t E D θx θy : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100) (ht : 0 < t)
    (hE : E ≤ δ ^ 2 * t) (hθx : 0 ≤ θx) (hθy : 0 ≤ θy) (hθyδ : θy ≤ 2 * δ)
    (hforward : |D + t * cos θx| ≤ E) (hback : |-D + t * cos θy| ≤ E) :
    (1 - 3 * δ ^ 2) * t ≤ D ∧ Real.pi - 4 * δ ≤ θx := by
  have hcos := cos_le_cos_of_nonneg_of_le_pi hθy
    (show 2 * δ ≤ Real.pi by linarith [two_le_pi]) hθyδ
  have hlower : 1 - 2 * δ ^ 2 ≤ cos θy := by
    nlinarith [one_sub_sq_div_two_le_cos (x := 2 * δ)]
  have hD : (1 - 3 * δ ^ 2) * t ≤ D := by
    have := mul_le_mul_of_nonneg_right hlower ht.le
    have := (abs_le.mp hback).2
    nlinarith
  refine ⟨hD, pi_sub_four_mul_le_of_one_add_cos_le hδ hδ1 hθx ?_⟩
  apply (mul_le_mul_iff_right₀ ht).mp
  have := (abs_le.mp hforward).2
  nlinarith

private theorem cross_change_le {δ t E D θx θy : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100) (ht : 0 ≤ t)
    (hE : E ≤ δ ^ 2 * t) (hθx : 0 ≤ θx) (hθy : 0 ≤ θy)
    (hθxδ : θx ≤ Real.pi / 2 + 5 * δ) (hθyδ : θy ≤ Real.pi / 2 + 2 * δ)
    (hforward : |D + t * cos θx| ≤ E) (hback : |-D + t * cos θy| ≤ E) :
    |D| ≤ 6 * δ * t := by
  have hcosx := cos_le_cos_of_nonneg_of_le_pi hθx
    (show Real.pi / 2 + 5 * δ ≤ Real.pi by linarith [two_le_pi]) hθxδ
  have hcosy := cos_le_cos_of_nonneg_of_le_pi hθy
    (show Real.pi / 2 + 2 * δ ≤ Real.pi by linarith [two_le_pi]) hθyδ
  simp only [cos_add, cos_pi_div_two, sin_pi_div_two, zero_mul, one_mul, zero_sub] at hcosx hcosy
  have hx : -5 * δ ≤ cos θx := by linarith [sin_le (show 0 ≤ 5 * δ by positivity)]
  have hy : -2 * δ ≤ cos θy := by linarith [sin_le (show 0 ≤ 2 * δ by positivity)]
  have hsq : δ ^ 2 ≤ δ := by nlinarith
  have hEt : E ≤ δ * t := hE.trans (mul_le_mul_of_nonneg_right hsq ht)
  apply abs_le.mpr
  constructor
  · have := mul_le_mul_of_nonneg_right hy ht
    have := (abs_le.mp hback).2
    nlinarith [mul_nonneg hδ ht]
  · have := mul_le_mul_of_nonneg_right hx ht
    have := (abs_le.mp hforward).2
    nlinarith

theorem exists_paired_geometric_correction
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ p u : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = u ∧
        eVariationOn c univ < ENNReal.ofReal (dist p u + η))
    {Ω V W : Set X} {x u v : X} {a A δ t : ℝ}
    (hcomp : fourPointComparison 1 Ω) (hV : V ⊆ Ω)
    (hanchors : insert u (insert v W) ⊆ Ω)
    (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100)
    (ht : 0 < t) (ht1 : t ≤ 1) (hta : t ≤ a / 2)
    (hscale : t ≤ δ ^ 2 / (4 * cosh (A + 1) / sinh a))
    (hball : Metric.closedBall x t ⊆ V)
    (hbounds : ∀ z ∈ V, ∀ c ∈ insert u (insert v W), dist z c ∈ Icc a A)
    (hpair : ∀ z ∈ V, Real.pi - δ <
      comparisonAngleNegCurvature 1 (dist z u) (dist z v) (dist u v))
    (hcross : ∀ z ∈ V, ∀ c ∈ W,
      Real.pi / 2 - δ < comparisonAngleNegCurvature 1 (dist z u) (dist z c) (dist u c) ∧
      Real.pi / 2 - δ < comparisonAngleNegCurvature 1 (dist z v) (dist z c) (dist v c)) :
    ∃ y ∈ V, dist x y = t ∧
      (1 - δ ^ 2) * t ≤ dist x u - dist y u ∧ dist x u - dist y u ≤ t ∧
      (1 - 3 * δ ^ 2) * t ≤ dist y v - dist x v ∧ dist y v - dist x v ≤ t ∧
      ∀ c ∈ W, |dist y c - dist x c| ≤ 6 * δ * t := by
  have hx : x ∈ V := hball (Metric.mem_closedBall_self ht.le)
  have hu : u ∈ insert u (insert v W) := mem_insert _ _
  have hv : v ∈ insert u (insert v W) := mem_insert_of_mem _ (mem_insert _ _)
  have hxub := hbounds x hx u hu
  obtain ⟨y, hxy, _, _, hang, _, hdrop, hdropupper, _⟩ :=
    exists_almost_radial_point_with_comparison_angles hcurves x u ha hxub.1 hxub.2
      ht ht1 hta hδ hδ1
  have hy : y ∈ V := hball (by rw [Metric.mem_closedBall, dist_comm y x, hxy])
  let θ (z b c : X) := comparisonAngleNegCurvature 1 (dist z b) (dist z c) (dist b c)
  have hsym (z b c : X) : θ z b c = θ z c b := by
    dsimp [θ]
    rw [comparisonAngleNegCurvature_comm, dist_comm b c]
  have hθ0 (z b c : X) : 0 ≤ θ z b c := (comparisonAngleNegCurvature_mem_Icc _ _ _ _).1
  change Real.pi - δ ≤ θ y u x at hang
  have hnear : Real.pi - δ < θ y u v := hpair y hy
  have hne (z : X) (hz : z ∈ V) (c : X) (hc : c ∈ insert u (insert v W)) : c ≠ z := by
    exact Ne.symm (dist_pos.mp (ha.trans_le (hbounds z hz c hc).1))
  have hxyne : x ≠ y := dist_pos.mp (hxy ▸ ht)
  have hfour : θ y u x + θ y x v + θ y v u ≤ 2 * Real.pi :=
    hcomp y (hV hy) u (hanchors hu) x (hV hx) v (hanchors hv)
      (hne y hy u hu) hxyne (hne y hy v hv)
  have hyangle : θ y v x ≤ 2 * δ := by
    rw [hsym y v u] at hfour
    rw [hsym y v x]
    linarith
  let K := 4 * cosh (A + 1) / sinh a
  have hK : 0 < K := div_pos (mul_pos (by norm_num) (cosh_pos _)) (sinh_pos_iff.mpr ha)
  have hKt : K * t ≤ δ ^ 2 := by
    have := (le_div_iff₀ hK).mp hscale
    nlinarith
  have hE : K * t ^ 2 ≤ δ ^ 2 * t := by nlinarith [mul_le_mul_of_nonneg_right hKt ht.le]
  have herror (z z' c : X) (hz : z ∈ V) (hzz' : dist z z' = t)
      (hc : c ∈ insert u (insert v W)) :
      |dist z' c - dist z c + t * cos (θ z c z')| ≤ K * t ^ 2 := by
    have hb := hbounds z hz c hc
    have he := abs_dist_sub_add_cos_comparisonAngleNegCurvature_one_le z z' c ha hb.1 hb.2
      (by rwa [hzz']) (by rwa [hzz']) (by rwa [hzz'])
    simpa only [θ, K, hzz', dist_comm z' c] using he
  have hyx : dist y x = t := by rw [dist_comm, hxy]
  have hforward := herror x y v hx hxy hv
  have hback := herror y x v hy hyx hv
  have hback' : |-(dist y v - dist x v) + t * cos (θ y v x)| ≤ K * t ^ 2 := by
    simpa only [neg_sub] using hback
  obtain ⟨hopp, hxangle⟩ := opposite_change_and_angle hδ.le hδ1 ht hE
    (hθ0 x v y) (hθ0 y v x) hyangle hforward hback'
  refine ⟨y, hy, hxy, hdrop, hdropupper, hopp, ?_, ?_⟩
  · have := dist_triangle y x v
    rw [hyx] at this
    linarith
  · intro c hcW
    have hc : c ∈ insert u (insert v W) := mem_insert_of_mem _ (mem_insert_of_mem _ hcW)
    have hfourx : θ x v c + θ x c y + θ x y v ≤ 2 * Real.pi :=
      hcomp x (hV hx) v (hanchors hv) c (hanchors hc) y (hV hy)
        (hne x hx v hv) (hne x hx c hc) hxyne.symm
    rw [hsym x y v] at hfourx
    have hcrossx : Real.pi / 2 - δ < θ x v c := (hcross x hx c hcW).2
    have hcx : θ x c y ≤ Real.pi / 2 + 5 * δ := by linarith
    have hfoury : θ y u c + θ y c x + θ y x u ≤ 2 * Real.pi :=
      hcomp y (hV hy) u (hanchors hu) c (hanchors hc) x (hV hx)
        (hne y hy u hu) (hne y hy c hc) hxyne
    rw [hsym y x u] at hfoury
    have hcrossy : Real.pi / 2 - δ < θ y u c := (hcross y hy c hcW).1
    have hcy : θ y c x ≤ Real.pi / 2 + 2 * δ := by linarith
    apply cross_change_le hδ.le hδ1 ht.le hE (hθ0 x c y) (hθ0 y c x) hcx hcy
      (herror x y c hx hxy hc)
    simpa only [neg_sub] using herror y x c hy hyx hc

end DifferentialGeometry.Geometry.Comparison.Toponogov
