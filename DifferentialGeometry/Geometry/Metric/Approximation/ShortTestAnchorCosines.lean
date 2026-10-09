import DifferentialGeometry.Geometry.Metric.Approximation.ProductAnchors

/-!
# Prescribed anchor comparison for half-unit tested segments

A lower bound of one half for the tested length keeps the genuine coarse-source
anchors and allows the physical length cutoff of a scale near one.
-/

set_option autoImplicit false

open Set Metric
open GC.MetricGeometry
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

private theorem square_error {a b η S : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbS : b ≤ S) (he : |a - b| ≤ η) : |a ^ 2 - b ^ 2| ≤ η * (2 * S + η) := by
  have hη : 0 ≤ η := (abs_nonneg _).trans he
  have haS : a ≤ S + η := by linarith [(abs_le.mp he).2]
  rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul,
    abs_of_nonneg (add_nonneg ha hb)]
  exact mul_le_mul he (by linarith) (by positivity) hη

private theorem short_cosine_bound {D E A C s B η l t u r v : ℝ}
    (hB : 1 ≤ B) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hs : 2 * (B + 1) < s)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hAs : |A - s| ≤ B) (hCs : |C - s| ≤ B)
    (hDA : |D - A| ≤ η) (hEC : |E - C| ≤ η)
    (ht : |t| ≤ B) (hu : |u| ≤ B) (hr : |r| ≤ B) (hv : |v| ≤ B)
    (hAA : A ^ 2 = (s - t) ^ 2 + r ^ 2)
    (hCC : C ^ 2 = (s - u) ^ 2 + v ^ 2)
    (hl : 1 / 2 ≤ l) (hlB : l ≤ 2 * B) :
    |comparisonCosine D l E - (u - t) / l| ≤ 64 * B ^ 2 / s + 8 * η := by
  have hs0 : 0 < s := by linarith
  have hDlo : s / 2 < D := by
    linarith [(abs_le.mp hAs).1, (abs_le.mp hDA).1]
  have hD0 : 0 < D := by linarith
  have hl0 : 0 < l := by linarith
  have hden : 0 < 2 * D * l := by positivity
  have hdenlo : s / 2 ≤ 2 * D * l := by nlinarith
  have hd := square_error hD hA
    (by linarith [(abs_le.mp hAs).2] : A ≤ s + B) hDA
  have he := square_error hE hC
    (by linarith [(abs_le.mp hCs).2] : C ≤ s + B) hEC
  have hsq (z : ℝ) (hz : |z| ≤ B) : z ^ 2 ≤ B ^ 2 := by
    nlinarith [sq_abs z, (sq_le_sq₀ (abs_nonneg z) (by linarith : 0 ≤ B)).mpr hz]
  have hds : |s - D| ≤ B + η := by
    have h := abs_sub_le s A D
    rw [abs_sub_comm s A, abs_sub_comm A D] at h
    linarith
  have hprod : |(s - D) * (u - t)| ≤ (B + η) * (2 * B) := by
    rw [abs_mul]
    exact mul_le_mul hds ((abs_sub _ _).trans (by linarith))
      (abs_nonneg _) (by linarith)
  have hηB : η ≤ B := by linarith
  have hηsq : η ^ 2 ≤ B ^ 2 := (sq_le_sq₀ hη (by linarith)).mpr hηB
  have hBη : B * η ≤ B ^ 2 := by nlinarith
  have hlsq : l ^ 2 ≤ 4 * B ^ 2 := by nlinarith
  have hnum : |D ^ 2 + l ^ 2 - E ^ 2 - 2 * D * (u - t)| ≤
      32 * B ^ 2 + 4 * s * η := by
    have hd' := abs_le.mp hd
    have he' := abs_le.mp he
    have hp := abs_le.mp hprod
    apply abs_le.mpr
    constructor <;> nlinarith only [hd'.1, hd'.2, he'.1, he'.2, hp.1, hp.2,
      hAA, hCC, hsq t ht, hsq u hu, hsq r hr, hsq v hv, hηsq, hBη, hlsq,
      sq_nonneg t, sq_nonneg u, sq_nonneg r, sq_nonneg v, sq_nonneg l, sq_nonneg B]
  have hid : comparisonCosine D l E - (u - t) / l =
      (D ^ 2 + l ^ 2 - E ^ 2 - 2 * D * (u - t)) / (2 * D * l) := by
    unfold comparisonCosine
    field_simp
  rw [hid, abs_div, abs_of_pos hden]
  calc
    _ ≤ (32 * B ^ 2 + 4 * s * η) / (2 * D * l) :=
      div_le_div_of_nonneg_right hnum hden.le
    _ ≤ (32 * B ^ 2 + 4 * s * η) / (s / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hdenlo
    _ = 64 * B ^ 2 / s + 8 * η := by field_simp; ring

namespace KleinerLottApprox

theorem supplied_positive_anchor_short_comparison {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] {o : X} {y₀ : Y} {ν R s : ℝ}
    (F : KleinerLottApprox o (WithLp.toLp 2 ((0 : ℝ), y₀)) ν)
    (hR : 1 ≤ R) (hν : 3 * ν ≤ 1) (hs : 2 * (R + ν + 1) < s)
    (hRν : R < ν⁻¹) (a : X) (ha : a ∈ ball o ν⁻¹)
    (himage : dist (F.toFun a) (WithLp.toLp 2 (s, y₀)) < 2 * ν)
    (x z : X) (hx : x ∈ ball o R) (hz : z ∈ ball o R) (hl : 1 / 2 ≤ dist x z) :
    |comparisonCosine (dist x a) (dist x z) (dist z a) -
      ((F.toFun z).fst - (F.toFun x).fst) / dist x z| ≤
        64 * (R + ν) ^ 2 / s + 24 * ν := by
  have hrad (w : X) (hw : w ∈ ball o R) :
      dist (F.toFun w) (WithLp.toLp 2 (0, y₀)) ≤ R + ν := by
    have he := (abs_le.mp (F.radial_error w (lt_trans hw hRν))).2
    linarith [Metric.mem_ball.mp hw]
  have hdata (w : X) (hw : w ∈ ball o R) :
      |(F.toFun w).fst| ≤ R + ν ∧ |dist (F.toFun w).snd y₀| ≤ R + ν ∧
      |dist (F.toFun w) (WithLp.toLp 2 (s, y₀)) - s| ≤ R + ν ∧
      dist (F.toFun w) (WithLp.toLp 2 (s, y₀)) ^ 2 =
        (s - (F.toFun w).fst) ^ 2 + dist (F.toFun w).snd y₀ ^ 2 := by
    have hs0 : 0 < s := by linarith [F.error_pos]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [WithLp.toLp_fst, Real.dist_eq, sub_zero] using
        (WithLp.dist_fst_le (F.toFun w) (WithLp.toLp 2 (0, y₀))).trans (hrad w hw)
    · simpa only [WithLp.toLp_snd, abs_of_nonneg dist_nonneg] using
        (WithLp.dist_snd_le (F.toFun w) (WithLp.toLp 2 (0, y₀))).trans (hrad w hw)
    · have he := abs_dist_sub_le (F.toFun w) (WithLp.toLp 2 (0, y₀))
        (WithLp.toLp 2 (s, y₀))
      have hbase := (WithLp.isometry_prodMk_right (E := ℝ) y₀).dist_eq 0 s
      simp only [Real.dist_eq, zero_sub, abs_neg, abs_of_pos hs0] at hbase
      rw [hbase] at he
      exact he.trans (hrad w hw)
    · have he := WithLp.prod_dist_sq_eq_add_sq (F.toFun w) (WithLp.toLp 2 (s, y₀))
      simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.dist_eq, sq_abs] at he
      nlinarith only [he]
  obtain ⟨ht, hr, hAs, hAsq⟩ := hdata x hx
  obtain ⟨hu, hv, hCs, hCsq⟩ := hdata z hz
  have hDA := F.supplied_anchor_distance_error a x (WithLp.toLp 2 (s, y₀)) ha
    (lt_trans hx hRν) himage
  have hEC := F.supplied_anchor_distance_error a z (WithLp.toLp 2 (s, y₀)) ha
    (lt_trans hz hRν) himage
  have hlB : dist x z ≤ 2 * (R + ν) := by
    have hh := dist_triangle x o z
    rw [dist_comm o z] at hh
    linarith [Metric.mem_ball.mp hx, Metric.mem_ball.mp hz, F.error_pos]
  convert short_cosine_bound (by linarith [F.error_pos] : 1 ≤ R + ν)
    (by linarith [F.error_pos] : 0 ≤ 3 * ν) hν hs dist_nonneg dist_nonneg dist_nonneg dist_nonneg
    hAs hCs hDA.le hEC.le ht hu hr hv hAsq hCsq hl hlB using 1
  ring

theorem supplied_negative_anchor_short_comparison {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] {o : X} {y₀ : Y} {ν R s : ℝ}
    (F : KleinerLottApprox o (WithLp.toLp 2 ((0 : ℝ), y₀)) ν)
    (hR : 1 ≤ R) (hν : 3 * ν ≤ 1) (hs : 2 * (R + ν + 1) < s)
    (hRν : R < ν⁻¹) (a : X) (ha : a ∈ ball o ν⁻¹)
    (himage : dist (F.toFun a) (WithLp.toLp 2 (-s, y₀)) < 2 * ν)
    (x z : X) (hx : x ∈ ball o R) (hz : z ∈ ball o R) (hl : 1 / 2 ≤ dist x z) :
    |comparisonCosine (dist x a) (dist x z) (dist z a) +
      ((F.toFun z).fst - (F.toFun x).fst) / dist x z| ≤
        64 * (R + ν) ^ 2 / s + 24 * ν := by
  let e : WithLp 2 (ℝ × Y) ≃ᵢ WithLp 2 (ℝ × Y) :=
    IsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.neg ℝ).toIsometryEquiv (IsometryEquiv.refl Y)
  have he0 : e (WithLp.toLp 2 ((0 : ℝ), y₀)) = WithLp.toLp 2 ((0 : ℝ), y₀) := by
    change WithLp.toLp 2 (-(0 : ℝ), y₀) = _
    rw [neg_zero]
  let F' := F.mapTargetIsometryAt e _ he0
  have heTarget : e (WithLp.toLp 2 (-s, y₀)) = WithLp.toLp 2 (s, y₀) := by
    change WithLp.toLp 2 (-(-s), y₀) = _
    rw [neg_neg]
  have he : dist (F'.toFun a) (WithLp.toLp 2 (s, y₀)) < 2 * ν := by
    rw [← heTarget]
    change dist (e (F.toFun a)) (e (WithLp.toLp 2 (-s, y₀))) < _
    rw [e.dist_eq]
    exact himage
  have hbound := F'.supplied_positive_anchor_short_comparison hR hν hs hRν a ha he
    x z hx hz hl
  change |comparisonCosine (dist x a) (dist x z) (dist z a) -
    (-(F.toFun z).fst - -(F.toFun x).fst) / dist x z| ≤ _ at hbound
  convert hbound using 1
  congr 1
  ring

end KleinerLottApprox
end GC.MetricGeometry
