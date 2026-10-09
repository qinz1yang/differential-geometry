import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottIsometryTransport
import DifferentialGeometry.Geometry.Metric.L2ProductAnchors
import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngle
import Mathlib.Analysis.Normed.Operator.LinearIsometry

set_option autoImplicit false

open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

namespace KleinerLottApprox

theorem supplied_anchor_distance_error {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {q : X} {y₀ : Y} {ν : ℝ} (F : KleinerLottApprox q y₀ ν)
    (a x : X) (b : Y) (ha : a ∈ Metric.ball q ν⁻¹)
    (hx : x ∈ Metric.ball q ν⁻¹) (hab : dist (F.toFun a) b < 2 * ν) :
    |dist x a - dist (F.toFun x) b| < 3 * ν := by
  have hd := F.distortion x hx a ha
  have ht := abs_dist_sub_le (F.toFun a) b (F.toFun x)
  rw [dist_comm (F.toFun a) (F.toFun x), dist_comm b (F.toFun x)] at ht
  have htri := abs_sub_le (dist x a) (dist (F.toFun x) (F.toFun a))
    (dist (F.toFun x) b)
  rw [abs_sub_comm (dist (F.toFun x) (F.toFun a))] at hd
  linarith

theorem supplied_positive_anchor_value_bound {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] {q : X} {y₀ : Y} {ν R s : ℝ}
    (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), y₀)) ν)
    (hs : R + ν < s) (hRν : R < ν⁻¹)
    (a : X) (ha : a ∈ Metric.ball q ν⁻¹)
    (haimage : dist (F.toFun a) (WithLp.toLp 2 (s, y₀)) < 2 * ν)
    (x : X) (hx : x ∈ Metric.ball q R) :
    |(dist q a - dist x a) - (F.toFun x).fst| <
      6 * ν + (R + ν) ^ 2 / (2 * (s - (R + ν))) := by
  have hR : 0 < R := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hx)
  have hxν : x ∈ Metric.ball q ν⁻¹ := lt_trans hx hRν
  have hqν : q ∈ Metric.ball q ν⁻¹ := Metric.mem_ball_self (inv_pos.mpr F.error_pos)
  have hxrad := F.radial_error x hxν
  have hrad : dist (F.toFun x) (WithLp.toLp 2 (0, y₀)) ≤ R + ν := by
    have := (abs_le.mp hxrad).2
    change dist x q < R at hx
    linarith
  have hvalue := product_positive_anchor_value_bound y₀ (F.toFun x)
    hs hrad
  have hdq := F.supplied_anchor_distance_error a q (WithLp.toLp 2 (s, y₀)) ha hqν haimage
  rw [F.basepoint] at hdq
  have hbase := (WithLp.isometry_prodMk_right (E := ℝ) y₀).dist_eq 0 s
  rw [hbase] at hdq
  have hs0 : 0 < s := by linarith [F.error_pos]
  simp only [Real.dist_eq, zero_sub, abs_neg, abs_of_pos hs0] at hdq
  have hdx := F.supplied_anchor_distance_error a x (WithLp.toLp 2 (s, y₀)) ha hxν haimage
  have hdq' := abs_lt.mp hdq
  have hdx' := abs_lt.mp hdx
  have hv := abs_le.mp hvalue
  apply abs_lt.mpr
  constructor <;> linarith

end KleinerLottApprox
end GC.MetricGeometry

namespace GC.MetricGeometry

private theorem square_perturbation_bound {a b L η : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hL : b ≤ L) (hη : |a - b| ≤ η) :
    |a ^ 2 - b ^ 2| ≤ η * (2 * L + η) := by
  have haL : a ≤ L + η := by linarith [(abs_le.mp hη).2]
  calc
    |a ^ 2 - b ^ 2| = |a - b| * |a + b| := by rw [← abs_mul]; congr 1; ring
    _ ≤ η * (2 * L + η) :=
      mul_le_mul hη (by rw [abs_of_nonneg (by linarith)]; linarith)
        (abs_nonneg _) ((abs_nonneg _).trans hη)

private theorem comparison_cosine_long_anchor_scalar_bound
    {B s η A C D E l t u r v : ℝ}
    (hB : 1 ≤ B) (hη : 0 ≤ η) (hηone : η ≤ 1)
    (hs : 2 * (B + 1) < s)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hAs : |A - s| ≤ B) (hCs : |C - s| ≤ B)
    (ht : |t| ≤ B) (hu : |u| ≤ B)
    (hr : |r| ≤ B) (hv : |v| ≤ B)
    (hAsq : A ^ 2 = (s - t) ^ 2 + r ^ 2)
    (hCsq : C ^ 2 = (s - u) ^ 2 + v ^ 2)
    (hDA : |D - A| ≤ η) (hEC : |E - C| ≤ η)
    (hl : 1 ≤ l) (hlB : l ≤ 2 * B) :
    |comparisonCosine D l E - (u - t) / l| ≤ 20 * B ^ 2 / s + 4 * η := by
  have hB0 : 0 ≤ B := by linarith
  have hs0 : 0 < s := by linarith
  have hDlo : s / 2 ≤ D := by
    linarith [(abs_le.mp hAs).1, (abs_le.mp hDA).1]
  have hDpos : 0 < D := by linarith
  have hlpos : 0 < l := by linarith
  have hden : 0 < 2 * D * l := by positivity
  have hdenlo : s ≤ 2 * D * l := by nlinarith only [hDlo, hl, hDpos]
  have hsqD := square_perturbation_bound hD hA (by linarith [(abs_le.mp hAs).2] : A ≤ s + B) hDA
  have hsqE := square_perturbation_bound hE hC (by linarith [(abs_le.mp hCs).2] : C ≤ s + B) hEC
  have ht2 : t ^ 2 ≤ B ^ 2 := by nlinarith only [sq_abs t, (sq_le_sq₀ (abs_nonneg t) hB0).mpr ht]
  have hu2 : u ^ 2 ≤ B ^ 2 := by nlinarith only [sq_abs u, (sq_le_sq₀ (abs_nonneg u) hB0).mpr hu]
  have hr2 : r ^ 2 ≤ B ^ 2 := by nlinarith only [sq_abs r, (sq_le_sq₀ (abs_nonneg r) hB0).mpr hr]
  have hv2 : v ^ 2 ≤ B ^ 2 := by nlinarith only [sq_abs v, (sq_le_sq₀ (abs_nonneg v) hB0).mpr hv]
  have hl2 : l ^ 2 ≤ 4 * B ^ 2 := by nlinarith only [hl, hlB, hB]
  have hDs : |s - D| ≤ B + η := by
    have hh := abs_sub_le s A D
    rw [abs_sub_comm s A, abs_sub_comm A D] at hh
    linarith
  have hut : |u - t| ≤ 2 * B := (abs_sub u t).trans (by linarith)
  have hprod : |(s - D) * (u - t)| ≤ (B + η) * (2 * B) := by
    rw [abs_mul]
    exact mul_le_mul hDs hut (abs_nonneg _) (by positivity)
  have hrem : |D ^ 2 + l ^ 2 - E ^ 2 - 2 * D * (u - t)| ≤
      20 * B ^ 2 + 4 * s * η := by
    have hd := abs_le.mp hsqD
    have he := abs_le.mp hsqE
    have hp := abs_le.mp hprod
    have hη2 : η ^ 2 ≤ B ^ 2 := by nlinarith only [hη, hηone, hB]
    have hBη : B * η ≤ B ^ 2 := by nlinarith only [hB, hηone, mul_nonneg hB0 (show 0 ≤ B - η by linarith)]
    apply abs_le.mpr
    constructor <;> nlinarith only [hd.1, hd.2, he.1, he.2, hp.1, hp.2,
      hAsq, hCsq, ht2, hu2, hr2, hv2, hl2, hη2, hBη,
      sq_nonneg t, sq_nonneg u, sq_nonneg r, sq_nonneg v, sq_nonneg l]
  have hid : comparisonCosine D l E - (u - t) / l =
      (D ^ 2 + l ^ 2 - E ^ 2 - 2 * D * (u - t)) / (2 * D * l) := by
    unfold comparisonCosine
    field_simp
  rw [hid, abs_div, abs_of_pos hden]
  calc
    _ ≤ (20 * B ^ 2 + 4 * s * η) / (2 * D * l) :=
      div_le_div_of_nonneg_right hrem hden.le
    _ ≤ (20 * B ^ 2 + 4 * s * η) / s :=
      div_le_div_of_nonneg_left (by positivity) hs0 hdenlo
    _ = 20 * B ^ 2 / s + 4 * η := by field_simp

end GC.MetricGeometry

namespace GC.MetricGeometry

private theorem comparison_cosine_opposite_anchor_scalar_bound {H s A C L : ℝ}
    (hH : 0 ≤ H) (hs : 2 * H < s)
    (hAs : |A - s| ≤ H) (hCs : |C - s| ≤ H)
    (hLs : |L - 2 * s| ≤ 2 * H) :
    comparisonCosine A C L ≤ -1 + 32 * H / s := by
  have hs0 : 0 < s := by linarith
  have hA : 0 < A := by linarith [(abs_le.mp hAs).1]
  have hC : 0 < C := by linarith [(abs_le.mp hCs).1]
  have hL : 0 ≤ L := by linarith [(abs_le.mp hLs).1]
  have hsumlo : 0 ≤ A + C := by positivity
  have hsum : A + C ≤ 2 * (s + H) := by
    linarith [(abs_le.mp hAs).2, (abs_le.mp hCs).2]
  have hLlo : 2 * (s - H) ≤ L := by linarith [(abs_le.mp hLs).1]
  have hN : (A + C) ^ 2 - L ^ 2 ≤ 16 * s * H := by
    nlinarith [sq_le_sq₀ hsumlo (by positivity : 0 ≤ 2 * (s + H)) |>.mpr hsum,
      sq_le_sq₀ (by linarith : 0 ≤ 2 * (s - H)) hL |>.mpr hLlo]
  have hden : 0 < 2 * A * C := by positivity
  have hdenlo : s ^ 2 / 2 ≤ 2 * A * C := by
    have hAlo : s / 2 ≤ A := by linarith [(abs_le.mp hAs).1]
    have hClo : s / 2 ≤ C := by linarith [(abs_le.mp hCs).1]
    nlinarith [mul_le_mul hAlo hClo (by positivity : 0 ≤ s / 2) hA.le]
  have hid : comparisonCosine A C L + 1 = ((A + C) ^ 2 - L ^ 2) / (2 * A * C) := by
    unfold comparisonCosine
    field_simp
    ring
  have hb : comparisonCosine A C L + 1 ≤ 32 * H / s := by
    rw [hid]
    calc
      _ ≤ (16 * s * H) / (2 * A * C) := div_le_div_of_nonneg_right hN hden.le
      _ ≤ (16 * s * H) / (s ^ 2 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hdenlo
      _ = 32 * H / s := by field_simp; ring
  linarith

end GC.MetricGeometry

namespace GC.MetricGeometry

private theorem product_positive_anchor_data {Y : Type*} [MetricSpace Y]
    (y₀ : Y) (x : WithLp 2 (ℝ × Y)) {B s : ℝ} (hs : 0 ≤ s)
    (hx : dist x (WithLp.toLp 2 (0, y₀)) ≤ B) :
    |x.fst| ≤ B ∧ |dist x.snd y₀| ≤ B ∧
      |dist x (WithLp.toLp 2 (s, y₀)) - s| ≤ B ∧
      dist x (WithLp.toLp 2 (s, y₀)) ^ 2 = (s - x.fst) ^ 2 + dist x.snd y₀ ^ 2 := by
  have ht := (WithLp.dist_fst_le x (WithLp.toLp 2 (0, y₀))).trans hx
  have hr := (WithLp.dist_snd_le x (WithLp.toLp 2 (0, y₀))).trans hx
  have hd := abs_dist_sub_le x (WithLp.toLp 2 (0, y₀)) (WithLp.toLp 2 (s, y₀))
  have hbase := (WithLp.isometry_prodMk_right (E := ℝ) y₀).dist_eq 0 s
  rw [hbase] at hd
  simp only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hs] at hd
  have hsq := WithLp.prod_dist_sq_eq_add_sq x (WithLp.toLp 2 (s, y₀))
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.dist_eq, sq_abs] at hsq
  refine ⟨?_, ?_, hd.trans hx, ?_⟩
  · simpa only [WithLp.toLp_fst, Real.dist_eq, sub_zero] using ht
  · simpa only [WithLp.toLp_snd, abs_of_nonneg dist_nonneg] using hr
  · nlinarith only [hsq]

namespace KleinerLottApprox

theorem supplied_positive_anchor_comparison_cosine_bound {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] {q : X} {y₀ : Y} {ν R s : ℝ}
    (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), y₀)) ν)
    (hR : 1 ≤ R) (hν : 3 * ν ≤ 1) (hs : 2 * (R + ν + 1) < s)
    (hRν : R < ν⁻¹) (a : X) (ha : a ∈ Metric.ball q ν⁻¹)
    (haimage : dist (F.toFun a) (WithLp.toLp 2 (s, y₀)) < 2 * ν)
    (x z : X) (hx : x ∈ Metric.ball q R) (hz : z ∈ Metric.ball q R)
    (hxz : 1 ≤ dist x z) :
    |comparisonCosine (dist x a) (dist x z) (dist z a) -
      ((F.toFun z).fst - (F.toFun x).fst) / dist x z| ≤
        20 * (R + ν) ^ 2 / s + 12 * ν := by
  have hxν : x ∈ Metric.ball q ν⁻¹ := lt_trans hx hRν
  have hzν : z ∈ Metric.ball q ν⁻¹ := lt_trans hz hRν
  have hrad (w : X) (hw : w ∈ Metric.ball q R) :
      dist (F.toFun w) (WithLp.toLp 2 (0, y₀)) ≤ R + ν := by
    have hh := (abs_le.mp (F.radial_error w (lt_trans hw hRν))).2
    change dist w q < R at hw
    linarith
  have hs0 : 0 ≤ s := by linarith [F.error_pos]
  obtain ⟨ht, hr, hAs, hAsq⟩ := product_positive_anchor_data y₀ (F.toFun x) hs0 (hrad x hx)
  obtain ⟨hu, hv, hCs, hCsq⟩ := product_positive_anchor_data y₀ (F.toFun z) hs0 (hrad z hz)
  have hDA := F.supplied_anchor_distance_error a x (WithLp.toLp 2 (s, y₀)) ha hxν haimage
  have hEC := F.supplied_anchor_distance_error a z (WithLp.toLp 2 (s, y₀)) ha hzν haimage
  have hlB : dist x z ≤ 2 * (R + ν) := by
    have htri := dist_triangle x q z
    rw [dist_comm q z] at htri
    change dist x q < R at hx
    change dist z q < R at hz
    linarith [F.error_pos]
  have hh := comparison_cosine_long_anchor_scalar_bound (by linarith [F.error_pos] : 1 ≤ R + ν)
    (mul_nonneg (by norm_num) F.error_pos.le) hν hs dist_nonneg dist_nonneg dist_nonneg dist_nonneg
    hAs hCs ht hu hr hv hAsq hCsq hDA.le hEC.le hxz hlB
  convert hh using 1
  ring

end KleinerLottApprox
end GC.MetricGeometry

namespace GC.MetricGeometry.KleinerLottApprox

theorem supplied_negative_anchor_comparison_cosine_bound {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] {q : X} {y₀ : Y} {ν R s : ℝ}
    (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), y₀)) ν)
    (hR : 1 ≤ R) (hν : 3 * ν ≤ 1) (hs : 2 * (R + ν + 1) < s)
    (hRν : R < ν⁻¹) (a : X) (ha : a ∈ Metric.ball q ν⁻¹)
    (haimage : dist (F.toFun a) (WithLp.toLp 2 (-s, y₀)) < 2 * ν)
    (x z : X) (hx : x ∈ Metric.ball q R) (hz : z ∈ Metric.ball q R)
    (hxz : 1 ≤ dist x z) :
    |comparisonCosine (dist x a) (dist x z) (dist z a) +
      ((F.toFun z).fst - (F.toFun x).fst) / dist x z| ≤
        20 * (R + ν) ^ 2 / s + 12 * ν := by
  let e : WithLp 2 (ℝ × Y) ≃ᵢ WithLp 2 (ℝ × Y) :=
    IsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.neg ℝ).toIsometryEquiv (IsometryEquiv.refl Y)
  have he (t : ℝ) (y : Y) : e (WithLp.toLp 2 (t, y)) = WithLp.toLp 2 (-t, y) := rfl
  have he0 : e (WithLp.toLp 2 (0, y₀)) = WithLp.toLp 2 (0, y₀) := by rw [he, neg_zero]
  let G := F.mapTargetIsometryAt e (WithLp.toLp 2 (0, y₀)) he0
  have haimage' : dist (G.toFun a) (WithLp.toLp 2 (s, y₀)) < 2 * ν := by
    change dist (e (F.toFun a)) (WithLp.toLp 2 (s, y₀)) < _
    rw [← neg_neg s, ← he, e.dist_eq]
    exact haimage
  have hh := G.supplied_positive_anchor_comparison_cosine_bound hR hν hs hRν a ha haimage'
    x z hx hz hxz
  change |comparisonCosine (dist x a) (dist x z) (dist z a) -
    (- (F.toFun z).fst - - (F.toFun x).fst) / dist x z| ≤ _ at hh
  convert hh using 1
  congr 1
  ring

theorem supplied_anchor_radius_error {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] {q : X} {y₀ : Y} {ν t : ℝ}
    (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), y₀)) ν)
    (a : X) (ha : a ∈ Metric.ball q ν⁻¹)
    (haimage : dist (F.toFun a) (WithLp.toLp 2 (t, y₀)) < 2 * ν) :
    |dist q a - (|t|)| < 3 * ν := by
  have hh := F.supplied_anchor_distance_error a q (WithLp.toLp 2 (t, y₀)) ha
    (Metric.mem_ball_self (inv_pos.mpr F.error_pos)) haimage
  rw [F.basepoint] at hh
  have hbase := (WithLp.isometry_prodMk_right (E := ℝ) y₀).dist_eq 0 t
  rw [hbase] at hh
  simpa only [Real.dist_eq, zero_sub, abs_neg] using hh

theorem supplied_opposite_anchor_comparison_cosine_bound {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] {q : X} {y₀ : Y} {ν R s : ℝ}
    (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), y₀)) ν)
    (hR : 1 ≤ R) (hν : 3 * ν ≤ 1) (hs : 2 * (R + 1) < s)
    (aPlus aMinus : X) (haPlus : aPlus ∈ Metric.ball q ν⁻¹) (haMinus : aMinus ∈ Metric.ball q ν⁻¹)
    (himagePlus : dist (F.toFun aPlus) (WithLp.toLp 2 (s, y₀)) < 2 * ν)
    (himageMinus : dist (F.toFun aMinus) (WithLp.toLp 2 (-s, y₀)) < 2 * ν)
    (x : X) (hx : x ∈ Metric.ball q R) :
    comparisonCosine (dist x aPlus) (dist x aMinus) (dist aPlus aMinus) ≤ -1 + 32 * (R + 1) / s := by
  have hs0 : 0 < s := by linarith
  have hradPlus := F.supplied_anchor_radius_error aPlus haPlus himagePlus
  have hradMinus := F.supplied_anchor_radius_error aMinus haMinus himageMinus
  simp only [abs_of_pos hs0, abs_neg] at hradPlus hradMinus
  have hdPlus := abs_dist_sub_le x q aPlus
  have hdMinus := abs_dist_sub_le x q aMinus
  change dist x q < R at hx
  have hA : |dist x aPlus - s| ≤ R + 1 := by
    exact (abs_sub_le _ (dist q aPlus) _).trans (by linarith)
  have hC : |dist x aMinus - s| ≤ R + 1 := by
    exact (abs_sub_le _ (dist q aMinus) _).trans (by linarith)
  have hd := F.distortion aPlus haPlus aMinus haMinus
  have hp := abs_dist_sub_le (F.toFun aPlus) (WithLp.toLp 2 (s, y₀)) (F.toFun aMinus)
  have hm := abs_dist_sub_le (F.toFun aMinus) (WithLp.toLp 2 (-s, y₀)) (WithLp.toLp 2 (s, y₀))
  rw [dist_comm (F.toFun aMinus) (WithLp.toLp 2 (s, y₀)),
    dist_comm (WithLp.toLp 2 (-s, y₀)) (WithLp.toLp 2 (s, y₀))] at hm
  have hbase := (WithLp.isometry_prodMk_right (E := ℝ) y₀).dist_eq s (-s)
  rw [hbase] at hm
  rw [Real.dist_eq, sub_neg_eq_add, abs_of_pos (by linarith : 0 < s + s)] at hm
  have hL : |dist aPlus aMinus - 2 * s| ≤ 2 * (R + 1) := by
    have hd' := abs_le.mp hd
    have hp' := abs_le.mp hp
    have hm' := abs_le.mp hm
    apply abs_le.mpr
    constructor <;> linarith
  exact comparison_cosine_opposite_anchor_scalar_bound (by linarith) hs hA hC hL

end GC.MetricGeometry.KleinerLottApprox
