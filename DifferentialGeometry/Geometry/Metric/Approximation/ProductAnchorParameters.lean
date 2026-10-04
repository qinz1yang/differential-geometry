import DifferentialGeometry.Geometry.Metric.Approximation.ProductAnchors
import DifferentialGeometry.Geometry.Comparison.Toponogov.UniformHyperbolicCosine

set_option autoImplicit false
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v

theorem exists_uniform_product_anchor_parameters {R ε : ℝ} (hR : 1 ≤ R) (hε : 0 < ε) :
    ∃ s > 2 * R + 10, ∃ ν₀ > 0, ∀ ν : ℝ, 0 < ν → ν < ν₀ →
      512 * (s + R + 1) < ν⁻¹ ∧
      ∀ (X : Type u) (Y : Type v) [MetricSpace X] [MetricSpace Y]
        (q : X) (y₀ : Y)
        (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), y₀)) ν)
        (aPlus aMinus : X),
        aPlus ∈ Metric.ball q ν⁻¹ → aMinus ∈ Metric.ball q ν⁻¹ →
        dist (F.toFun aPlus) (WithLp.toLp 2 (s, y₀)) < 2 * ν →
        dist (F.toFun aMinus) (WithLp.toLp 2 (-s, y₀)) < 2 * ν →
        dist q aPlus < s + 1 ∧ dist q aMinus < s + 1 ∧
        (∀ x ∈ Metric.ball q R,
          |(dist q aPlus - dist x aPlus) - (F.toFun x).fst| < ε) ∧
        (∀ x ∈ Metric.ball q R,
          hyperbolicComparisonCosine ν (dist x aPlus) (dist x aMinus) (dist aPlus aMinus)
            < -1 + ε) ∧
        (∀ x ∈ Metric.ball q R, ∀ z ∈ Metric.ball q R, 1 ≤ dist x z →
          hyperbolicComparisonCosine ν (dist x aPlus) (dist x z) (dist z aPlus)
            < ((F.toFun z).fst - (F.toFun x).fst) / dist x z + ε ∧
          hyperbolicComparisonCosine ν (dist x aMinus) (dist x z) (dist z aMinus)
            < -((F.toFun z).fst - (F.toFun x).fst) / dist x z + ε) := by
  obtain ⟨s, hs⟩ := exists_gt (max (2 * R + 10)
    (max (80 * (R + 1) ^ 2 / ε) (128 * (R + 1) / ε)))
  have hsR : 2 * R + 10 < s := lt_of_le_of_lt (le_max_left _ _) hs
  have hsP : 80 * (R + 1) ^ 2 / ε < s :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hs
  have hsO : 128 * (R + 1) / ε < s :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hs
  have hs0 : 0 < s := by linarith
  have hL : 0 < s + R + 1 := by linarith
  have hprod : 20 * (R + 1) ^ 2 / s < ε / 4 := by
    rw [div_lt_iff₀ hs0]
    have hh := (div_lt_iff₀ hε).mp hsP
    nlinarith only [hh]
  have hopp : 32 * (R + 1) / s < ε / 4 := by
    rw [div_lt_iff₀ hs0]
    have hh := (div_lt_iff₀ hε).mp hsO
    nlinarith only [hh]
  obtain ⟨δ, hδ, hhyper⟩ := exists_hyperbolic_comparison_cosine_tolerance (by linarith : 0 < ε / 2)
  let ν₀ := min (1 / 6 : ℝ) (min (ε / 48)
    (min (512 * (s + R + 1))⁻¹ (δ / (2 * (s + R + 1)))))
  have hν₀ : 0 < ν₀ := by dsimp [ν₀]; positivity
  refine ⟨s, hsR, ν₀, hν₀, ?_⟩
  intro ν hνpos hνsmall
  have hνsix : ν < 1 / 6 := lt_of_lt_of_le hνsmall (min_le_left _ _)
  have hνε : ν < ε / 48 :=
    lt_of_lt_of_le hνsmall ((min_le_right _ _).trans (min_le_left _ _))
  have hνinv : ν < (512 * (s + R + 1))⁻¹ :=
    lt_of_lt_of_le hνsmall ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hνδ : ν < δ / (2 * (s + R + 1)) :=
    lt_of_lt_of_le hνsmall ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hbuffer : 512 * (s + R + 1) < ν⁻¹ := by
    have hh := (inv_lt_inv₀ (inv_pos.mpr (by positivity : 0 < 512 * (s + R + 1))) hνpos).mpr hνinv
    simpa only [inv_inv] using hh
  have hRν : R < ν⁻¹ := by linarith
  have hν : 3 * ν ≤ 1 := by linarith
  have hsν : 2 * (R + ν + 1) < s := by linarith
  have hscale : ν * (s + R + 1) < δ := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2 * (s + R + 1))).mp hνδ
    nlinarith only [hh, hδ]
  have hscalar : 20 * (R + ν) ^ 2 / s + 12 * ν < ε / 2 := by
    have hsq : (R + ν) ^ 2 ≤ (R + 1) ^ 2 := by nlinarith only [hR, hνsix, hνpos]
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num : 0 ≤ (20 : ℝ))) hs0.le
    linarith
  have hval : 6 * ν + (R + ν) ^ 2 / (2 * (s - (R + ν))) < ε := by
    have hsq : (R + ν) ^ 2 ≤ (R + 1) ^ 2 := by nlinarith only [hR, hνsix, hνpos]
    have hden : s ≤ 2 * (s - (R + ν)) := by linarith
    have hh : (R + ν) ^ 2 / (2 * (s - (R + ν))) ≤ (R + 1) ^ 2 / s := by
      exact (div_le_div_of_nonneg_right hsq (by linarith)).trans
        (div_le_div_of_nonneg_left (sq_nonneg _) hs0 hden)
    have hprod' : (R + 1) ^ 2 / s < ε / 4 := by
      have hn : 0 ≤ (R + 1) ^ 2 / s := by positivity
      have hid : 20 * (R + 1) ^ 2 / s = 20 * ((R + 1) ^ 2 / s) := by ring
      rw [hid] at hprod
      linarith
    linarith
  refine ⟨hbuffer, ?_⟩
  intro X Y mX mY q y₀ F aPlus aMinus haPlus haMinus himagePlus himageMinus
  have hrPlus := F.supplied_anchor_radius_error aPlus haPlus himagePlus
  have hrMinus := F.supplied_anchor_radius_error aMinus haMinus himageMinus
  simp only [abs_neg, abs_of_pos hs0] at hrPlus hrMinus
  have hradPlus : dist q aPlus < s + 1 := by linarith [(abs_lt.mp hrPlus).2]
  have hradMinus : dist q aMinus < s + 1 := by linarith [(abs_lt.mp hrMinus).2]
  have harm (a : X) (hr : |dist q a - s| < 3 * ν) (x : X) (hx : x ∈ Metric.ball q R) :
      0 < dist x a ∧ dist x a < s + R + 1 := by
    have ht := dist_triangle q x a
    have ht' := dist_triangle x q a
    rw [dist_comm q x] at ht
    change dist x q < R at hx
    have hr' := abs_lt.mp hr
    constructor <;> linarith
  have htri (x a b : X) : |dist x a - dist x b| ≤ dist a b ∧ dist a b ≤ dist x a + dist x b := by
    constructor
    · simpa only [dist_comm a x, dist_comm b x] using abs_dist_sub_le a b x
    · simpa only [dist_comm a x] using dist_triangle a x b
  have hhypermetric (x a b : X) (ha : 0 < dist x a) (hb : 0 < dist x b)
      (hLa : dist x a < s + R + 1) (hLb : dist x b < s + R + 1) :
      |hyperbolicComparisonCosine ν (dist x a) (dist x b) (dist a b) -
        comparisonCosine (dist x a) (dist x b) (dist a b)| < ε / 2 := by
    exact hhyper ν _ _ _ hνpos ha hb (htri x a b).1 (htri x a b).2
      ((mul_lt_mul_of_pos_left (max_lt hLa hLb) hνpos).trans hscale)
  refine ⟨hradPlus, hradMinus, ?_, ?_, ?_⟩
  · intro x hx
    exact (F.supplied_positive_anchor_value_bound (by linarith) hRν
      aPlus haPlus himagePlus x hx).trans hval
  · intro x hx
    have hxp := harm aPlus hrPlus x hx
    have hxm := harm aMinus hrMinus x hx
    have hh := hhypermetric x aPlus aMinus hxp.1 hxm.1 hxp.2 hxm.2
    have he := F.supplied_opposite_anchor_comparison_cosine_bound hR hν (by linarith)
      aPlus aMinus haPlus haMinus himagePlus himageMinus x hx
    linarith [(abs_lt.mp hh).2]
  · intro x hx z hz hxz
    have hxp := harm aPlus hrPlus x hx
    have hxm := harm aMinus hrMinus x hx
    have hxzL : dist x z < s + R + 1 := by
      have ht := dist_triangle x q z
      rw [dist_comm q z] at ht
      change dist x q < R at hx
      change dist z q < R at hz
      linarith
    have hhp := hhypermetric x aPlus z hxp.1 (by linarith) hxp.2 hxzL
    have hhm := hhypermetric x aMinus z hxm.1 (by linarith) hxm.2 hxzL
    have hep := F.supplied_positive_anchor_comparison_cosine_bound hR hν hsν hRν
      aPlus haPlus himagePlus x z hx hz hxz
    have hem := F.supplied_negative_anchor_comparison_cosine_bound hR hν hsν hRν
      aMinus haMinus himageMinus x z hx hz hxz
    rw [dist_comm aPlus z] at hhp
    rw [dist_comm aMinus z] at hhm
    constructor
    · linarith [(abs_lt.mp hhp).2, (abs_le.mp hep).2]
    · rw [neg_div]
      linarith [(abs_lt.mp hhm).2, (abs_le.mp hem).2]

end GC.MetricGeometry
