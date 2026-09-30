import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.Scaling.Rescale
import DifferentialGeometry.Geometry.Metric.Approximation.RayRescalingBounds

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry.KleinerLottApprox

variable {X : Type*} [mX : MetricSpace X] {p : X} {C : ℝ} {q : Icc (0 : ℝ) C} {ε δ c : ℝ}

noncomputable def recenterRescaleMarkedInterval (f : KleinerLottApprox p q ε)
    (a : X) (hc : 0 < c) (hδ : 0 < δ) (hδone : δ < 1)
    (hsource : dist a p + δ⁻¹ / c ≤ ε⁻¹)
    (htarget : δ⁻¹ / c + q.val + ε ≤ ε⁻¹)
    (hbudget : 3 * c * ε + c * (f.toFun a).val ≤ δ) :
    let hL : 0 ≤ c * C := mul_nonneg hc.le (q.property.1.trans q.property.2)
    letI : MetricSpace X := mX.rescale c hc
    KleinerLottApprox a (⟨0, le_rfl, hL⟩ : Icc (0 : ℝ) (c * C)) δ := by
  classical
  have hε := f.error_pos
  have hce : 0 < c * ε := mul_pos hc hε
  have hq : 0 ≤ q.val := q.property.1
  have hfa0 : 0 ≤ (f.toFun a).val := (f.toFun a).property.1
  have hi : 0 < δ⁻¹ / c := div_pos (inv_pos.mpr hδ) hc
  have hheight : 0 ≤ c * (f.toFun a).val := mul_nonneg hc.le (f.toFun a).property.1
  have hL : 0 ≤ c * C := mul_nonneg hc.le (q.property.1.trans q.property.2)
  let F : X → Icc (0 : ℝ) (c * C) := fun x =>
    if x = a then ⟨0, le_rfl, hL⟩ else
      ⟨c * (f.toFun x).val, mul_nonneg hc.le (f.toFun x).property.1,
        mul_le_mul_of_nonneg_left (f.toFun x).property.2 hc.le⟩
  have hin (x : X) (hx : c * dist x a < δ⁻¹) : x ∈ ball p ε⁻¹ := by
    have hh : dist x a < δ⁻¹ / c := (lt_div_iff₀ hc).mpr (by nlinarith)
    have ht := dist_triangle x a p
    change dist x p < _
    linarith
  have ha : a ∈ ball p ε⁻¹ := hin a (by simpa using inv_pos.mpr hδ)
  have hF (x : X) :
      dist (F x).val (c * (f.toFun x).val) ≤ c * (f.toFun a).val := by
    by_cases hxa : x = a
    · subst x
      simp only [F, ite_true, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hheight, le_refl]
    · simp only [F, ite_eq_right hxa, dist_self]
      exact hheight
  have hscaled (x y : X) :
      dist (c * (f.toFun x).val) (c * (f.toFun y).val) = c * dist (f.toFun x) (f.toFun y) := by
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hc, Subtype.dist_eq, Real.dist_eq]
  have hdist (x y : X) (hx : c * dist x a < δ⁻¹) (hy : c * dist y a < δ⁻¹) :
      |dist (F x) (F y) - c * dist x y| ≤ δ := by
    have hp := dist_dist_dist_le (F x).val (F y).val (c * (f.toFun x).val) (c * (f.toFun y).val)
    rw [hscaled x y, Real.dist_eq] at hp
    have hm : |c * dist (f.toFun x) (f.toFun y) - c * dist x y| ≤ c * ε := by
      rw [← mul_sub, abs_mul, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left (f.distortion x (hin x hx) y (hin y hy)) hc.le
    have ht := abs_add_le (dist (F x) (F y) - c * dist (f.toFun x) (f.toFun y))
      (c * dist (f.toFun x) (f.toFun y) - c * dist x y)
    rw [sub_add_sub_cancel] at ht
    change |dist (F x) (F y) - c * dist (f.toFun x) (f.toFun y)| ≤
      dist (F x).val (c * (f.toFun x).val) + dist (F y).val (c * (f.toFun y).val) at hp
    by_cases hxa : x = a
    · subst x
      by_cases hya : y = a
      · subst y; simp [hδ.le]
      · have heq : (F y).val = c * (f.toFun y).val := by
          simp only [F, ite_eq_right hya]
        have hfy : dist (F y).val (c * (f.toFun y).val) = 0 := by rw [heq, dist_self]
        nlinarith [hF a]
    · have heq : (F x).val = c * (f.toFun x).val := by
        simp only [F, ite_eq_right hxa]
      have hfx : dist (F x).val (c * (f.toFun x).val) = 0 := by rw [heq, dist_self]
      nlinarith [hF y]
  have hcover (y : Icc (0 : ℝ) (c * C)) (hy : y.val < δ⁻¹ - δ) :
      ∃ x : X, c * dist x a < δ⁻¹ ∧ dist y (F x) ≤ δ := by
    let z : Icc (0 : ℝ) C := ⟨y.val / c, div_nonneg y.property.1 hc.le,
      (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using y.property.2)⟩
    have hz0 : 0 ≤ z.val := z.property.1
    have hcz : c * z.val = y.val := mul_div_cancel₀ _ hc.ne'
    have hz : dist z q < ε⁻¹ - ε := by
      have hdistz : dist z q ≤ z.val + q.val := by
        rw [Subtype.dist_eq, Real.dist_eq]
        exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
      have hz' : z.val < δ⁻¹ / c := by
        apply (div_lt_div_iff_of_pos_right hc).mpr
        linarith
      linarith
    obtain ⟨x, hx, hxf⟩ := f.coverage_witness z hz
    have hd := (abs_le.mp (f.distortion x hx a ha)).1
    have htri := dist_triangle (f.toFun x) z (f.toFun a)
    rw [dist_comm (f.toFun x) z] at htri
    have hza : dist z (f.toFun a) ≤ z.val + (f.toFun a).val := by
      rw [Subtype.dist_eq, Real.dist_eq]
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    have hxin : c * dist x a < δ⁻¹ := by
      nlinarith [mul_lt_mul_of_pos_left hxf hc, mul_le_mul_of_nonneg_left hd hc.le,
        mul_le_mul_of_nonneg_left htri hc.le, mul_le_mul_of_nonneg_left hza hc.le]
    have herr : dist y.val (c * (f.toFun x).val) < 2 * c * ε := by
      rw [← hcz, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hc]
      change |z.val - (f.toFun x).val| < 2 * ε at hxf
      nlinarith [mul_lt_mul_of_pos_left hxf hc]
    have ht := dist_triangle y.val (c * (f.toFun x).val) (F x).val
    rw [dist_comm (c * (f.toFun x).val) (F x).val] at ht
    refine ⟨x, hxin, ?_⟩
    change dist y.val (F x).val ≤ δ
    nlinarith [hF x]
  letI : MetricSpace X := mX.rescale c hc
  refine ⟨hδ, hδone, F, ?_, ?_, ?_⟩
  · simp only [F, ite_true]
  · exact fun x hx y hy => hdist x y hx hy
  · intro y hy
    have hyr : y.val < δ⁻¹ - δ := by
      simpa only [Subtype.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg y.property.1] using hy
    obtain ⟨x, hx, hd⟩ := hcover y hyr
    exact (infDist_le_dist_of_mem (show F x ∈ F '' ball a δ⁻¹ from ⟨x, hx, rfl⟩)).trans hd

theorem recenterRescaleMarkedInterval_apply (f : KleinerLottApprox p q ε)
    (a : X) (hc : 0 < c) (hδ : 0 < δ) (hδone : δ < 1)
    (hsource : dist a p + δ⁻¹ / c ≤ ε⁻¹)
    (htarget : δ⁻¹ / c + q.val + ε ≤ ε⁻¹)
    (hbudget : 3 * c * ε + c * (f.toFun a).val ≤ δ) (x : X) :
    letI : Decidable (x = a) := Classical.propDecidable _
    let value := c * (f.toFun x).val
    let g := f.recenterRescaleMarkedInterval a hc hδ hδone hsource htarget hbudget
    letI : MetricSpace X := mX.rescale c hc
    (g.toFun x).val = if x = a then 0 else value := by
  classical
  dsimp only
  by_cases hx : x = a
  · simp only [recenterRescaleMarkedInterval, hx, ite_true]
  · simp only [recenterRescaleMarkedInterval, ite_eq_right hx]

theorem exists_strong_edge_interval_model (f : KleinerLottApprox p q ε) (a : X)
    {Δ e θ : ℝ} (hΔ : 1 ≤ Δ) (hC : 500 * Δ < C)
    (hδ : 0 < δ) (hδsmall : δ < 1 / 100)
    (hεs : ε ≤ δ / 1000) (hεΔ : ε ≤ 1 / (100000 * Δ))
    (hc : (1 / 2 : ℝ) ≤ c ∧ c ≤ 2)
    (ha : dist a p ≤ 13 * Δ + 1) (hq : q.val ≤ Δ / 2)
    (he : e ≤ δ / 1000) (hθ : θ ≤ δ / 1000)
    (hh : (f.toFun a).val ≤ 2 * e + θ) :
    let values := fun x => c * (f.toFun x).val
    let hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc.1
    letI : MetricSpace X := mX.rescale c hc0
    ∃ (hD : 0 ≤ c * C)
        (g : KleinerLottApprox a (⟨0, le_rfl, hD⟩ : Icc (0 : ℝ) (c * C)) δ),
      200 * Δ < c * C ∧ g.toFun a = ⟨0, le_rfl, hD⟩ ∧
      ∀ x, x ≠ a → (g.toFun x).val = values x := by
  have hc0 : 0 < c := by linarith [hc.1]
  have hδone : δ < 1 := by linarith
  obtain ⟨_, hsource, htarget, hbudget, _⟩ :=
    strong_edge_ray_rescaling_bounds hΔ hδ hδsmall f.error_pos hεs hεΔ hc ha hq he hθ hh
  have hD : 0 ≤ c * C := mul_nonneg hc0.le (q.property.1.trans q.property.2)
  have hDlarge : 200 * Δ < c * C := by
    have h1 := mul_lt_mul_of_pos_left hC hc0
    have h2 := mul_le_mul_of_nonneg_right hc.1 (show 0 ≤ Δ by linarith)
    nlinarith
  let g := f.recenterRescaleMarkedInterval a hc0 hδ hδone hsource htarget hbudget
  have hg (x : X) (hx : x ≠ a) :
      (@KleinerLottApprox.toFun X _ (mX.rescale c hc0) inferInstance a
        (⟨0, le_rfl, hD⟩ : Icc (0 : ℝ) (c * C)) δ g x).val = c * (f.toFun x).val := by
    have h := f.recenterRescaleMarkedInterval_apply a hc0 hδ hδone hsource htarget hbudget x
    simpa only [ite_eq_right hx] using h
  let : MetricSpace X := mX.rescale c hc0
  exact ⟨hD, g, hDlarge, g.basepoint, hg⟩

end GC.MetricGeometry.KleinerLottApprox
