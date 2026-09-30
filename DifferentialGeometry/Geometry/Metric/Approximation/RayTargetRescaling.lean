import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.Scaling.Rescale
import DifferentialGeometry.Geometry.Metric.Approximation.RayRescalingBounds

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry.KleinerLottApprox

variable {X : Type*} [mX : MetricSpace X] {p : X} {q : Ici (0 : ℝ)} {ε δ c L : ℝ}

noncomputable def recenterRescaleRayToInterval (f : KleinerLottApprox p q ε)
    (a : X) (hc : 0 < c) (hδ : 0 < δ) (hδone : δ < 1)
    (hsource : dist a p + δ⁻¹ / c ≤ ε⁻¹)
    (htarget : δ⁻¹ / c + q.val + ε ≤ ε⁻¹)
    (hbudget : 3 * c * ε + c * (f.toFun a).val ≤ δ)
    (hclip : δ⁻¹ + c * (f.toFun a).val + c * ε ≤ L) :
    let hL : 0 ≤ L := by
      have hε := f.error_pos
      have hf : 0 ≤ (f.toFun a).val := (f.toFun a).property
      exact le_trans (by positivity) hclip
    letI : MetricSpace X := mX.rescale c hc
    KleinerLottApprox a (⟨0, le_rfl, hL⟩ : Icc (0 : ℝ) L) δ := by
  classical
  have hε := f.error_pos
  have hce : 0 < c * ε := mul_pos hc hε
  have hq : 0 ≤ q.val := q.property
  have hfa0 : 0 ≤ (f.toFun a).val := (f.toFun a).property
  have hi : 0 < δ⁻¹ / c := div_pos (inv_pos.mpr hδ) hc
  have hheight : 0 ≤ c * (f.toFun a).val := mul_nonneg hc.le (f.toFun a).property
  have hL : 0 ≤ L := le_trans (by positivity) hclip
  let F : X → Icc (0 : ℝ) L := fun x =>
    if x = a then ⟨0, le_rfl, hL⟩ else
      ⟨min (c * (f.toFun x).val) L,
        le_min (mul_nonneg hc.le (f.toFun x).property) hL, min_le_right _ _⟩
  have hin (x : X) (hx : c * dist x a < δ⁻¹) : x ∈ ball p ε⁻¹ := by
    have hh : dist x a < δ⁻¹ / c := (lt_div_iff₀ hc).mpr (by nlinarith)
    have ht := dist_triangle x a p
    change dist x p < _
    linarith
  have ha : a ∈ ball p ε⁻¹ := hin a (by simpa using inv_pos.mpr hδ)
  have hnoclip (x : X) (hx : c * dist x a < δ⁻¹) : c * (f.toFun x).val < L := by
    have hd := (abs_le.mp (f.distortion x (hin x hx) a ha)).2
    have hv : (f.toFun x).val - (f.toFun a).val ≤ dist (f.toFun x) (f.toFun a) := by
      exact le_abs_self _
    have h1 := mul_le_mul_of_nonneg_left hd hc.le
    have h2 := mul_le_mul_of_nonneg_left hv hc.le
    linarith
  have hF (x : X) (hx : c * dist x a < δ⁻¹) :
      dist (F x).val (c * (f.toFun x).val) ≤ c * (f.toFun a).val := by
    by_cases hxa : x = a
    · subst x
      simp only [F, ite_true, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hheight, le_refl]
    · simp only [F, ite_eq_right hxa, min_eq_left (hnoclip x hx).le, dist_self]
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
          simp only [F, ite_eq_right hya, min_eq_left (hnoclip y hy).le]
        have hfy : dist (F y).val (c * (f.toFun y).val) = 0 := by rw [heq, dist_self]
        nlinarith [hF a hx]
    · have heq : (F x).val = c * (f.toFun x).val := by
        simp only [F, ite_eq_right hxa, min_eq_left (hnoclip x hx).le]
      have hfx : dist (F x).val (c * (f.toFun x).val) = 0 := by rw [heq, dist_self]
      nlinarith [hF y hy]
  have hcover (y : Icc (0 : ℝ) L) (hy : y.val < δ⁻¹ - δ) :
      ∃ x : X, c * dist x a < δ⁻¹ ∧ dist y (F x) ≤ δ := by
    let z : Ici (0 : ℝ) := ⟨y.val / c, div_nonneg y.property.1 hc.le⟩
    have hz0 : 0 ≤ z.val := z.property
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
    nlinarith [hF x hxin]
  letI : MetricSpace X := mX.rescale c hc
  refine ⟨hδ, hδone, F, ?_, ?_, ?_⟩
  · simp only [F, ite_true]
  · exact fun x hx y hy => hdist x y hx hy
  · intro y hy
    have hyr : y.val < δ⁻¹ - δ := by
      simpa only [Subtype.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg y.property.1] using hy
    obtain ⟨x, hx, hd⟩ := hcover y hyr
    exact (infDist_le_dist_of_mem (show F x ∈ F '' ball a δ⁻¹ from ⟨x, hx, rfl⟩)).trans hd

theorem recenterRescaleRayToInterval_apply (f : KleinerLottApprox p q ε)
    (a : X) (hc : 0 < c) (hδ : 0 < δ) (hδone : δ < 1)
    (hsource : dist a p + δ⁻¹ / c ≤ ε⁻¹)
    (htarget : δ⁻¹ / c + q.val + ε ≤ ε⁻¹)
    (hbudget : 3 * c * ε + c * (f.toFun a).val ≤ δ)
    (hclip : δ⁻¹ + c * (f.toFun a).val + c * ε ≤ L) (x : X) :
    letI : Decidable (x = a) := Classical.propDecidable _
    let value := min (c * (f.toFun x).val) L
    let g := f.recenterRescaleRayToInterval a hc hδ hδone hsource htarget hbudget hclip
    letI : MetricSpace X := mX.rescale c hc
    (g.toFun x).val = if x = a then 0 else value := by
  classical
  dsimp only
  by_cases hx : x = a
  · simp only [recenterRescaleRayToInterval, hx, ite_true]
  · simp only [recenterRescaleRayToInterval, ite_eq_right hx]

theorem exists_strong_edge_ray_model (f : KleinerLottApprox p q ε) (a : X)
    {Δ e θ : ℝ} (hΔ : 1 ≤ Δ) (hδ : 0 < δ) (hδsmall : δ < 1 / 100)
    (hεs : ε ≤ δ / 1000) (hεΔ : ε ≤ 1 / (100000 * Δ))
    (hc : (1 / 2 : ℝ) ≤ c ∧ c ≤ 2)
    (ha : dist a p ≤ 13 * Δ + 1) (hq : q.val ≤ Δ / 2)
    (he : e ≤ δ / 1000) (hθ : θ ≤ δ / 1000)
    (hh : (f.toFun a).val ≤ 2 * e + θ) :
    let D := max (201 * Δ) (4 / δ)
    let values := fun x => min (c * (f.toFun x).val) D
    let hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc.1
    letI : MetricSpace X := mX.rescale c hc0
    ∃ (hD : 0 ≤ D) (g : KleinerLottApprox a (⟨0, le_rfl, hD⟩ : Icc (0 : ℝ) D) δ),
      200 * Δ < D ∧ g.toFun a = ⟨0, le_rfl, hD⟩ ∧
      ∀ x, x ≠ a → (g.toFun x).val = values x := by
  have hc0 : 0 < c := by linarith [hc.1]
  have hδone : δ < 1 := by linarith
  let D := max (201 * Δ) (4 / δ)
  obtain ⟨hDlarge, hsource, htarget, hbudget, hclip⟩ :=
    strong_edge_ray_rescaling_bounds hΔ hδ hδsmall f.error_pos hεs hεΔ hc ha hq he hθ hh
  have hD : 0 ≤ D := (by dsimp [D]; positivity)
  let g := f.recenterRescaleRayToInterval a hc0 hδ hδone hsource htarget hbudget hclip
  have hg (x : X) (hx : x ≠ a) :
      (@KleinerLottApprox.toFun X _ (mX.rescale c hc0) inferInstance a
        (⟨0, le_rfl, hD⟩ : Icc (0 : ℝ) D) δ g x).val = min (c * (f.toFun x).val) D := by
    have h := f.recenterRescaleRayToInterval_apply a hc0 hδ hδone
      hsource htarget hbudget hclip x
    simpa only [ite_eq_right hx] using h
  let : MetricSpace X := mX.rescale c hc0
  exact ⟨hD, g, hDlarge, g.basepoint, hg⟩

end GC.MetricGeometry.KleinerLottApprox
