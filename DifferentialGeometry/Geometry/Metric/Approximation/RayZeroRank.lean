import DifferentialGeometry.Geometry.Metric.Approximation.SplittingRank

/-!
A metric approximation based at the endpoint of a half-ray excludes every positive Euclidean
splitting at sufficiently small error. Opposite unit vectors in the proposed Euclidean factor
would lift to two points almost one unit from the basepoint and almost two units apart, while
their half-ray coordinates are almost equal. The finite rank-zero consumer uses the original
rank tolerances and does not assert the existence of a geometric zero-model family.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace GC.MetricGeometry

universe u v

private theorem lifted_unit_radius {X Y : Type*} [mX : MetricSpace X] [mY : MetricSpace Y]
    {p : X} {q y : Y} {β : ℝ} (F : KleinerLottApprox p q β) {x : X}
    (hx : x ∈ ball p β⁻¹) (hy : dist y q = 1) (hxy : dist y (F.toFun x) < 2 * β) :
    |dist x p - 1| ≤ 3 * β := by
  have hrad := abs_le.mp (F.radial_error x hx)
  have hlo := dist_triangle y (F.toFun x) q
  have hhi := dist_triangle (F.toFun x) y q
  rw [hy] at hlo hhi
  rw [dist_comm (F.toFun x) y] at hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem not_hasEuclideanSplitting_of_endpoint_ray {X : Type u} [mX : MetricSpace X]
    {p : X} {δ β : ℝ}
    (F : KleinerLottApprox p (⟨0, by simp⟩ : Ici (0 : ℝ)) δ)
    (hδ : δ < 1 / 100) (hβ : β < 1 / 100) {k : ℕ} (hk : 0 < k) :
    ¬ HasEuclideanSplitting.{u, v} p k β := by
  rintro ⟨Y, mY, q, ⟨G⟩⟩
  let residualMetric : MetricSpace Y := mY
  let v : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single ⟨0, hk⟩ 1
  have hv : ‖v‖ = 1 := by simp [v, PiLp.norm_single]
  let yp := WithLp.toLp 2 (v, q)
  let yn := WithLp.toLp 2 (-v, q)
  let y0 := WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), q)
  have hpos : dist yp y0 = 1 := by
    change dist (WithLp.toLp 2 (v, q)) (WithLp.toLp 2 (0, q)) = 1
    exact ((WithLp.isometry_prodMk_right q).dist_eq v 0).trans
      (by rw [dist_zero_right, hv])
  have hneg : dist yn y0 = 1 := by
    change dist (WithLp.toLp 2 (-v, q)) (WithLp.toLp 2 (0, q)) = 1
    exact ((WithLp.isometry_prodMk_right q).dist_eq (-v) 0).trans
      (by rw [dist_zero_right, norm_neg, hv])
  have hpair : dist yp yn = 2 := by
    change dist (WithLp.toLp 2 (v, q)) (WithLp.toLp 2 (-v, q)) = 2
    exact ((WithLp.isometry_prodMk_right q).dist_eq v (-v)).trans
      (by rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ, norm_smul,
        Real.norm_two, hv, mul_one])
  have hβinv : 100 < β⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) G.error_pos]
    simpa only [one_div] using hβ
  obtain ⟨xp, hxp, hxpG⟩ := G.coverage_witness yp (by rw [hpos]; linarith)
  obtain ⟨xn, hxn, hxnG⟩ := G.coverage_witness yn (by rw [hneg]; linarith)
  have hrp := abs_le.mp (lifted_unit_radius G hxp hpos hxpG)
  have hrn := abs_le.mp (lifted_unit_radius G hxn hneg hxnG)
  have hδinv : 100 < δ⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) F.error_pos]
    simpa only [one_div] using hδ
  have hxpF : xp ∈ ball p δ⁻¹ := by change dist xp p < δ⁻¹; linarith
  have hxnF : xn ∈ ball p δ⁻¹ := by change dist xn p < δ⁻¹; linarith
  have hFp := abs_le.mp (F.radial_error xp hxpF)
  have hFn := abs_le.mp (F.radial_error xn hxnF)
  have hray (x : X) : dist (F.toFun x) (⟨0, by simp⟩ : Ici (0 : ℝ)) = (F.toFun x).val := by
    rw [Subtype.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg (F.toFun x).property]
  rw [hray] at hFp hFn
  have hdiff : dist (F.toFun xp) (F.toFun xn) ≤ 6 * β + 2 * δ := by
    rw [Subtype.dist_eq, Real.dist_eq]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hGdist := abs_le.mp (G.distortion xp hxp xn hxn)
  have htriangle := dist_triangle4 yp (G.toFun xp) (G.toFun xn) yn
  rw [hpair, dist_comm (G.toFun xn) yn] at htriangle
  have hFdist := abs_le.mp (F.distortion xp hxpF xn hxnF)
  linarith

theorem splittingRank_zero_of_endpoint_ray {X : Type u} [mX : MetricSpace X]
    {p : X} {δ : ℝ} {β : ℕ → ℝ}
    (F : KleinerLottApprox p (⟨0, by simp⟩ : Ici (0 : ℝ)) δ) (hδ : δ < 1 / 100)
    (hβ : ∀ k, 0 < k → k ≤ 3 → β k < 1 / 100) : splittingRank.{u, v} p β 3 = 0 := by
  apply (splittingRank_zero_iff p β 3).mpr
  intro k hk hk3
  exact not_hasEuclideanSplitting_of_endpoint_ray F hδ (hβ k hk hk3) hk

end GC.MetricGeometry
