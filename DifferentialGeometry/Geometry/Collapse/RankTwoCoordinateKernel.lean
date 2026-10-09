import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Analysis.InnerProductSpace.AlmostOrthonormalPair

/-!
# LFR06: the assembly steps of rank-two adapted coordinates that need no geometry

Blueprint 207A, LFR06 (`thm:collapse-rank-two-adapted-existence`, A:25225–25320). The geometric
inputs (LC78 per coordinate of a 2-splitting with inner radius 3, the mixed-anchor Gram estimate,
LC28 smoothing) are not proved here; see `build-logs/resume/request-LFR06-to-X83.md`. Proved:

* `rankTwo_norm_of_almostOrthonormal`: a linear map `L : V → ℝ²` with components `⟪wⱼ, ·⟫`, `wⱼ`
  within `ε` of unit `uⱼ`, `|⟪u₁, u₂⟫| ≤ δ`, `δ + 4ε < 1`, is surjective (rank two) and has norm
  `≤ √(1 + δ) + √2 ε` (the row's Gram-matrix step, giving `Lip η ≤ 1 + γ`).
* `exists_mem_ball_near_of_splitting`: the row's Hausdorff coverage — through the same splitting,
  every point of the unit disk is within `γ` of `η(B(q, 1))` when `24ν < γ < 1` and `|η − Φ| < γ/8`.
-/

set_option autoImplicit false

open Set Metric GC.MetricGeometry
open scoped RealInnerProductSpace

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- **LFR06, image coverage.** If `F` is a pointed `ν`-splitting of `(M, q)` to `ℝ² × Y` with
`24 ν < γ < 1` and `η` is within `γ/8` of the `ℝ²`-coordinate on `B(q, 1)`, then every point of
the unit disk is within `γ` of `η(B(q, 1))` (lift `((1 − γ/4) y, a)` through the same splitting). -/
theorem exists_mem_ball_near_of_splitting {M Y : Type*} [MetricSpace M] [MetricSpace Y] {q : M}
    {a : Y} {ν γ : ℝ} (F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ²), a)) ν)
    (hγ1 : γ < 1) (hν : 24 * ν < γ) {η : M → ℝ²}
    (hclose : ∀ x ∈ ball q 1, ‖η x - (F.toFun x).fst‖ < γ / 8) :
    ∀ y ∈ ball (0 : ℝ²) 1, ∃ x ∈ ball q 1, ‖η x - y‖ < γ := by
  intro y hy
  have hν0 := F.error_pos
  have hγ0 : 0 < γ := by linarith
  have hy1 : ‖y‖ < 1 := by simpa using hy
  set c : ℝ := 1 - γ / 4
  have hc0 : 0 < c := by simp only [c]; linarith
  set y' : WithLp 2 (ℝ² × Y) := WithLp.toLp 2 (c • y, a)
  have hνinv : 24 < ν⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hν0]
    nlinarith
  have hy'f : y'.fst = c • y := rfl
  have hy's : y'.snd = a := rfl
  have hy'q : dist y' (WithLp.toLp 2 ((0 : ℝ²), a)) < c := by
    rw [WithLp.prod_dist_eq_add (by norm_num), hy'f, hy's, WithLp.toLp_fst, WithLp.toLp_snd,
      dist_self, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
    norm_num
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
    nlinarith [norm_nonneg y]
  obtain ⟨x, hx, hxy⟩ := F.coverage_witness y' (by
    have : c ≤ 1 := by simp only [c]; linarith
    linarith)
  have hxq : dist x q < 1 := by
    have hd := F.distortion x hx q (mem_ball_self (inv_pos.mpr hν0))
    rw [F.basepoint] at hd
    have htri := dist_triangle (F.toFun x) y' (WithLp.toLp 2 ((0 : ℝ²), a))
    rw [dist_comm (F.toFun x) y'] at htri
    have := (abs_le.mp hd).1
    simp only [c] at hy'q
    linarith
  refine ⟨x, mem_ball.mpr hxq, ?_⟩
  have hfst : ‖(F.toFun x).fst - c • y‖ < 2 * ν := by
    have h := WithLp.dist_fst_le (p := 2) (F.toFun x) y'
    rw [dist_eq_norm, dist_comm] at h
    simp only [y', WithLp.toLp_fst] at h
    linarith
  have h1 := hclose x (mem_ball.mpr hxq)
  have hsplit : η x - y = (η x - (F.toFun x).fst) + ((F.toFun x).fst - c • y) - (γ / 4) • y := by
    simp only [c, sub_smul, one_smul]
    abel
  rw [hsplit]
  have h3 : ‖(γ / 4) • y‖ ≤ γ / 4 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    nlinarith [norm_nonneg y]
  calc ‖(η x - (F.toFun x).fst) + ((F.toFun x).fst - c • y) - (γ / 4) • y‖
      ≤ ‖η x - (F.toFun x).fst‖ + ‖(F.toFun x).fst - c • y‖ + ‖(γ / 4) • y‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ < γ / 8 + 2 * ν + γ / 4 := by linarith
    _ < γ := by linarith

/-- **LFR06, rank two and the Lipschitz constant of the differential.** -/
theorem rankTwo_norm_of_almostOrthonormal {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u₁ u₂ w₁ w₂ : V} (hu₁ : ‖u₁‖ = 1) (hu₂ : ‖u₂‖ = 1) {ε δ : ℝ} (hε : 0 ≤ ε)
    (h₁ : ‖w₁ - u₁‖ ≤ ε) (h₂ : ‖w₂ - u₂‖ ≤ ε) (hδ : |⟪u₁, u₂⟫| ≤ δ) (hsmall : δ + 4 * ε < 1)
    (L : V →ₗ[ℝ] ℝ²) (hL : ∀ v, L v 0 = ⟪w₁, v⟫ ∧ L v 1 = ⟪w₂, v⟫) :
    Function.Surjective L ∧ ∀ v, ‖L v‖ ≤ (Real.sqrt (1 + δ) + Real.sqrt 2 * ε) * ‖v‖ := by
  obtain ⟨hnorm, hsurj⟩ := DifferentialGeometry.Analysis.almostOrthonormal_pair_bounds hu₁ hu₂ hε
    h₁ h₂ hδ
  refine ⟨fun t => ?_, fun v => ?_⟩
  · obtain ⟨v, hv₁, hv₂⟩ := hsurj hsmall (t 0) (t 1)
    refine ⟨v, ?_⟩
    ext i
    fin_cases i
    · simpa [hv₁] using (hL v).1
    · simpa [hv₂] using (hL v).2
  · have hsq : ‖L v‖ ^ 2 = ⟪w₁, v⟫ ^ 2 + ⟪w₂, v⟫ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, (hL v).1, (hL v).2, Real.norm_eq_abs,
        Real.norm_eq_abs, sq_abs, sq_abs]
    have hb := hnorm v
    rw [← hsq] at hb
    have hr : 0 ≤ (Real.sqrt (1 + δ) + Real.sqrt 2 * ε) * ‖v‖ := by positivity
    exact abs_le_of_sq_le_sq' hb hr |>.2 |> fun h => (le_abs_self _).trans
      (by rw [abs_of_nonneg (norm_nonneg _)]; exact h)

end DifferentialGeometry.Geometry.Collapse
