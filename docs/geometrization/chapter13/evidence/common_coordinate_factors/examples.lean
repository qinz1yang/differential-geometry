import DifferentialGeometry.Geometry.Metric.Approximation.CommonCoordinateCancellation
import DifferentialGeometry.Geometry.Metric.Approximation.BoundedFactorRestriction
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open Set Metric
open GC.MetricGeometry

namespace FactorRegression

private def exactApprox {X : Type*} [MetricSpace X] (p : X) {b : ℝ}
    (hb : 0 < b) (hb1 : b < 1) : KleinerLottApprox p p b where
  error_pos := hb
  error_lt_one := hb1
  toFun := id
  basepoint := rfl
  distortion _ _ _ _ := by simp; exact hb.le
  coverage y hy := by
    have hm : y ∈ id '' ball p b⁻¹ := ⟨y, by change dist y p < b⁻¹; linarith, rfl⟩
    exact (infDist_le_dist_of_mem hm).trans (by simpa using hb.le)

theorem two_dimensional_common_factor :
    ∃ G : KleinerLottApprox (1 : ℝ) 1 (1 / 2),
      ∀ z : WithLp 2 (WithLp 2 (ℝ × ℝ) × ℝ),
        z ∈ ball (WithLp.toLp 2 (WithLp.toLp 2 (2, 3), 1)) 1 →
          dist (G.toFun z.snd) z.snd < 1 / 10 := by
  obtain ⟨ε, hε, h⟩ := exists_factor_approximation_of_common_coordinate
    (L := 1) (η := 1 / 2) (θ := 1 / 10) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  let b := min ε 1 / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hbe : b < ε := by dsimp [b]; linarith [min_le_left ε 1]
  have hb1 : b < 1 := by dsimp [b]; linarith [min_le_right ε 1]
  let p := WithLp.toLp 2 (WithLp.toLp 2 ((2 : ℝ), (3 : ℝ)), (1 : ℝ))
  exact h p p.fst 1 1 b b hbe hbe (exactApprox p hb hb1) (exactApprox p hb hb1)
    (fun _ => rfl)

theorem coarse_jump_below_gap :
    let f : ℝ → ℝ := fun x => if x < 0 then 0 else 1 / 2
    ∀ x y, f x < 1 ↔ f y < 1 := by
  intro f x y
  apply isPreconnected_univ.lt_iff_lt_of_coarse_bound f
    (C := 0) (ε := 1 / 2) (a := 1) (b := 2) (by norm_num) _ _ (mem_univ x) (mem_univ y)
  · intro s _ t _
    simp only [f, zero_mul, zero_add]
    split_ifs <;> norm_num
  · intro s _
    left
    dsimp [f]
    split_ifs <;> norm_num

theorem bounded_factor_preserves_error
    {Z E X Y : Type*} [MetricSpace Z] [MetricSpace E] [MetricSpace X] [MetricSpace Y]
    (p : Z) (u : E) (x₀ : X) (y₀ : Y)
    (f : KleinerLottApprox p (WithLp.toLp 2 (u, x₀)) (1 / 2))
    (g : KleinerLottApprox x₀ y₀ (1 / 10000))
    (hsegments : ∀ x y : Z, ∃ c : Icc (0 : ℝ) 1 → Z,
      c ⟨0, by norm_num⟩ = x ∧ c ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (c s) (c t) = dist x y * dist s t)
    (hY : Bornology.IsBounded (univ : Set Y)) (hD : diam (univ : Set Y) ≤ 500) :
    ∃ F : KleinerLottApprox p
      (WithLp.toLp 2 (u, (⟨x₀, mem_ball_self (by norm_num)⟩ : ball x₀ (600 * (1 : ℝ))))) (1 / 2),
      (∀ z, (F.toFun z).fst = (f.toFun z).fst) ∧
      (∀ z ∈ ball p ((1 / 2 : ℝ)⁻¹), ((F.toFun z).snd : X) = (f.toFun z).snd) ∧
      Bornology.IsBounded (univ : Set (ball x₀ (600 * (1 : ℝ)))) ∧
      diam (univ : Set (ball x₀ (600 * (1 : ℝ)))) < 1000 * 1 := by
  have h := exists_factor_approximation_of_bounded_target f g hsegments hY
    (Δ := 1) (by simpa using hD) (by norm_num) (by norm_num)
  exact h

#print axioms two_dimensional_common_factor
#print axioms coarse_jump_below_gap
#print axioms bounded_factor_preserves_error
end FactorRegression
