import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.Approximation.PrescribedProductCoordinates
import DifferentialGeometry.Geometry.Metric.Approximation.Bilipschitz

/-!
# Transport of a Kleiner–Lott approximation along a ball isometry (lane BCG-1)

A Kleiner–Lott `δ`-approximation of `(X, p)` only sees the ball `B(p, δ⁻¹)`. If `φ : X' → X` maps
`p'` to `p`, preserves distances on `B(p', δ⁻¹)` and its image of that ball contains `B(p, δ⁻¹)`,
then `f ∘ φ` is a Kleiner–Lott `δ`-approximation of `(X', p')` with the same model point.

* `KleinerLottApprox.transportBall_BCG1`, `KleinerLottApprox.transportBall_toFun_BCG1`.
* `PointedBallApprox.exists_kleinerLott_with_first_coordinate_BCG1`: a bi-Lipschitz product map
  `x ↦ (Φ x, φT (τ x))` into `ℝ ×₂ Y` with coverage gives a Kleiner–Lott approximation whose
  first coordinate is EXACTLY `Φ` (the coordinate form of the rank-one splitting kernel).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function

namespace GC.MetricGeometry

universe u u' v

namespace KleinerLottApprox

variable {X' : Type u'} {X : Type u} {Y : Type v} [MetricSpace X'] [MetricSpace X] [MetricSpace Y]
  {p : X} {q : Y} {δ : ℝ}

/-- **Transport along a ball isometry.** -/
def transportBall_BCG1 (f : KleinerLottApprox p q δ) (φ : X' → X) {p' : X'} (hp : φ p' = p)
    (hiso : ∀ x ∈ ball p' δ⁻¹, ∀ y ∈ ball p' δ⁻¹, dist (φ x) (φ y) = dist x y)
    (himg : ball p δ⁻¹ ⊆ φ '' ball p' δ⁻¹) : KleinerLottApprox p' q δ where
  error_pos := f.error_pos
  error_lt_one := f.error_lt_one
  toFun := f.toFun ∘ φ
  basepoint := by simp only [comp_apply, hp, f.basepoint]
  distortion := by
    intro x hx x' hx'
    have hp' : p' ∈ ball p' δ⁻¹ := mem_ball_self (inv_pos.mpr f.error_pos)
    have hφx : φ x ∈ ball p δ⁻¹ := by
      rw [mem_ball, ← hp, hiso x hx p' hp']
      exact hx
    have hφx' : φ x' ∈ ball p δ⁻¹ := by
      rw [mem_ball, ← hp, hiso x' hx' p' hp']
      exact hx'
    have h := f.distortion (φ x) hφx (φ x') hφx'
    rw [hiso x hx x' hx'] at h
    exact h
  coverage := by
    intro y hy
    have hsub : f.toFun '' ball p δ⁻¹ ⊆ (f.toFun ∘ φ) '' ball p' δ⁻¹ := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨x, hx, rfl⟩ := himg hz
      exact ⟨x, hx, rfl⟩
    exact (infDist_le_infDist_of_subset hsub f.image_nonempty).trans (f.coverage y hy)

theorem transportBall_toFun_BCG1 (f : KleinerLottApprox p q δ) (φ : X' → X) {p' : X'}
    (hp : φ p' = p)
    (hiso : ∀ x ∈ ball p' δ⁻¹, ∀ y ∈ ball p' δ⁻¹, dist (φ x) (φ y) = dist x y)
    (himg : ball p δ⁻¹ ⊆ φ '' ball p' δ⁻¹) (x : X') :
    (f.transportBall_BCG1 φ hp hiso himg).toFun x = f.toFun (φ x) := rfl

end KleinerLottApprox

namespace PointedBallApprox

/-- **A bi-Lipschitz product map with coverage gives a Kleiner–Lott approximation with the
prescribed first coordinate.** For `x ↦ (Φ x, φT (τ x))` `(1 ± a)`-bi-Lipschitz on the closed
ball of radius `β⁻¹ + β` about `p₀` and `β/4`-covering (measured with `√(ΔΦ² + (c d_T)²)`,
`φT` a surjective metric model of `c d_T`), there is a Kleiner–Lott `β`-approximation of
`(X, p₀)` to `(ℝ ×₂ Y, (0, φT (τ p₀)))` whose first coordinate is `Φ` everywhere. -/
theorem exists_kleinerLott_with_first_coordinate_BCG1 {Xs : Type u} [MetricSpace Xs] {p₀ : Xs}
    {β a c : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (ha : 0 ≤ a) (ha1 : a < 1)
    (herr : 2 * a * (β⁻¹ + β) < β / 4) {T : Type v} (Φ : Xs → ℝ) (τ : Xs → T)
    (dT : T → T → ℝ) (hbase : Φ p₀ = 0)
    (hdist : ∀ x x', dist x p₀ ≤ β⁻¹ + β → dist x' p₀ ≤ β⁻¹ + β →
      (1 - a) * dist x x' ≤ Real.sqrt ((Φ x - Φ x') ^ 2 + (c * dT (τ x) (τ x')) ^ 2) ∧
        Real.sqrt ((Φ x - Φ x') ^ 2 + (c * dT (τ x) (τ x')) ^ 2) ≤ (1 + a) * dist x x')
    (hcov : ∀ (s : ℝ) (t : T),
      Real.sqrt (s ^ 2 + (c * dT t (τ p₀)) ^ 2) ≤ β⁻¹ + β - β / 4 →
        ∃ x, dist x p₀ ≤ β⁻¹ + β ∧ Real.sqrt ((s - Φ x) ^ 2 + (c * dT t (τ x)) ^ 2) < β / 4)
    {Y : Type v} [MetricSpace Y] (φT : T → Y) (hφT : Surjective φT)
    (hdY : ∀ t t', dist (φT t) (φT t') = c * dT t t') :
    ∃ f : KleinerLottApprox p₀ (WithLp.toLp 2 ((0 : ℝ), φT (τ p₀))) β,
      ∀ x, (f.toFun x).fst = Φ x := by
  have hd : ∀ (u u' : ℝ) (t t' : T),
      dist (WithLp.toLp 2 (u, φT t) : WithLp 2 (ℝ × Y)) (WithLp.toLp 2 (u', φT t')) =
        Real.sqrt ((u - u') ^ 2 + (c * dT t t') ^ 2) := by
    intro u u' t t'
    have h := WithLp.prod_dist_sq_eq_add_sq (WithLp.toLp 2 (u, φT t) : WithLp 2 (ℝ × Y))
      (WithLp.toLp 2 (u', φT t'))
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.dist_eq, sq_abs, hdY] at h
    rw [← h, Real.sqrt_sq dist_nonneg]
  have hε : 0 < β / 4 := by positivity
  have hεR : β / 4 < β⁻¹ + β := by
    have := inv_pos.mpr hβ
    linarith
  let F : Xs → WithLp 2 (ℝ × Y) := fun x => WithLp.toLp 2 (Φ x, φT (τ x))
  have hbaseF : F p₀ = WithLp.toLp 2 ((0 : ℝ), φT (τ p₀)) := by
    simp only [F, hbase]
  let f : PointedBallApprox p₀ (WithLp.toLp 2 ((0 : ℝ), φT (τ p₀))) (β⁻¹ + β) (β / 4) :=
    PointedBallApprox.ofBilipschitz ⟨ha, ha1⟩ hε hεR herr (fun x => F x.val) hbaseF
      (fun x x' => by
        change (1 - a) * dist x.val x'.val ≤ dist (F x.val) (F x'.val) ∧
          dist (F x.val) (F x'.val) ≤ (1 + a) * dist x.val x'.val
        simp only [F]
        rw [hd]
        exact hdist x.val x'.val x.property x'.property)
      (fun y hy => by
        obtain ⟨t, ht⟩ := hφT y.snd
        have hy' : y = WithLp.toLp 2 (y.fst, φT t) := by
          rw [ht]
          rfl
        rw [hy', hd, sub_zero] at hy
        obtain ⟨x, hx, hxy⟩ := hcov y.fst t hy
        refine ⟨⟨x, hx⟩, ?_⟩
        change dist y (F x) < β / 4
        rw [hy']
        simp only [F]
        rw [hd]
        exact hxy)
  refine ⟨f.toKleinerLottWithFirstCoordinate Φ hβ hβ1 (by linarith) (by
    have := hβ.le
    linarith), fun x => ?_⟩
  exact f.toKleinerLottWithFirstCoordinate_fst Φ (fun x => rfl) hβ hβ1 _ _ x

end PointedBallApprox

end GC.MetricGeometry
