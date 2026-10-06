import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.Approximation.IsometricKleinerLottApproximation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Kleiner-Lott witness error (review 75, section C.2, S-X144 group G2)

For `f : KleinerLottApprox p q δ` and targets `y i` with `dist (y i) q < δ⁻¹ - δ`, coverage gives
witnesses `x i ∈ B(p, δ⁻¹)` with `dist (y i) (f (x i)) < 2 δ`. Two covering errors and one
distortion give `|d(x i, x j) - d(y i, y j)| < 5 δ`; the radial error gives
`d(x i, p) < d(y i, q) + 3 δ`. These are the constants of C.2 (`5 β` and `3 β`, NOT `2 β`); the
statement is for an arbitrary (not only finite) family of targets.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

namespace KleinerLottApprox

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {p : X} {q : Y} {δ : ℝ}

/-- **C.2, the KL witness error lemma.** -/
theorem kl_witness_error_SMR (f : KleinerLottApprox p q δ) {ι : Type*} (y : ι → Y)
    (hy : ∀ i, dist (y i) q < δ⁻¹ - δ) :
    ∃ x : ι → X, (∀ i, x i ∈ Metric.ball p δ⁻¹) ∧
      (∀ i, dist (y i) (f.toFun (x i)) < 2 * δ) ∧
      (∀ i j, |dist (x i) (x j) - dist (y i) (y j)| < 5 * δ) ∧
      (∀ i, dist (x i) p < dist (y i) q + 3 * δ) := by
  choose x hx hxy using fun i => f.coverage_witness (y i) (hy i)
  refine ⟨x, hx, hxy, ?_, ?_⟩
  · intro i j
    have hd := f.distortion (x i) (hx i) (x j) (hx j)
    have h1 := hxy i
    have h2 := hxy j
    have h3 := dist_triangle4 (f.toFun (x i)) (y i) (y j) (f.toFun (x j))
    have h4 := dist_triangle4 (y i) (f.toFun (x i)) (f.toFun (x j)) (y j)
    rw [dist_comm (f.toFun (x i)) (y i)] at h3
    rw [dist_comm (f.toFun (x j)) (y j)] at h4
    rw [abs_lt]
    rw [abs_le] at hd
    constructor <;> linarith [hd.1, hd.2]
  · intro i
    have hr := f.radial_error (x i) (hx i)
    have h1 := hxy i
    have h2 := dist_triangle (f.toFun (x i)) (y i) q
    rw [dist_comm (f.toFun (x i)) (y i)] at h2
    rw [abs_le] at hr
    linarith [hr.1, hr.2]

/-- The constants at `δ = 3/20` (the `β₃` of the review): `5 δ = 3/4`, `3 δ = 9/20`, and the
coverage radius `δ⁻¹ - δ = 391/60`. -/
theorem kl_witness_error_three_twentieths_SMR (f : KleinerLottApprox p q (3 / 20)) {ι : Type*}
    (y : ι → Y) (hy : ∀ i, dist (y i) q < 391 / 60) :
    ∃ x : ι → X, (∀ i, x i ∈ Metric.ball p (20 / 3)) ∧
      (∀ i j, |dist (x i) (x j) - dist (y i) (y j)| < 3 / 4) ∧
      (∀ i, dist (x i) p < dist (y i) q + 9 / 20) := by
  have hinv : (3 / 20 : ℝ)⁻¹ = 20 / 3 := by norm_num
  obtain ⟨x, hx, -, hpair, hrad⟩ := f.kl_witness_error_SMR y (fun i => by
    have := hy i
    rw [hinv]
    linarith)
  refine ⟨x, fun i => by simpa only [hinv] using hx i, fun i j => ?_, fun i => ?_⟩
  · have := hpair i j
    linarith
  · have := hrad i
    linarith

end KleinerLottApprox

/-- **Consumer (explicit numbers).** The identity of `ℝ` is a KL approximation at `δ = 3/20`; two
targets `1` and `2` (both within `391/60` of the base point `0`) have witnesses
`x₀, x₁ ∈ (-20/3, 20/3)` with `|d(x₀, x₁) - 1| < 3/4` and `d(xᵢ, 0) < d(yᵢ, 0) + 9/20`. -/
theorem kl_witness_error_consumer_SMR :
    ∃ x₀ x₁ : ℝ, |x₀| < 20 / 3 ∧ |x₁| < 20 / 3 ∧ |dist x₀ x₁ - 1| < 3 / 4 ∧
      |x₀| < 1 + 9 / 20 ∧ |x₁| < 2 + 9 / 20 := by
  let f : KleinerLottApprox (0 : ℝ) (0 : ℝ) (3 / 20) :=
    (IsometryEquiv.refl ℝ).toKleinerLottApprox rfl (by norm_num) (by norm_num)
  obtain ⟨x, hx, hpair, hrad⟩ := f.kl_witness_error_three_twentieths_SMR
    (fun i : Fin 2 => ((i : ℕ) + 1 : ℝ)) (fun i => by
      fin_cases i <;> simp [Real.dist_eq] <;> norm_num)
  refine ⟨x 0, x 1, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Real.dist_eq] using hx 0
  · simpa [Real.dist_eq] using hx 1
  · have := hpair 0 1
    simpa [Real.dist_eq] using this
  · have := hrad 0
    simpa [Real.dist_eq] using this
  · have := hrad 1
    simp [Real.dist_eq] at this
    linarith

end GC.MetricGeometry
