import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EndpointBand
import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# LFR23: no endpoint interval model on a space with a translation along a segment

Route (ii) for the torus case of LFR23 (blueprint master207A:26745, lane SF-C; decision of the
coordinator, 2026-10-04).  On a flat torus every translation is an isometry, so for a unit-speed
minimizing segment `γ` from `z₀` the translation `τ` with `τ z₀ = γ s` also has `τ (γ s) = γ (2s)`.
Then `p = τ⁻¹ z₀` and `γ s` lie on the same distance level `s` from `z₀`, at mutual distance `2s`,
while LFR23's interval model `q` (based at `z₀`, distortion `δ`) puts any two points of one level
within `3δ` (W4-F7c's `dist_le_three_mul_of_level`).  Hence `2s ≤ 3δ`, and with `s = 5/2` a flat torus
carries no such model once `δ < 5/3`.  This replaces the topological torus dichotomy and the
"embedded lifted disk" clause of LFR23's proof; the isometry `τ` is the producer of lane SF-B.
-/

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Collapse

variable {Z : Type*} [PseudoMetricSpace Z]

/-- **LFR23, translation exclusion (kernel).** An isometry `τ` translating a unit-speed minimizing
segment `γ` from `z₀` by `s` (`τ z₀ = γ s`, `τ (γ s) = γ (2s)`) forces `2s ≤ 3δ` for LFR23's interval
model `q` based at `z₀` with distortion `δ`, provided `s ≤ 10`. -/
theorem two_mul_le_three_mul_of_translation {z₀ : Z} {q : Z → ℝ} {δ s : ℝ} (hq0 : q z₀ = 0)
    (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hs : 0 ≤ s) (hs10 : s ≤ 10) {γ : ℝ → Z} (hγ0 : γ 0 = z₀)
    (hγ : ∀ t ∈ Icc 0 (2 * s), ∀ t' ∈ Icc 0 (2 * s), dist (γ t) (γ t') = |t - t'|)
    (τ : Z ≃ᵢ Z) (hτ0 : τ z₀ = γ s) (hτs : τ (γ s) = γ (2 * s)) :
    2 * s ≤ 3 * δ := by
  have h0 : (0 : ℝ) ∈ Icc 0 (2 * s) := ⟨le_refl 0, by linarith⟩
  have hs' : s ∈ Icc 0 (2 * s) := ⟨hs, by linarith⟩
  have h2s : 2 * s ∈ Icc 0 (2 * s) := ⟨by linarith, le_refl _⟩
  have hda : dist z₀ (γ s) = s := by
    rw [← hγ0, hγ 0 h0 s hs', zero_sub, abs_neg, abs_of_nonneg hs]
  have hdb : dist z₀ (γ (2 * s)) = 2 * s := by
    rw [← hγ0, hγ 0 h0 (2 * s) h2s, zero_sub, abs_neg, abs_of_nonneg (by linarith)]
  set p := τ.symm z₀
  have hp : dist z₀ p = s := by
    rw [← τ.dist_eq z₀ p, hτ0, show τ p = z₀ from τ.apply_symm_apply z₀, dist_comm, hda]
  have hpa : dist p (γ s) = 2 * s := by
    rw [← τ.dist_eq p (γ s), show τ p = z₀ from τ.apply_symm_apply z₀, hτs, hdb]
  have := dist_le_three_mul_of_level hq0 hqnn hdist hs10 hp hda
  rwa [hpa] at this

/-- **LFR23, torus exclusion by translation.** With a segment of length five (`s = 5/2`), an isometry
translating it by `5/2` is incompatible with LFR23's interval model once `δ < 5/3`. -/
theorem false_of_translation_of_lt {z₀ : Z} {q : Z → ℝ} {δ : ℝ} (hq0 : q z₀ = 0)
    (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hδ : δ < 5 / 3) {γ : ℝ → Z} (hγ0 : γ 0 = z₀)
    (hγ : ∀ t ∈ Icc 0 5, ∀ t' ∈ Icc 0 5, dist (γ t) (γ t') = |t - t'|)
    (τ : Z ≃ᵢ Z) (hτ0 : τ z₀ = γ (5 / 2)) (hτs : τ (γ (5 / 2)) = γ 5) : False := by
  have h5 : (2 : ℝ) * (5 / 2) = 5 := by norm_num
  have h := two_mul_le_three_mul_of_translation (s := 5 / 2) hq0 hqnn hdist (by norm_num)
    (by norm_num) hγ0 (by rw [h5]; exact hγ) τ hτ0 (by rw [h5]; exact hτs)
  linarith

end DifferentialGeometry.Geometry.Collapse
