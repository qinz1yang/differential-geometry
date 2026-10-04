import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EdgeModelCore
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EndpointBand
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimGraph
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.VerticalSegment
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.TorusFlatness
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Consumers of the LFR17–LFR24 kernels

Concrete instances of every kernel group of lane W4-F7c:

* LFR24: the core of the identity radius on the real line (`edgeModelCore_line`) and the metric
  binding for `F = |·|` (`edgeModelCore_abs_isCompact`);
* LFR23: the endpoint comparison angle on the half-line `ℝ≥0` (`endpoint_angle_nnreal`) and the
  exclusion of an equilateral triangle (`not_exists_small_distortion_of_equilateral`);
* LFR20: the root of `f(t,z) = t` (`root_of_fst`) and the constants at `Δ = 1`;
* LFR18: uniqueness of the midpoint of a vertical pair in an `ℓ²` product (`eq_vertical_midpoint`);
* LFR17: the torus clause for Lebesgue measure on the line (`eq_zero_of_integral_line`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.Geometry.Collapse

/-- **LFR24 consumer.** For the identity radius on `ℝ` the core function is smooth on a
neighbourhood of `(-∞,9]` and `D_4 = (-∞,4]`. -/
theorem edgeModelCore_line :
    (∃ W : Set ℝ, IsOpen W ∧ {x : ℝ | x ≤ 9} ⊆ W ∧
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (edgeModelCore fun x : ℝ => x) W) ∧
    edgeCoreSublevel (fun x : ℝ => x) (fun x : ℝ => x) 4 = Iic 4 := by
  have hFr : ∀ x : ℝ, |x - x| < 1 / 100 := fun x => by simp
  refine ⟨contMDiffOn_edgeModelCore (r := fun x : ℝ => x) continuous_id isOpen_univ
    contMDiff_id.contMDiffOn (fun _ _ _ => mem_univ _) le_rfl hFr, ?_⟩
  rw [edgeCoreSublevel_eq le_rfl hFr ⟨by norm_num, by norm_num⟩]
  rfl

/-- **LFR24 consumer (metric binding).** For `F = |·|` on `ℝ`, `z₀ = 0`, `Δ = 1`, the sublevel
`D_4` is compact and contains `[-3.99, 3.99]`. -/
theorem edgeModelCore_abs_isCompact :
    IsCompact (edgeCoreSublevel (fun x : ℝ => dist x 0 / 1) (fun x : ℝ => |x|) 4) ∧
      closedBall (0 : ℝ) ((4 - 1 / 100) * 1) ⊆
        edgeCoreSublevel (fun x : ℝ => dist x 0 / 1) (fun x : ℝ => |x|) 4 := by
  have hFr : ∀ x : ℝ, |(|x|) - dist x 0 / 1| < 1 / 100 := fun x => by simp
  obtain ⟨h₁, h₂, -⟩ := edgeModelCore_dist_isCompact (z₀ := (0 : ℝ)) one_pos continuous_abs le_rfl
    hFr (⟨by norm_num, by norm_num⟩ : (4 : ℝ) ∈ Icc (3 : ℝ) 6)
  exact ⟨h₁, h₂⟩

/-- **LFR23 consumer.** On the half-line `ℝ≥0` with the inclusion `q` (distortion `0 ≤ δ`), the
comparison angle at `5` of the triangle `(0, 5, 19/2)` has `1 + cos ∠̃ < 300 δ`. -/
theorem endpoint_angle_nnreal {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 1000) :
    1 + Real.cos (DifferentialGeometry.Geometry.Comparison.Toponogov.metricComparisonAngle
      (0 : ℝ≥0) 5 (19 / 2)) < 300 * δ := by
  refine one_add_cos_metricComparisonAngle_lt (q := fun y : ℝ≥0 => (y : ℝ)) hδ hδ' rfl
    (fun y _ => y.2) (fun y _ y' _ => ?_) ?_ ?_ ?_
  · rw [NNReal.dist_eq, Real.dist_eq, sub_self, abs_zero]; exact hδ.le
  · rw [NNReal.dist_eq]; norm_num
  · rw [NNReal.dist_eq]; norm_num
  · rw [NNReal.dist_eq]; norm_num

/-- **LFR23 consumer (torus exclusion).** No map of an equilateral triple of side `1/2` into `ℝ`
has distortion below `1/6`. -/
theorem not_exists_small_distortion_of_equilateral {X : Type*} [PseudoMetricSpace X]
    {y₁ y₂ y₃ : X} (h₁₂ : dist y₁ y₂ = 1 / 2) (h₁₃ : dist y₁ y₃ = 1 / 2)
    (h₂₃ : dist y₂ y₃ = 1 / 2) :
    ¬ ∃ (q : X → ℝ) (δ : ℝ), δ < 1 / 6 ∧ |dist (q y₁) (q y₂) - dist y₁ y₂| ≤ δ ∧
      |dist (q y₁) (q y₃) - dist y₁ y₃| ≤ δ ∧ |dist (q y₂) (q y₃) - dist y₂ y₃| ≤ δ := by
  rintro ⟨q, δ, hδ, d₁₂, d₁₃, d₂₃⟩
  have := half_le_three_mul_of_equilateral h₁₂ h₁₃ h₂₃ d₁₂ d₁₃ d₂₃
  linarith

/-- **LFR20 consumer.** For `f(t,z) = t` on `ℝ × Unit` the root of `f = s` is `s` itself. -/
theorem root_of_fst {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    ∃ T : ℝ × Unit → ℝ, ContinuousOn T (Icc (-1) 1 ×ˢ univ) ∧ T (s, ()) = s := by
  obtain ⟨T, hT, hroot⟩ := exists_continuousOn_root (Z := Unit) (f := Prod.fst) (a := 1) (b := 2)
    (c := 1) continuous_fst (fun _ => strictMono_id.strictMonoOn _) (fun t _ _ => by simp)
    one_pos (by norm_num)
  exact ⟨T, hT, ((hroot s hs ()).2.2.2 s ⟨by linarith [hs.1], by linarith [hs.2]⟩ rfl).symm⟩

/-- **LFR20 consumer.** The numerical inequalities hold at `Δ = 1`, `σ = 1/100`, `β = 1`. -/
theorem slimPacket_constants_one :
    Real.sqrt ((9 * (10 ^ 6 * (1 : ℝ)) / 10 + 1 / 100) ^ 2 + (10 ^ 3 * (1 : ℝ)) ^ 2) + 1 <
      91 / 100 * (10 ^ 6 * (1 : ℝ)) := by
  have h := slimPacket_constants (Δ := 1) (σ := 1 / 100) (β := 1) le_rfl (by norm_num) le_rfl le_rfl
  exact h.2.2.1

/-- **LFR18 consumer.** In the `ℓ²` product `ℝ × Z`, the only midpoint of `(t,z)` and `(t+ℓ,z)` is
`(t + ℓ/2, z)`. -/
theorem eq_vertical_midpoint {Z : Type*} [MetricSpace Z] {t ℓ : ℝ} {z : Z}
    {m : WithLp 2 (ℝ × Z)} (h₁ : dist (WithLp.toLp 2 (t, z)) m = ℓ / 2)
    (h₂ : dist m (WithLp.toLp 2 (t + ℓ, z)) = ℓ / 2) : m = WithLp.toLp 2 (t + ℓ / 2, z) := by
  obtain ⟨hsnd, -, hdist⟩ := vertical_of_dist_add_dist_le (t := t) (ℓ := ℓ) (z := z) (m := m)
    (by linarith)
  rw [← WithLp.toLp_ofLp (p := 2) m]
  congr 1
  exact Prod.ext (show m.fst = t + ℓ / 2 by linarith) hsnd

/-- **LFR17 consumer.** On the line with Lebesgue measure, a continuous nonnegative integrable
function with zero integral is zero. -/
theorem eq_zero_of_integral_line {f : ℝ → ℝ} (hf : Continuous f)
    (hnn : ∀ x, 0 ≤ f x) (hint : Integrable f) (h0 : ∫ x, f x = 0) : f = 0 :=
  eq_zero_of_integral_eq_zero_of_continuous_nonneg volume hf hnn hint h0

end DifferentialGeometry.Geometry.Collapse
