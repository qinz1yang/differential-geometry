import DifferentialGeometry.Geometry.Comparison.ModelSideStability
import DifferentialGeometry.Geometry.Comparison.CradleSequenceThreeFifths

set_option autoImplicit false



open Set Filter Real Metric Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem tendsto_modelSideNegCurvature_deficit_of_cradle_recurrence_three_fifths
    {κ ℓ : ℝ} (hκ : 0 ≤ κ) (hℓ : 0 < ℓ) {a b c α : ℕ → ℝ}
    (hwindow : ∀ n, 0 ≤ a n ∧ a n ≤ b n ∧ 3 * ℓ / 5 ≤ a n + b n ∧ a n + b n < ℓ)
    (hc : ∀ n, 0 ≤ c n ∧ c n ≤ a n + (3 * ℓ / 5 - a n) / 3)
    (harec : ∀ n, a (n + 1) = min (c n) (b n - (3 * ℓ / 5 - a n) / 3))
    (hbrec : ∀ n, b (n + 1) = max (c n) (b n - (3 * ℓ / 5 - a n) / 3))
    (hα : ∀ n, α n ∈ Icc (0 : ℝ) Real.pi)
    (hangle : ∀ n, comparisonAngleNegCurvature κ (a n)
      ((3 * ℓ / 5 - a n) / 3) (c n) ≤ α n) :
    Tendsto (fun n => a n + b n - modelSideNegCurvature κ (a n) (b n) (α n)) atTop (𝓝 0) := by
  have hmodel := tendsto_comparisonAngleNegCurvature_pi_of_cradle_recurrence_three_fifths
    hκ hℓ hwindow hc harec hbrec
  have hαlim : Tendsto α atTop (𝓝 Real.pi) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hmodel tendsto_const_nhds hangle (fun n => (hα n).2)
  apply tendsto_modelSideNegCurvature_deficit_of_angle_pi (L := ℓ) hκ _ hαlim
  apply Eventually.of_forall
  intro n
  have hn := hwindow n
  exact ⟨⟨hn.1, by linarith [hn.2.1, hn.2.2.2]⟩,
    ⟨hn.1.trans hn.2.1, by linarith [hn.2.2.2]⟩, hα n⟩

theorem le_modelSideNegCurvature_of_cradle_recurrence_three_fifths
    {κ ℓ D : ℝ} (hκ : 0 ≤ κ) (hℓ : 0 < ℓ) {a b c α : ℕ → ℝ}
    (hwindow : ∀ n, 0 ≤ a n ∧ a n ≤ b n ∧ 3 * ℓ / 5 ≤ a n + b n ∧ a n + b n < ℓ)
    (hc : ∀ n, 0 ≤ c n ∧ c n ≤ a n + (3 * ℓ / 5 - a n) / 3)
    (harec : ∀ n, a (n + 1) = min (c n) (b n - (3 * ℓ / 5 - a n) / 3))
    (hbrec : ∀ n, b (n + 1) = max (c n) (b n - (3 * ℓ / 5 - a n) / 3))
    (hα : ∀ n, α n ∈ Icc (0 : ℝ) Real.pi)
    (hangle : ∀ n, comparisonAngleNegCurvature κ (a n)
      ((3 * ℓ / 5 - a n) / 3) (c n) ≤ α n)
    (hmono : Antitone (fun n => modelSideNegCurvature κ (a n) (b n) (α n)))
    (hD : ∀ n, D ≤ a n + b n) :
    ∀ n, D ≤ modelSideNegCurvature κ (a n) (b n) (α n) := by
  have hlim := tendsto_modelSideNegCurvature_deficit_of_cradle_recurrence_three_fifths
    hκ hℓ hwindow hc harec hbrec hα hangle
  intro N
  have hle : D - modelSideNegCurvature κ (a N) (b N) (α N) ≤ 0 := by
    apply ge_of_tendsto hlim
    apply eventually_atTop.mpr
    refine ⟨N, ?_⟩
    intro n hn
    linarith [hmono hn, hD n]
  linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov
