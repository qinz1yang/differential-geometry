import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalCovering
import DifferentialGeometry.Geometry.Comparison.CurvatureWeakening
import DifferentialGeometry.Topology.MetricSpace.CeilCoveringBound

set_option autoImplicit false

open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [CompleteSpace X]

theorem exists_polynomial_net_of_nonnegative_comparison
    (hcurves : ∀ a b : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hcomp : fourPointComparison 0 (univ : Set X)) {n : ℕ} (hn : 1 ≤ n)
    (hdim : dimH (univ : Set X) ≤ n) (p : X)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (hεone : ε ≤ 1) :
    ∃ T : Finset X,
      (T.card : ℝ) ≤ (2 + 4 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh (2 * R)) ^ n *
        ε ^ (-(n : ℝ)) ∧
      (∀ x ∈ T, dist x p ≤ R) ∧
      ∀ x : X, dist x p ≤ R → ∃ y ∈ T, dist x y ≤ ε := by
  obtain ⟨T, hcard, hT, hnet⟩ := exists_closedBall_net_of_local_comparison_and_dimH
    hcurves p hR hε hn ((dimH_mono (subset_univ _)).trans hdim)
    (fun z _ => ⟨univ, isOpen_univ, hcomp.of_zero (by norm_num), mem_univ z⟩)
  refine ⟨T, ?_, fun x hx => hT hx, fun x hx => ?_⟩
  · have hB : 0 ≤ 4 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh (2 * R) := by positivity
    exact (show (T.card : ℝ) ≤
      ((1 + Nat.ceil (4 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh (2 * R) / ε)) ^ n : ℕ) by
        exact_mod_cast hcard).trans (ceil_covering_bound_le_polynomial hB hε hεone n)
  · obtain ⟨y, hy, hxy⟩ := hnet x hx
    exact ⟨y, hy, hxy.le⟩

theorem polynomial_nets_of_nonnegative_comparison
    (hcurves : ∀ a b : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hcomp : fourPointComparison 0 (univ : Set X)) {n : ℕ} (hn : 1 ≤ n)
    (hdim : dimH (univ : Set X) ≤ n) (p : X) :
    ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ T : Finset X,
        (T.card : ℝ) ≤ C * ε ^ (-(n : ℝ)) ∧
        (∀ x ∈ T, dist x p ≤ R) ∧
        ∀ x : X, dist x p ≤ R → ∃ y ∈ T, dist x y ≤ ε := by
  intro R hR
  refine ⟨(2 + 4 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh (2 * R)) ^ n, by positivity, ?_⟩
  intro ε hε hεone
  exact exists_polynomial_net_of_nonnegative_comparison hcurves hcomp hn hdim p hR hε hεone

end DifferentialGeometry.Geometry.Comparison.Toponogov
