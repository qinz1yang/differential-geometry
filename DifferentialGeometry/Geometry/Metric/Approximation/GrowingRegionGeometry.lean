import DifferentialGeometry.Geometry.Comparison.VaryingCurvatureCovering
import DifferentialGeometry.Geometry.Comparison.VaryingLocalGeometry
import Mathlib.Order.Filter.AtTopBot.Tendsto

set_option autoImplicit false

open Set Metric Real Filter
open scoped Topology

namespace GC.MetricGeometry

open DifferentialGeometry.Geometry.Comparison.Toponogov

universe u
variable {X : ℕ → Type u} [∀ i, MetricSpace (X i)] [∀ i, CompleteSpace (X i)]

theorem eventual_internal_nets_of_growing_local_geometry
    (p : ∀ i, X i) {κ ρ : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hcurves : ∀ i, ∀ a b : X i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hκ : ∀ i, 0 ≤ κ i) (hκzero : Tendsto κ atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop)
    (hdim : ∀ i, dimH (ball (p i) (ρ i)) ≤ n)
    (hlocal : ∀ i, ∀ z ∈ ball (p i) (ρ i),
      ∃ Ω : Set (X i), IsOpen Ω ∧ fourPointComparison (κ i) Ω ∧ z ∈ Ω)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∃ T : Finset (X i),
      T.card ≤ (1 + ⌈4 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh (2 * R) / ε⌉₊) ^ n ∧
      (T : Set (X i)) ⊆ closedBall (p i) R ∧
      ∀ x ∈ closedBall (p i) R, ∃ y ∈ T, dist x y < ε := by
  filter_upwards [hκzero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hρ.eventually (eventually_gt_atTop (256 * R))] with i hki hri
  have hsub : ball (p i) (256 * R) ⊆ ball (p i) (ρ i) := ball_subset_ball hri.le
  exact exists_closedBall_net_of_bounded_local_curvature_and_dimH (hcurves i) (p i)
    (hκ i) hki.le hR hε hn ((dimH_mono hsub).trans (hdim i))
    (fun z hz => hlocal i z (hsub hz))

theorem eventual_fourPointComparison_of_growing_local_geometry
    (p : ∀ i, X i) {κ ρ : ℕ → ℝ} {n : ℕ}
    (hcurves : ∀ i, ∀ a b : X i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hκ : ∀ i, 0 ≤ κ i) (hρ : Tendsto ρ atTop atTop)
    (hdim : ∀ i, dimH (ball (p i) (ρ i)) ≤ n)
    (hlocal : ∀ i, ∀ z ∈ ball (p i) (ρ i),
      ∃ Ω : Set (X i), IsOpen Ω ∧ fourPointComparison (κ i) Ω ∧ z ∈ Ω)
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ i in atTop, fourPointComparison (κ i) (ball (p i) R) := by
  filter_upwards [hρ.eventually (eventually_gt_atTop (256 * R))] with i hri
  have hsub : ball (p i) (256 * R) ⊆ ball (p i) (ρ i) := ball_subset_ball hri.le
  exact (fourPointComparison_two_ball_of_local_comparison_and_dimH (hcurves i) (p i)
    (hκ i) hR ((dimH_mono hsub).trans (hdim i))
    (fun z hz => hlocal i z (hsub hz))).mono (ball_subset_ball (by linarith))

end GC.MetricGeometry
