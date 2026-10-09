import DifferentialGeometry.Geometry.Comparison.AngleExcess
import Mathlib.Topology.Instances.ENNReal.Lemmas

open Filter
open scoped Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem opposite_endpoint_excess_bound {X : Type*} [MetricSpace X]
    {p aPlus aMinus : X} {σ L : ℝ}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hL : 0 < L)
    (hp : dist p aPlus = L) (hm : dist p aMinus = L)
    (hangle : Real.pi - σ ≤ comparisonAngleNegCurvature σ
      (dist p aPlus) (dist p aMinus) (dist aPlus aMinus)) :
    0 ≤ 2 * L - dist aPlus aMinus ∧
      2 * L - dist aPlus aMinus ≤ -(2 / Real.sqrt σ) * Real.log (Real.cos (σ / 2)) ∧
      -(2 / Real.sqrt σ) * Real.log (Real.cos (σ / 2)) ≤ σ ^ (3 / 2 : ℝ) / 2 := by
  rw [hp, hm] at hangle
  apply equal_side_excess_bound_of_angle_lower_bound hσ hσ1 hL dist_nonneg _ hangle
  have ht := dist_triangle aPlus p aMinus
  rw [dist_comm aPlus p, hp, hm] at ht
  linarith

theorem tendsto_opposite_endpoint_excess_zero {A : ℕ → Type*} [∀ i, MetricSpace (A i)]
    {σ L : ℕ → ℝ} {p aPlus aMinus : ∀ i, A i}
    (hσpos : ∀ i, 0 < σ i) (hσ : Tendsto σ atTop (𝓝 0))
    (hL : ∀ i, 0 < L i)
    (hp : ∀ i, dist (p i) (aPlus i) = L i)
    (hm : ∀ i, dist (p i) (aMinus i) = L i)
    (hangle : ∀ᶠ i in atTop, Real.pi - σ i ≤ comparisonAngleNegCurvature (σ i)
      (dist (p i) (aPlus i)) (dist (p i) (aMinus i)) (dist (aPlus i) (aMinus i))) :
    Tendsto (fun i => 2 * L i - dist (aPlus i) (aMinus i)) atTop (𝓝 0) := by
  have hbound := hσ.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hlim : Tendsto (fun i => σ i * Real.sqrt (σ i) / 2) atTop (𝓝 0) := by
    simpa using (hσ.mul hσ.sqrt).div_const 2
  apply squeeze_zero' _ _ hlim
  · exact Eventually.of_forall fun i => by
      have ht := dist_triangle (aPlus i) (p i) (aMinus i)
      rw [dist_comm (aPlus i) (p i), hp, hm] at ht
      linarith
  · filter_upwards [hbound, hangle] with i hi hai
    have hb := opposite_endpoint_excess_bound (hσpos i) hi.le (hL i) (hp i) (hm i) hai
    have hrpow : σ i ^ (3 / 2 : ℝ) = σ i * Real.sqrt (σ i) := by
      rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add (hσpos i), Real.rpow_one]
    simpa only [hrpow] using hb.2.1.trans hb.2.2

end DifferentialGeometry.Geometry.Comparison.Toponogov
