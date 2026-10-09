import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateCutBoundaryDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.DerivativeAssembly

/-!
# CH12-S16: T1 wiring (picked boundary derivative bound -> S5 `hT1` shape) and numerics

`LateCutFamily.hT1_of_picked_S16` is the sibling theorem restated in the exact shape of the
`hT1` input of `late_derivative_tests_of_flow_assembly_W1`.  The numerical side conditions of
the small parameter `w̄ = 1/10000` and of the collar estimates are explicit lemmas.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- The fixed small volume parameter used in the boundary alternatives. -/
def wbar_S16 : ℝ := 1 / 10000

theorem wbar_S16_pos : 0 < wbar_S16 := by unfold wbar_S16; norm_num

theorem wbar_S16_lt_euclideanThreeUnitBallVolume : wbar_S16 < euclideanThreeUnitBallVolume := by
  unfold wbar_S16 euclideanThreeUnitBallVolume
  nlinarith [Real.pi_gt_three]

/-- Numerical side conditions of the collar estimates for `δ ≤ 1/10000`: the constants used in
`exists_collar_localization_of_distanceToBoundary_le` (ball containment of radius `24` in height
`< 25`, vertical path `√(1+δ) < 2`) and in the interior negative-plane estimate (radius `3/2`
inside height `< 2`). -/
theorem collarNumerics_S16 {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 10000) :
    δ < 1 / 2 ∧ (1 - δ)⁻¹ ≤ 100 / 99 ∧ (24 : ℝ) ≤ 25 / Real.sqrt ((1 - δ)⁻¹) ∧
      (3 / 2 : ℝ) ≤ 2 / Real.sqrt ((1 - δ)⁻¹) ∧ Real.sqrt (1 + δ) < 2 := by
  have hden : 0 < 1 - δ := by linarith
  have hinv : (1 - δ)⁻¹ ≤ (100 : ℝ) / 99 := by
    rw [inv_eq_one_div, div_le_iff₀ hden]
    linarith
  have hspos : 0 < Real.sqrt ((1 - δ)⁻¹) := Real.sqrt_pos.mpr (inv_pos.mpr hden)
  have hsb : Real.sqrt ((1 - δ)⁻¹) ≤ (25 : ℝ) / 24 :=
    (Real.sqrt_le_left (by norm_num)).mpr (hinv.trans (by norm_num))
  refine ⟨by linarith, hinv, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hspos).mpr
    nlinarith
  · apply (le_div_iff₀ hspos).mpr
    nlinarith
  · have hs := Real.sqrt_lt_sqrt (by linarith : 0 ≤ 1 + δ) (by linarith : 1 + δ < 4)
    norm_num at hs
    exact hs

theorem wbar_S16_collar_ok :
    0 < wbar_S16 ∧ wbar_S16 < euclideanThreeUnitBallVolume ∧
      (1 / 10000 : ℝ) ≤ 1 / 10000 ∧ ((1 / 10000 : ℝ) < 1 / 2 ∧
        (24 : ℝ) ≤ 25 / Real.sqrt ((1 - (1 / 10000 : ℝ))⁻¹)) :=
  ⟨wbar_S16_pos, wbar_S16_lt_euclideanThreeUnitBallVolume, le_rfl,
    (collarNumerics_S16 (by norm_num) (le_refl _)).1, (collarNumerics_S16 (by norm_num) (le_refl _)).2.2.1⟩

theorem LateCutFamily.hT1_of_picked_S16 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ}
    {slices : ℕ → RegularSlice F.observation} (L : GC.LongTime.LateCutFamily F K slices) :
    ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, ∀ j, N ≤ j → ∀ C i, L.thin j C i →
      ∀ p : ((L.decomposition j C).component i).Carrier,
        distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p ≤
          ENNReal.ofReal 10 →
      ∀ r : ℝ, 0 < r → ENNReal.ofReal r < curvatureRadius (L.metric j C i) p →
      ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf (L.metric j C i) p r,
        curvatureDerivativeNorm (L.metric j C i) k q ≤ A * (r ^ (k + 2))⁻¹ :=
  L.exists_eventual_nearBoundary_derivative_bound

end GC.LongTime.Ch12
