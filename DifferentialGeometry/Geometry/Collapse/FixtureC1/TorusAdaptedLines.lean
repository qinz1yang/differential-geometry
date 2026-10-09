import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusCircleChart
import DifferentialGeometry.Geometry.Collapse.FixtureC1.TorusGeodesic

/-!
# Projected lines and the plane coordinate (S-FIXTURE-C1b, F1, G4 file 1)

The physical (instance-free) part of the geodesic test of the circle adapted centre. Along the line
`t ↦ π(x̃ + t v)` with `x̃` in the slab of the lift `j̃` the normalized plane coordinate
`η_j = R⁻¹ · ell(j̃)` is affine: `η(π(x̃ + D v)) - η(π x̃) = D · R⁻¹ planeL v` while the line stays
in the slab, and `dη(dπ u) = R⁻¹ planeL u`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] torMS_FXC1

section Lines

variable (Λ : TorusPeriods_FXC1) {R : ℝ} (hR : 0 < R) {β : ℕ → ℝ} (hβ2 : 0 < β 2)
  (hβ2s : β 2 ≤ 1 / 10 ^ 7) (hLp : 8 * R / β 2 ≤ planePeriod_FXC1 Λ)

include hR hβ2 hβ2s hLp in
/-- A point of `ℝ³` within `4·10⁷ R` of the lift `j̃` lies in the slab of `j̃`. -/
theorem mem_ellDom_of_norm_lt_FXC1 (j : Tor_FXC1 Λ) {y : E3}
    (hy : ‖y - torLift_FXC1 Λ j‖ < 4 * 10 ^ 7 * R) :
    y ∈ ellDom_FXC1 Λ (torLift_FXC1 Λ j) := by
  have hLp' := torLp_ge_FXC1 Λ hR hβ2 hβ2s hLp
  change ‖planeL_FXC1 (y - torLift_FXC1 Λ j)‖ < _
  have := norm_planeL_le_FXC1 (y - torLift_FXC1 Λ j)
  linarith

include hR hβ2 hβ2s hLp in
/-- **The plane coordinate is affine along a projected line** while it stays in the slab. -/
theorem torEta_line_FXC1 (j : Tor_FXC1 Λ) (xt v : E3) {D : ℝ} (hD0 : 0 ≤ D)
    (hx : ‖xt - torLift_FXC1 Λ j‖ < 200 * R) (hv : ‖v‖ = R) (hD : D < 2010200) :
    torEta_FXC1 Λ R j (torPi_FXC1 Λ (xt + D • v)) - torEta_FXC1 Λ R j (torPi_FXC1 Λ xt) =
      D • (R⁻¹ • planeL_FXC1 v) := by
  have hDv : ‖D • v‖ ≤ 2010200 * R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hD0, hv]
    exact mul_le_mul_of_nonneg_right hD.le hR.le
  have hx' := mem_ellDom_of_norm_lt_FXC1 Λ hR hβ2 hβ2s hLp j (y := xt) (by linarith)
  have hy' := mem_ellDom_of_norm_lt_FXC1 Λ hR hβ2 hβ2s hLp j (y := xt + D • v) (by
    have := norm_add_le (xt - torLift_FXC1 Λ j) (D • v)
    rw [show xt + D • v - torLift_FXC1 Λ j = xt - torLift_FXC1 Λ j + D • v by abel]
    linarith)
  rw [torEta_FXC1, torEta_FXC1, ell_torPi_FXC1 Λ hx', ell_torPi_FXC1 Λ hy', ← smul_sub,
    ← map_sub, show xt + D • v - torLift_FXC1 Λ j - (xt - torLift_FXC1 Λ j) = D • v by abel,
    map_smul, smul_comm]

include hR hβ2 hβ2s hLp in
/-- **The derivative of the plane coordinate** along the pushforward of `u`:
`dη(dπ u) = R⁻¹ planeL u`. -/
theorem mfderiv_torEta_FXC1 (j : Tor_FXC1 Λ) (xt : E3) (hx : ‖xt - torLift_FXC1 Λ j‖ < 200 * R)
    (u : E3) :
    mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (torEta_FXC1 Λ R j) (torPi_FXC1 Λ xt)
      (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) xt u) = R⁻¹ • planeL_FXC1 u := by
  have hmem := mem_ellDom_of_norm_lt_FXC1 Λ hR hβ2 hβ2s hLp j (y := xt) (by linarith)
  have hell : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (ell_FXC1 Λ (torLift_FXC1 Λ j))
      (torPi_FXC1 Λ xt) :=
    ((contMDiffOn_ell_FXC1 Λ (torLift_FXC1 Λ j)).contMDiffAt
      ((isOpen_image_ellDom_FXC1 Λ (torLift_FXC1 Λ j)).mem_nhds ⟨xt, hmem, rfl⟩)).mdifferentiableAt
      (by simp)
  have hpi : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) xt :=
    ((contMDiff_torPi_FXC1 Λ) xt).mdifferentiableAt (by simp)
  have hev : (ell_FXC1 Λ (torLift_FXC1 Λ j) ∘ torPi_FXC1 Λ) =ᶠ[nhds xt]
      fun z : E3 => planeL_FXC1 (z - torLift_FXC1 Λ j) := by
    filter_upwards [(isOpen_ellDom_FXC1 Λ (torLift_FXC1 Λ j)).mem_nhds hmem] with z hz
    exact ell_torPi_FXC1 Λ hz
  have hcomp := mfderiv_comp xt hell hpi
  have hD : mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (ell_FXC1 Λ (torLift_FXC1 Λ j) ∘ torPi_FXC1 Λ) xt =
      (planeL_FXC1 : E3 →L[ℝ] ℝ²) := by
    rw [hev.mfderiv_eq, mfderiv_eq_fderiv]
    exact ((planeL_FXC1.hasFDerivAt.comp xt
      ((hasFDerivAt_id xt).sub_const (torLift_FXC1 Λ j)))).fderiv
  have hdiff : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (ell_FXC1 Λ (torLift_FXC1 Λ j))
      (torPi_FXC1 Λ xt) := hell
  have hL : MDifferentiableAt 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ²) (fun v : ℝ² => R⁻¹ • v)
      (ell_FXC1 Λ (torLift_FXC1 Λ j) (torPi_FXC1 Λ xt)) :=
    ((contDiff_const_smul R⁻¹ : ContDiff ℝ ∞ fun v : ℝ² => R⁻¹ • v).contMDiff.mdifferentiableAt
      (by simp))
  have hcomp2 := mfderiv_comp (torPi_FXC1 Λ xt) hL hdiff
  have hLd : mfderiv 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ²) (fun v : ℝ² => R⁻¹ • v)
      (ell_FXC1 Λ (torLift_FXC1 Λ j) (torPi_FXC1 Λ xt)) =
      (R⁻¹ • ContinuousLinearMap.id ℝ ℝ² : ℝ² →L[ℝ] ℝ²) := by
    rw [mfderiv_eq_fderiv]
    exact ((hasFDerivAt_id (ell_FXC1 Λ (torLift_FXC1 Λ j) (torPi_FXC1 Λ xt))).const_smul
      R⁻¹).fderiv
  have hη : torEta_FXC1 Λ R j =
      (fun v : ℝ² => R⁻¹ • v) ∘ ell_FXC1 Λ (torLift_FXC1 Λ j) := rfl
  have h1 := DFunLike.congr_fun hcomp u
  rw [hD] at h1
  rw [hη, hcomp2, hLd]
  change R⁻¹ • mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (ell_FXC1 Λ (torLift_FXC1 Λ j)) (torPi_FXC1 Λ xt)
    (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) (torPi_FXC1 Λ) xt u) = R⁻¹ • planeL_FXC1 u
  exact (congrArg (fun a : ℝ² => R⁻¹ • a) h1).symm

end Lines

end DifferentialGeometry.Geometry.Collapse
