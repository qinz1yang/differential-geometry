import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersRim
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereSlimLabels

/-!
# FC39 producer, packet P0 (gate 1): the S³ corner tubes in the handle charts

Part B of the circle kind of the S³ inhabitant, geometry of the saturated tube over a corner chart
target (no junction data needed): a circle point `J((ψ, r), θ)` whose `(ψ, r)` has small slacks
for the corner `(b, b')` is the handle point `χ_b(w, t)` with

* `w = ψ • planeOfCircle θ` (`b = false`) or `(4/ψ) • planeOfCircle (−θ)` (`b = true`), so the
  edge height `‖w‖²` is `slack_ψ + 1` (`circTube_height`);
* `t = handleRadiusParam b s`, `s = r − 1` (`b' = false`) or `2 − 4/r` (`b' = true`), so the handle
  radius is `r` and the edge coordinate is `t + shift` (`circTube_projE`);

and on the whole circle domain the stereographic height is `q₀(r)` (`sphereHeight_circDomain`), so
the residual functions are the `r`-slacks (`residualFn_circDomain`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The handle coordinates of a circle point -/

/-- The handle radius parameter with radius `r`: `r − 1` (side `1`) or `2 − 4/r` (side `4`). -/
def circHandleS : Bool → ℝ → ℝ
  | false, r => r - 1
  | true, r => 2 - 4 / r

/-- The handle disk coordinate of the circle point `(ψ, θ)` on the side `b`. -/
def circHandleW : Bool → ℝ → Circle → E2
  | false, ψ, θ => ψ • planeOfCircle θ
  | true, ψ, θ => (4 / ψ) • planeOfCircle (circleAntipode_CIRCA θ)

theorem abs_sixteen_mul_lt_CIRCC {s : ℝ} (h : |16 * s| < 2) : -(1 / 8) < s ∧ s < 1 / 8 := by
  rw [abs_lt] at h
  constructor <;> linarith [h.1, h.2]

/-- The `r`-slack is small only near the side value: bounds of `r` and of `s`. -/
theorem circHandleS_mem (σ' : Bool) {r : ℝ} (hr : 0 < r) (h : |16 * circSlack true σ' r| < 2) :
    circHandleS σ' r ∈ Ioo (-1 / 2 : ℝ) (3 / 2) ∧ cycleHandleRadius (circHandleS σ' r) = r ∧
      (σ' = false → circHandleS σ' r ≤ 1 / 4) ∧ (σ' = true → 3 / 4 ≤ circHandleS σ' r) := by
  have hb := abs_sixteen_mul_lt_CIRCC h
  have hD : 0 < 5 * (r ^ 2 + 4) := by positivity
  cases σ'
  · simp only [circSlack] at hb
    rw [circHeight_add] at hb
    have h1 := hb.1
    have h2 := hb.2
    rw [lt_div_iff₀ hD] at h1
    rw [div_lt_iff₀ hD] at h2
    have hr1 : r < 5 / 4 := by nlinarith
    have hr2 : 1 / 2 < r := by nlinarith
    simp only [circHandleS]
    refine ⟨⟨by linarith, by linarith⟩, ?_, fun _ => by linarith, fun h => absurd h (by decide)⟩
    rw [cycleHandleRadius_inner (by linarith)]
    ring
  · simp only [circSlack] at hb
    rw [circHeight_sub] at hb
    have h1 := hb.1
    have h2 := hb.2
    rw [lt_div_iff₀ hD] at h1
    rw [div_lt_iff₀ hD] at h2
    have hr1 : 16 / 5 < r := by nlinarith
    have hr2 : r < 6 := by nlinarith
    have hq1 : 4 / r < 5 / 4 := by rw [div_lt_iff₀ hr]; linarith
    have hq2 : 2 / 3 < 4 / r := by rw [lt_div_iff₀ hr]; linarith
    simp only [circHandleS]
    refine ⟨⟨by linarith, by linarith⟩, ?_, fun h => absurd h (by decide), fun _ => by linarith⟩
    rw [cycleHandleRadius_outer (by linarith)]
    field_simp
    ring

theorem circHandleW_norm (b : Bool) {ψ : ℝ} (hψ : 0 < ψ) (θ : Circle) :
    ‖circHandleW b ψ θ‖ = if b then 4 / ψ else ψ := by
  cases b
  · exact norm_smul_planeOfCircle_CIRCA hψ θ
  · exact norm_smul_planeOfCircle_CIRCA (div_pos (by norm_num) hψ) _

/-- The `ψ`-slack is the edge height minus one. -/
theorem circHandleW_norm_sq (b : Bool) {ψ : ℝ} (hψ : 0 < ψ) (θ : Circle) :
    ‖circHandleW b ψ θ‖ ^ 2 = circSlack false b ψ + 1 := by
  rw [circHandleW_norm b hψ]
  cases b
  · simp [circSlack]
  · simp only [↓reduceIte, circSlack]
    rw [div_pow]
    norm_num

theorem circHandleW_mem_ball (b : Bool) {ψ : ℝ} (hψ : 0 < ψ) (θ : Circle)
    (h : |16 * circSlack false b ψ| < 2) : circHandleW b ψ θ ∈ Metric.ball (0 : E2) 2 := by
  have hb := abs_sixteen_mul_lt_CIRCC h
  rw [Metric.mem_ball, dist_zero_right]
  have hsq := circHandleW_norm_sq b hψ θ
  have hn := norm_nonneg (circHandleW b ψ θ)
  nlinarith

/-- The handle chart point of a corner tube point. -/
theorem circTube_mem_edgeBox {b σ' : Bool} {u : ℝ × ℝ} (hu : u ∈ circPlaneTarget b σ')
    (θ : Circle) :
    (circHandleW b u.1 θ, handleRadiusParam b (circHandleS σ' u.2)) ∈ edgeBox :=
  ⟨circHandleW_mem_ball b hu.1 θ hu.2.2.1,
    handleRadiusParam_mem_Ioo b (circHandleS_mem σ' hu.2.1 hu.2.2.2).1⟩

theorem handleRadiusParam_involutive_CIRCC (b : Bool) (s : ℝ) :
    handleRadiusParam b (handleRadiusParam b s) = s := by
  cases b <;> simp [handleRadiusParam]

/-- **A corner tube point is a handle chart point.** -/
theorem sphereCircleChart_eq_handle {b σ' : Bool} {u : ℝ × ℝ} (hu : u ∈ circPlaneTarget b σ')
    (θ : Circle) :
    sphereCircleChart (sphereCircleEquiv.symm u, θ) =
      cycleHandleChart b (circHandleW b u.1 θ, handleRadiusParam b (circHandleS σ' u.2)) := by
  have hr := (circHandleS_mem σ' hu.2.1 hu.2.2.2).2.1
  have hψ : 0 < u.1 := hu.1
  rw [show u = (u.1, u.2) from rfl, sphereCircleChart_equiv_symm, cycleHandleChart_eq_FC39P0]
  dsimp only
  cases b
  · simp only [handleRadiusParam, Bool.cond_false, Bool.false_eq_true, ↓reduceIte, hr]
    rfl
  · simp only [handleRadiusParam, Bool.cond_true, ↓reduceIte, sub_sub_cancel, hr]
    have hs := sphereCircleChart_neg (div_pos (by norm_num : (0 : ℝ) < 4) hψ) u.2
      (circleAntipode_CIRCA θ)
    rw [circleAntipode_antipode_CIRCA] at hs
    rw [show 4 / (4 / u.1) = u.1 by field_simp] at hs
    rw [show circHandleW true u.1 θ = (4 / u.1) • planeOfCircle (circleAntipode_CIRCA θ) from rfl,
      hs, sphereCircleChart_equiv_symm]

/-! ## Circle domain points -/

/-- Every point of the circle domain is the chart image of its base point. -/
theorem circDomain_eq_chart (x : sphereCircleDomain) :
    x.val = sphereCircleChart (sphereCircleEquiv.symm (sphereCircleEquiv (sphereCircleProj x).val),
      (sphereCircleChart.symm x.val).2) := by
  rw [ContinuousLinearEquiv.symm_apply_apply, sphereCircleProj_val]
  exact (sphereCircleChart.right_inv (mem_sphereCircleDomain_iff.1 x.2)).symm

/-- **The stereographic height on the circle domain** is `q₀(r)`. -/
theorem sphereHeight_circDomain (x : sphereCircleDomain) :
    sphereHeight x.val = circHeight (circCoordL true (sphereCircleProj x).val) := by
  have hr := circCoordL_pos true (sphereCircleProj x)
  rw [circDomain_eq_chart x, sphereCircleChart_apply, ContinuousLinearEquiv.apply_symm_apply,
    sphereHeight_ambient_false]
  have hθ : ‖((Handle.stereoChart northPole).symm
      ((sphereCircleEquiv (sphereCircleProj x).val).1 • planeOfCircle
        (sphereCircleChart.symm x.val).2) : E3)‖ = 1 := norm_eq_of_mem_sphere _
  rw [norm_smul, hθ, mul_one,
    show (sphereCircleEquiv (sphereCircleProj x).val).2 = circCoordL true (sphereCircleProj x).val
      from rfl, Real.norm_of_nonneg hr.le]
  rfl

/-- **The residual functions on the circle domain** are the `r`-slacks. -/
theorem residualFn_circDomain (σ' : Bool) (x : sphereCircleDomain) :
    sphereSlimPieces.residualFn (sphereResidual σ') x.val =
      circSlack true σ' (circCoordL true (sphereCircleProj x).val) := by
  cases σ'
  · rw [residualFn_sphereResidual_false]
    change sphereHeight x.val + 3 / 5 = _
    rw [sphereHeight_circDomain]
    rfl
  · rw [residualFn_sphereResidual_true]
    change 3 / 5 - sphereHeight x.val = _
    rw [sphereHeight_circDomain]
    rfl

/-! ## Corner tube points -/

section Tube

variable {b σ' : Bool} {x : sphereCircleDomain}

theorem circTube_eq_handle
    (hx : sphereCircleEquiv (sphereCircleProj x).val ∈ circPlaneTarget b σ') :
    x.val = cycleHandleChart b
      (circHandleW b (circCoordL false (sphereCircleProj x).val) (sphereCircleChart.symm x.val).2,
        handleRadiusParam b (circHandleS σ' (circCoordL true (sphereCircleProj x).val))) :=
  (circDomain_eq_chart x).trans (sphereCircleChart_eq_handle hx _)

theorem circTube_mem_box
    (hx : sphereCircleEquiv (sphereCircleProj x).val ∈ circPlaneTarget b σ') :
    (circHandleW b (circCoordL false (sphereCircleProj x).val) (sphereCircleChart.symm x.val).2,
        handleRadiusParam b (circHandleS σ' (circCoordL true (sphereCircleProj x).val))) ∈
      edgeBox :=
  circTube_mem_edgeBox hx _

/-- A corner tube point lies in the edge source. -/
theorem circTube_mem_edgeSource
    (hx : sphereCircleEquiv (sphereCircleProj x).val ∈ circPlaneTarget b σ') :
    x.val ∈ edgeSource := by
  rw [circTube_eq_handle hx]
  exact chart_mem_edgeSource (circTube_mem_box hx)

/-- **The edge height on a corner tube** is `slack_ψ + 1`. -/
theorem circTube_height
    (hx : sphereCircleEquiv (sphereCircleProj x).val ∈ circPlaneTarget b σ') :
    edgeHeightR x.val = circSlack false b (circCoordL false (sphereCircleProj x).val) + 1 := by
  rw [circTube_eq_handle hx, edgeHeightR_chart (circTube_mem_box hx)]
  exact circHandleW_norm_sq b (circCoordL_pos false _) _

/-- **The edge coordinate on a corner tube** is `handleRadiusParam b s + shift b`. -/
theorem circTube_projE
    (hx : sphereCircleEquiv (sphereCircleProj x).val ∈ circPlaneTarget b σ') :
    edgeProjE x.val = edgeLineEquiv
      (handleRadiusParam b (circHandleS σ' (circCoordL true (sphereCircleProj x).val)) +
        edgeShift b) := by
  rw [circTube_eq_handle hx, edgeProjE_chart (circTube_mem_box hx)]

end Tube

end GC.GraphManifold.Assembly.FC39P0
