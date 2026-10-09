/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.FixtureSolidTorusBasic
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PrimitiveCurveJordan
import DifferentialGeometry.Topology.PiecewiseLinear.CircleHomotopy

set_option autoImplicit false

/-!
# Fixture FX2 (main): meridian, spanning disk, Loop Theorem and primitivity on the solid torus
-/

noncomputable section
open Set Topology
open DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff

namespace GC.LongTime.CuspP1
open GC.Endpoint

/-! ### Boundary map and meridian -/

theorem σ0_mem_FX2 (x : Torus) : σ_FX2 (((), x), 0) ∈ W_FX2 := by
  change cliffordHeight (σ_FX2 (((), x), 0)) ≤ 0
  rw [cliffordHeight_σ_FX2 (by rw [σ_FX2_source]; simp)]; simp

theorem continuous_σ0_FX2 : Continuous fun x : Torus => σ_FX2 (((), x), 0) :=
  σ_FX2.continuousOn.comp_continuous (by fun_prop) (fun x => by
    rw [σ_FX2_source]; simp)

/-- The boundary torus (Clifford torus) as a map into `W`. -/
def φ_FX2 : C(Torus, ↥W_FX2) :=
  ⟨fun x => ⟨σ_FX2 (((), x), 0), σ0_mem_FX2 x⟩, continuous_σ0_FX2.subtype_mk _⟩

theorem φ_FX2_apply (x : Torus) :
    (φ_FX2 x : M_FX2) = σ_FX2 (((), x), 0) := rfl

/-- The meridian `γ(θ) = (e^{2πiθ}, 1)`. -/
def γ_FX2 : freeLoop Torus :=
  ⟨fun θ => (AddCircle.toCircle θ, 1), by fun_prop⟩

theorem γ_FX2_apply (θ : loopCircle) : γ_FX2 θ = (AddCircle.toCircle θ, 1) := rfl

/-! ### The spanning disk `u(z) = (z, 1)` -/

/-- Normalising constant. -/
def cc_FX2 (z : ℂ) : ℝ := Real.sqrt (1 / (1 + ‖z‖ ^ 2))

theorem cc_FX2_sq (z : ℂ) : cc_FX2 z ^ 2 = 1 / (1 + ‖z‖ ^ 2) := by
  have : (0 : ℝ) ≤ 1 / (1 + ‖z‖ ^ 2) := by positivity
  exact Real.sq_sqrt this

theorem norm_cc_FX2 (z : ℂ) : ‖(cc_FX2 z • z : ℂ)‖ ^ 2 + ‖(cc_FX2 z • (1 : ℂ))‖ ^ 2 = 1 := by
  rw [norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, sq_abs, cc_FX2_sq, norm_one]
  field_simp
  ring

/-- `z ↦ (z, 1)/‖(z,1)‖ ∈ S³`. -/
def U_FX2 (z : ℂ) : M_FX2 := sphereOfPair (cc_FX2 z • z) (cc_FX2 z • (1 : ℂ)) (norm_cc_FX2 z)

theorem contDiff_cc_FX2 : ContDiff ℝ ∞ cc_FX2 := by
  unfold cc_FX2
  refine ContDiff.sqrt (contDiff_const.div (contDiff_const.add (contDiff_norm_sq ℝ))
    (fun z => by positivity)) (fun z => by positivity)

theorem contMDiff_U_FX2 : ContMDiff 𝓘(ℝ, ℂ) (𝓡 3) ∞ U_FX2 := by
  rw [← contMDiffOn_univ]
  refine contMDiffOn_of_sphereFirst_sphereSecond isOpen_univ ?_ ?_
  · simp only [U_FX2, sphereFirst_sphereOfPair]
    exact (contDiff_cc_FX2.smul contDiff_id).contMDiff.contMDiffOn
  · simp only [U_FX2, sphereSecond_sphereOfPair]
    exact (contDiff_cc_FX2.smul contDiff_const).contMDiff.contMDiffOn

theorem cliffordHeight_U_FX2 (z : ℂ) : cliffordHeight (U_FX2 z) = cc_FX2 z ^ 2 * (‖z‖ ^ 2 - 1) := by
  rw [cliffordHeight]
  simp only [U_FX2, sphereFirst_sphereOfPair, sphereSecond_sphereOfPair, norm_smul, norm_one,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- The disk `u(z) = (z, 1)` in `S³`. -/
def u_FX2 : C(closedDisk, M_FX2) :=
  ⟨fun z => U_FX2 z.1, contMDiff_U_FX2.continuous.comp continuous_subtype_val⟩

theorem u_FX2_mem_W (z : closedDisk) : u_FX2 z ∈ W_FX2 := by
  change cliffordHeight (U_FX2 z.1) ≤ 0
  rw [cliffordHeight_U_FX2]
  have hz : ‖z.1‖ ≤ 1 := by
    have := z.2
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have : ‖z.1‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z.1]
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)

/-- The disk as a map into `W`. -/
def uW_FX2 : C(closedDisk, ↥W_FX2) := ⟨fun z => ⟨u_FX2 z, u_FX2_mem_W z⟩, by fun_prop⟩

theorem range_u_FX2_subset : range u_FX2 ⊆ W_FX2 := by
  rintro _ ⟨z, rfl⟩; exact u_FX2_mem_W z

/-- Interior of the disk lies in the interior of `W`. -/
theorem u_FX2_interior (z : closedDisk) (hz : ‖z.1‖ < 1) : u_FX2 z ∈ interior W_FX2 := by
  have hlt : cliffordHeight (u_FX2 z) < 0 := by
    change cliffordHeight (U_FX2 z.1) < 0
    rw [cliffordHeight_U_FX2]
    have hc : 0 < cc_FX2 z.1 ^ 2 := by rw [cc_FX2_sq]; positivity
    have : ‖z.1‖ ^ 2 < 1 := by nlinarith [norm_nonneg z.1]
    exact mul_neg_of_pos_of_neg hc (by linarith)
  exact interior_maximal (fun q hq => le_of_lt hq)
    (isOpen_lt contMDiff_cliffordHeight.continuous continuous_const) hlt

/-- Exact boundary trace: `u ∘ ∂ = φ ∘ γ` in `M`, pointwise. -/
theorem u_boundary_FX2 (θ : loopCircle) :
    u_FX2 (diskBoundary θ) = (φ_FX2 (γ_FX2 θ) : M_FX2) := by
  have hn : ‖(AddCircle.toCircle θ : ℂ)‖ = 1 := Circle.norm_coe _
  have hc : cc_FX2 (AddCircle.toCircle θ : ℂ) = seamFirst 0 := by
    rw [cc_FX2, hn, seamFirst, seamClamp_of_mem (by norm_num) (by norm_num)]
    norm_num
  have hs : seamSecond 0 = seamFirst 0 := by
    rw [seamSecond, seamFirst, seamClamp_of_mem (by norm_num) (by norm_num)]; norm_num
  have h1 : u_FX2 (diskBoundary θ) = sphereOfPair (seamFirst 0 • (AddCircle.toCircle θ : ℂ))
      (seamSecond 0 • ((1 : Circle) : ℂ)) (norm_seam_sq 0 _ _) := by
    apply sphere_ext
    · change sphereFirst (U_FX2 (AddCircle.toCircle θ : ℂ)) = _
      simp only [U_FX2, sphereFirst_sphereOfPair, hc]
    · change sphereSecond (U_FX2 (AddCircle.toCircle θ : ℂ)) = _
      simp only [U_FX2, sphereSecond_sphereOfPair, hc, hs, Circle.coe_one]
  rw [h1]
  change _ = cliffordSeamMap (((AddCircle.toCircle θ, (1 : Circle)) : Torus), -(0 : ℝ))
  rw [neg_zero]
  rfl

end GC.LongTime.CuspP1
