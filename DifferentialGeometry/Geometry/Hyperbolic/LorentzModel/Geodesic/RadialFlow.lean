import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.Normal
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Manifold
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Geometry.Manifold.Algebra.Structures

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.AxisGeometry

open Hyperbolic HyperbolicBoundary

variable {n : ℕ}

private theorem contMDiff_upper_val (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, LorVec n) r
      (fun y : HUpper n => y.val) := by
  apply contMDiff_pi_space.mpr
  intro i
  cases i with
  | inl j =>
      have hc : ContDiff ℝ r (fun v : EuclideanSpace ℝ (Fin n) => v j) :=
        (contDiff_apply ℝ ℝ j).comp
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).contDiff
      exact hc.contMDiff.comp
        (Hyperboloid.contMDiff_space.comp (Hyperboloid.hUpperDiffeomorph n r).contMDiff)
  | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact Hyperboloid.contMDiff_time.comp (Hyperboloid.hUpperDiffeomorph n r).contMDiff

section SmoothMaps

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private theorem contMDiff_upper_of_val {r : ℕ∞ω} (f : M → HUpper n)
    (hf : ContMDiff I 𝓘(ℝ, LorVec n) r (fun y => (f y).val)) :
    ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) r f := by
  have hcoords : ContMDiff I 𝓘(ℝ, Fin n → ℝ) r
      (fun y => fun j : Fin n => (f y).val (Sum.inl j)) :=
    contMDiff_pi_space.mpr fun j => contMDiff_pi_space.mp hf (Sum.inl j)
  have hs := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.contDiff.contMDiff.comp hcoords
  have h := (Hyperboloid.hUpperDiffeomorph n r).symm.contMDiff.comp
    (Hyperboloid.contMDiff_ofSpace.comp hs)
  apply h.congr
  intro y
  apply (Hyperboloid.hUpperIsometryEquiv n).injective
  dsimp only [Function.comp_def]
  rw [Hyperboloid.hUpperDiffeomorph_symm_apply, IsometryEquiv.apply_symm_apply]
  apply Hyperboloid.ext
  apply PiLp.ext
  intro j
  exact Hyperboloid.hUpperIsometryEquiv_space_apply n (f y) j

private theorem contMDiff_lorB {r : ℕ∞ω} {f g : M → LorVec n}
    (hf : ContMDiff I 𝓘(ℝ, LorVec n) r f) (hg : ContMDiff I 𝓘(ℝ, LorVec n) r g) :
    ContMDiff I 𝓘(ℝ, ℝ) r (fun y => lorB (f y) (g y)) := by
  unfold lorB sdot tc
  exact (ContMDiff.sum fun j _ =>
    (contMDiff_pi_space.mp hf (Sum.inl j)).mul (contMDiff_pi_space.mp hg (Sum.inl j))).sub
      ((contMDiff_pi_space.mp hf (Sum.inr 0)).mul (contMDiff_pi_space.mp hg (Sum.inr 0)))

private theorem contMDiff_planeProject {r : ℕ∞ω} (ξ η : BoundaryH n) {f : M → LorVec n}
    (hf : ContMDiff I 𝓘(ℝ, LorVec n) r f) :
    ContMDiff I 𝓘(ℝ, LorVec n) r (fun y => planeProject ξ η (f y)) := by
  exact ((contMDiff_lorB hf contMDiff_const).div_const _).smul contMDiff_const |>.add
    (((contMDiff_lorB hf contMDiff_const).div_const _).smul contMDiff_const)

end SmoothMaps

theorem contMDiff_axisRadius (ξ η : BoundaryH n) (hne : ξ ≠ η) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) r (axisRadius ξ η) := by
  have hp := contMDiff_planeProject ξ η (contMDiff_upper_val (n := n) r)
  have h := (contMDiff_lorB hp hp).neg
  intro y
  exact (Real.contDiffAt_sqrt (show -lorB (planeProject ξ η y.val) (planeProject ξ η y.val) ≠ 0 by
    have := one_le_neg_planeProject_norm ξ η hne y
    linarith)).contMDiffAt.comp y (h y)

theorem contMDiff_axisFoot (ξ η : BoundaryH n) (hne : ξ ≠ η) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) r
      (axisFoot ξ η hne) := by
  apply contMDiff_upper_of_val
  exact ((contMDiff_axisRadius ξ η hne r).inv₀ (fun y => (axisRadius_pos ξ η hne y).ne')).smul
    (contMDiff_planeProject ξ η (contMDiff_upper_val r))

theorem dist_axisFoot_eq_arcosh (ξ η : BoundaryH n) (hne : ξ ≠ η) (y : HUpper n) :
    dist y (axisFoot ξ η hne y) = Real.arcosh (axisRadius ξ η y) := by
  rw [← cosh_dist_axisFoot ξ η hne y, Real.arcosh_cosh dist_nonneg]

theorem contMDiffOn_dist_axisFoot (ξ η : BoundaryH n) (hne : ξ ≠ η) (r : ℕ∞ω) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) r
      (fun y : HUpper n => dist y (axisFoot ξ η hne y)) (axis ξ η)ᶜ := by
  have he : (fun y : HUpper n => dist y (axisFoot ξ η hne y)) =
      fun y => Real.arcosh (axisRadius ξ η y) := funext (dist_axisFoot_eq_arcosh ξ η hne)
  rw [he]
  intro y hy
  have hd : 0 < dist y (axisFoot ξ η hne y) := dist_pos.mpr fun h =>
    hy (h.symm ▸ axisFoot_mem ξ η hne y)
  have hR : 1 < axisRadius ξ η y := by
    rw [← cosh_dist_axisFoot ξ η hne y]
    simpa only [Real.cosh_zero] using Real.cosh_strictMonoOn (by norm_num : (0 : ℝ) ∈ Set.Ici 0)
      dist_nonneg hd
  exact ((Real.contDiffAt_arcosh hR).contMDiffAt.comp y
    (contMDiff_axisRadius ξ η hne r y)).contMDiffWithinAt

private def radialScale (ξ η : BoundaryH n) (t : ℝ) (y : HUpper n) : ℝ :=
  Real.sqrt (1 + Real.exp t ^ 2 * (axisRadius ξ η y ^ 2 - 1))

private theorem radialScale_pos (ξ η : BoundaryH n) (hne : ξ ≠ η) (t : ℝ) (y : HUpper n) :
    0 < radialScale ξ η t y := by
  have h : 0 ≤ axisRadius ξ η y ^ 2 - 1 := by nlinarith [one_le_axisRadius ξ η hne y]
  exact Real.sqrt_pos.mpr (by positivity)

private theorem radialScale_sq (ξ η : BoundaryH n) (hne : ξ ≠ η) (t : ℝ) (y : HUpper n) :
    radialScale ξ η t y ^ 2 = 1 + Real.exp t ^ 2 * (axisRadius ξ η y ^ 2 - 1) := by
  have h : 0 ≤ axisRadius ξ η y ^ 2 - 1 := by nlinarith [one_le_axisRadius ξ η hne y]
  exact Real.sq_sqrt (by positivity)

private theorem normalPart_norm (ξ η : BoundaryH n) (hne : ξ ≠ η) (y : HUpper n) :
    lorB (y.val - planeProject ξ η y.val) (y.val - planeProject ξ η y.val) =
      axisRadius ξ η y ^ 2 - 1 := by
  rw [normal_norm_eq ξ η hne y, axisRadius_sq ξ η hne y]

private def radialFlowVec (ξ η : BoundaryH n) (hne : ξ ≠ η) (t : ℝ) (y : HUpper n) : LorVec n :=
  radialScale ξ η t y • (axisFoot ξ η hne y).val +
    Real.exp t • (y.val - planeProject ξ η y.val)

private theorem radialFlowVec_unit (ξ η : BoundaryH n) (hne : ξ ≠ η) (t : ℝ) (y : HUpper n) :
    lorB (radialFlowVec ξ η hne t y) (radialFlowVec ξ η hne t y) = -1 := by
  have ho := normal_orthogonal ξ η hne y.val _ (axisFoot_mem ξ η hne y)
  have ho' : lorB (axisFoot ξ η hne y).val (y.val - planeProject ξ η y.val) = 0 := by
    rw [lorB_comm]
    exact ho
  simp only [radialFlowVec, lorB_add_left, lorB_add_right, lorB_smul_left,
    lorB_smul_right, (axisFoot ξ η hne y).is_unit, ho, ho', mul_zero, zero_add, add_zero,
    normalPart_norm ξ η hne y]
  nlinarith only [radialScale_sq ξ η hne t y]

private theorem radialFlowVec_future (ξ η : BoundaryH n) (hne : ξ ≠ η) (t : ℝ) (y : HUpper n) :
    0 < tc (radialFlowVec ξ η hne t y) := by
  have ho := normal_orthogonal ξ η hne y.val _ (axisFoot_mem ξ η hne y)
  have hp : lorB (axisFoot ξ η hne y).val (radialFlowVec ξ η hne t y) < 0 := by
    simp only [radialFlowVec, lorB_add_right, lorB_smul_right, (axisFoot ξ η hne y).is_unit]
    rw [lorB_comm (axisFoot ξ η hne y).val, ho]
    simpa only [mul_neg_one, mul_zero, add_zero] using neg_neg_of_pos (radialScale_pos ξ η hne t y)
  exact (HyperbolicAction.tc_pos_iff_tc_pos_of_lorB_neg
    (axisFoot ξ η hne y).is_unit (radialFlowVec_unit ξ η hne t y) hp).mp
      (axisFoot ξ η hne y).future

def axisRadialFlow (ξ η : BoundaryH n) (hne : ξ ≠ η) (t : ℝ) (y : HUpper n) : HUpper n where
  val := radialFlowVec ξ η hne t y
  is_unit := radialFlowVec_unit ξ η hne t y
  future := radialFlowVec_future ξ η hne t y

theorem axisRadialFlow_val (ξ η : BoundaryH n) (hne : ξ ≠ η) (t : ℝ) (y : HUpper n) :
    (axisRadialFlow ξ η hne t y).val =
      Real.sqrt (1 + Real.exp t ^ 2 * (axisRadius ξ η y ^ 2 - 1)) • (axisFoot ξ η hne y).val +
        Real.exp t • (y.val - planeProject ξ η y.val) := rfl

private theorem planeProject_add (ξ η : BoundaryH n) (v w : LorVec n) :
    planeProject ξ η (v + w) = planeProject ξ η v + planeProject ξ η w := by
  simp only [planeProject, lorB_add_left, add_div, add_smul]
  abel

private theorem planeProject_smul (ξ η : BoundaryH n) (c : ℝ) (v : LorVec n) :
    planeProject ξ η (c • v) = c • planeProject ξ η v := by
  simp only [planeProject, lorB_smul_left, mul_div_assoc, smul_add, smul_smul]

private theorem planeProject_sub (ξ η : BoundaryH n) (v w : LorVec n) :
    planeProject ξ η (v - w) = planeProject ξ η v - planeProject ξ η w := by
  simp only [planeProject, lorB_sub_left, sub_div, sub_smul]
  abel

private theorem planeProject_idempotent (ξ η : BoundaryH n) (hne : ξ ≠ η) (v : LorVec n) :
    planeProject ξ η (planeProject ξ η v) = planeProject ξ η v := by
  change (lorB (planeProject ξ η v) η.val / lorB ξ.val η.val) • ξ.val +
    (lorB (planeProject ξ η v) ξ.val / lorB ξ.val η.val) • η.val = _
  rw [planeProject_pair_right ξ η hne, planeProject_pair_left ξ η hne]
  rfl

private theorem planeProject_radialFlow (ξ η : BoundaryH n) (hne : ξ ≠ η) (t : ℝ) (y : HUpper n) :
    planeProject ξ η (axisRadialFlow ξ η hne t y).val =
      radialScale ξ η t y • (axisFoot ξ η hne y).val := by
  change planeProject ξ η (radialFlowVec ξ η hne t y) = _
  rw [radialFlowVec, planeProject_add, planeProject_smul, planeProject_smul,
    planeProject_eq_self ξ η hne (axisFoot_mem ξ η hne y), planeProject_sub,
    planeProject_idempotent ξ η hne, sub_self, smul_zero, add_zero]

private theorem axisRadius_radialFlow (ξ η : BoundaryH n) (hne : ξ ≠ η) (t : ℝ) (y : HUpper n) :
    axisRadius ξ η (axisRadialFlow ξ η hne t y) = radialScale ξ η t y := by
  rw [axisRadius, planeProject_radialFlow, lorB_smul_left, lorB_smul_right,
    (axisFoot ξ η hne y).is_unit]
  convert Real.sqrt_sq (radialScale_pos ξ η hne t y).le using 1
  congr 1
  ring

theorem axisFoot_axisRadialFlow (ξ η : BoundaryH n) (hne : ξ ≠ η) (t : ℝ) (y : HUpper n) :
    axisFoot ξ η hne (axisRadialFlow ξ η hne t y) = axisFoot ξ η hne y := by
  apply HUpper.ext
  change (axisRadius ξ η (axisRadialFlow ξ η hne t y))⁻¹ •
    planeProject ξ η (axisRadialFlow ξ η hne t y).val = _
  rw [axisRadius_radialFlow, planeProject_radialFlow, smul_smul,
    inv_mul_cancel₀ (radialScale_pos ξ η hne t y).ne', one_smul]

theorem axisRadius_axisRadialFlow (ξ η : BoundaryH n) (hne : ξ ≠ η) (t : ℝ) (y : HUpper n) :
    axisRadius ξ η (axisRadialFlow ξ η hne t y) =
      Real.sqrt (1 + Real.exp t ^ 2 * (axisRadius ξ η y ^ 2 - 1)) :=
  axisRadius_radialFlow ξ η hne t y

private theorem radialScale_zero (ξ η : BoundaryH n) (hne : ξ ≠ η) (y : HUpper n) :
    radialScale ξ η 0 y = axisRadius ξ η y := by
  simp only [radialScale, Real.exp_zero, one_pow, one_mul]
  rw [show 1 + (axisRadius ξ η y ^ 2 - 1) = axisRadius ξ η y ^ 2 by ring]
  exact Real.sqrt_sq (axisRadius_pos ξ η hne y).le

theorem axisRadialFlow_zero (ξ η : BoundaryH n) (hne : ξ ≠ η) (y : HUpper n) :
    axisRadialFlow ξ η hne 0 y = y := by
  apply HUpper.ext
  change radialScale ξ η 0 y • (axisFoot ξ η hne y).val +
    Real.exp 0 • (y.val - planeProject ξ η y.val) = y.val
  rw [radialScale_zero ξ η hne, Real.exp_zero, one_smul,
    ← planeProject_eq_radius_smul_foot ξ η hne y]
  abel

private theorem normalPart_radialFlow (ξ η : BoundaryH n) (hne : ξ ≠ η) (t : ℝ) (y : HUpper n) :
    (axisRadialFlow ξ η hne t y).val - planeProject ξ η (axisRadialFlow ξ η hne t y).val =
      Real.exp t • (y.val - planeProject ξ η y.val) := by
  rw [planeProject_radialFlow]
  change (radialScale ξ η t y • (axisFoot ξ η hne y).val +
    Real.exp t • (y.val - planeProject ξ η y.val)) - _ = _
  abel

private theorem radialScale_comp (ξ η : BoundaryH n) (hne : ξ ≠ η) (s t : ℝ) (y : HUpper n) :
    radialScale ξ η s (axisRadialFlow ξ η hne t y) = radialScale ξ η (s + t) y := by
  unfold radialScale
  rw [axisRadius_radialFlow, radialScale_sq ξ η hne, Real.exp_add]
  congr 1
  ring

theorem axisRadialFlow_add (ξ η : BoundaryH n) (hne : ξ ≠ η) (s t : ℝ) (y : HUpper n) :
    axisRadialFlow ξ η hne s (axisRadialFlow ξ η hne t y) = axisRadialFlow ξ η hne (s + t) y := by
  apply HUpper.ext
  change radialScale ξ η s (axisRadialFlow ξ η hne t y) •
      (axisFoot ξ η hne (axisRadialFlow ξ η hne t y)).val +
      Real.exp s • ((axisRadialFlow ξ η hne t y).val -
        planeProject ξ η (axisRadialFlow ξ η hne t y).val) =
      radialScale ξ η (s + t) y • (axisFoot ξ η hne y).val +
        Real.exp (s + t) • (y.val - planeProject ξ η y.val)
  rw [radialScale_comp ξ η hne, axisFoot_axisRadialFlow, normalPart_radialFlow,
    smul_smul, Real.exp_add]

theorem axisRadialFlow_eq_self_of_mem_axis (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (t : ℝ) {y : HUpper n} (hy : y ∈ axis ξ η) : axisRadialFlow ξ η hne t y = y := by
  have hR : axisRadius ξ η y = 1 := by
    rw [← cosh_dist_axisFoot ξ η hne y, axisFoot_eq_self ξ η hne hy, dist_self, Real.cosh_zero]
  apply HUpper.ext
  rw [axisRadialFlow_val, hR, axisFoot_eq_self ξ η hne hy, planeProject_eq_self ξ η hne hy]
  simp

theorem axisRadialFlow_mem_axis_iff (ξ η : BoundaryH n) (hne : ξ ≠ η) (t : ℝ) (y : HUpper n) :
    axisRadialFlow ξ η hne t y ∈ axis ξ η ↔ y ∈ axis ξ η := by
  constructor
  · intro hy
    have h := axisRadialFlow_eq_self_of_mem_axis ξ η hne (-t) hy
    rw [axisRadialFlow_add, neg_add_cancel, axisRadialFlow_zero] at h
    exact h.symm ▸ hy
  · intro hy
    rw [axisRadialFlow_eq_self_of_mem_axis ξ η hne t hy]
    exact hy

theorem contMDiff_axisRadialFlow (ξ η : BoundaryH n) (hne : ξ ≠ η) (r : ℕ∞ω) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) r (fun z : ℝ × HUpper n => axisRadialFlow ξ η hne z.1 z.2) := by
  apply contMDiff_upper_of_val
  have hR := (contMDiff_axisRadius ξ η hne r).comp
    (contMDiff_snd (M := ℝ) (N := HUpper n) (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
  have he := (Real.contDiff_exp (n := r)).contMDiff.comp
    (contMDiff_fst (M := ℝ) (N := HUpper n) (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
  have harg := (contMDiff_const (c := (1 : ℝ))).add
    ((he.pow 2).mul ((hR.pow 2).sub (contMDiff_const (c := (1 : ℝ)))))
  have hb : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, ℝ) r
      (fun z : ℝ × HUpper n => radialScale ξ η z.1 z.2) := by
    intro z
    have hnn : 0 ≤ axisRadius ξ η z.2 ^ 2 - 1 := by nlinarith [one_le_axisRadius ξ η hne z.2]
    exact (Real.contDiffAt_sqrt (show (1 + Real.exp z.1 ^ 2 * (axisRadius ξ η z.2 ^ 2 - 1) : ℝ) ≠ 0 by
      positivity)).contMDiffAt.comp z (harg z)
  have hv := (contMDiff_upper_val (n := n) r).comp
    (contMDiff_snd (M := ℝ) (N := HUpper n) (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
  have hp := (contMDiff_upper_val r).comp ((contMDiff_axisFoot ξ η hne r).comp
    (contMDiff_snd (M := ℝ) (N := HUpper n) (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))))
  exact (hb.smul hp).add (he.smul (hv.sub (contMDiff_planeProject ξ η hv)))

theorem sinh_dist_axisFoot_axisRadialFlow (ξ η : BoundaryH n) (hne : ξ ≠ η) (t : ℝ) (y : HUpper n) :
    Real.sinh (dist (axisRadialFlow ξ η hne t y) (axisFoot ξ η hne (axisRadialFlow ξ η hne t y))) =
      Real.exp t * Real.sinh (dist y (axisFoot ξ η hne y)) := by
  have h1 := Real.cosh_sq_sub_sinh_sq
    (dist (axisRadialFlow ξ η hne t y) (axisFoot ξ η hne (axisRadialFlow ξ η hne t y)))
  have h2 := Real.cosh_sq_sub_sinh_sq (dist y (axisFoot ξ η hne y))
  rw [cosh_dist_axisFoot, axisRadius_radialFlow] at h1
  rw [cosh_dist_axisFoot] at h2
  have hsq := radialScale_sq ξ η hne t y
  have hp := Real.sinh_nonneg_iff.mpr
    (show 0 ≤ dist (axisRadialFlow ξ η hne t y) (axisFoot ξ η hne (axisRadialFlow ξ η hne t y)) from dist_nonneg)
  have hq := Real.sinh_nonneg_iff.mpr (show 0 ≤ dist y (axisFoot ξ η hne y) from dist_nonneg)
  apply (sq_eq_sq₀ hp (mul_nonneg (Real.exp_pos t).le hq)).mp
  nlinarith only [h1, h2, hsq]

theorem log_sinh_dist_axisFoot_axisRadialFlow (ξ η : BoundaryH n) (hne : ξ ≠ η) (t : ℝ)
    {y : HUpper n} (hy : y ∉ axis ξ η) :
    Real.log (Real.sinh (dist (axisRadialFlow ξ η hne t y)
      (axisFoot ξ η hne (axisRadialFlow ξ η hne t y)))) =
        Real.log (Real.sinh (dist y (axisFoot ξ η hne y))) + t := by
  have hd : 0 < dist y (axisFoot ξ η hne y) := dist_pos.mpr fun h =>
    hy (h.symm ▸ axisFoot_mem ξ η hne y)
  rw [sinh_dist_axisFoot_axisRadialFlow, Real.log_mul (Real.exp_ne_zero t)
    (Real.sinh_pos_iff.mpr hd).ne', Real.log_exp, add_comm]

private theorem po_smul_linear_combination (m : ℕ) (g : ProjectiveOrthogonalGroup.PO (m + 1) 1)
    (x y z : HUpper (m + 1)) (a b : ℝ) (hz : z.val = a • x.val + b • y.val) :
    ((HyperbolicAction.poMulAction (by omega : 1 ≤ m + 1)).smul g z).val =
      a • ((HyperbolicAction.poMulAction (by omega : 1 ≤ m + 1)).smul g x).val +
        b • ((HyperbolicAction.poMulAction (by omega : 1 ≤ m + 1)).smul g y).val := by
  let J := Hyperboloid.hUpperIsometryEquiv (m + 1)
  let e := (Hyperboloid.projectiveOrthogonalGroupEquiv m).symm g
  have hraw : ((J z).time, (J z).space) =
      a • ((J x).time, (J x).space) + b • ((J y).time, (J y).space) := by
    apply Prod.ext
    · exact congrFun hz (Sum.inr 0)
    · apply PiLp.ext
      intro i
      exact congrFun hz (Sum.inl i)
  have hlin := congrArg (Hyperboloid.lorentzExtension e) hraw
  rw [map_add, map_smul, map_smul, Hyperboloid.lorentzExtension_apply,
    Hyperboloid.lorentzExtension_apply, Hyperboloid.lorentzExtension_apply] at hlin
  have hact (w : HUpper (m + 1)) : e (J w) =
      J ((HyperbolicAction.poMulAction (by omega : 1 ≤ m + 1)).smul g w) :=
    Hyperboloid.projectiveOrthogonalGroupEquiv_symm_apply m g w
  rw [hact z, hact x, hact y] at hlin
  funext i
  cases i with
  | inl j => exact congrArg (fun w : ℝ × EuclideanSpace ℝ (Fin (m + 1)) => w.2 j) hlin
  | inr j =>
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact congrArg Prod.fst hlin

private theorem radialFlow_decomposition (ξ η : BoundaryH n) (hne : ξ ≠ η) (t : ℝ) (y : HUpper n) :
    (axisRadialFlow ξ η hne t y).val =
      Real.exp t • y.val +
        (radialScale ξ η t y - Real.exp t * axisRadius ξ η y) • (axisFoot ξ η hne y).val := by
  change radialScale ξ η t y • (axisFoot ξ η hne y).val +
    Real.exp t • (y.val - planeProject ξ η y.val) = _
  rw [planeProject_eq_radius_smul_foot ξ η hne y, smul_sub, smul_smul, sub_smul]
  abel

theorem axisRadialFlow_smul (hn : 1 ≤ n) (g : ProjectiveOrthogonalGroup.PO n 1)
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hpair : (poBoundaryMulAction hn).smul g ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g η ∈ ({ξ, η} : Set (BoundaryH n))) (t : ℝ) (y : HUpper n) :
    axisRadialFlow ξ η hne t ((HyperbolicAction.poMulAction hn).smul g y) =
      (HyperbolicAction.poMulAction hn).smul g (axisRadialFlow ξ η hne t y) := by
  cases n with
  | zero => omega
  | succ m =>
      have hR : axisRadius ξ η ((HyperbolicAction.poMulAction hn).smul g y) = axisRadius ξ η y := by
        rw [← cosh_dist_axisFoot ξ η hne, dist_axisFoot_smul hn g ξ η hne hpair,
          cosh_dist_axisFoot]
      have hb : radialScale ξ η t ((HyperbolicAction.poMulAction hn).smul g y) =
          radialScale ξ η t y := by rw [radialScale, hR]; rfl
      have hlin := po_smul_linear_combination m g y (axisFoot ξ η hne y)
        (axisRadialFlow ξ η hne t y) (Real.exp t)
        (radialScale ξ η t y - Real.exp t * axisRadius ξ η y)
        (radialFlow_decomposition ξ η hne t y)
      apply HUpper.ext
      rw [radialFlow_decomposition, hR, hb, axisFoot_smul hn g ξ η hne hpair]
      exact hlin.symm

theorem axisRadialFlow_eq_normal_geod (ξ η : BoundaryH n) (hne : ξ ≠ η) (t : ℝ)
    (y : HUpper n) (hy : axisFoot ξ η hne y ≠ y) :
    axisRadialFlow ξ η hne t y =
      HyperbolicConvexity.geodFromTo (axisFoot ξ η hne y) y hy
        (dist (axisRadialFlow ξ η hne t y) (axisFoot ξ η hne y)) := by
  have hc : Real.cosh (dist (axisRadialFlow ξ η hne t y) (axisFoot ξ η hne y)) =
      radialScale ξ η t y := by
    rw [← axisFoot_axisRadialFlow ξ η hne t y, cosh_dist_axisFoot, axisRadius_radialFlow]
  have hs := sinh_dist_axisFoot_axisRadialFlow ξ η hne t y
  rw [axisFoot_axisRadialFlow] at hs
  have hd : Real.sinh (dist (axisFoot ξ η hne y) y) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (dist_pos.mpr hy)).ne'
  apply HUpper.ext
  change radialScale ξ η t y • (axisFoot ξ η hne y).val +
      Real.exp t • (y.val - planeProject ξ η y.val) =
      Real.cosh (dist (axisRadialFlow ξ η hne t y) (axisFoot ξ η hne y)) • (axisFoot ξ η hne y).val +
        Real.sinh (dist (axisRadialFlow ξ η hne t y) (axisFoot ξ η hne y)) •
          HyperbolicConvexity.dirVec (axisFoot ξ η hne y) y
  rw [hc, hs, HyperbolicConvexity.dirVec,
    dist_comm y (axisFoot ξ η hne y), smul_smul]
  rw [show (Real.exp t * Real.sinh (dist (axisFoot ξ η hne y) y)) *
      (Real.sinh (dist (axisFoot ξ η hne y) y))⁻¹ = Real.exp t by
      rw [mul_assoc, mul_inv_cancel₀ hd, mul_one]]
  congr 3
  rw [dist_comm (axisFoot ξ η hne y) y, cosh_dist_axisFoot,
    ← planeProject_eq_radius_smul_foot ξ η hne y]

end DifferentialGeometry.AxisGeometry
