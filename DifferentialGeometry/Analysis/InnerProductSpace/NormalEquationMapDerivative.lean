import DifferentialGeometry.Analysis.InnerProductSpace.NormalGraphVariableRemainder
import DifferentialGeometry.Analysis.InnerProductSpace.OrthogonalErrorCoordinates
import Mathlib.Analysis.Calculus.FDeriv.Congr

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace DifferentialGeometry.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem norm_fderiv_tangent_map_sub_projection_le_of_normal_equation
    (L : Submodule ℝ H) [CompleteSpace L] [CompleteSpace Lᗮ]
    (o : H) (g : L → Lᗮ) (T : H → L) (z : H) (R a : ℝ)
    (hR : 0 < R) (ha : a ≤ 1 / 100)
    (hT : DifferentiableAt ℝ T z) (hg : DifferentiableAt ℝ g (T z))
    (hdg : DifferentiableAt ℝ (fderiv ℝ g) (T z))
    (hvalue : ‖g (T z)‖ ≤ a * R) (hfirst : ‖fderiv ℝ g (T z)‖ ≤ a)
    (hsecond : ‖fderiv ℝ (fderiv ℝ g) (T z)‖ ≤ a / R)
    (hvnorm : ‖Lᗮ.orthogonalProjectionOnto (z - o)‖ ≤ R)
    (hequation : ∀ᶠ y in 𝓝 z,
      T y - L.orthogonalProjectionOnto (y - o) +
        (ContinuousLinearMap.adjoint (fderiv ℝ g (T y)))
          (g (T y) - Lᗮ.orthogonalProjectionOnto (y - o)) = 0) :
    ‖fderiv ℝ T z - L.orthogonalProjectionOnto‖ ≤ 5 * a := by
  let u : H → L := fun y => L.orthogonalProjectionOnto (y-o)
  let v : H → Lᗮ := fun y => Lᗮ.orthogonalProjectionOnto (y-o)
  let e : H → L := fun y => (ContinuousLinearMap.adjoint (fderiv ℝ g (T y)))
    (g (T y)-v y)
  let J : (L →L[ℝ] Lᗮ) →L[ℝ] (Lᗮ →L[ℝ] L) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hu : HasFDerivAt u L.orthogonalProjectionOnto z := by
    simpa only [ContinuousLinearMap.comp_id,Function.comp_def] using
      L.orthogonalProjectionOnto.hasFDerivAt.comp (f := fun y : H => y-o) z
        ((hasFDerivAt_id (𝕜 := ℝ) z).sub_const o)
  have hv : HasFDerivAt v Lᗮ.orthogonalProjectionOnto z := by
    simpa only [ContinuousLinearMap.comp_id,Function.comp_def] using
      Lᗮ.orthogonalProjectionOnto.hasFDerivAt.comp (f := fun y : H => y-o) z
        ((hasFDerivAt_id (𝕜 := ℝ) z).sub_const o)
  have he : DifferentiableAt ℝ e z :=
    (J.differentiableAt.comp z (hdg.comp z hT)).clm_apply
      ((hg.comp z hT).sub hv.differentiableAt)
  have heq : (fun y => T y-u y) =ᶠ[𝓝 z] (fun y => -e y) := by
    filter_upwards [hequation] with y hy
    exact eq_neg_of_add_eq_zero_left hy
  have hderiv : fderiv ℝ T z-L.orthogonalProjectionOnto = -fderiv ℝ e z := by
    have hh := heq.fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (T - u) z = fderiv ℝ (-e) z at hh
    rwa [(hT.hasFDerivAt.sub hu).fderiv,he.hasFDerivAt.neg.fderiv] at hh
  have hnorm : ‖fderiv ℝ T z-L.orthogonalProjectionOnto‖ = ‖fderiv ℝ e z‖ := by
    rw [hderiv,norm_neg]
  have ha0 : 0 ≤ a := (norm_nonneg _).trans hfirst
  have hres : ‖g (T z)-v z‖ ≤ (a+1)*R := by
    have hh := (norm_sub_le (g (T z)) (v z)).trans (add_le_add hvalue hvnorm)
    nlinarith
  have hvar := norm_fderiv_variable_normal_graph_remainder_le g T v z hg hdg hT hv.differentiableAt
  rw [hv.fderiv] at hvar
  have hvop : ‖Lᗮ.orthogonalProjectionOnto‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    simpa only [one_mul] using Lᗮ.norm_orthogonalProjectionOnto_apply_le w
  have hscaled : ‖fderiv ℝ e z‖ ≤ a+(a+2*a^2)*‖fderiv ℝ T z‖ := by
    apply hvar.trans
    calc
      _ ≤ a*(a*‖fderiv ℝ T z‖+1)+(a/R)*‖fderiv ℝ T z‖*((a+1)*R) := by
        gcongr
      _ = _ := by field_simp [hR.ne']; ring
  let c : ℝ := ‖fderiv ℝ T z-L.orthogonalProjectionOnto‖
  let q : ℝ := a+2*a^2
  have hc0 : 0 ≤ c := norm_nonneg _
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hDT : ‖fderiv ℝ T z‖ ≤ 1+c := by
    have hh := norm_add_le (fderiv ℝ T z-L.orthogonalProjectionOnto) L.orthogonalProjectionOnto
    have hp : ‖L.orthogonalProjectionOnto‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro w
      simpa only [one_mul] using L.norm_orthogonalProjectionOnto_apply_le w
    rw [sub_add_cancel] at hh
    dsimp [c]
    linarith
  have habsorb : c ≤ a+q*(1+c) := by
    change ‖fderiv ℝ T z-L.orthogonalProjectionOnto‖ ≤ _
    rw [hnorm]
    exact hscaled.trans (add_le_add (le_refl a) (mul_le_mul_of_nonneg_left hDT hq0))
  have haa : a*a ≤ a/100 := by nlinarith [mul_le_mul_of_nonneg_left ha ha0]
  have hqhalf : q ≤ 1/2 := by dsimp [q]; nlinarith
  have hqc : q*c ≤ c/2 := by nlinarith [mul_le_mul_of_nonneg_right hqhalf hc0]
  have hc : c ≤ 2*(a+q) := by nlinarith
  change c ≤ 5*a
  dsimp [q] at hc
  nlinarith

end DifferentialGeometry.Analysis
