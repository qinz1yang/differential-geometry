import DifferentialGeometry.Analysis.InnerProductSpace.NormalGraphRemainder

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Analysis

variable {E F Z : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem norm_fderiv_variable_normal_graph_remainder_le
    (g : E → F) (u : Z → E) (v : Z → F) (x : Z)
    (hg : DifferentiableAt ℝ g (u x))
    (hdg : DifferentiableAt ℝ (fderiv ℝ g) (u x))
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    ‖fderiv ℝ (fun z => (ContinuousLinearMap.adjoint (fderiv ℝ g (u z)))
      (g (u z)-v z)) x‖ ≤
      ‖fderiv ℝ g (u x)‖ *
        (‖fderiv ℝ g (u x)‖ * ‖fderiv ℝ u x‖ + ‖fderiv ℝ v x‖) +
      ‖fderiv ℝ (fderiv ℝ g) (u x)‖ * ‖fderiv ℝ u x‖ * ‖g (u x)-v x‖ := by
  let J : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hJnorm (A : E →L[ℝ] F) : ‖J A‖ = ‖A‖ :=
    ContinuousLinearMap.adjoint.norm_map A
  have hc := (J.hasFDerivAt.comp x (hdg.hasFDerivAt.comp x hu.hasFDerivAt)).clm_apply
    ((hg.hasFDerivAt.comp x hu.hasFDerivAt).sub hv.hasFDerivAt)
  change ‖fderiv ℝ (fun z =>
    (((J : (E →L[ℝ] F) → F →L[ℝ] E) ∘ (fderiv ℝ g ∘ u)) z)
      ((g ∘ u - v) z)) x‖ ≤ _
  rw [hc.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  change ‖J (fderiv ℝ g (u x))
      ((fderiv ℝ g (u x)) ((fderiv ℝ u x) w)-(fderiv ℝ v x) w) +
    J ((fderiv ℝ (fderiv ℝ g) (u x)) ((fderiv ℝ u x) w)) (g (u x)-v x)‖ ≤ _
  have huapply := (fderiv ℝ u x).le_opNorm w
  have hres : ‖(fderiv ℝ g (u x)) ((fderiv ℝ u x) w)-(fderiv ℝ v x) w‖ ≤
      (‖fderiv ℝ g (u x)‖ * ‖fderiv ℝ u x‖ + ‖fderiv ℝ v x‖)*‖w‖ := by
    calc
      _ ≤ ‖(fderiv ℝ g (u x)) ((fderiv ℝ u x) w)‖ + ‖(fderiv ℝ v x) w‖ := norm_sub_le _ _
      _ ≤ ‖fderiv ℝ g (u x)‖ * (‖fderiv ℝ u x‖ * ‖w‖) + ‖fderiv ℝ v x‖ * ‖w‖ := by
        apply add_le_add _ ((fderiv ℝ v x).le_opNorm w)
        exact ((fderiv ℝ g (u x)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left huapply (norm_nonneg _))
      _ = _ := by ring
  have hfirst : ‖J (fderiv ℝ g (u x))
      ((fderiv ℝ g (u x)) ((fderiv ℝ u x) w)-(fderiv ℝ v x) w)‖ ≤
      (‖fderiv ℝ g (u x)‖ *
        (‖fderiv ℝ g (u x)‖ * ‖fderiv ℝ u x‖ + ‖fderiv ℝ v x‖))*‖w‖ := by
    calc
      _ ≤ ‖J (fderiv ℝ g (u x))‖ *
          ‖(fderiv ℝ g (u x)) ((fderiv ℝ u x) w)-(fderiv ℝ v x) w‖ :=
        (J (fderiv ℝ g (u x))).le_opNorm _
      _ ≤ ‖fderiv ℝ g (u x)‖ *
          ((‖fderiv ℝ g (u x)‖ * ‖fderiv ℝ u x‖ + ‖fderiv ℝ v x‖)*‖w‖) := by
        rw [hJnorm]
        exact mul_le_mul_of_nonneg_left hres (norm_nonneg _)
      _ = _ := by ring
  have hsecond : ‖J ((fderiv ℝ (fderiv ℝ g) (u x)) ((fderiv ℝ u x) w)) (g (u x)-v x)‖ ≤
      (‖fderiv ℝ (fderiv ℝ g) (u x)‖ * ‖fderiv ℝ u x‖ * ‖g (u x)-v x‖)*‖w‖ := by
    calc
      _ ≤ ‖J ((fderiv ℝ (fderiv ℝ g) (u x)) ((fderiv ℝ u x) w))‖ * ‖g (u x)-v x‖ :=
        (J ((fderiv ℝ (fderiv ℝ g) (u x)) ((fderiv ℝ u x) w))).le_opNorm _
      _ ≤ (‖fderiv ℝ (fderiv ℝ g) (u x)‖ * (‖fderiv ℝ u x‖ * ‖w‖))*‖g (u x)-v x‖ := by
        rw [hJnorm]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact ((fderiv ℝ (fderiv ℝ g) (u x)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left huapply (norm_nonneg _))
      _ = _ := by ring
  exact (norm_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq (by ring))

end DifferentialGeometry.Analysis
