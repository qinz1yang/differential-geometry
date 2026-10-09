import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Connection
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian
import DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def nullHeight (ξ : E) (x : Hyperboloid E) : ℝ :=
  x.time - inner ℝ ξ x.space

private def nullSlope (ξ w : E) (x : Hyperboloid E) : ℝ :=
  inner ℝ w x.space / x.time - inner ℝ ξ w

private theorem nullHeight_pos (ξ : Metric.sphere (0 : E) 1) (x : Hyperboloid E) :
    0 < nullHeight (ξ : E) x := by
  have hξ : ‖(ξ : E)‖ = 1 := norm_eq_of_mem_sphere ξ
  have hi : inner ℝ (ξ : E) x.space ≤ ‖x.space‖ := by
    simpa only [hξ, one_mul] using real_inner_le_norm (ξ : E) x.space
  have ht : ‖x.space‖ < x.time := by
    nlinarith [x.time_sq, x.time_pos, norm_nonneg x.space]
  exact sub_pos.mpr (hi.trans_lt ht)

private theorem hasFDerivAt_time_ofSpace (x : Hyperboloid E) :
    HasFDerivAt (fun y : E => (ofSpace y).time)
      (x.time⁻¹ • innerSL ℝ x.space) x.space := by
  have hd : HasFDerivAt (fun y : E => 1 + ‖y‖ ^ 2) (2 • innerSL ℝ x.space) x.space := by
    simpa only [zero_add] using!
      (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x.space).add
        (hasStrictFDerivAt_norm_sq x.space).hasFDerivAt
  have hf := hd.sqrt (show (1 + ‖x.space‖ ^ 2 : ℝ) ≠ 0 by positivity)
  have he : (1 / (2 * Real.sqrt (1 + ‖x.space‖ ^ 2))) • (2 • innerSL ℝ x.space) =
      x.time⁻¹ • innerSL ℝ x.space := by
    rw [← x.time_eq_sqrt]
    ext w
    simp only [smul_apply, two_smul, add_apply, smul_eq_mul]
    field_simp
    ring
  exact he ▸ hf

private theorem hasFDerivAt_nullHeight (ξ : E) (x : Hyperboloid E) :
    HasFDerivAt (fun y : E => nullHeight ξ (ofSpace y))
      (x.time⁻¹ • innerSL ℝ x.space - innerSL ℝ ξ) x.space :=
  (hasFDerivAt_time_ofSpace x).sub (innerSL ℝ ξ).hasFDerivAt

private theorem contMDiff_nullHeight (ξ : E) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (nullHeight ξ) :=
  contMDiff_time.sub ((innerSL ℝ ξ).contDiff.contMDiff.comp contMDiff_space)

private theorem contMDiff_log_nullHeight (ξ : Metric.sphere (0 : E) 1) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => Real.log (nullHeight (ξ : E) x)) := by
  intro x
  exact (Real.contDiffAt_log.mpr (nullHeight_pos ξ x).ne').contMDiffAt.comp x
    (contMDiff_nullHeight (ξ : E)).contMDiffAt

private theorem mvfderiv_comp_space (F : E → ℝ) (x : Hyperboloid E) (v : E)
    (hF : DifferentiableAt ℝ F x.space) :
    mvfderiv 𝓘(ℝ, E) (fun y : Hyperboloid E => F y.space) x (spaceVectorField v x) =
      fderiv ℝ F x.space v := by
  change mvfderiv 𝓘(ℝ, E) (fun y : Hyperboloid E => F (spaceDiffeomorph y)) x
    (spaceVectorField v x) = _
  rw [mvfderiv_comp_diffeomorph F spaceDiffeomorph x (spaceVectorField v x)
    hF.mdifferentiableAt, mvfderiv_model_apply_eq_fderiv, mfderiv_spaceDiffeomorph]
  rfl

private theorem mvfderiv_log_nullHeight_spaceVectorField
    (ξ : Metric.sphere (0 : E) 1) (x : Hyperboloid E) (v : E) :
    mvfderiv 𝓘(ℝ, E) (fun y => Real.log (nullHeight (ξ : E) y)) x
      (spaceVectorField v x) = nullSlope (ξ : E) v x / nullHeight (ξ : E) x := by
  have hd := (hasFDerivAt_nullHeight (ξ : E) x).log (by simpa only [ofSpace_space] using (nullHeight_pos ξ x).ne')
  have he : (fun y : Hyperboloid E => Real.log (nullHeight (ξ : E) y)) =
      fun y : Hyperboloid E => Real.log (nullHeight (ξ : E) (ofSpace y.space)) := by
    simp only [ofSpace_space]
  rw [he, mvfderiv_comp_space _ x v hd.differentiableAt, hd.fderiv]
  simp only [smul_apply, sub_apply, ofSpace_space,
    innerSL_apply_apply, smul_eq_mul, nullSlope, inv_mul_eq_div]
  rw [real_inner_comm x.space v]

private theorem mvfderiv_nullSlope_div_nullHeight
    (ξ : Metric.sphere (0 : E) 1) (x : Hyperboloid E) (v w : E) :
    mvfderiv 𝓘(ℝ, E) (fun y => nullSlope (ξ : E) w y / nullHeight (ξ : E) y) x
      (spaceVectorField v x) =
        (inner ℝ v w - inner ℝ x.space v * inner ℝ x.space w / x.time ^ 2) /
          (x.time * nullHeight (ξ : E) x) -
        nullSlope (ξ : E) v x * nullSlope (ξ : E) w x / nullHeight (ξ : E) x ^ 2 := by
  have ht := hasFDerivAt_time_ofSpace x
  have hw : HasFDerivAt (innerSL ℝ w) (innerSL ℝ w) x.space :=
    (innerSL ℝ w).hasFDerivAt
  have hti := (hasFDerivAt_inv
    (show (ofSpace x.space).time ≠ 0 by simpa only [ofSpace_space] using x.time_pos.ne')).comp x.space ht
  have hs := (hw.mul hti).sub_const (inner ℝ (ξ : E) w)
  have hh := hasFDerivAt_nullHeight (ξ : E) x
  have hhi := (hasFDerivAt_inv
    (show nullHeight (ξ : E) (ofSpace x.space) ≠ 0 by
      simpa only [ofSpace_space] using (nullHeight_pos ξ x).ne')).comp x.space hh
  have hf := hs.mul hhi
  have hF : (fun y : E => nullSlope (ξ : E) w (ofSpace y) /
      nullHeight (ξ : E) (ofSpace y)) =
      (fun y : E => ((innerSL ℝ w) y * ((fun a : ℝ => a⁻¹) ∘
        (fun z : E => (ofSpace z).time)) y - inner ℝ (ξ : E) w) *
          ((fun a : ℝ => a⁻¹) ∘ (fun z : E => nullHeight (ξ : E) (ofSpace z))) y) := by
    simp only [nullSlope, space_ofSpace, div_eq_mul_inv, innerSL_apply_apply, Function.comp_def]
  change HasFDerivAt (fun y : E => ((innerSL ℝ w) y * ((fun a : ℝ => a⁻¹) ∘
      (fun z : E => (ofSpace z).time)) y - inner ℝ (ξ : E) w) *
        ((fun a : ℝ => a⁻¹) ∘ (fun z : E => nullHeight (ξ : E) (ofSpace z))) y) _ x.space at hf
  rw [← hF] at hf
  have he : (fun y : Hyperboloid E => nullSlope (ξ : E) w y / nullHeight (ξ : E) y) =
      fun y : Hyperboloid E => nullSlope (ξ : E) w (ofSpace y.space) /
        nullHeight (ξ : E) (ofSpace y.space) := by simp only [ofSpace_space]
  rw [he, mvfderiv_comp_space _ x v hf.differentiableAt, hf.fderiv]
  simp only [smul_apply, sub_apply, ofSpace_space, innerSL_apply_apply, smul_eq_mul,
    nullSlope, ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    Function.comp_apply, Pi.mul_apply, add_apply, smul_eq_mul]
  rw [real_inner_comm w x.space, real_inner_comm w v, real_inner_comm v x.space]
  field_simp [x.time_pos.ne', (nullHeight_pos ξ x).ne']
  ring

theorem contMDiff_log_time_sub_inner (ξ : Metric.sphere (0 : E) 1) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (fun x : Hyperboloid E => Real.log (x.time - inner ℝ (ξ : E) x.space)) :=
  contMDiff_log_nullHeight ξ

private theorem mvfderiv_mul_log_time_sub_inner
    (c : ℝ) (ξ : Metric.sphere (0 : E) 1) (x : Hyperboloid E)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    mvfderiv 𝓘(ℝ, E) (fun y => c * Real.log (y.time - inner ℝ (ξ : E) y.space)) x v =
      c * mvfderiv 𝓘(ℝ, E) (fun y => Real.log (y.time - inner ℝ (ξ : E) y.space)) x v := by
  have hf := (contMDiff_log_time_sub_inner ξ).mdifferentiableAt (x := x) (by simp)
  simpa only [mvfderiv_const, smul_zero, add_zero, smul_apply, smul_eq_mul] using
    congrArg (fun L : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ => L v)
      (mvfderiv_fun_mul (mdifferentiableAt_const (I := 𝓘(ℝ, E)) (c := c)) hf)

variable [FiniteDimensional ℝ E]

private theorem cov_spaceVectorField_eq (x : Hyperboloid E) (v w : E) :
    (Geometry.Connection.LeviCivita riemannianMetric).toFun (spaceVectorField w) x
      (spaceVectorField v x) =
        spaceVectorField (-(riemannianMetric.inner x (spaceVectorField v x)
          (spaceVectorField w x)) • x.space) x := by
  have h := leviCivita_tangentConstAt x (spaceVectorField v x) (spaceVectorField w x)
  rw [tangentConstAt_spaceVectorField, mfderiv_spaceDiffeomorph] at h
  exact h

omit [FiniteDimensional ℝ E] in
private theorem riemannianMetric_inner_spaceVectorField
    (x : Hyperboloid E) (v w : E) :
    riemannianMetric.inner x (spaceVectorField v x) (spaceVectorField w x) =
      inner ℝ v w - inner ℝ x.space v * inner ℝ x.space w / x.time ^ 2 := by
  rw [riemannianMetric_inner, mfderiv_spaceDiffeomorph, x.time_sq]
  rfl

private theorem hessFun_log_nullHeight_spaceVectorField
    (ξ : Metric.sphere (0 : E) 1) (x : Hyperboloid E) (v w : E) :
    Geometry.Operator.hessFun riemannianMetric (fun y => Real.log (nullHeight (ξ : E) y)) x
      (spaceVectorField v x) (spaceVectorField w x) =
        riemannianMetric.inner x (spaceVectorField v x) (spaceVectorField w x) -
          (nullSlope (ξ : E) v x / nullHeight (ξ : E) x) *
            (nullSlope (ξ : E) w x / nullHeight (ξ : E) x) := by
  let : T2Space (Hyperboloid E) := (spaceHomeomorph (E := E)).isEmbedding.t2Space
  have hf := contMDiff_log_nullHeight ξ
  rw [Geometry.Connection.hessFun_eq_abstract riemannianMetric hf]
  have hθ := (Geometry.Connection.cotangentCov_mvfderiv_smooth hf x).mdifferentiableAt
    (by simp)
  have hp := Geometry.Connection.cotangentCov_dualPairing
    (Geometry.Connection.LeviCivita riemannianMetric) hθ
    (mdifferentiableAt_spaceVectorField x w) (spaceVectorField v x)
  have he : (fun y : Hyperboloid E =>
      mvfderiv 𝓘(ℝ, E) (fun z => Real.log (nullHeight (ξ : E) z)) y (spaceVectorField w y)) =
      fun y => nullSlope (ξ : E) w y / nullHeight (ξ : E) y := by
    funext y
    exact mvfderiv_log_nullHeight_spaceVectorField ξ y w
  rw [he, mvfderiv_nullSlope_div_nullHeight, cov_spaceVectorField_eq,
    mvfderiv_log_nullHeight_spaceVectorField] at hp
  change _ = Geometry.Connection.abstractHessian _ _ x (spaceVectorField v x)
    (spaceVectorField w x) + _ at hp
  rw [riemannianMetric_inner_spaceVectorField] at hp ⊢
  rw [show nullSlope (ξ : E)
      (-(inner ℝ v w - inner ℝ x.space v * inner ℝ x.space w / x.time ^ 2) • x.space) x =
      -(inner ℝ v w - inner ℝ x.space v * inner ℝ x.space w / x.time ^ 2) *
        nullSlope (ξ : E) x.space x by
      simp only [nullSlope, real_inner_smul_left, real_inner_smul_right]
      ring] at hp
  have hs : nullSlope (ξ : E) x.space x = nullHeight (ξ : E) x - x.time⁻¹ := by
    dsimp only [nullSlope, nullHeight]
    have ht := x.time_sq_sub_inner_self
    field_simp [x.time_pos.ne']
    nlinarith
  rw [hs] at hp
  apply (eq_sub_iff_add_eq.mpr hp.symm).trans
  field_simp [x.time_pos.ne', (nullHeight_pos ξ x).ne']
  ring

theorem hessFun_log_time_sub_inner (ξ : Metric.sphere (0 : E) 1) (x : Hyperboloid E)
    (v w : TangentSpace 𝓘(ℝ, E) x) :
    Geometry.Operator.hessFun riemannianMetric
      (fun y => Real.log (y.time - inner ℝ (ξ : E) y.space)) x v w =
        riemannianMetric.inner x v w -
          mvfderiv 𝓘(ℝ, E) (fun y => Real.log (y.time - inner ℝ (ξ : E) y.space)) x v *
            mvfderiv 𝓘(ℝ, E) (fun y => Real.log (y.time - inner ℝ (ξ : E) y.space)) x w := by
  let e := tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x
  have hv : spaceVectorField (e v) x = v := e.symm_apply_apply v
  have hw : spaceVectorField (e w) x = w := e.symm_apply_apply w
  have h := hessFun_log_nullHeight_spaceVectorField ξ x (e v) (e w)
  rw [← mvfderiv_log_nullHeight_spaceVectorField ξ x (e v),
    ← mvfderiv_log_nullHeight_spaceVectorField ξ x (e w), hv, hw] at h
  exact h

omit [FiniteDimensional ℝ E] in
private theorem nullGradient_pair (ξ : Metric.sphere (0 : E) 1) (x : Hyperboloid E) (v : E) :
    riemannianMetric.inner x
      (spaceVectorField (x.space - (nullHeight (ξ : E) x)⁻¹ • (ξ : E)) x)
      (spaceVectorField v x) = nullSlope (ξ : E) v x / nullHeight (ξ : E) x := by
  rw [riemannianMetric_inner_spaceVectorField]
  simp only [inner_sub_left, real_inner_smul_left, inner_sub_right, real_inner_smul_right]
  have hx : inner ℝ x.space x.space = x.time ^ 2 - 1 := by
    linarith [x.time_sq_sub_inner_self]
  rw [hx, real_inner_comm (ξ : E) x.space]
  dsimp only [nullSlope, nullHeight]
  rw [real_inner_comm v x.space]
  field_simp [x.time_pos.ne', (show x.time - inner ℝ (ξ : E) x.space ≠ 0 from (nullHeight_pos ξ x).ne')]
  ring

omit [FiniteDimensional ℝ E] in
private theorem nullGradient_unit (ξ : Metric.sphere (0 : E) 1) (x : Hyperboloid E) :
    riemannianMetric.inner x
      (spaceVectorField (x.space - (nullHeight (ξ : E) x)⁻¹ • (ξ : E)) x)
      (spaceVectorField (x.space - (nullHeight (ξ : E) x)⁻¹ • (ξ : E)) x) = 1 := by
  rw [nullGradient_pair]
  have hx : inner ℝ x.space x.space = x.time ^ 2 - 1 := by
    linarith [x.time_sq_sub_inner_self]
  have hξ : inner ℝ (ξ : E) (ξ : E) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere ξ]
    norm_num
  dsimp only [nullSlope]
  rw [inner_sub_left, real_inner_smul_left, inner_sub_right, real_inner_smul_right, hx, hξ]
  dsimp only [nullHeight]
  field_simp [x.time_pos.ne', (show x.time - inner ℝ (ξ : E) x.space ≠ 0 from (nullHeight_pos ξ x).ne')]
  ring

omit [FiniteDimensional ℝ E] in
theorem sq_mvfderiv_log_time_sub_inner_le (ξ : Metric.sphere (0 : E) 1)
    (x : Hyperboloid E) (v : TangentSpace 𝓘(ℝ, E) x) :
    (mvfderiv 𝓘(ℝ, E) (fun y => Real.log (y.time - inner ℝ (ξ : E) y.space)) x v) ^ 2 ≤
      riemannianMetric.inner x v v := by
  let e := tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x
  have hv : spaceVectorField (e v) x = v := e.symm_apply_apply v
  let W := spaceVectorField (x.space - (nullHeight (ξ : E) x)⁻¹ • (ξ : E)) x
  let a := mvfderiv 𝓘(ℝ, E) (fun y => Real.log (nullHeight (ξ : E) y)) x v
  have hW : riemannianMetric.inner x W W = 1 := nullGradient_unit ξ x
  have hWv : riemannianMetric.inner x W v = a := by
    rw [← hv, nullGradient_pair, ← mvfderiv_log_nullHeight_spaceVectorField]
    rw [hv]
  have hvW : riemannianMetric.inner x v W = a := (riemannianMetric.symm x v W).trans hWv
  have hnonneg : 0 ≤ riemannianMetric.inner x (v - a • W) (v - a • W) := by
    rcases eq_or_ne (v - a • W) 0 with h | h
    · simp only [h, map_zero, le_refl]
    · exact (riemannianMetric.pos x _ h).le
  simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul, hW, hWv, hvW] at hnonneg
  change a ^ 2 ≤ _
  nlinarith

theorem hessFun_mul_log_time_sub_inner_scaleMetric
    (c : ℝ) (hc : 0 < c) (ξ : Metric.sphere (0 : E) 1) (x : Hyperboloid E)
    (v w : TangentSpace 𝓘(ℝ, E) x) :
    Geometry.Operator.hessFun (scaleMetric (c ^ 2) (sq_pos_of_pos hc) riemannianMetric)
      (fun y => c * Real.log (y.time - inner ℝ (ξ : E) y.space)) x v w =
        c⁻¹ * ((scaleMetric (c ^ 2) (sq_pos_of_pos hc) riemannianMetric).inner x v w -
          mvfderiv 𝓘(ℝ, E) (fun y => c * Real.log (y.time - inner ℝ (ξ : E) y.space)) x v *
            mvfderiv 𝓘(ℝ, E) (fun y => c * Real.log (y.time - inner ℝ (ξ : E) y.space)) x w) := by
  let : T2Space (Hyperboloid E) := (spaceHomeomorph (E := E)).isEmbedding.t2Space
  have hf := contMDiff_log_time_sub_inner ξ
  have he : Geometry.Operator.hessFun
      (scaleMetric (c ^ 2) (sq_pos_of_pos hc) riemannianMetric)
      (fun y => Real.log (y.time - inner ℝ (ξ : E) y.space)) x v w =
      Geometry.Operator.hessFun riemannianMetric
        (fun y => Real.log (y.time - inner ℝ (ξ : E) y.space)) x v w := by
    rw [Geometry.Connection.hessFun_eq_abstract _ hf,
      Geometry.Connection.hessFun_eq_abstract _ hf]
    simp only [Geometry.Connection.abstractHessian, Geometry.Connection.LeviCivita,
      Geometry.Connection.lcConn_scaleMetric]
  change Geometry.Operator.hessFun
    (scaleMetric (c ^ 2) (sq_pos_of_pos hc) riemannianMetric)
    (c • (fun y => Real.log (y.time - inner ℝ (ξ : E) y.space))) x v w = _
  rw [Geometry.Operator.hessFun_smul]
  change c * Geometry.Operator.hessFun
    (scaleMetric (c ^ 2) (sq_pos_of_pos hc) riemannianMetric)
    (fun y => Real.log (y.time - inner ℝ (ξ : E) y.space)) x v w = _
  rw [he, hessFun_log_time_sub_inner,
    mvfderiv_mul_log_time_sub_inner, mvfderiv_mul_log_time_sub_inner]
  let d := mvfderiv 𝓘(ℝ, E) (fun y => Real.log (y.time - inner ℝ (ξ : E) y.space)) x
  change c * (riemannianMetric.inner x v w - d v * d w) =
    c⁻¹ * (c ^ 2 * riemannianMetric.inner x v w - (c * d v) * (c * d w))
  field_simp [hc.ne']

omit [FiniteDimensional ℝ E] in
theorem sq_mvfderiv_mul_log_time_sub_inner_le_scaleMetric
    (c : ℝ) (hc : 0 < c) (ξ : Metric.sphere (0 : E) 1) (x : Hyperboloid E)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    (mvfderiv 𝓘(ℝ, E) (fun y => c * Real.log (y.time - inner ℝ (ξ : E) y.space)) x v) ^ 2 ≤
      (scaleMetric (c ^ 2) (sq_pos_of_pos hc) riemannianMetric).inner x v v := by
  rw [mvfderiv_mul_log_time_sub_inner, mul_pow]
  exact mul_le_mul_of_nonneg_left (sq_mvfderiv_log_time_sub_inner_le ξ x v) (sq_nonneg c)

end DifferentialGeometry.Hyperboloid
