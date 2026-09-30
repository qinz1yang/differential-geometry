import DifferentialGeometry.Geometry.Metric.RoundPolarAlgebra
import DifferentialGeometry.Geometry.Exponential.NormalBall.Metric
import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.LocalInverse
import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.FixedBasePartialDiffeomorph
import DifferentialGeometry.Geometry.Exponential.Smoothness.AtZero.IntrinsicDerivative
import DifferentialGeometry.Geometry.Metric.Sphere.Round.BasisPoints
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Intrinsic
import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Bundle.FiberBundleHausdorff

noncomputable section

open Bundle Set DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Bundle Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Geometry.Riemannian

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev Sphere3 := Metric.sphere (0 : E4) 1

private local instance ambientDimension : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩
private local instance modelDimension : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private local instance roundBundleInstance :
    RiemannianBundle (fun x : Sphere3 => TangentSpace (𝓡 3) x) := roundBundle

private local instance roundContinuousInstance :
    IsContinuousRiemannianBundle E3 (fun x : Sphere3 => TangentSpace (𝓡 3) x) :=
  ⟨roundMetric.inner, roundMetric.contMDiff.continuous, fun _ _ _ => rfl⟩

private local instance roundPseudo : PseudoEMetricSpace Sphere3 :=
  PseudoEMetricSpace.ofRiemannianMetric (𝓡 3) Sphere3

private local instance roundRiemannianInstance : IsRiemannianManifold (𝓡 3) Sphere3 :=
  ⟨fun _ _ => rfl⟩

private local instance roundCompleteInstance :
    @CompleteSpace Sphere3 (@PseudoEMetricSpace.toUniformSpace _ roundPseudo) :=
  @complete_of_compact Sphere3 (@PseudoEMetricSpace.toUniformSpace _ roundPseudo) inferInstance

private theorem round_metric_norm :
    DifferentialGeometry.Geometry.Riemannian.IsMetricNorm
      (roundMetric (E := E4) (n := 3)) := round_enorm

private def normalizedFrame (p : Sphere3) : E3 ≃L[ℝ] E3 :=
  ((LinearEquiv.smulOfNeZero ℝ E3 (Real.sqrt 2)⁻¹
      (inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num)))).toContinuousLinearEquiv).trans
    (normalFrame (roundMetric (E := E4) (n := 3)) p)

private theorem normalizedFrame_apply (p : Sphere3) (x : E3) :
    normalizedFrame p x =
      (Real.sqrt 2)⁻¹ • normalFrame (roundMetric (E := E4) (n := 3)) p x := by
  change normalFrame (roundMetric (E := E4) (n := 3)) p ((Real.sqrt 2)⁻¹ • x) = _
  exact map_smul _ _ _

def roundNormalMap (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (x : EuclideanSpace ℝ (Fin 3)) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  expMapIntrinsic (roundMetric (E := E4) (n := 3)) round_metric_norm p
    (normalizedFrame p x)

theorem roundNormalMap_smooth (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (roundNormalMap p) :=
  (intrinsicFiber_smooth (roundMetric (E := E4) (n := 3)) round_metric_norm p).comp
    (normalizedFrame p).toContinuousLinearMap.contMDiff

@[simp] theorem roundNormalMap_zero
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) : roundNormalMap p 0 = p := by
  unfold roundNormalMap
  rw [map_zero]
  exact expMapIntrinsic_zero _ round_metric_norm p

theorem roundNormalMap_mfderiv_zero
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (v : EuclideanSpace ℝ (Fin 3)) :
    mfderiv (𝓡 3) (𝓡 3) (roundNormalMap p) 0 v =
      (Real.sqrt 2)⁻¹ • normalFrame (roundMetric (E := EuclideanSpace ℝ (Fin 4))
        (n := 3)) p v := by
  let F : E3 → Sphere3 := fun x =>
    expMapIntrinsic (roundMetric (E := E4) (n := 3)) round_metric_norm p x
  let L : E3 →L[ℝ] E3 := (normalizedFrame p).toContinuousLinearMap
  have hF : MDifferentiableAt (𝓡 3) (𝓡 3) F (L 0) := by
    rw [map_zero]
    exact (intrinsicFiber_smooth (roundMetric (E := E4) (n := 3))
      round_metric_norm p).contMDiffAt.mdifferentiableAt (by decide)
  have hLs : ContMDiff (𝓡 3) (𝓡 3) ∞ L := L.contMDiff
  have hL : MDifferentiableAt (𝓡 3) (𝓡 3) L 0 :=
    hLs.contMDiffAt.mdifferentiableAt (by decide)
  have hc := mfderiv_comp (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3) 0 hF hL
  have hFd : mfderiv (𝓡 3) (𝓡 3) F (L 0) = ContinuousLinearMap.id ℝ E3 := by
    rw [map_zero]
    exact mfderiv_expMapIntrinsic_at_zero _ round_metric_norm p
  have hLd : mfderiv (𝓡 3) (𝓡 3) L 0 = L := by
    exact L.mfderiv_eq
  rw [hFd, hLd] at hc
  have hv : mfderiv (𝓡 3) (𝓡 3) (roundNormalMap p) 0 v = normalizedFrame p v := by
    with_unfolding_all exact congrArg (fun D : E3 →L[ℝ] E3 => D v) hc
  exact hv.trans (normalizedFrame_apply p v)

theorem roundNormalMap_val
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (x : EuclideanSpace ℝ (Fin 3)) :
    (roundNormalMap p x : EuclideanSpace ℝ (Fin 4)) =
      Real.cos (‖x‖ / Real.sqrt 2) • (p : EuclideanSpace ℝ (Fin 4)) +
        (Real.sin (‖x‖ / Real.sqrt 2) / ‖x‖) •
          dIncl (n := 3) p (normalFrame (roundMetric (E := EuclideanSpace ℝ (Fin 4))
            (n := 3)) p x) := by
  by_cases hx : x = 0
  · subst x
    simp
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hnorm : ‖dIncl (n := 3) p (normalFrame (roundMetric (E := E4) (n := 3)) p x)‖ =
      ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← real_inner_self_eq_norm_sq, ← roundMetric_inner, normalFrame_inner,
      real_inner_self_eq_norm_sq]
  let u : TangentSpace (𝓡 3) p :=
    ‖x‖⁻¹ • normalFrame (roundMetric (E := E4) (n := 3)) p x
  have hu : ‖dIncl (n := 3) p u‖ = 1 := by
    simp only [u, map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, hnorm,
      inv_mul_cancel₀ hr]
  have hmul : (‖x‖ / Real.sqrt 2) * ‖x‖⁻¹ = (Real.sqrt 2)⁻¹ := by
    field_simp
  have hinput : normalizedFrame p x = (‖x‖ / Real.sqrt 2) • u := by
    rw [normalizedFrame_apply]
    simp only [u, smul_smul, hmul]
    rfl
  unfold roundNormalMap
  rw [hinput, round_exp_val round_metric_norm p u hu]
  simp only [u, map_smul, smul_smul, div_eq_mul_inv]

section AmbientCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

private theorem norm_hasFDerivAt {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hr)
  convert h using 1
  · simp only [Real.sqrt_sq (norm_nonneg _)]
  · rw [Real.sqrt_sq (norm_nonneg _)]
    ext z
    simp [smul_eq_mul]
    ring

private def roundExpression (p : F) (K : E →L[ℝ] F) (y : E) : F :=
  Real.cos (‖y‖ / Real.sqrt 2) • p +
    (Real.sin (‖y‖ / Real.sqrt 2) / ‖y‖) • K y

private theorem roundExpression_fderiv (p : F) (K : E →L[ℝ] F) {x : E} (hx : x ≠ 0) (v : E) :
    fderiv ℝ (roundExpression p K) x v =
      (-(Real.sin (‖x‖ / Real.sqrt 2)) * (⟪x, v⟫_ℝ / ‖x‖ / Real.sqrt 2)) • p +
      ((Real.cos (‖x‖ / Real.sqrt 2) * (⟪x, v⟫_ℝ / ‖x‖ / Real.sqrt 2) * ‖x‖ -
        Real.sin (‖x‖ / Real.sqrt 2) * (⟪x, v⟫_ℝ / ‖x‖)) / ‖x‖ ^ 2) • K x +
      (Real.sin (‖x‖ / Real.sqrt 2) / ‖x‖) • K v := by
  have hn := norm_hasFDerivAt hx
  have hangle : HasFDerivAt (fun y : E => ‖y‖ / Real.sqrt 2)
      ((Real.sqrt 2)⁻¹ • (‖x‖⁻¹ • innerSL ℝ x)) x := by
    simpa only [div_eq_mul_inv] using hn.mul_const (Real.sqrt 2)⁻¹
  have hcos := hangle.cos.smul_const p
  have hinv := (hasDerivAt_inv (norm_ne_zero_iff.mpr hx)).comp_hasFDerivAt x hn
  have hratio := hangle.sin.mul hinv
  have hprod := hratio.smul K.hasFDerivAt
  have hd := hcos.add hprod
  have happ := congrArg (fun D : E →L[ℝ] F => D v) hd.fderiv
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, innerSL_apply_apply, Pi.mul_apply, Function.comp_apply, smul_eq_mul] at happ
  change fderiv ℝ (roundExpression p K) x v = _ at happ
  rw [happ]
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hb :
      (Real.sin (‖x‖ / Real.sqrt 2) * (-(‖x‖ ^ 2)⁻¹ * (‖x‖⁻¹ * ⟪x, v⟫_ℝ)) +
        ‖x‖⁻¹ * (Real.cos (‖x‖ / Real.sqrt 2) * ((Real.sqrt 2)⁻¹ * (‖x‖⁻¹ * ⟪x, v⟫_ℝ)))) =
      ((Real.cos (‖x‖ / Real.sqrt 2) * (⟪x, v⟫_ℝ / ‖x‖ / Real.sqrt 2) * ‖x‖ -
        Real.sin (‖x‖ / Real.sqrt 2) * (⟪x, v⟫_ℝ / ‖x‖)) / ‖x‖ ^ 2) := by
    field_simp [hr]
    ring
  rw [hb]
  simp only [div_eq_mul_inv]
  module

end AmbientCalculus

private def normalAmbientFrame (p : Sphere3) : E3 →ₗᵢ[ℝ] E4 where
  toLinearMap := (dIncl (n := 3) p).toLinearMap.comp
    (normalFrame (roundMetric (E := E4) (n := 3)) p).toLinearEquiv.toLinearMap
  norm_map' x := by
    change ‖dIncl (n := 3) p (normalFrame (roundMetric (E := E4) (n := 3)) p x)‖ = ‖x‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← real_inner_self_eq_norm_sq, ← roundMetric_inner, normalFrame_inner,
      real_inner_self_eq_norm_sq]

private theorem roundNormalMap_ambient_eq (p : Sphere3) :
    (fun x => (roundNormalMap p x : E4)) =
      roundExpression (p : E4) (normalAmbientFrame p).toContinuousLinearMap := by
  funext x
  exact roundNormalMap_val p x

theorem roundNormalMap_fderiv
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) (v : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun y => (roundNormalMap p y : EuclideanSpace ℝ (Fin 4))) x v =
      (-(Real.sin (‖x‖ / Real.sqrt 2)) * (⟪x, v⟫_ℝ / ‖x‖ / Real.sqrt 2)) •
        (p : EuclideanSpace ℝ (Fin 4)) +
      ((Real.cos (‖x‖ / Real.sqrt 2) * (⟪x, v⟫_ℝ / ‖x‖ / Real.sqrt 2) * ‖x‖ -
        Real.sin (‖x‖ / Real.sqrt 2) * (⟪x, v⟫_ℝ / ‖x‖)) / ‖x‖ ^ 2) •
          dIncl (n := 3) p (normalFrame (roundMetric (E := EuclideanSpace ℝ (Fin 4))
            (n := 3)) p x) +
      (Real.sin (‖x‖ / Real.sqrt 2) / ‖x‖) •
        dIncl (n := 3) p (normalFrame (roundMetric (E := EuclideanSpace ℝ (Fin 4))
          (n := 3)) p v) := by
  rw [roundNormalMap_ambient_eq]
  exact roundExpression_fderiv (p : E4) (normalAmbientFrame p).toContinuousLinearMap hx v

private def precompLinear (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Sphere3 ∞)
    (L : E3 ≃L[ℝ] E3) : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Sphere3 ∞ where
  toFun := fun z => Φ (L z)
  invFun := fun q => L.symm (Φ.symm q)
  source := L ⁻¹' Φ.source
  target := Φ.target
  map_source' := fun _ hz => Φ.map_source hz
  map_target' := by
    intro q hq
    change L (L.symm (Φ.symm q)) ∈ Φ.source
    rw [L.apply_symm_apply]
    exact Φ.map_target hq
  left_inv' := fun z hz =>
    (congrArg L.symm (Φ.left_inv hz)).trans (L.symm_apply_apply z)
  right_inv' := by
    intro q hq
    rw [L.apply_symm_apply]
    exact Φ.right_inv hq
  open_source := Φ.open_source.preimage L.continuous
  open_target := Φ.open_target
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.comp
    L.toContinuousLinearMap.contMDiff.contMDiffOn (fun _ hz => hz)
  contMDiffOn_invFun :=
    L.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn Φ.contMDiffOn_invFun

def roundNormalDiffeomorph
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞ :=
  precompLinear (standardDiagonalInverseBranch (roundMetric (E := E4) (n := 3)) round_metric_norm p).fixedBasePartialDiffeomorph
    (normalizedFrame p)

theorem roundNormalDiffeomorph_apply (p : Sphere3) (x : E3) :
    roundNormalDiffeomorph p x = roundNormalMap p x := rfl

private theorem roundNormalDiffeomorph_zero_mem (p : Sphere3) :
    (0 : E3) ∈ (roundNormalDiffeomorph p).source := by
  change normalizedFrame p 0 ∈
    (standardDiagonalInverseBranch (roundMetric (E := E4) (n := 3)) round_metric_norm p).fixedBasePartialDiffeomorph.source
  rw [map_zero]
  exact DiagonalInverseBranch.fixedBasePartialDiffeomorph_zero_mem_source _

private def roundNormalChart (p : Sphere3) : NormalBallChart (I := 𝓡 3) p := by
  let Φ := roundNormalDiffeomorph p
  have hex := Metric.isOpen_iff.mp Φ.open_source 0 (roundNormalDiffeomorph_zero_mem p)
  let r := hex.choose
  have hr : 0 < r := hex.choose_spec.1
  have hsub : Metric.ball 0 r ⊆ Φ.source := hex.choose_spec.2
  exact NormalBallChart.ofHigher hr Φ hsub (roundNormalMap_zero p)

private theorem roundNormalChart_apply (p : Sphere3) :
    (roundNormalChart p).hom = roundNormalMap p := rfl

def roundNormalRadius (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) : ℝ :=
  (roundNormalChart p).radius / 4

theorem roundNormalRadius_pos (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    0 < roundNormalRadius p := div_pos (roundNormalChart p).radius_pos (by norm_num)

theorem ball_subset_roundNormalDiffeomorph_source
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (roundNormalRadius p) ⊆
      (roundNormalDiffeomorph p).source := by
  intro x hx
  apply (roundNormalChart p).ball_subset
  apply Metric.ball_subset_ball (show roundNormalRadius p ≤ (roundNormalChart p).radius from ?_) hx
  dsimp only [roundNormalRadius]
  linarith [(roundNormalChart p).radius_pos]

def roundNormalMetric (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    SmoothRiemannianMetric (𝓡 3) (EuclideanSpace ℝ (Fin 3)) :=
  (roundNormalChart p).totalMetric
    (scaleMetric 2 (by norm_num) (roundMetric (E := E4) (n := 3)))

theorem roundNormalMetric_inner
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ < roundNormalRadius p)
    (v w : EuclideanSpace ℝ (Fin 3)) :
    (roundNormalMetric p).inner x v w =
      2 * (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)).inner
        (roundNormalMap p x) (mfderiv (𝓡 3) (𝓡 3) (roundNormalMap p) x v)
        (mfderiv (𝓡 3) (𝓡 3) (roundNormalMap p) x w) := by
  have h := (roundNormalChart p).totalMetric_inner
    (scaleMetric 2 (by norm_num) (roundMetric (E := E4) (n := 3))) x
    (by simpa [roundNormalRadius, Metric.mem_ball, dist_zero_right] using hx) v w
  simp only [tangentSpaceModelContinuousLinearEquiv_symm_apply,
    NormalBallChart.metric_apply, roundNormalChart_apply] at h
  with_unfolding_all exact h

theorem roundNormalMetric_inner_fderiv
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : ‖x‖ < roundNormalRadius p)
    (v w : EuclideanSpace ℝ (Fin 3)) :
    (roundNormalMetric p).inner x v w =
      2 * ⟪fderiv ℝ (fun y => (roundNormalMap p y : EuclideanSpace ℝ (Fin 4))) x v,
        fderiv ℝ (fun y => (roundNormalMap p y : EuclideanSpace ℝ (Fin 4))) x w⟫_ℝ := by
  have hcoesm : ContMDiff (𝓡 3) 𝓘(ℝ, E4) ∞ (Subtype.val : Sphere3 → E4) :=
    contMDiff_coe_sphere
  have hcoe : MDifferentiableAt (𝓡 3) 𝓘(ℝ, E4)
      (Subtype.val : Sphere3 → E4) (roundNormalMap p x) :=
    hcoesm.contMDiffAt.mdifferentiableAt (by decide)
  have hc := mfderiv_comp (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓘(ℝ, E4)) x
    hcoe ((roundNormalMap_smooth p).contMDiffAt.mdifferentiableAt (by decide))
  rw [mfderiv_eq_fderiv] at hc
  have hD (z : E3) :
      dIncl (n := 3) (roundNormalMap p x)
          (mfderiv (𝓡 3) (𝓡 3) (roundNormalMap p) x z) =
        fderiv ℝ (fun y => (roundNormalMap p y : E4)) x z := by
    exact (congrArg (fun D : E3 →L[ℝ] E4 => D z) hc).symm
  rw [roundNormalMetric_inner p hx, roundMetric_inner, hD, hD]

@[simp] theorem roundNormalMetric_inner_zero
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (v w : EuclideanSpace ℝ (Fin 3)) :
    (roundNormalMetric p).inner 0 v w = ⟪v, w⟫_ℝ := by
  rw [roundNormalMetric_inner p (by simpa using roundNormalRadius_pos p)]
  with_unfolding_all rw [roundNormalMap_mfderiv_zero, roundNormalMap_mfderiv_zero,
    roundNormalMap_zero]
  simp only [map_smul, smul_apply, smul_eq_mul, normalFrame_inner]
  have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  field_simp [hs]
  rw [Real.sq_sqrt (by norm_num)]

theorem roundNormalMetric_inner_eq_radialBilinearForm
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0)
    (hxr : ‖x‖ < roundNormalRadius p) (v w : EuclideanSpace ℝ (Fin 3)) :
    (roundNormalMetric p).inner x v w =
      radialBilinearForm (‖x‖⁻¹ • x)
        ((Real.sqrt 2 * Real.sin (‖x‖ / Real.sqrt 2) / ‖x‖) ^ 2) v w := by
  rw [roundNormalMetric_inner_fderiv p hxr, roundNormalMap_fderiv p hx,
    roundNormalMap_fderiv p hx]
  exact round_normal_inner_eq_radialBilinearForm (normalAmbientFrame p)
    (norm_eq_of_mem_sphere p)
    (fun z => dIncl_orth p (normalFrame (roundMetric (E := E4) (n := 3)) p z)) hx v w

end DifferentialGeometry.Geometry.Riemannian
