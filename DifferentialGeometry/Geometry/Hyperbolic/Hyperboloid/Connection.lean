import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.RiemannianMetric
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.CorrectionContraction
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.VectorField
import DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative

noncomputable section

open scoped _root_.Manifold ContDiff

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def spatialInner (x v w : E) : ℝ :=
  inner ℝ v w - inner ℝ v x * inner ℝ w x / (1 + ‖x‖ ^ 2)

private theorem differentiable_spatialInner (v w : E) :
    Differentiable ℝ (fun x : E => spatialInner x v w) := by
  have hd : Differentiable ℝ (fun x : E => (1 + ‖x‖ ^ 2)⁻¹) :=
    ((differentiable_const (1 : ℝ)).add
      ((contDiff_norm_sq ℝ (n := ∞)).differentiable (by decide))).inv
        (fun x => by
          change (1 + ‖x‖ ^ 2 : ℝ) ≠ 0
          positivity)
  simpa only [spatialInner, div_eq_mul_inv] using!
    (differentiable_const (inner ℝ v w)).sub
      (((innerSL ℝ v).differentiable.mul (innerSL ℝ w).differentiable).mul hd)

private theorem fderiv_spatialInner (x u v w : E) :
    fderiv ℝ (fun y : E => spatialInner y v w) x u =
      -((inner ℝ v u * inner ℝ w x + inner ℝ v x * inner ℝ w u) /
          (1 + ‖x‖ ^ 2)) +
        inner ℝ v x * inner ℝ w x * (2 * inner ℝ x u) / (1 + ‖x‖ ^ 2) ^ 2 := by
  have hd : HasFDerivAt (fun y : E => 1 + ‖y‖ ^ 2) (2 • innerSL ℝ x) x := by
    simpa only [zero_add] using!
      (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x).add
        (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hv := (innerSL ℝ v).hasFDerivAt (x := x)
  have hw := (innerSL ℝ w).hasFDerivAt (x := x)
  have h := (hasFDerivAt_const (𝕜 := ℝ) (inner ℝ v w) x).sub
    ((hv.mul hw).mul ((hasFDerivAt_inv (show (1 + ‖x‖ ^ 2 : ℝ) ≠ 0 by positivity)).comp x hd))
  have heq : (fun y : E => spatialInner y v w) =
      (fun _ : E => inner ℝ v w) - (innerSL ℝ v : E → ℝ) * (innerSL ℝ w : E → ℝ) *
        ((fun a : ℝ => a⁻¹) ∘ (fun y : E => 1 + ‖y‖ ^ 2)) := by
    funext y
    change inner ℝ v w - inner ℝ v y * inner ℝ w y / (1 + ‖y‖ ^ 2) =
      inner ℝ v w - inner ℝ v y * inner ℝ w y * (1 + ‖y‖ ^ 2)⁻¹
    rw [div_eq_mul_inv]
  rw [heq, h.fderiv]
  simp only [sub_apply, zero_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    Function.comp_apply, Pi.mul_apply, innerSL_apply_apply, smul_eq_mul]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, two_smul, smul_eq_mul]
  simp only [div_eq_mul_inv]
  ring

private theorem spatialInner_koszul (x v w z : E) :
    (1 / 2 : ℝ) *
      (fderiv ℝ (fun y : E => spatialInner y w z) x v +
        fderiv ℝ (fun y : E => spatialInner y z v) x w -
        fderiv ℝ (fun y : E => spatialInner y v w) x z) =
      -(spatialInner x v w) * spatialInner x x z := by
  rw [fderiv_spatialInner, fderiv_spatialInner, fderiv_spatialInner]
  simp only [spatialInner, real_inner_self_eq_norm_sq]
  rw [real_inner_comm w v, real_inner_comm z v, real_inner_comm z w,
    real_inner_comm z x, real_inner_comm v x, real_inner_comm w x]
  field_simp [show (1 + ‖x‖ ^ 2 : ℝ) ≠ 0 by positivity]
  ring

private theorem spatialInner_smul_left (x v w : E) (a : ℝ) :
    spatialInner x (a • v) w = a * spatialInner x v w := by
  simp only [spatialInner, real_inner_smul_left, div_eq_mul_inv]
  ring

private theorem metric_spaceVectorField (x : Hyperboloid E) (v w : E) :
    riemannianMetric.inner x (spaceVectorField v x) (spaceVectorField w x) =
      spatialInner x.space v w := by
  rw [riemannianMetric_inner, mfderiv_spaceDiffeomorph]
  change inner ℝ v w - inner ℝ x.space v * inner ℝ x.space w / (1 + ‖x.space‖ ^ 2) = _
  rw [real_inner_comm v x.space, real_inner_comm w x.space]
  rfl

private theorem directional_spatialInner (x : Hyperboloid E) (u v w : E) :
    Geometry.Connection.directionalDerivAlong (spaceVectorField u)
      (fun y : Hyperboloid E => riemannianMetric.inner y (spaceVectorField v y) (spaceVectorField w y)) x =
        fderiv ℝ (fun y : E => spatialInner y v w) x.space u := by
  have heq : (fun y : Hyperboloid E =>
      riemannianMetric.inner y (spaceVectorField v y) (spaceVectorField w y)) =
      fun y : Hyperboloid E => spatialInner (spaceDiffeomorph y) v w :=
    funext fun y => metric_spaceVectorField y v w
  rw [heq, Geometry.Connection.directionalDerivAlong]
  rw [mvfderiv_comp_diffeomorph (fun y : E => spatialInner y v w) spaceDiffeomorph x
    (spaceVectorField u x) ((differentiable_spatialInner v w x.space).mdifferentiableAt)]
  rw [mvfderiv_model_apply_eq_fderiv, mfderiv_spaceDiffeomorph]
  rfl

private theorem mpullback_constantModelVectorField (v : E) :
    VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) spaceDiffeomorph
      (constantModelVectorField v) = spaceVectorField v := by
  funext x
  unfold VectorField.mpullback
  rw [mfderiv_spaceDiffeomorph]
  change (ContinuousLinearMap.id ℝ E).inverse v = v
  rw [ContinuousLinearMap.inverse_id]
  rfl

variable [FiniteDimensional ℝ E]

private theorem bracket_spaceVectorField (x : Hyperboloid E) (v w : E) :
    VectorField.mlieBracket 𝓘(ℝ, E) (spaceVectorField v) (spaceVectorField w) x = 0 := by
  have hc (u : E) : MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (fun y : E => (⟨y, constantModelVectorField u y⟩ : TangentBundle 𝓘(ℝ, E) E))
      (spaceDiffeomorph x) := by
    rw [mdifferentiableAt_totalSpace]
    refine ⟨mdifferentiableAt_id, ?_⟩
    convert (mdifferentiableAt_const (I := 𝓘(ℝ, E)) (c := u)) using 1
    ext y
    simp only [trivializationAt_model_space_apply]
    rfl
  have hz : VectorField.mlieBracket 𝓘(ℝ, E)
      (constantModelVectorField v) (constantModelVectorField w) = 0 := by
    funext y
    rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_eq_lieBracketWithin]
    change VectorField.lieBracketWithin ℝ (fun _ : E => v) (fun _ : E => w) Set.univ y = 0
    simp [VectorField.lieBracketWithin]
  have h := VectorField.mpullback_mlieBracket (hc v) (hc w)
    (spaceDiffeomorph (E := E)).contMDiffAt (by simp)
  rw [hz, mpullback_constantModelVectorField, mpullback_constantModelVectorField] at h
  simpa only [VectorField.mpullback, Pi.zero_apply, map_zero] using h.symm

private theorem leviCivita_spaceVectorField (x : Hyperboloid E) (v w : E) :
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x
      (Geometry.Connection.leviCivitaConnectionOfMetric riemannianMetric
        (spaceVectorField w) x (spaceVectorField v x)) =
      -(spatialInner x.space v w) • x.space := by
  let A := Geometry.Connection.leviCivitaConnectionOfMetric riemannianMetric
    (spaceVectorField w) x (spaceVectorField v x)
  let B := spaceVectorField (-(spatialInner x.space v w) • x.space) x
  have hpair (z : E) : riemannianMetric.inner x A (spaceVectorField z x) =
      riemannianMetric.inner x B (spaceVectorField z x) := by
    have h := Geometry.Connection.leviCivitaConnectionOfMetric_inner_eq_koszulScalar
      riemannianMetric (spaceVectorField v) (spaceVectorField w) (spaceVectorField z) x
      (mdifferentiableAt_spaceVectorField x v) (mdifferentiableAt_spaceVectorField x w)
      (mdifferentiableAt_spaceVectorField x z)
    rw [Geometry.Connection.koszulScalar] at h
    simp only [directional_spatialInner, bracket_spaceVectorField, map_zero, add_zero, sub_zero] at h
    rw [spatialInner_koszul] at h
    change riemannianMetric.inner x A (spaceVectorField z x) =
      riemannianMetric.inner x
        (spaceVectorField (-(spatialInner x.space v w) • x.space) x) (spaceVectorField z x)
    rw [metric_spaceVectorField, spatialInner_smul_left]
    exact h
  have hAB : A = B := by
    by_contra hne
    let d : TangentSpace 𝓘(ℝ, E) x := A - B
    have hd : d ≠ 0 := sub_ne_zero.mpr hne
    have h := hpair (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x d)
    have hrec : spaceVectorField (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x d) x = d :=
      (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).symm_apply_apply d
    rw [hrec] at h
    have hz : riemannianMetric.inner x d d = 0 := by
      change riemannianMetric.inner x (A - B) d = 0
      rw [map_sub (riemannianMetric.inner x) A B, sub_apply, h, sub_self]
    exact (ne_of_gt (riemannianMetric.pos x d hd)) hz
  change tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x A = _
  rw [hAB]
  exact (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x).apply_symm_apply _

theorem leviCivita_tangentConstAt (x : Hyperboloid E) (v w : TangentSpace 𝓘(ℝ, E) x) :
    NormedSpace.fromTangentSpace (𝕜 := ℝ) x.space
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) spaceDiffeomorph x
        (Geometry.Connection.leviCivitaConnectionOfMetric riemannianMetric
          (Geometry.Connection.tangentConstAt x w) x v)) =
      -(riemannianMetric.inner x v w) • x.space := by
  let e := tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x
  have hv : spaceVectorField (e v) x = v := e.symm_apply_apply v
  have hw : spaceVectorField (e w) x = w := e.symm_apply_apply w
  have h := leviCivita_spaceVectorField x (e v) (e w)
  rw [← metric_spaceVectorField x (e v) (e w), hv, hw] at h
  have hY := tangentConstAt_spaceVectorField x (e w)
  rw [hw] at hY
  rw [← hY] at h
  rw [mfderiv_spaceDiffeomorph]
  exact h

omit [FiniteDimensional ℝ E] in
open Geometry.Connection in
private theorem chartESectionRepr_spaceVectorField (x : Hyperboloid E) (w : E) :
    chartESectionRepr (I := 𝓘(ℝ, E)) x (spaceVectorField w) = fun _ => w := by
  funext y
  have hb : y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet, chartAt_eq_spaceHomeomorph]
    trivial
  have h := (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearMapAt_symmL
    (R := ℝ) hb w
  rw [tangent_trivializationAt_symmL] at h
  exact h

open Geometry.Connection in
theorem chartChristoffelContraction_eq (x : Hyperboloid E) (v w : E) :
    Geometry.Riemannian.Geodesic.chartChristoffelContraction
      (I := 𝓘(ℝ, E)) riemannianMetric x v w x.space =
      -(riemannianMetric.inner x (spaceVectorField v x) (spaceVectorField w x)) • x.space := by
  let _ : T2Space (Hyperboloid E) := (spaceHomeomorph (E := E)).isEmbedding.t2Space
  have hx := self_mem_chartLeviCivitaGoodSet (I := 𝓘(ℝ, E)) x
  have hc := LeviCivita_chart_apply (I := 𝓘(ℝ, E)) riemannianMetric x hx
    (mdifferentiableAt_spaceVectorField x w) (spaceVectorField v x)
  rw [chartLeviCivita_apply (I := 𝓘(ℝ, E)) riemannianMetric x
    (spaceVectorField w) hx (spaceVectorField v x),
    chartESectionRepr_spaceVectorField] at hc
  rw [show ((fun _ : Hyperboloid E => w) ∘ (extChartAt 𝓘(ℝ, E) x).symm) =
    (fun _ : E => w) from rfl, fderiv_const_apply, zero_apply, zero_add,
    correction_eq_contr] at hc
  have hcoord : trivToE (I := 𝓘(ℝ, E)) x x (spaceVectorField v x) = v :=
    congrFun (chartESectionRepr_spaceVectorField x v) x
  rw [hcoord] at hc
  have hext : extChartAt 𝓘(ℝ, E) x x = x.space := by
    rw [extChartAt_coe, chartAt_eq_spaceHomeomorph]
    rfl
  rw [hext] at hc
  change leviCivitaConnectionOfMetric riemannianMetric (spaceVectorField w) x
    (spaceVectorField v x) = _ at hc
  have h := leviCivita_tangentConstAt x (spaceVectorField v x) (spaceVectorField w x)
  rw [tangentConstAt_spaceVectorField, mfderiv_spaceDiffeomorph] at h
  change leviCivitaConnectionOfMetric riemannianMetric (spaceVectorField w) x
    (spaceVectorField v x) = _ at h
  rw [hc] at h
  simp only [trivFromE, tangent_trivializationAt_symmL] at h
  exact h

end DifferentialGeometry.Hyperboloid
