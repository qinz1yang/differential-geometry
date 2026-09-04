import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Formula
import DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.CorrectionContraction
import DifferentialGeometry.Geometry.Geodesic.Equation.Koszul
import DifferentialGeometry.Geometry.Coordinates.FixedBaseDerivative
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section


namespace DifferentialGeometry
namespace Geometry
namespace Connection

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]

local instance modelCLMOneNormedAddCommGroup :
    NormedAddCommGroup (E →L[Real] Real) := inferInstance

local instance modelCLMOneNormedSpace :
    NormedSpace Real (E →L[Real] Real) := inferInstance

local instance modelCLMTwoNormedAddCommGroup :
    NormedAddCommGroup (E →L[Real] E →L[Real] Real) := inferInstance

local instance modelCLMTwoNormedSpace :
    NormedSpace Real (E →L[Real] E →L[Real] Real) := inferInstance

omit [FiniteDimensional Real E] in
private theorem fderiv_eval2
    {B : E → E →L[Real] E →L[Real] Real} {z : E}
    (hB : DifferentiableAt Real B z) (u v w : E) :
    fderiv Real (fun y ↦ B y w u) z v = fderiv Real B z v w u := by
  have hw : HasFDerivAt (fun _ : E ↦ w) 0 z :=
    hasFDerivAt_const (𝕜 := Real) w z
  have hu : HasFDerivAt (fun _ : E ↦ u) 0 z :=
    hasFDerivAt_const (𝕜 := Real) u z
  have hfirst := hB.hasFDerivAt.clm_apply hw
  have hsecond := hfirst.clm_apply hu
  have hfd := hsecond.fderiv
  have happ := DFunLike.congr_fun hfd v
  simpa using happ

omit [FiniteDimensional Real E] in
private theorem dir_const_eval2
    {B : E → E →L[Real] E →L[Real] Real} {z : E}
    (hB : DifferentiableAt Real B z) (u v w : E) :
    directionalDerivAlong (I := 𝓘(Real, E)) (constantModelVectorField v)
        (fun y ↦ B y w u) z =
      fderiv Real B z v w u := by
  unfold directionalDerivAlong
  rw [mvfderiv_model_apply_eq_fderiv, constantModelVectorField_apply]
  exact fderiv_eval2 hB u v w

omit [FiniteDimensional Real E] in
private theorem bracket_const_eq_zero (z v w : E) :
    VectorField.mlieBracket 𝓘(Real, E)
        (constantModelVectorField v) (constantModelVectorField w) z = 0 := by
  rw [← VectorField.mlieBracketWithin_univ]
  rw [VectorField.mlieBracketWithin_eq_lieBracketWithin]
  unfold constantModelVectorField tangentSpaceModelContinuousLinearEquiv
  change VectorField.lieBracketWithin Real (fun _ : E ↦ v)
    (fun _ : E ↦ w) Set.univ z = 0
  simp [VectorField.lieBracketWithin]

omit [FiniteDimensional Real E] in
private theorem tangentConst_model (z v : E) :
    tangentConstAt (I := 𝓘(Real, E)) z (constantModelVectorField v z) =
      constantModelVectorField v := by
  funext y
  unfold tangentConstAt TensorLieDeriv.tangentConstInChart
  rw [TangentBundle.symmL_trivializationAt_eq_core
    (I := 𝓘(Real, E)) (b₀ := z) (b := y) (by
      rw [chartAt_self_eq]
      exact Set.mem_univ y)]
  rw [TangentBundle.coordChange_model_space,
    TangentBundle.continuousLinearMapAt_model_space]
  exact (tangentSpaceModelContinuousLinearEquiv
    (I := 𝓘(Real, E)) y).symm_apply_apply v

theorem const_flat_eq_koszul
    (g : SmoothRiemannianMetric 𝓘(Real, E) E)
    (B : E → E →L[Real] E →L[Real] Real)
    (hB : ∀ y : E, tangentBilinearFormToModel y (g.inner y) = B y) {z : E}
    (hBdiff : DifferentiableAt Real B z) (v w : E) :
    B z
        (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z
          ((leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
            (constantModelVectorField w) z)
            ((tangentSpaceModelContinuousLinearEquiv
              (I := 𝓘(Real, E)) z).symm v))) =
      MetricKoszul.koszulCov (fderiv Real B z) v w := by
  apply ContinuousLinearMap.ext
  intro u
  have hv := mdifferentiableAt_tangentConstAt_self
    (I := 𝓘(Real, E)) z (constantModelVectorField v z)
  have hw := mdifferentiableAt_tangentConstAt_self
    (I := 𝓘(Real, E)) z (constantModelVectorField w z)
  have hu := mdifferentiableAt_tangentConstAt_self
    (I := 𝓘(Real, E)) z (constantModelVectorField u z)
  have hKos := leviCivitaConnectionOfMetric_inner_eq_koszulScalar
    (I := 𝓘(Real, E)) g
      (tangentConstAt (I := 𝓘(Real, E)) z (constantModelVectorField v z))
      (tangentConstAt (I := 𝓘(Real, E)) z (constantModelVectorField w z))
      (tangentConstAt (I := 𝓘(Real, E)) z (constantModelVectorField u z)) z hv hw hu
  rw [tangentConst_model z v, tangentConst_model z w,
    tangentConst_model z u] at hKos
  have hwu :
      (fun y : E ↦ g.inner y (constantModelVectorField w y)
        (constantModelVectorField u y)) = fun y ↦ B y w u := by
    funext y
    exact (tangentBilinearFormToModel_apply y (g.inner y) w u).symm.trans
      (congrArg (fun L : E →L[Real] E →L[Real] Real ↦ L w u) (hB y))
  have huv :
      (fun y : E ↦ g.inner y (constantModelVectorField u y)
        (constantModelVectorField v y)) = fun y ↦ B y v u := by
    funext y
    calc
      g.inner y (constantModelVectorField u y) (constantModelVectorField v y) =
          g.inner y (constantModelVectorField v y) (constantModelVectorField u y) :=
        g.symm y _ _
      _ = B y v u :=
        (tangentBilinearFormToModel_apply y (g.inner y) v u).symm.trans
          (congrArg (fun L : E →L[Real] E →L[Real] Real ↦ L v u) (hB y))
  have hvw :
      (fun y : E ↦ g.inner y (constantModelVectorField v y)
        (constantModelVectorField w y)) = fun y ↦ B y v w := by
    funext y
    exact (tangentBilinearFormToModel_apply y (g.inner y) v w).symm.trans
      (congrArg (fun L : E →L[Real] E →L[Real] Real ↦ L v w) (hB y))
  change tangentBilinearFormToModel z (g.inner z)
    (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z
      ((leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
        (constantModelVectorField w) z)
        (constantModelVectorField v z))) u = _ at hKos
  rw [hB z] at hKos
  unfold koszulScalar at hKos
  rw [hwu, huv, hvw, bracket_const_eq_zero, bracket_const_eq_zero,
    bracket_const_eq_zero] at hKos
  simp only [map_zero, sub_zero, add_zero] at hKos
  rw [dir_const_eval2 hBdiff u v w, dir_const_eval2 hBdiff u w v,
    dir_const_eval2 hBdiff w u v] at hKos
  rw [MetricKoszul.koszul_cov_apply]
  exact hKos

theorem const_flat_eq_nhds
    (g : SmoothRiemannianMetric 𝓘(Real, E) E)
    (B : E → E →L[Real] E →L[Real] Real) {z : E}
    (hB : (fun y : E ↦ tangentBilinearFormToModel y (g.inner y)) =ᶠ[nhds z] B)
    (hBdiff : DifferentiableAt Real B z) (v w : E) :
    B z
        (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z
          ((leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
            (constantModelVectorField w) z)
            ((tangentSpaceModelContinuousLinearEquiv
              (I := 𝓘(Real, E)) z).symm v))) =
      MetricKoszul.koszulCov (fderiv Real B z) v w := by
  apply ContinuousLinearMap.ext
  intro u
  have hv := mdifferentiableAt_tangentConstAt_self
    (I := 𝓘(Real, E)) z (constantModelVectorField v z)
  have hw := mdifferentiableAt_tangentConstAt_self
    (I := 𝓘(Real, E)) z (constantModelVectorField w z)
  have hu := mdifferentiableAt_tangentConstAt_self
    (I := 𝓘(Real, E)) z (constantModelVectorField u z)
  have hKos := leviCivitaConnectionOfMetric_inner_eq_koszulScalar
    (I := 𝓘(Real, E)) g
      (tangentConstAt (I := 𝓘(Real, E)) z (constantModelVectorField v z))
      (tangentConstAt (I := 𝓘(Real, E)) z (constantModelVectorField w z))
      (tangentConstAt (I := 𝓘(Real, E)) z (constantModelVectorField u z)) z hv hw hu
  rw [tangentConst_model z v, tangentConst_model z w,
    tangentConst_model z u] at hKos
  have hwu :
      (fun y : E ↦ g.inner y (constantModelVectorField w y)
        (constantModelVectorField u y)) =ᶠ[nhds z] fun y ↦ B y w u := by
    filter_upwards [hB] with y hy
    exact (tangentBilinearFormToModel_apply y (g.inner y) w u).symm.trans
      (congrArg (fun L : E →L[Real] E →L[Real] Real ↦ L w u) hy)
  have huv :
      (fun y : E ↦ g.inner y (constantModelVectorField u y)
        (constantModelVectorField v y)) =ᶠ[nhds z] fun y ↦ B y v u := by
    filter_upwards [hB] with y hy
    calc
      g.inner y (constantModelVectorField u y) (constantModelVectorField v y) =
          g.inner y (constantModelVectorField v y) (constantModelVectorField u y) :=
        g.symm y _ _
      _ = B y v u :=
        (tangentBilinearFormToModel_apply y (g.inner y) v u).symm.trans
          (congrArg (fun L : E →L[Real] E →L[Real] Real ↦ L v u) hy)
  have hvw :
      (fun y : E ↦ g.inner y (constantModelVectorField v y)
        (constantModelVectorField w y)) =ᶠ[nhds z] fun y ↦ B y v w := by
    filter_upwards [hB] with y hy
    exact (tangentBilinearFormToModel_apply y (g.inner y) v w).symm.trans
      (congrArg (fun L : E →L[Real] E →L[Real] Real ↦ L v w) hy)
  have hdir_wu :
      directionalDerivAlong (I := 𝓘(Real, E)) (constantModelVectorField v)
          (fun y ↦ g.inner y (constantModelVectorField w y)
            (constantModelVectorField u y)) z =
        fderiv Real B z v w u := by
    unfold directionalDerivAlong
    rw [mvfderiv_model_apply_eq_fderiv, constantModelVectorField_apply,
      hwu.fderiv_eq]
    exact fderiv_eval2 hBdiff u v w
  have hdir_uv :
      directionalDerivAlong (I := 𝓘(Real, E)) (constantModelVectorField w)
          (fun y ↦ g.inner y (constantModelVectorField u y)
            (constantModelVectorField v y)) z =
        fderiv Real B z w v u := by
    unfold directionalDerivAlong
    rw [mvfderiv_model_apply_eq_fderiv, constantModelVectorField_apply,
      huv.fderiv_eq]
    exact fderiv_eval2 hBdiff u w v
  have hdir_vw :
      directionalDerivAlong (I := 𝓘(Real, E)) (constantModelVectorField u)
          (fun y ↦ g.inner y (constantModelVectorField v y)
            (constantModelVectorField w y)) z =
        fderiv Real B z u v w := by
    unfold directionalDerivAlong
    rw [mvfderiv_model_apply_eq_fderiv, constantModelVectorField_apply,
      hvw.fderiv_eq]
    exact fderiv_eval2 hBdiff w u v
  change tangentBilinearFormToModel z (g.inner z)
    (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z
      ((leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
        (constantModelVectorField w) z)
        (constantModelVectorField v z))) u = _ at hKos
  rw [hB.eq_of_nhds] at hKos
  unfold koszulScalar at hKos
  rw [bracket_const_eq_zero, bracket_const_eq_zero,
    bracket_const_eq_zero] at hKos
  simp only [map_zero, sub_zero, add_zero] at hKos
  rw [hdir_wu, hdir_uv, hdir_vw] at hKos
  rw [MetricKoszul.koszul_cov_apply]
  exact hKos

theorem const_cov_eq_koszul
    (g : SmoothRiemannianMetric 𝓘(Real, E) E)
    (B : E → E →L[Real] E →L[Real] Real)
    (hB : ∀ y : E, tangentBilinearFormToModel y (g.inner y) = B y) {z : E}
    (hBdiff : DifferentiableAt Real B z)
    (hco : IsCoercive (B z)) (v w : E) :
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z
        ((leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
          (constantModelVectorField w) z)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) z).symm v)) =
      MetricKoszul.koszulVec hco (fderiv Real B z) v w := by
  calc
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z
        ((leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
          (constantModelVectorField w) z)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) z).symm v)) =
        hco.sharp (B z
          (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z
            ((leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
              (constantModelVectorField w) z)
              ((tangentSpaceModelContinuousLinearEquiv
                (I := 𝓘(Real, E)) z).symm v)))) :=
      (hco.sharp_apply _).symm
    _ = hco.sharp (MetricKoszul.koszulCov (fderiv Real B z) v w) := by
      rw [const_flat_eq_koszul g B hB hBdiff v w]
    _ = MetricKoszul.koszulVec hco (fderiv Real B z) v w := rfl

theorem const_cov_eq_nhds
    (g : SmoothRiemannianMetric 𝓘(Real, E) E)
    (B : E → E →L[Real] E →L[Real] Real) {z : E}
    (hB : (fun y : E ↦ tangentBilinearFormToModel y (g.inner y)) =ᶠ[nhds z] B)
    (hBdiff : DifferentiableAt Real B z)
    (hco : IsCoercive (B z)) (v w : E) :
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z
        ((leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
          (constantModelVectorField w) z)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) z).symm v)) =
      MetricKoszul.koszulVec hco (fderiv Real B z) v w := by
  calc
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z
        ((leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
          (constantModelVectorField w) z)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) z).symm v)) =
        hco.sharp (B z
          (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z
            ((leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
              (constantModelVectorField w) z)
              ((tangentSpaceModelContinuousLinearEquiv
                (I := 𝓘(Real, E)) z).symm v)))) :=
      (hco.sharp_apply _).symm
    _ = hco.sharp (MetricKoszul.koszulCov (fderiv Real B z) v w) := by
      rw [const_flat_eq_nhds g B hB hBdiff v w]
    _ = MetricKoszul.koszulVec hco (fderiv Real B z) v w := rfl

theorem cov_eq_fderiv_add
    (g : SmoothRiemannianMetric 𝓘(Real, E) E)
    (B : E → E →L[Real] E →L[Real] Real) {z : E}
    (hB : (fun y : E ↦ tangentBilinearFormToModel y (g.inner y)) =ᶠ[nhds z] B)
    (hBdiff : DifferentiableAt Real B z)
    (hco : IsCoercive (B z)) (V : E → E)
    (hV : MDifferentiableAt 𝓘(Real, E)
      (𝓘(Real, E).prod 𝓘(Real, E))
      (fun y : E ↦
        (⟨y, (tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(Real, E)) y).symm (V y)⟩ : TangentBundle 𝓘(Real, E) E)) z)
    (v : E) :
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z
        ((leviCivitaConnectionOfMetric (I := 𝓘(Real, E)) g
          (fun y : E ↦ (tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) y).symm (V y)) z)
          ((tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(Real, E)) z).symm v)) =
      fderiv Real V z v +
        MetricKoszul.koszulVec hco (fderiv Real B z) v (V z) := by
  let Vfield : (y : E) → TangentSpace 𝓘(Real, E) y := fun y ↦
    (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) y).symm (V y)
  have hzgood : z ∈ chartLeviCivitaGoodSet (I := 𝓘(Real, E)) z :=
    self_mem_chartLeviCivitaGoodSet (I := 𝓘(Real, E)) (α := z)
  have hrepr :
      chartESectionRepr (I := 𝓘(Real, E)) z Vfield = V := by
    funext y
    rw [chartE_section_repr_eq_trivToE]
    unfold trivToE Vfield
    rw [TangentBundle.continuousLinearMapAt_model_space]
    exact (tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(Real, E)) y).apply_symm_apply (V y)
  have hcorr :
      Geometry.Riemannian.Geodesic.chartChristoffelContraction
          (I := 𝓘(Real, E)) g z v (V z) z =
        MetricKoszul.koszulVec hco (fderiv Real B z) v (V z) := by
    rw [← const_cov_eq_contr g z z v (V z)]
    exact const_cov_eq_nhds g B hB hBdiff hco v (V z)
  change tangentSpaceModelContinuousLinearEquiv (I := 𝓘(Real, E)) z
    ((LeviCivita (I := 𝓘(Real, E)) g).toFun Vfield z
      ((tangentSpaceModelContinuousLinearEquiv
        (I := 𝓘(Real, E)) z).symm v)) = _
  rw [LeviCivita_chart_apply (I := 𝓘(Real, E)) g z hzgood hV
    ((tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(Real, E)) z).symm v)]
  rw [chartLeviCivita_apply (I := 𝓘(Real, E)) g z Vfield hzgood
    ((tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(Real, E)) z).symm v)]
  rw [hrepr]
  rw [show (V ∘ (extChartAt 𝓘(Real, E) z).symm) = V by rfl]
  rw [correction_eq_contr]
  simp only [trivFromE, trivToE, TangentBundle.symmL_model_space,
    TangentBundle.continuousLinearMapAt_model_space,
    tangentSpaceModelContinuousLinearEquiv_apply,
    tangentSpaceModelContinuousLinearEquiv_symm_apply,
    extChartAt_self_apply, modelWithCornersSelf_coe, id_eq]
  exact congrArg (fun w ↦ fderiv Real V z v + w) hcorr

end Connection
end Geometry
end DifferentialGeometry
