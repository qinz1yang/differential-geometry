import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Metric.PullbackCross
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Normalized
import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentity
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Connection Curvature Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

noncomputable def gaussianPotential : C^∞⟮𝓘(Real, E), E; Real⟯ :=
  ⟨fun x : E => ‖x‖ ^ 2 / 4,
    ((contDiff_norm_sq Real).div_const 4).contMDiff⟩

omit [FiniteDimensional Real E] in
@[simp] theorem gaussianPotential_apply (x : E) :
    gaussianPotential x = ‖x‖ ^ 2 / 4 := by
  rfl

private lemma euclideanMetric_chartGramOnE
    (x : E) (i j : Fin (Module.finrank Real E)) :
    chartGramOnE (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x i j =
      fun _ => inner Real (chartModelBasis E i) (chartModelBasis E j) := by
  funext y
  simp only [chartGramOnE, chartGramMatrix, Matrix.of_apply,
    chartBasisVecFiber]
  simp only [TangentBundle.symmL_model_space]
  rw [DifferentialGeometry.euclideanMetric_inner]
  change inner Real ((1 : E →L[Real] E) (chartModelBasis E i))
      ((1 : E →L[Real] E) (chartModelBasis E j)) = _
  rfl

private lemma euclideanMetric_chartChristoffel
    (x : E) (i j k : Fin (Module.finrank Real E)) :
    chartChristoffel (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x i j k = 0 := by
  funext y
  rw [chartChristoffel_def]
  simp_rw [euclideanMetric_chartGramOnE]
  simp [partialDeriv]

private lemma euclideanMetric_chartRiemannTensor
    (x : E) (i j k l : Fin (Module.finrank Real E)) :
    chartRiemannTensor (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x i j k l = 0 := by
  funext y
  rw [chartRiemannTensor_def]
  simp_rw [euclideanMetric_chartChristoffel]
  simp [partialDeriv]

theorem euclideanMetric_ricciTensor
    (x : E) (v w : TangentSpace 𝓘(Real, E) x) :
    ricciTensor (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x v w = 0 := by
  rw [Connection.ricciTensor_eq_chartRicciSwap_of_basis_identity
    (euclideanMetric (E := E)) x
    (Connection.chartRiemannBasisIdentity_holds
      (euclideanMetric (E := E)) x)]
  simp only [chartRicciTensor_def, euclideanMetric_chartRiemannTensor]
  simp

private lemma gaussianPotential_partialDeriv
    (i : Fin (Module.finrank Real E)) (y : E) :
    partialDeriv (E := E) i (fun z : E => ‖z‖ ^ 2 / 4) y =
      (1 / 2 : Real) * inner Real y (chartModelBasis E i) := by
  unfold partialDeriv
  have hfun : (fun z : E => ‖z‖ ^ 2 / 4) =
      (1 / 4 : Real) • (fun z : E => ‖z‖ ^ 2) := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, congrFun (fderiv_const_smul_field
    (𝕜 := Real) (f := fun z : E => ‖z‖ ^ 2) (1 / 4 : Real)) y]
  simp only [Pi.smul_apply, smul_apply, smul_eq_mul]
  rw [fderiv_norm_sq_apply]
  simp only [smul_apply, innerSL_apply_apply]
  ring

private lemma gaussianPotential_iteratedPartialDeriv
    (i j : Fin (Module.finrank Real E)) (y : E) :
    partialDeriv (E := E) i
        (partialDeriv (E := E) j (fun z : E => ‖z‖ ^ 2 / 4)) y =
      (1 / 2 : Real) * inner Real (chartModelBasis E i) (chartModelBasis E j) := by
  have hfirst : partialDeriv (E := E) j (fun z : E => ‖z‖ ^ 2 / 4) =
      fun z : E => (1 / 2 : Real) * inner Real z (chartModelBasis E j) := by
    funext z
    exact gaussianPotential_partialDeriv j z
  rw [hfirst]
  unfold partialDeriv
  have hfun :
      (fun z : E => (1 / 2 : Real) * inner Real z (chartModelBasis E j)) =
        (1 / 2 : Real) • (fun z : E => inner Real (chartModelBasis E j) z) := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [real_inner_comm]
  rw [hfun, congrFun (fderiv_const_smul_field
    (𝕜 := Real) (f := fun z : E => inner Real (chartModelBasis E j) z)
      (1 / 2 : Real)) y]
  simp only [Pi.smul_apply, smul_apply]
  change (1 / 2 : Real) *
      fderiv Real (innerSL Real (chartModelBasis E j)) y (chartModelBasis E i) = _
  rw [(innerSL Real (chartModelBasis E j)).fderiv]
  simp only [innerSL_apply_apply]
  rw [real_inner_comm]

private lemma gaussianPotential_chartHessianTensor
    (x : E) (i j : Fin (Module.finrank Real E)) :
    chartHessianTensor (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x
        (gaussianPotential (E := E)) i j x =
      (1 / 2 : Real) * inner Real (chartModelBasis E i) (chartModelBasis E j) := by
  rw [chartHessianTensor_def, chartIteratedPartialDeriv_def]
  have hscalar : scalarOnE (I := 𝓘(Real, E)) x
      (gaussianPotential (E := E)) = fun z : E => ‖z‖ ^ 2 / 4 := by
    funext z
    simp only [scalarOnE_def, gaussianPotential_apply]
    rw [extChartAt_model_space_eq_id]
    rfl
  rw [hscalar, gaussianPotential_iteratedPartialDeriv]
  simp_rw [euclideanMetric_chartChristoffel]
  simp

private lemma gaussianPotential_hessFun_eq (x : E) :
    hessFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
        (gaussianPotential (E := E)) x =
      (1 / 2 : Real) • metricFlatLinear (I := 𝓘(Real, E))
        (euclideanMetric (E := E)) x := by
  apply Module.Basis.ext (centeredChartTangentBasis (I := 𝓘(Real, E)) x)
  intro i
  apply Module.Basis.ext (centeredChartTangentBasis (I := 𝓘(Real, E)) x)
  intro j
  rw [hessFun_basis_apply, gaussianPotential_chartHessianTensor]
  change (1 / 2 : Real) * inner Real (chartModelBasis E i) (chartModelBasis E j) =
    (1 / 2 : Real) * (euclideanMetric (E := E)).inner x
      (centeredChartTangentBasis (I := 𝓘(Real, E)) x i)
      (centeredChartTangentBasis (I := 𝓘(Real, E)) x j)
  rw [DifferentialGeometry.euclideanMetric_inner,
    centeredChartTangentBasis_apply, centeredChartTangentBasis_apply,
    centeredChartTangentEquiv_symm_apply, centeredChartTangentEquiv_symm_apply]
  rfl

theorem gaussianPotential_hessian
    (x : E) (v w : TangentSpace 𝓘(Real, E) x) :
    hessFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
        (gaussianPotential (E := E)) x v w =
      (1 / 2 : Real) * (euclideanMetric (E := E)).inner x v w := by
  have h := LinearMap.congr_fun
    (LinearMap.congr_fun (gaussianPotential_hessFun_eq x) v) w
  exact h

omit [FiniteDimensional Real E] in
private lemma gaussianPotential_mfderiv
    (x : E) (v : TangentSpace 𝓘(Real, E) x) :
    mfderiv 𝓘(Real, E) 𝓘(Real, Real) (gaussianPotential (E := E)) x v =
      (1 / 2 : Real) * inner Real x v := by
  rw [mfderiv_eq_fderiv]
  change fderiv Real (fun z : E => ‖z‖ ^ 2 / 4) x v = _
  have hfun : (fun z : E => ‖z‖ ^ 2 / 4) =
      (1 / 4 : Real) • (fun z : E => ‖z‖ ^ 2) := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun, congrFun (fderiv_const_smul_field
    (𝕜 := Real) (f := fun z : E => ‖z‖ ^ 2) (1 / 4 : Real)) x]
  have hfd : ((1 / 4 : Real) • fderiv Real (fun z : E => ‖z‖ ^ 2)) x =
      (1 / 2 : Real) • innerSL Real x := by
    ext u
    simp only [Pi.smul_apply, smul_apply]
    rw [fderiv_norm_sq_apply]
    simp only [smul_apply, innerSL_apply_apply]
    ring
  rw [hfd]
  rfl

theorem gaussianPotential_normGradSqFun (x : E) :
    normGradSqFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
        (gaussianPotential (E := E)) x = gaussianPotential x := by
  rw [normGradSqFun_def, inner_gradFun, gaussianPotential_mfderiv]
  have hx := inner_gradFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
    (gaussianPotential (E := E)) x x
  have hdx : mfderiv 𝓘(Real, E) 𝓘(Real, Real) (gaussianPotential (E := E)) x
      (x : TangentSpace 𝓘(Real, E) x) = (1 / 2 : Real) * inner Real x x :=
    gaussianPotential_mfderiv x x
  rw [hdx] at hx
  change (1 / 2 : Real) * inner Real x
      (gradFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
        (gaussianPotential (E := E)) x) = gaussianPotential x
  have heuc : (euclideanMetric (E := E)).inner x
      (x : TangentSpace 𝓘(Real, E) x)
      (gradFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
        (gaussianPotential (E := E)) x) =
    inner Real x (gradFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
      (gaussianPotential (E := E)) x) :=
    DifferentialGeometry.euclideanMetric_inner x x _
  have hsymm : (euclideanMetric (E := E)).inner x
      (x : TangentSpace 𝓘(Real, E) x)
      (gradFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
        (gaussianPotential (E := E)) x) =
    (euclideanMetric (E := E)).inner x
      (gradFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
        (gaussianPotential (E := E)) x)
      (x : TangentSpace 𝓘(Real, E) x) :=
    (euclideanMetric (E := E)).symm x x _
  calc
    (1 / 2 : Real) * inner Real x
        (gradFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
          (gaussianPotential (E := E)) x) =
      (1 / 2 : Real) * (euclideanMetric (E := E)).inner x x
        (gradFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
          (gaussianPotential (E := E)) x) := by
        rw [heuc]
    _ = (1 / 2 : Real) * (euclideanMetric (E := E)).inner x
        (gradFun (I := 𝓘(Real, E)) (euclideanMetric (E := E))
          (gaussianPotential (E := E)) x) x := by
        rw [hsymm]
    _ = (1 / 2 : Real) * ((1 / 2 : Real) * inner Real x x) := by
        rw [hx]
    _ = gaussianPotential x := by
        rw [gaussianPotential_apply, real_inner_self_eq_norm_sq]
        ring

theorem euclideanMetric_scalarCurvature (x : E) :
    metricScalarAt (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x = 0 := by
  have hRicci : metricRicciAt (I := 𝓘(Real, E))
      (euclideanMetric (E := E)) x = 0 := by
    apply Tensor0SBundle.ext0S_basis
      (centeredChartTangentBasis (I := 𝓘(Real, E)) x)
    intro slots
    simp only [Tensor0SBundle.component0S_apply]
    change metricRicciAt (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x
      (fun a : Fin 2 => centeredChartTangentBasis (I := 𝓘(Real, E)) x (slots a)) = 0
    have hslots :
        (fun a : Fin 2 => centeredChartTangentBasis (I := 𝓘(Real, E)) x (slots a)) =
          vec2 (I := 𝓘(Real, E))
            (centeredChartTangentBasis (I := 𝓘(Real, E)) x (slots 0))
            (centeredChartTangentBasis (I := 𝓘(Real, E)) x (slots 1)) := by
      funext a
      fin_cases a <;> rfl
    rw [hslots]
    rw [metricRicciAt_apply_eq_ricciTensor]
    exact euclideanMetric_ricciTensor x _ _
  rw [metricScalarAt_def, hRicci]
  change Tensor0SBundle.inner0S (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x 2
    (metricTensor0S (I := 𝓘(Real, E)) (euclideanMetric (E := E)) x) 0 = 0
  rw [show (0 : Tensor0SBundle.Tensor0SSpace 2 𝓘(Real, E) x) =
      (0 : Real) • metricTensor0S (I := 𝓘(Real, E))
        (euclideanMetric (E := E)) x by simp,
    Tensor0SBundle.inner0S_smul_right]
  ring

theorem gradientRicciSoliton_gaussian :
    gradientRicciSoliton (I := 𝓘(Real, E))
      (euclideanMetric (E := E)) (gaussianPotential (E := E)) 1 := by
  intro x v w
  rw [euclideanMetric_ricciTensor, gaussianPotential_hessian]
  ring

theorem normalizedGradientRicciSoliton_gaussian :
    normalizedGradientRicciSoliton (I := 𝓘(Real, E))
      (euclideanMetric (E := E)) (gaussianPotential (E := E)) := by
  refine ⟨euclideanMetric_complete (E := E),
    gradientRicciSoliton_gaussian (E := E), ?_⟩
  intro x
  rw [euclideanMetric_scalarCurvature, gaussianPotential_normGradSqFun]
  ring

theorem gaussian_hamiltonNormalized :
    hamiltonNormalized (I := 𝓘(Real, E))
      (euclideanMetric (E := E)) (gaussianPotential (E := E)) 1 :=
  normalizedGradientRicciSoliton_hamilton_normalized
    (normalizedGradientRicciSoliton_gaussian (E := E))

def isGaussianGradientRicciSoliton
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (σ : Real) : Prop :=
  ∃ hσ : 0 < σ, ∃ Ψ : M ≃ₘ⟮I, 𝓘(Real, E)⟯ E, ∃ b : Real,
    Diffeomorph.pullbackMetricCross euclideanMetric Ψ =
        scaleMetric (I := I) σ hσ g ∧
      f + ContMDiffMap.const b = gaussianPotential.comp Ψ.toContMDiffMap

theorem isGaussianGradientRicciSoliton_add_const
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (c : Real) :
    isGaussianGradientRicciSoliton (I := I) g
      (f + ContMDiffMap.const c) σ ↔
      isGaussianGradientRicciSoliton (I := I) g f σ := by
  constructor
  · rintro ⟨hσ, Ψ, b, hmetric, hpotential⟩
    refine ⟨hσ, Ψ, b + c, hmetric, ?_⟩
    apply ContMDiffMap.ext
    intro x
    have hx := congrArg (fun q : C^∞⟮I, M; Real⟯ => q x) hpotential
    change f x + (b + c) = gaussianPotential (Ψ x)
    change (f x + c) + b = gaussianPotential (Ψ x) at hx
    rw [show f x + (b + c) = (f x + c) + b by ring]
    exact hx
  · rintro ⟨hσ, Ψ, b, hmetric, hpotential⟩
    refine ⟨hσ, Ψ, b - c, hmetric, ?_⟩
    apply ContMDiffMap.ext
    intro x
    have hx := congrArg (fun q : C^∞⟮I, M; Real⟯ => q x) hpotential
    change (f x + c) + (b - c) = gaussianPotential (Ψ x)
    change f x + b = gaussianPotential (Ψ x) at hx
    rw [show (f x + c) + (b - c) = f x + b by ring]
    exact hx

theorem isGaussianGradientRicciSoliton_euclidean :
    isGaussianGradientRicciSoliton
      (euclideanMetric (E := E)) (gaussianPotential (E := E)) 1 := by
  refine ⟨zero_lt_one, _root_.Diffeomorph.refl 𝓘(Real, E) E ∞, 0, ?_, ?_⟩
  · rw [Diffeomorph.pullbackMetricCross_refl]
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [scaleMetric_inner]
    ring
  · apply ContMDiffMap.ext
    intro x
    change gaussianPotential x + 0 = gaussianPotential x
    ring

end DifferentialGeometry.Geometry
