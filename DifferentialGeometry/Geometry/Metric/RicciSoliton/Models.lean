import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Metric.PullbackCross
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Normalized
import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentity
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciNaturalityCross
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Real.Sqrt

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

noncomputable def roundSphereShrinkerRadius (n : Nat) : Real :=
  Real.sqrt (2 * ((n : Real) - 1))

theorem roundSphereShrinkerRadius_pos {n : Nat} (hn : 2 ≤ n) :
    0 < roundSphereShrinkerRadius n := by
  rw [roundSphereShrinkerRadius, Real.sqrt_pos]
  have h : (1 : Real) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  positivity

theorem roundSphereShrinkerRadius_sq {n : Nat} (hn : 2 ≤ n) :
    roundSphereShrinkerRadius n ^ 2 = 2 * ((n : Real) - 1) := by
  rw [roundSphereShrinkerRadius, Real.sq_sqrt]
  exact le_of_lt (by
    have h : (1 : Real) < n := by
      exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
    positivity)

@[simp] theorem roundSphereShrinkerRadius_two :
    roundSphereShrinkerRadius 2 = Real.sqrt 2 := by
  norm_num [roundSphereShrinkerRadius]

@[simp] theorem roundSphereShrinkerRadius_three :
    roundSphereShrinkerRadius 3 = 2 := by
  norm_num [roundSphereShrinkerRadius]

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace Real A]
  [FiniteDimensional Real A]
variable {n : Nat} [Fact (Module.finrank Real A = n + 1)]

noncomputable def roundSphereShrinkerMetric (hn : 2 ≤ n) :
    SmoothRiemannianMetric (𝓡 n) (Metric.sphere (0 : A) 1) :=
  scaleMetric (roundSphereShrinkerRadius n ^ 2)
    (sq_pos_of_pos (roundSphereShrinkerRadius_pos hn))
    (roundMetric (E := A) (n := n))

noncomputable def roundSphereShrinkerPotential :
    C^∞⟮𝓡 n, Metric.sphere (0 : A) 1; Real⟯ :=
  ContMDiffMap.const ((n : Real) / 2)

omit [FiniteDimensional Real A] in
@[simp] theorem roundSphereShrinkerPotential_apply
    (x : Metric.sphere (0 : A) 1) :
    roundSphereShrinkerPotential (A := A) (n := n) x = (n : Real) / 2 := by
  rfl

omit [FiniteDimensional Real A] in
theorem roundSphereShrinkerMetric_ricciTensor
    (hn : 2 ≤ n) (x : Metric.sphere (0 : A) 1)
    (v w : TangentSpace (𝓡 n) x) :
    ricciTensor (I := 𝓡 n) (roundSphereShrinkerMetric (A := A) hn) x v w =
      (1 / 2 : Real) *
        (roundSphereShrinkerMetric (A := A) hn).inner x v w := by
  let : NeZero n :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (Nat.zero_lt_succ 1) hn)⟩
  rw [roundSphereShrinkerMetric, Curvature.ricciTensor_scaleMetric,
    roundMetric_ricciTensor, scaleMetric_inner,
    roundSphereShrinkerRadius_sq hn]
  ring

omit [FiniteDimensional Real A] in
theorem roundSphereShrinkerPotential_hessian
    (hn : 2 ≤ n) (x : Metric.sphere (0 : A) 1)
    (v w : TangentSpace (𝓡 n) x) :
    hessFun (I := 𝓡 n) (roundSphereShrinkerMetric (A := A) hn)
        (roundSphereShrinkerPotential (A := A) (n := n)) x v w = 0 := by
  change hessFun (I := 𝓡 n) (roundSphereShrinkerMetric (A := A) hn)
      (fun _ : Metric.sphere (0 : A) 1 => (n : Real) / 2) x v w = 0
  rw [Connection.hessFun_eq_abstract
    (roundSphereShrinkerMetric (A := A) hn) contMDiff_const x v w]
  rw [Connection.abstractHessian_apply]
  have hderiv : mvfderiv (I := 𝓡 n)
      (fun _ : Metric.sphere (0 : A) 1 => (n : Real) / 2) =
        fun _ => 0 := by
    funext y
    exact mvfderiv_const (I := 𝓡 n)
      (M := Metric.sphere (0 : A) 1) ((n : Real) / 2) (x := y)
  rw [hderiv]
  let cov := Connection.cotangentCov
    (Connection.LeviCivita (I := 𝓡 n)
      (roundSphereShrinkerMetric (A := A) hn))
  change ((cov.toFun
    (fun y : Metric.sphere (0 : A) 1 =>
      (0 : TangentSpace (𝓡 n) y →L[Real] Real)) x v) w) = 0
  have hzero : cov.toFun
      (fun y : Metric.sphere (0 : A) 1 =>
        (0 : TangentSpace (𝓡 n) y →L[Real] Real)) x = 0 := by
    exact congrArg (fun φ => φ x) cov.zero
  rw [hzero]
  rfl

omit [FiniteDimensional Real A] in
theorem gradientRicciSoliton_roundSphere (hn : 2 ≤ n) :
    gradientRicciSoliton (I := 𝓡 n)
      (roundSphereShrinkerMetric (A := A) hn)
      (roundSphereShrinkerPotential (A := A) (n := n)) 1 := by
  intro x v w
  rw [roundSphereShrinkerMetric_ricciTensor hn,
    roundSphereShrinkerPotential_hessian hn]
  ring

theorem roundSphereShrinkerMetric_complete (hn : 2 ≤ n) :
    RiemannianMetricComplete (I := 𝓡 n)
      (roundSphereShrinkerMetric (A := A) hn) := by
  let : CompactSpace (Metric.sphere (0 : A) 1) :=
    Metric.sphere.compactSpace 0 1
  have hround : RiemannianMetricComplete (I := 𝓡 n)
      (roundMetric (E := A) (n := n)) := by
    refine ⟨?_⟩
    infer_instance
  exact RiemannianMetricComplete.scaleMetric
    hround
    (roundSphereShrinkerRadius n ^ 2)
    (sq_pos_of_pos (roundSphereShrinkerRadius_pos hn))

omit [FiniteDimensional Real A] in
theorem roundSphereShrinkerMetric_scalarCurvature
    (hn : 2 ≤ n) (x : Metric.sphere (0 : A) 1) :
    metricScalarAt (I := 𝓡 n) (roundSphereShrinkerMetric (A := A) hn) x =
      (n : Real) / 2 := by
  have h := gradientRicciSoliton_trace
    (gradientRicciSoliton_roundSphere (A := A) hn) x
  rw [show roundSphereShrinkerPotential (A := A) (n := n) =
      ContMDiffMap.const ((n : Real) / 2) by rfl,
    Operator.Δ_g_const] at h
  simpa [finrank_euclideanSpace_fin] using h

omit [FiniteDimensional Real A] in
theorem roundSphereShrinkerPotential_normGradSqFun
    (hn : 2 ≤ n) (x : Metric.sphere (0 : A) 1) :
    normGradSqFun (I := 𝓡 n) (roundSphereShrinkerMetric (A := A) hn)
        (roundSphereShrinkerPotential (A := A) (n := n)) x = 0 := by
  change normGradSqFun (I := 𝓡 n) (roundSphereShrinkerMetric (A := A) hn)
      (fun _ : Metric.sphere (0 : A) 1 => (n : Real) / 2) x = 0
  rw [normGradSqFun_def, Operator.gradFun_const]
  simp

theorem normalizedGradientRicciSoliton_roundSphere (hn : 2 ≤ n) :
    normalizedGradientRicciSoliton (I := 𝓡 n)
      (roundSphereShrinkerMetric (A := A) hn)
      (roundSphereShrinkerPotential (A := A) (n := n)) := by
  refine ⟨roundSphereShrinkerMetric_complete (A := A) hn,
    gradientRicciSoliton_roundSphere (A := A) hn, ?_⟩
  intro x
  rw [roundSphereShrinkerMetric_scalarCurvature hn,
    roundSphereShrinkerPotential_normGradSqFun hn,
    roundSphereShrinkerPotential_apply]
  ring

theorem roundSphere_hamiltonNormalized (hn : 2 ≤ n) :
    hamiltonNormalized (I := 𝓡 n)
      (roundSphereShrinkerMetric (A := A) hn)
      (roundSphereShrinkerPotential (A := A) (n := n)) 1 :=
  normalizedGradientRicciSoliton_hamilton_normalized
    (normalizedGradientRicciSoliton_roundSphere (A := A) hn)

noncomputable def roundTwoSphereShrinkerMetric :
    SmoothRiemannianMetric (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  exact roundSphereShrinkerMetric
    (A := EuclideanSpace Real (Fin 3)) (n := 2) (by decide)

noncomputable def roundTwoSphereShrinkerPotential :
    C^∞⟮𝓡 2, Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1; Real⟯ :=
  ContMDiffMap.const 1

@[simp] theorem roundTwoSphereShrinkerPotential_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    roundTwoSphereShrinkerPotential x = 1 := by
  rfl

theorem normalizedGradientRicciSoliton_roundTwoSphere :
    normalizedGradientRicciSoliton (I := 𝓡 2)
      roundTwoSphereShrinkerMetric roundTwoSphereShrinkerPotential := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  simpa [roundTwoSphereShrinkerMetric, roundTwoSphereShrinkerPotential,
    roundSphereShrinkerPotential] using
    (normalizedGradientRicciSoliton_roundSphere
      (A := EuclideanSpace Real (Fin 3)) (n := 2) (by decide))

theorem roundTwoSphereShrinkerMetric_scalarCurvature
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    metricScalarAt (I := 𝓡 2) roundTwoSphereShrinkerMetric x = 1 := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  simpa [roundTwoSphereShrinkerMetric] using
    (roundSphereShrinkerMetric_scalarCurvature
      (A := EuclideanSpace Real (Fin 3)) (n := 2) (by decide) x)

theorem roundTwoSphere_hamiltonNormalized :
    hamiltonNormalized (I := 𝓡 2)
      roundTwoSphereShrinkerMetric roundTwoSphereShrinkerPotential 1 :=
  normalizedGradientRicciSoliton_hamilton_normalized
    normalizedGradientRicciSoliton_roundTwoSphere

noncomputable def roundThreeSphereShrinkerMetric :
    SmoothRiemannianMetric (𝓡 3)
      (Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 4)) = 3 + 1) :=
    ⟨by simp⟩
  exact roundSphereShrinkerMetric
    (A := EuclideanSpace Real (Fin 4)) (n := 3) (by decide)

noncomputable def roundThreeSphereShrinkerPotential :
    C^∞⟮𝓡 3, Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1; Real⟯ :=
  ContMDiffMap.const (3 / 2 : Real)

@[simp] theorem roundThreeSphereShrinkerPotential_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) :
    roundThreeSphereShrinkerPotential x = (3 / 2 : Real) := by
  rfl

theorem normalizedGradientRicciSoliton_roundThreeSphere :
    normalizedGradientRicciSoliton (I := 𝓡 3)
      roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 4)) = 3 + 1) :=
    ⟨by simp⟩
  simpa [roundThreeSphereShrinkerMetric, roundThreeSphereShrinkerPotential,
    roundSphereShrinkerPotential] using
    (normalizedGradientRicciSoliton_roundSphere
      (A := EuclideanSpace Real (Fin 4)) (n := 3) (by decide))

theorem roundThreeSphereShrinkerMetric_scalarCurvature
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) :
    metricScalarAt (I := 𝓡 3) roundThreeSphereShrinkerMetric x =
      (3 / 2 : Real) := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 4)) = 3 + 1) :=
    ⟨by simp⟩
  simpa [roundThreeSphereShrinkerMetric] using
    (roundSphereShrinkerMetric_scalarCurvature
      (A := EuclideanSpace Real (Fin 4)) (n := 3) (by decide) x)

theorem roundThreeSphere_hamiltonNormalized :
    hamiltonNormalized (I := 𝓡 3)
      roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential 1 :=
  normalizedGradientRicciSoliton_hamilton_normalized
    normalizedGradientRicciSoliton_roundThreeSphere

noncomputable def roundThreeCylinderShrinkerMetric :
    SmoothRiemannianMetric ((𝓡 2).prod 𝓘(Real, Real))
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :=
  roundTwoSphereShrinkerMetric.prod (euclideanMetric (E := Real))

noncomputable def roundThreeCylinderShrinkerPotential :
    C^∞⟮(𝓡 2).prod 𝓘(Real, Real),
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real; Real⟯ :=
  roundTwoSphereShrinkerPotential.comp ContMDiffMap.fst +
    gaussianPotential.comp ContMDiffMap.snd

@[simp] theorem roundThreeCylinderShrinkerPotential_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    roundThreeCylinderShrinkerPotential x = 1 + x.2 ^ 2 / 4 := by
  change roundTwoSphereShrinkerPotential x.1 + gaussianPotential x.2 = _
  rw [roundTwoSphereShrinkerPotential_apply, gaussianPotential_apply]
  simp [Real.norm_eq_abs]

def roundThreeCylinderCentralSlice :
    Set (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :=
  {x | x.2 = 0}

@[simp] theorem mem_roundThreeCylinderCentralSlice
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    x ∈ roundThreeCylinderCentralSlice ↔ x.2 = 0 :=
  Iff.rfl

theorem roundThreeCylinderShrinkerPotential_eq_one_iff
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    roundThreeCylinderShrinkerPotential x = 1 ↔
      x ∈ roundThreeCylinderCentralSlice := by
  rw [roundThreeCylinderShrinkerPotential_apply,
    mem_roundThreeCylinderCentralSlice]
  constructor
  · intro h
    nlinarith [sq_nonneg x.2]
  · intro h
    rw [h]
    norm_num

theorem roundThreeCylinderCentralSlice_preimage_eq_of_potential_preserving
    (γ : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real →
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (hγ : ∀ x, roundThreeCylinderShrinkerPotential (γ x) =
      roundThreeCylinderShrinkerPotential x) :
    γ ⁻¹' roundThreeCylinderCentralSlice =
      roundThreeCylinderCentralSlice := by
  ext x
  calc
    x ∈ γ ⁻¹' roundThreeCylinderCentralSlice ↔
        roundThreeCylinderShrinkerPotential (γ x) = 1 :=
      roundThreeCylinderShrinkerPotential_eq_one_iff (γ x) |>.symm
    _ ↔ roundThreeCylinderShrinkerPotential x = 1 := by rw [hγ x]
    _ ↔ x ∈ roundThreeCylinderCentralSlice :=
      roundThreeCylinderShrinkerPotential_eq_one_iff x

theorem gradientRicciSoliton_roundThreeCylinder :
    gradientRicciSoliton (I := (𝓡 2).prod 𝓘(Real, Real))
      roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential 1 := by
  simpa [roundThreeCylinderShrinkerMetric,
    roundThreeCylinderShrinkerPotential] using
    gradientRicciSoliton_prod
      normalizedGradientRicciSoliton_roundTwoSphere.2.1
      (gradientRicciSoliton_gaussian (E := Real))

theorem roundThreeCylinderShrinkerMetric_complete :
    RiemannianMetricComplete (I := (𝓡 2).prod 𝓘(Real, Real))
      roundThreeCylinderShrinkerMetric := by
  simpa [roundThreeCylinderShrinkerMetric] using
    RiemannianMetricComplete.prod
      normalizedGradientRicciSoliton_roundTwoSphere.1
      (normalizedGradientRicciSoliton_gaussian (E := Real)).1

theorem roundThreeCylinderShrinkerMetric_scalarCurvature
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    metricScalarAt (I := (𝓡 2).prod 𝓘(Real, Real))
      roundThreeCylinderShrinkerMetric x = 1 := by
  rw [roundThreeCylinderShrinkerMetric, Curvature.metricScalarAt_prod,
    roundTwoSphereShrinkerMetric_scalarCurvature,
    euclideanMetric_scalarCurvature]
  ring

theorem roundThreeCylinderShrinkerPotential_normGradSqFun
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    normGradSqFun (I := (𝓡 2).prod 𝓘(Real, Real))
        roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential x =
      x.2 ^ 2 / 4 := by
  have hsphere := normalizedGradientRicciSoliton_roundTwoSphere.2.2 x.1
  rw [roundTwoSphereShrinkerMetric_scalarCurvature,
    roundTwoSphereShrinkerPotential_apply] at hsphere
  have hnorm : normGradSqFun (I := 𝓡 2) roundTwoSphereShrinkerMetric
      roundTwoSphereShrinkerPotential x.1 = 0 := by
    linarith [hsphere]
  change normGradSqFun (I := (𝓡 2).prod 𝓘(Real, Real))
      (roundTwoSphereShrinkerMetric.prod (euclideanMetric (E := Real)))
      (fun q : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real =>
        roundTwoSphereShrinkerPotential q.1 + gaussianPotential q.2) x = _
  rw [Operator.normGradSqFun_prod, hnorm,
    gaussianPotential_normGradSqFun, gaussianPotential_apply]
  simp [Real.norm_eq_abs]

theorem normalizedGradientRicciSoliton_roundThreeCylinder :
    normalizedGradientRicciSoliton
      (I := (𝓡 2).prod 𝓘(Real, Real))
      roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential := by
  simpa [roundThreeCylinderShrinkerMetric,
    roundThreeCylinderShrinkerPotential] using
    normalizedGradientRicciSoliton_prod
      normalizedGradientRicciSoliton_roundTwoSphere
      (normalizedGradientRicciSoliton_gaussian (E := Real))

theorem roundThreeCylinder_hamiltonNormalized :
    hamiltonNormalized (I := (𝓡 2).prod 𝓘(Real, Real))
      roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential 1 :=
  normalizedGradientRicciSoliton_hamilton_normalized
    normalizedGradientRicciSoliton_roundThreeCylinder

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

theorem isGaussianGradientRicciSoliton_scaleMetric
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (hσ : 0 < σ) :
    isGaussianGradientRicciSoliton (E := E)
        (scaleMetric (I := I) σ hσ g) f 1 ↔
      isGaussianGradientRicciSoliton (E := E) g f σ := by
  constructor
  · rintro ⟨hone, Ψ, b, hmetric, hpotential⟩
    refine ⟨hσ, Ψ, b, ?_, hpotential⟩
    calc
      Diffeomorph.pullbackMetricCross euclideanMetric Ψ =
          scaleMetric (I := I) 1 hone
            (scaleMetric (I := I) σ hσ g) := hmetric
      _ = scaleMetric (I := I) σ hσ g := by
        apply SmoothRiemannianMetric.ext_inner
        intro x v w
        simp only [scaleMetric_inner, one_mul]
  · rintro ⟨hσ', Ψ, b, hmetric, hpotential⟩
    refine ⟨zero_lt_one, Ψ, b, ?_, hpotential⟩
    calc
      Diffeomorph.pullbackMetricCross euclideanMetric Ψ =
          scaleMetric (I := I) σ hσ' g := hmetric
      _ = scaleMetric (I := I) 1 zero_lt_one
          (scaleMetric (I := I) σ hσ g) := by
        apply SmoothRiemannianMetric.ext_inner
        intro x v w
        simp only [scaleMetric_inner, one_mul]

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

theorem isGaussianGradientRicciSoliton_ricciTensor_eq_zero
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (hGaussian : isGaussianGradientRicciSoliton (E := E) g f σ)
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) g x v w = 0 := by
  obtain ⟨hσ, Ψ, b, hmetric, hpotential⟩ := hGaussian
  have hRicci := Curvature.ricciTensor_pullbackCross
    (g := euclideanMetric (E := E)) Ψ x v w
  rw [euclideanMetric_ricciTensor] at hRicci
  rw [hmetric, Curvature.ricciTensor_scaleMetric] at hRicci
  exact hRicci

theorem isGaussianGradientRicciSoliton_scalarCurvature_eq_zero
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (hGaussian : isGaussianGradientRicciSoliton (E := E) g f σ)
    (x : M) :
    metricScalarAt (I := I) g x = 0 := by
  apply metricScalarAt_eq_zero_of_ricciTensor_eq_zero
  exact isGaussianGradientRicciSoliton_ricciTensor_eq_zero hGaussian x

end DifferentialGeometry.Geometry
