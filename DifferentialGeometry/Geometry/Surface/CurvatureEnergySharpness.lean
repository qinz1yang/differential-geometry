import DifferentialGeometry.Geometry.Surface.CurvatureEnergyIdentity
import DifferentialGeometry.Geometry.Metric.Conformal
import DifferentialGeometry.Geometry.Metric.Sphere.RoundProjConnLC
import DifferentialGeometry.Geometry.Metric.Sphere.RoundChartGram
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Operator.HessianTraceRealization
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.TotalNabla0S
import DifferentialGeometry.Geometry.Metric.Sphere.QuotientDescent
import DifferentialGeometry.Geometry.Curvature.Sphere.RoundGaussCurvature
import DifferentialGeometry.Geometry.Surface.ConformalGaussCurvature
import DifferentialGeometry.Geometry.Metric.Sphere.RoundZonalIntegral
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.ConformalScaling
import DifferentialGeometry.Analysis.Integration.Measure.ConformalScaling
import DifferentialGeometry.Tensor.RSTensor.NormSqProduct
import DifferentialGeometry.Geometry.Operator.LaplacianBridge
import DifferentialGeometry.Tensor.Multilinear.DomDomCongrSection

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open MeasureTheory
open Bundle Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian.Forms
open DifferentialGeometry.Integral.DivergenceTheorem
open Metric
open scoped Manifold ContDiff BigOperators

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [I.Boundaryless] [BoundarylessManifold I M]
variable [CompactSpace M] [T2Space M] [SigmaCompactSpace M]

def curvatureEnergy (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M))
    (nablaH : TwoTensorSection (I := I) (M := M))
    (nabla2H : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) : Real :=
  (∫ x, normSq0S (I := I) g x 1
        (roughLap0STensor (I := I) g (s := 1) (nabla2H x))
      ∂(riemannianVolumeMeasure (I := I) (M := M) g))
    - (∫ x, gaussCurvature (I := I) g x * normSq0S (I := I) g x 2 (nablaH x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g))
    - (∫ x, inner0S (I := I) g x 2 (oneFormReaction2D (I := I) g (h x)) (nablaH x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g))

end General

section Sphere

local instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

def sphereHeight (p : sphere (0 : EuclideanSpace Real (Fin 3)) 1) : Real :=
  innerCoordFun (E := EuclideanSpace Real (Fin 3)) (n := 2)
    (EuclideanSpace.single (2 : Fin 3) (1 : Real)) p

theorem sphereHeight_contMDiff :
    ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ sphereHeight :=
  (innerCoordFun (E := EuclideanSpace Real (Fin 3)) (n := 2)
    (EuclideanSpace.single (2 : Fin 3) (1 : Real))).contMDiff

def legendreConformalFactor (ε : Real)
    (p : sphere (0 : EuclideanSpace Real (Fin 3)) 1) : Real :=
  ε * ((3 * sphereHeight p ^ 2 - 1) / 2)

theorem legendreConformalFactor_contMDiff (ε : Real) :
    ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (legendreConformalFactor ε) :=
  contMDiff_const.mul
    (((contMDiff_const.mul (sphereHeight_contMDiff.pow 2)).sub contMDiff_const).div_const 2)

def sphereConformalMetric (ε : Real) :
    SmoothRiemannianMetric (𝓡 2) (sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
  conformalMetric (legendreConformalFactor ε) (legendreConformalFactor_contMDiff ε)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))

def sphereHeightOneForm :
    OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
  duSec (I := 𝓡 2) sphereHeight sphereHeight_contMDiff

def sphereConformalDerivs (ε : Real) :
    CanonicalSpatialDerivs0S (𝕜 := Real)
      (metricCov (I := 𝓡 2) (sphereConformalMetric ε)) sphereHeightOneForm :=
  CanonicalSpatialDerivs0S.of_smooth_connection
    (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
    (metricCov_smooth (I := 𝓡 2) (sphereConformalMetric ε))
    sphereHeightOneForm

def sphereCurvatureEnergy (ε : Real) : Real :=
  curvatureEnergy (sphereConformalMetric ε) sphereHeightOneForm
    (sphereConformalDerivs ε).nablaA
    (fun x => (sphereConformalDerivs ε).nabla2A x)

private theorem sphereConformalMetric_zero_eq :
    sphereConformalMetric 0
      = roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2) := by
  apply DifferentialGeometry.Geometry.SmoothRiemannianMetric.ext'
  intro x v w
  rw [sphereConformalMetric, conformalMetric_inner]
  rw [show (2 : Real) * (legendreConformalFactor 0 x) = 0 by
        simp [legendreConformalFactor]]
  rw [Real.exp_zero, one_mul]

section SphereHessian

open scoped RealInnerProductSpace

private theorem swapSlots0S_apply'
    {x : sphere (0 : EuclideanSpace Real (Fin 3)) 1}
    (A : Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) 2 x)
    (v : Fin 2 → TangentSpace (𝓡 2) x) :
    swapSlots0S (I := 𝓡 2) A v = A (fun i => v (Equiv.swap (0 : Fin 2) 1 i)) := by
  change A (fun i => v ((Equiv.swap (0 : Fin 2) 1).symm i))
      = A (fun i => v (Equiv.swap (0 : Fin 2) 1 i))
  rw [Equiv.symm_swap]

private theorem trace_oneform_metric
    (g : SmoothRiemannianMetric (𝓡 2) (sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : sphere (0 : EuclideanSpace Real (Fin 3)) 1}
    (basis : Module.Basis Idx Real (TangentSpace (𝓡 2) x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis_gen (I := 𝓡 2) g x basis gInv)
    (A : Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) 1 x)
    (w : TangentSpace (𝓡 2) x) :
    (∑ i : Idx, ∑ j : Idx,
        gInv i j * (A (fun _ : Fin 1 => basis i) * g.inner x (basis j) w))
      = A (fun _ : Fin 1 => w) := by
  classical
  set L : TangentSpace (𝓡 2) x →L[Real] Real :=
    continuousMultilinearCurryFin1 Real (TangentSpace (𝓡 2) x) Real A with hLdef
  have hLA : ∀ v : TangentSpace (𝓡 2) x, A (fun _ : Fin 1 => v) = L v := by
    intro v
    rw [hLdef, continuousMultilinearCurryFin1_apply]
    exact congrArg (⇑A) (Fin.snoc_zero _ v).symm
  have hexp : ∀ j : Idx,
      g.inner x (basis j) w = ∑ k : Idx, basis.repr w k * g.inner x (basis j) (basis k) := by
    intro j
    conv_lhs => rw [← basis.sum_repr w]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul, smul_eq_mul]
  have hcoord : ∀ i : Idx,
      (∑ j : Idx, gInv i j * g.inner x (basis j) w) = basis.repr w i := by
    intro i
    calc
      (∑ j : Idx, gInv i j * g.inner x (basis j) w)
          = ∑ j : Idx, ∑ k : Idx,
              basis.repr w k * (gInv i j * g.inner x (basis j) (basis k)) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hexp j, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = ∑ k : Idx, basis.repr w k *
              (∑ j : Idx, gInv i j * g.inner x (basis j) (basis k)) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
      _ = ∑ k : Idx, basis.repr w k * (if i = k then (1 : Real) else 0) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [(hinv i k).1]
      _ = basis.repr w i := by
            rw [Finset.sum_congr rfl (fun k _ => by rw [mul_ite, mul_one, mul_zero])]
            rw [Finset.sum_ite_eq Finset.univ i (fun k => basis.repr w k)]
            simp
  calc
    (∑ i : Idx, ∑ j : Idx,
        gInv i j * (A (fun _ : Fin 1 => basis i) * g.inner x (basis j) w))
        = ∑ i : Idx, A (fun _ : Fin 1 => basis i) *
            (∑ j : Idx, gInv i j * g.inner x (basis j) w) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ∑ i : Idx, A (fun _ : Fin 1 => basis i) * basis.repr w i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hcoord i]
    _ = ∑ i : Idx, basis.repr w i • L (basis i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hLA (basis i), smul_eq_mul]
          ring
    _ = L (∑ i : Idx, basis.repr w i • basis i) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [map_smul]
    _ = L w := by rw [basis.sum_repr w]
    _ = A (fun _ : Fin 1 => w) := (hLA w).symm

private theorem sphereGrad_dIncl
    (p : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    dIncl (n := 2)
        p (gradientFun (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
            sphereHeight p)
      = (EuclideanSpace.single (2 : Fin 3) (1 : Real))
        - ⟪(EuclideanSpace.single (2 : Fin 3) (1 : Real)),
            (↑p : EuclideanSpace Real (Fin 3))⟫
          • (↑p : EuclideanSpace Real (Fin 3)) := by
  have hincl_mem : ∀ v : TangentSpace (𝓡 2) p,
      dIncl (n := 2) p v ∈ (Real ∙ (↑p : EuclideanSpace Real (Fin 3)))ᗮ := by
    intro v
    rw [← range_mfderiv_coe_sphere (n := 2) p]
    exact ⟨v, rfl⟩
  set e₃ : EuclideanSpace Real (Fin 3) := EuclideanSpace.single (2 : Fin 3) (1 : Real) with he3
  set a : EuclideanSpace Real (Fin 3) :=
    dIncl (n := 2) p (gradientFun (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
      sphereHeight p) with ha
  set b : EuclideanSpace Real (Fin 3) := e₃ - ⟪e₃, (↑p : EuclideanSpace Real (Fin 3))⟫ • (↑p)
    with hb
  have hnorm : ‖(↑p : EuclideanSpace Real (Fin 3))‖ = 1 := norm_eq_of_mem_sphere p
  have key1 : ∀ v : TangentSpace (𝓡 2) p,
      ⟪a, dIncl (n := 2) p v⟫ = ⟪b, dIncl (n := 2) p v⟫ := by
    intro v
    have ha' : ⟪a, dIncl (n := 2) p v⟫ = ⟪e₃, dIncl (n := 2) p v⟫ := by
      have h1 : ⟪a, dIncl (n := 2) p v⟫
          = (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner p
              (gradientFun (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) sphereHeight p)
              v := by
        rw [ha, roundMetric_inner]
      rw [h1, inner_gradientFun]
      exact mfderiv_innerCoordFun (E := EuclideanSpace Real (Fin 3)) (n := 2) e₃ p v
    have hb' : ⟪b, dIncl (n := 2) p v⟫ = ⟪e₃, dIncl (n := 2) p v⟫ := by
      rw [hb, inner_sub_left, real_inner_smul_left]
      have hperp : ⟪(↑p : EuclideanSpace Real (Fin 3)), dIncl (n := 2) p v⟫ = 0 :=
        Submodule.inner_right_of_mem_orthogonal
          (Submodule.mem_span_singleton_self _) (hincl_mem v)
      rw [hperp]
      simp
    rw [ha', hb']
  have hb_mem : b ∈ (Real ∙ (↑p : EuclideanSpace Real (Fin 3)))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, hb, inner_sub_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hnorm,
      real_inner_comm (↑p : EuclideanSpace Real (Fin 3)) e₃]
    ring
  have ha_mem : a ∈ (Real ∙ (↑p : EuclideanSpace Real (Fin 3)))ᗮ := by
    rw [ha]; exact hincl_mem _
  have hdiff_mem : a - b ∈ (Real ∙ (↑p : EuclideanSpace Real (Fin 3)))ᗮ :=
    Submodule.sub_mem _ ha_mem hb_mem
  obtain ⟨v0, hv0⟩ := (range_mfderiv_coe_sphere (n := 2) p).ge hdiff_mem
  have hzero : ⟪a - b, a - b⟫ = 0 := by
    nth_rewrite 2 [show (a - b) = dIncl (n := 2) p v0 from hv0.symm]
    rw [inner_sub_left, key1 v0, sub_self]
  have hab : a - b = 0 := inner_self_eq_zero.mp hzero
  exact sub_eq_zero.mp hab

private theorem sphere_ambDeriv_grad_inner
    (y : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (v w : TangentSpace (𝓡 2) y) :
    ⟪ambDeriv (n := 2)
        (fun z => gradientFun (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
          sphereHeight z) y v,
        dIncl (n := 2) y w⟫
      = -(sphereHeight y) *
          roundInner (n := 2) y v w := by
  set e₃ : EuclideanSpace Real (Fin 3) := EuclideanSpace.single (2 : Fin 3) (1 : Real) with he3
  set u : EuclideanSpace Real (Fin 3) := dIncl (n := 2) y w with hu
  have hSm : MDifferentiableAt (𝓡 2) (𝓡 2).tangent
      (fun z => (TotalSpace.mk' (EuclideanSpace Real (Fin 2)) z
        (gradientFun (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) sphereHeight z))) y :=
    gradientFun_mdiffAt (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) sphereHeight_contMDiff y
  have hFm : MDifferentiableAt (𝓡 2) 𝓘(Real, EuclideanSpace Real (Fin 3))
      (dInclField (n := 2)
        (fun z => gradientFun (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
          sphereHeight z)) y := dInclField_mdifferentiableAt (n := 2) hSm
  have hstart : ⟪ambDeriv (n := 2)
        (fun z => gradientFun (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
          sphereHeight z) y v, u⟫
      = mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => ⟪u,
          dInclField (n := 2)
            (fun z => gradientFun (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
              sphereHeight z) q⟫) y v := by
    rw [ambDeriv_apply, real_inner_comm]
    exact (mfderiv_inner_left (n := 2) u hFm v).symm
  have hfun : (fun q => ⟪u,
        dInclField (n := 2)
          (fun z => gradientFun (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
            sphereHeight z) q⟫)
      = fun q => (⟪u, e₃⟫ : Real)
          - (innerCoordFun (E := EuclideanSpace Real (Fin 3)) (n := 2) e₃) q
            * (innerCoordFun (E := EuclideanSpace Real (Fin 3)) (n := 2) u) q := by
    funext q
    change ⟪u, dIncl (n := 2) q
        (gradientFun (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) sphereHeight q)⟫
      = (⟪u, e₃⟫ : Real)
        - (innerCoordFun (E := EuclideanSpace Real (Fin 3)) (n := 2) e₃) q
          * (innerCoordFun (E := EuclideanSpace Real (Fin 3)) (n := 2) u) q
    rw [sphereGrad_dIncl q, inner_sub_right, real_inner_smul_right]
    rfl
  have hprodDiff : MDifferentiableAt (𝓡 2) 𝓘(Real, Real)
      (fun q => (innerCoordFun (E := EuclideanSpace Real (Fin 3)) (n := 2) e₃) q
        * (innerCoordFun (E := EuclideanSpace Real (Fin 3)) (n := 2) u) q) y :=
    (((innerCoordFun (E := EuclideanSpace Real (Fin 3)) (n := 2) e₃).contMDiff.mul
        (innerCoordFun (E := EuclideanSpace Real (Fin 3)) (n := 2) u).contMDiff).contMDiffAt).mdifferentiableAt
      (by simp)
  have hφdiff : MDifferentiableAt (𝓡 2) 𝓘(Real, Real)
      (fun q => (innerCoordFun (E := EuclideanSpace Real (Fin 3)) (n := 2) e₃) q) y :=
    ((innerCoordFun (E := EuclideanSpace Real (Fin 3)) (n := 2) e₃).contMDiff.contMDiffAt).mdifferentiableAt
      (by simp)
  have horth : ⟪u, (↑y : EuclideanSpace Real (Fin 3))⟫ = 0 := by
    rw [hu, real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal
      (Submodule.mem_span_singleton_self _)
      (by rw [← range_mfderiv_coe_sphere (n := 2) y]; exact ⟨w, rfl⟩)
  have hz : (innerCoordFun (E := EuclideanSpace Real (Fin 3)) (n := 2) e₃) y = sphereHeight y := rfl
  have hinnerval : ⟪u, dIncl (n := 2) y v⟫ = roundInner (n := 2) y v w := by
    rw [hu, roundInner_apply]
    exact real_inner_comm _ _
  have hconst0 : extDerivFun (I := 𝓡 2)
      (fun _ : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => (⟪u, e₃⟫ : Real)) y v = 0 := by
    rw [extDerivFun_real_eq_mfderiv, mfderiv_const]
    rfl
  rw [hstart, ← extDerivFun_real_eq_mfderiv (𝓡 2) _ y v, hfun,
    extDerivFun_sub_at v
      (mdifferentiableAt_const (I := 𝓡 2) (I' := 𝓘(Real, Real)) (c := ⟪u, e₃⟫)) hprodDiff,
    hconst0, zero_sub, extDerivFun_real_eq_mfderiv (𝓡 2) _ y v,
    mfderiv_mul_innerCoordFun_of_inner_eq_zero (n := 2) u hφdiff horth v, hz, hinnerval]
  ring

private theorem sphereNablaA_eq
    (y : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    (sphereConformalDerivs 0).nablaA y
      = (-(sphereHeight y)) •
          metricTensor0S (I := 𝓡 2)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) y := by
  have hcov_eq : metricCov (I := 𝓡 2) (sphereConformalMetric 0)
      = metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) :=
    congrArg (metricCov (I := 𝓡 2)) sphereConformalMetric_zero_eq
  have hcovsm := metricCov_smooth (I := 𝓡 2)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
  have h1 : TotalNabla0SRealizes (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
      (I := 𝓡 2) 1
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      sphereHeightOneForm ((sphereConformalDerivs 0).nablaA) := by
    rw [← hcov_eq]; exact (sphereConformalDerivs 0).first
  have h2 : TotalNabla0SRealizes (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
      (I := 𝓡 2) 1
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      (duSec (I := 𝓡 2) sphereHeight sphereHeight_contMDiff)
      (hessianSec (I := 𝓡 2)
        (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
        hcovsm sphereHeight sphereHeight_contMDiff) :=
    totalNabla0S_realizes 1
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      (duSec (I := 𝓡 2) sphereHeight sphereHeight_contMDiff)
      (totalNabla0S_reg 1
        (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
        hcovsm (duSec (I := 𝓡 2) sphereHeight sphereHeight_contMDiff))
  have hnablaeq : (sphereConformalDerivs 0).nablaA
      = hessianSec (I := 𝓡 2)
          (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
          hcovsm sphereHeight sphereHeight_contMDiff :=
    totalNabla0SRealizes_unique h1 h2
  have hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen
      (I := 𝓡 2)
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) :=
    leviCivitaConnectionOfMetric_isMetricCompatible (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
  have hkey : ∀ vv wv : TangentSpace (𝓡 2) y,
      hessianSec (I := 𝓡 2)
          (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
          hcovsm sphereHeight sphereHeight_contMDiff y (vec2 (I := 𝓡 2) vv wv)
        = -(sphereHeight y)
            * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner y vv wv := by
    intro vv wv
    rw [hessSec_inner_cov (I := 𝓡 2)
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      hcovsm (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) hmc
      sphereHeight sphereHeight_contMDiff y vv wv, roundMetric_inner,
      inner_dIncl_metricCov (n := 2)
        (gradientFun_mdiffAt (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) sphereHeight_contMDiff y) vv wv,
      sphere_ambDeriv_grad_inner y vv wv]
    rfl
  rw [hnablaeq]
  ext vv
  rw [show vv = vec2 (I := 𝓡 2) (vv 0) (vv 1) from by funext i; fin_cases i <;> rfl,
    hkey (vv 0) (vv 1)]
  change -(sphereHeight y) * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner y (vv 0) (vv 1)
      = -(sphereHeight y)
        * metricTensor0S (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) y
            (vec2 (I := 𝓡 2) (vv 0) (vv 1))
  rw [metricTensor0S_apply]
  rfl

private theorem ahlfors_smul_metric
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) (c : Real) :
    ahlforsOperator (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
        (c • metricTensor0S (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x) = 0 := by
  set g := roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2) with hg
  set M := metricTensor0S (I := 𝓡 2) g x with hM
  have hswapc : swapSlots0S (I := 𝓡 2) (c • M) = c • M := by
    ext vvv
    rw [swapSlots0S_apply']
    change c * (M (fun i => vvv (Equiv.swap (0 : Fin 2) 1 i))) = c * (M vvv)
    rw [hM, metricTensor0S_apply, metricTensor0S_apply]
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [g.symm x (vvv 1) (vvv 0)]
  have hsym : symmetricPart0S (I := 𝓡 2) (c • M) = c • M := by
    unfold symmetricPart0S
    rw [hswapc]
    module
  have htr : metricTracePair0SAt (I := 𝓡 2) g M = 2 := by
    rw [hM]
    unfold metricTracePair0SAt
    rw [← normSq0S_eq_inner,
      normSq0S_metricTensor0S_eq_card (I := 𝓡 2) g
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := 𝓡 2) x)
        (fun k l => DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
          (I := 𝓡 2) g x k l (extChartAt (𝓡 2) x x))
        (DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
          (I := 𝓡 2) g x)]
    have hc2 : Fintype.card
        (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
          (EuclideanSpace Real (Fin 2))) = 2 := by
      rw [← Module.finrank_eq_card_basis
        (DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := 𝓡 2) x)]
      exact finrank_euclideanSpace_fin
    rw [hc2]; norm_num
  have htrc : metricTracePair0SAt (I := 𝓡 2) g (c • M) = c * 2 := by
    have hstep : metricTracePair0SAt (I := 𝓡 2) g (c • M)
        = c * metricTracePair0SAt (I := 𝓡 2) g M := by
      unfold metricTracePair0SAt
      rw [inner0S_smul_right]
    rw [hstep, htr]
  unfold ahlforsOperator
  rw [hsym]
  unfold traceFreePart0S
  rw [htrc, ← hM,
    show (Module.finrank Real (EuclideanSpace Real (Fin 2)) : Real) = 2 from by
      rw [finrank_euclideanSpace_fin]; norm_num,
    show (2 : Real)⁻¹ * (c * 2) = c from by ring]
  exact sub_self _

end SphereHessian

set_option maxHeartbeats 800000 in
theorem sphereConformalDerivs_zero_nabla2A_roughLap
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    roughLap0STensor (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (s := 1)
        ((sphereConformalDerivs 0).nabla2A x)
      = -(sphereHeightOneForm x) := by
  have hnegf : ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun p => -(sphereHeight p)) := sphereHeight_contMDiff.neg
  set df : OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
    duSec (I := 𝓡 2) (fun p => -(sphereHeight p)) hnegf with hdfdef
  have hdf : ∀ (z : sphere (0 : EuclideanSpace Real (Fin 3)) 1) (vv : TangentSpace (𝓡 2) z),
      df z (fun _ : Fin 1 => vv)
        = extDerivFun (I := 𝓡 2) (fun p => -(sphereHeight p)) z vv := by
    intro z vv
    rw [hdfdef, duSec_apply]
    exact differential1FormFun_apply_eq_extDerivFun (I := 𝓡 2) (fun p => -(sphereHeight p)) z vv
  have hcov_eq : metricCov (I := 𝓡 2) (sphereConformalMetric 0)
      = metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) :=
    congrArg (metricCov (I := 𝓡 2)) sphereConformalMetric_zero_eq
  have hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen
      (I := 𝓡 2)
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) :=
    leviCivitaConnectionOfMetric_isMetricCompatible (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
  have hFieldEq : (sphereConformalDerivs 0).nablaA
      = tensor0SField_smulByFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
          (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) (s := 2)
          (fun p => -(sphereHeight p)) hnegf
          (metricTensorField (I := 𝓡 2)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) := by
    apply DFunLike.ext
    intro y
    rw [sphereNablaA_eq y, tensor0SField_smulByFun_apply, metricTrace_metricField_eq0S]
  have hsmul := nabla_smul_metric (I := 𝓡 2)
    (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) hmc
    (fun p => -(sphereHeight p)) hnegf df hdf
  have hsecond : TotalNabla0SRealizes (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
      (I := 𝓡 2) 2
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      (tensor0SField_smulByFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
        (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) (s := 2)
        (fun p => -(sphereHeight p)) hnegf
        (metricTensorField (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))))
      ((sphereConformalDerivs 0).nabla2A) := by
    rw [← hFieldEq, ← hcov_eq]
    exact (sphereConformalDerivs 0).second
  have hnabla2eq : MultilinearSection.product (𝕜 := Real)
        (F := EuclideanSpace Real (Fin 2)) (IB := 𝓡 2)
        (E := TangentSpace (𝓡 2)) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
        df (metricTensorField (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      = (sphereConformalDerivs 0).nabla2A :=
    totalNabla0SRealizes_unique hsmul hsecond
  ext ww
  set basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := 𝓡 2) x
    with hbasis
  set gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
        (EuclideanSpace Real (Fin 2))
      → DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
          (EuclideanSpace Real (Fin 2)) → Real :=
    fun k l => DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x k l
      (extChartAt (𝓡 2) x x) with hgInv
  have hinv : MetricInverseInBasis_gen (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x basis gInv :=
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
  rw [← hnabla2eq, roughLap0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) basis gInv hinv _ ww]
  unfold metricTrace0S2InBasis
  have hprodval : ∀ X Y : TangentSpace (𝓡 2) x,
      MultilinearSection.product (𝕜 := Real)
        (F := EuclideanSpace Real (Fin 2)) (IB := 𝓡 2)
        (E := TangentSpace (𝓡 2)) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
        df (metricTensorField (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x
          (metricTraceInput (I := 𝓡 2) X Y ww)
        = df x (fun _ : Fin 1 => X)
          * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x Y (ww 0) := by
    intro X Y
    change Bundle.continuousMultilinearMap.product_fun (df x)
        (metricTensorField (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x)
        (metricTraceInput (I := 𝓡 2) X Y ww) = _
    rw [metricTrace_metricField_eq0S, Bundle.continuousMultilinearMap.product_fun_apply]
    have hL : metricTraceInput (I := 𝓡 2) X Y ww ∘ Fin.castAdd 2 = fun _ : Fin 1 => X := by
      funext a; fin_cases a; rfl
    have hR : metricTraceInput (I := 𝓡 2) X Y ww ∘ Fin.natAdd 1 = Fin.cons Y ww := by
      funext a; fin_cases a <;> rfl
    rw [hL, hR]
    change df x (fun _ : Fin 1 => X)
        * metricTensor0S (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
            (Fin.cons Y ww)
      = df x (fun _ : Fin 1 => X)
        * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x Y (ww 0)
    rw [metricTensor0S_apply, Fin.cons_zero,
      show (Fin.cons Y ww : Fin 2 → TangentSpace (𝓡 2) x) 1 = ww 0 from by
        rw [← Fin.succ_zero_eq_one, Fin.cons_succ]]
  have hRHS : (-(sphereHeightOneForm x)) ww = df x (fun _ : Fin 1 => ww 0) := by
    rw [hdf x (ww 0),
      extDerivFun_neg_at (I := 𝓡 2) (f := sphereHeight) (x := x) (ww 0)
        (sphereHeight_contMDiff.contMDiffAt.mdifferentiableAt (by simp))]
    change -(sphereHeightOneForm x ww) = -(extDerivFun (I := 𝓡 2) sphereHeight x (ww 0))
    congr 1
  rw [hRHS, ← trace_oneform_metric (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
      basis gInv hinv (df x) (ww 0)]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  exact congrArg (fun t => gInv i j * t) (hprodval (basis i) (basis j))

theorem sphereConformalDerivs_zero_nablaA_ahlfors
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    ahlforsOperator (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
        ((sphereConformalDerivs 0).nablaA x)
      = 0 := by
  rw [sphereNablaA_eq x]
  exact ahlfors_smul_metric x (-(sphereHeight x))

set_option maxHeartbeats 400000 in
theorem sphereCurvatureEnergy_zero : sphereCurvatureEnergy 0 = 0 := by
  have hmetric : sphereConformalMetric 0
      = roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2) := by
    apply DifferentialGeometry.Geometry.SmoothRiemannianMetric.ext'
    intro x v w
    rw [sphereConformalMetric, conformalMetric_inner]
    rw [show (2 : Real) * (legendreConformalFactor 0 x) = 0 by
          simp [legendreConformalFactor]]
    rw [Real.exp_zero, one_mul]
  have hK1 : ∀ x, gaussCurvature (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x = 1 :=
    roundMetric_gaussCurvature_eq_one
  have hKfun : gaussCurvature (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) = fun _ => (1 : Real) :=
    funext hK1
  have hK : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞
      (gaussCurvature (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) := by
    rw [hKfun]; exact contMDiff_const
  have hR2' : ∀ x, Nabla2OneFormRealizesAt (I := 𝓡 2)
      (metricCov (I := 𝓡 2) (sphereConformalMetric 0))
      sphereHeightOneForm ((sphereConformalDerivs 0).nablaA) x
      ((sphereConformalDerivs 0).nabla2A x) :=
    fun x => nabla2OneFormRealizesAt_of_totalNabla
      (metricCov (I := 𝓡 2) (sphereConformalMetric 0))
      sphereHeightOneForm ((sphereConformalDerivs 0).nablaA)
      ((sphereConformalDerivs 0).nabla2A)
      (sphereConformalDerivs 0).first (sphereConformalDerivs 0).second x
  have hR2 : ∀ x, Nabla2OneFormRealizesAt (I := 𝓡 2)
      (metricCov (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      sphereHeightOneForm ((sphereConformalDerivs 0).nablaA) x
      ((sphereConformalDerivs 0).nabla2A x) := by
    rw [← hmetric]; exact hR2'
  have hR1 : NablaOneFormSectionRealizes (I := 𝓡 2)
      (metricCov (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      sphereHeightOneForm ((sphereConformalDerivs 0).nablaA) :=
    fun x => (hR2 x).1 x
  have hLap0 : ∀ x, formLaplacianScalar (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) hK x = 0 := by
    have hgrad_zero : grad_g (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) hK = 0 := by
      apply ContMDiffSection.ext
      intro y
      change gradFun (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
          (gaussCurvature (I := 𝓡 2)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) y
          = (0 : TangentSpace (𝓡 2) y)
      apply gradFun_eq_zero_of_mfderiv_eq_zero
      rw [hKfun]
      exact mfderiv_const
    intro x
    rw [formLaplacianScalar_def, hgrad_zero, codifferentialOfVectorField_zero]
  have hdim : Module.finrank Real (EuclideanSpace Real (Fin 2)) = 2 :=
    finrank_euclideanSpace_fin
  have hid := curvatureEnergyIdentity_twoDim hdim
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
    sphereHeightOneForm ((sphereConformalDerivs 0).nablaA)
    (fun x => (sphereConformalDerivs 0).nabla2A x) hK hR1 hR2
  have hz1 : ∀ x, normSq0S (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x 1
      (roughLap0STensor (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (s := 1)
          ((sphereConformalDerivs 0).nabla2A x)
        + gaussCurvature (I := 𝓡 2)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
            • (sphereHeightOneForm x)) = 0 := by
    intro x
    have harg : roughLap0STensor (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (s := 1)
          ((sphereConformalDerivs 0).nabla2A x)
        + gaussCurvature (I := 𝓡 2)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
            • (sphereHeightOneForm x) = 0 := by
      rw [sphereConformalDerivs_zero_nabla2A_roughLap x, hK1 x, one_smul]
      abel
    rw [harg]
    exact (normSq0S_eq_zero_iff (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x 1 0).mpr rfl
  have hz2 : ∀ x, gaussCurvature (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x *
      normSq0S (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x 2
        (ahlforsOperator (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
          ((sphereConformalDerivs 0).nablaA x)) = 0 := by
    intro x
    rw [sphereConformalDerivs_zero_nablaA_ahlfors x,
      (normSq0S_eq_zero_iff (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x 2 0).mpr rfl]
    ring
  have hz3 : ∀ x, formLaplacianScalar (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) hK x *
      normSq0S (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x 1
        (sphereHeightOneForm x) = 0 := by
    intro x
    rw [hLap0 x]
    ring
  have hstep : sphereCurvatureEnergy 0
      = curvatureEnergy (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
          sphereHeightOneForm ((sphereConformalDerivs 0).nablaA)
          (fun x => (sphereConformalDerivs 0).nabla2A x) :=
    congrArg
      (fun g => curvatureEnergy g sphereHeightOneForm ((sphereConformalDerivs 0).nablaA)
        (fun x => (sphereConformalDerivs 0).nabla2A x)) hmetric
  rw [hstep]
  unfold curvatureEnergy
  rw [hid]
  simp only [hz1, hz2, hz3, MeasureTheory.integral_zero, mul_zero, add_zero]

section SharpnessDerivative

open scoped RealInnerProductSpace

private theorem sphereHeightOneForm_apply
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) (v : TangentSpace (𝓡 2) x) :
    sphereHeightOneForm x (fun _ : Fin 1 => v)
      = extDerivFun (I := 𝓡 2) sphereHeight x v := by
  rw [sphereHeightOneForm, duSec_apply]
  exact differential1FormFun_apply_eq_extDerivFun (I := 𝓡 2) sphereHeight x v

private theorem sphereHeight_mdiffAt
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    MDifferentiableAt (𝓡 2) 𝓘(Real, Real) sphereHeight x :=
  sphereHeight_contMDiff.contMDiffAt.mdifferentiableAt (by simp)

private theorem sphereOneForm_eq_inner_grad
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) (v : TangentSpace (𝓡 2) x) :
    sphereHeightOneForm x (fun _ : Fin 1 => v)
      = (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
          (gradFun (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
            sphereHeight x) v := by
  rw [sphereHeightOneForm_apply, extDerivFun_real_eq_mfderiv]
  exact (inner_gradFun (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
    sphereHeight x v).symm

private theorem sphereGradZ_normSq
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
        (gradFun (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
          sphereHeight x)
        (gradFun (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
          sphereHeight x)
      = 1 - sphereHeight x ^ 2 := by
  have hgg : gradFun (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
      sphereHeight x
      = gradientFun (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
          sphereHeight x := rfl
  rw [hgg, roundMetric_inner, sphereGrad_dIncl x]
  have he3n : ⟪(EuclideanSpace.single (2 : Fin 3) (1 : Real)),
      (EuclideanSpace.single (2 : Fin 3) (1 : Real))⟫ = (1 : Real) := by
    simp
  have hpn : ⟪(↑x : EuclideanSpace Real (Fin 3)), (↑x : EuclideanSpace Real (Fin 3))⟫
      = (1 : Real) := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere x]
    norm_num
  have hz : ⟪(EuclideanSpace.single (2 : Fin 3) (1 : Real)),
      (↑x : EuclideanSpace Real (Fin 3))⟫ = sphereHeight x := rfl
  have hz' : ⟪(↑x : EuclideanSpace Real (Fin 3)),
      (EuclideanSpace.single (2 : Fin 3) (1 : Real))⟫ = sphereHeight x :=
    (real_inner_comm _ _).trans hz
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  simp only [real_inner_smul_left, real_inner_smul_right, he3n, hpn, hz, hz']
  ring

private theorem sphereOneForm_gradZ
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    sphereHeightOneForm x (fun _ : Fin 1 =>
        gradFun (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
          sphereHeight x)
      = 1 - sphereHeight x ^ 2 := by
  rw [sphereOneForm_eq_inner_grad, sphereGradZ_normSq]

private theorem sphereNormSq_h
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    normSq0S (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x 1
        (sphereHeightOneForm x)
      = 1 - sphereHeight x ^ 2 := by
  classical
  set basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := 𝓡 2) x
    with hbasis
  set gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
        (EuclideanSpace Real (Fin 2))
      → DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
          (EuclideanSpace Real (Fin 2)) → Real :=
    fun k l => DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x k l
      (extChartAt (𝓡 2) x x) with hgInv
  have hinv : MetricInverseInBasis_gen (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x basis gInv :=
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
  rw [normSq0S_eq_inner,
    inner0S_eq_coord (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
      x 1 basis gInv hinv (sphereHeightOneForm x) (sphereHeightOneForm x),
    coordInner0S_one_eq]
  simp only [cotangentToDual_apply_gen]
  have hstep : ∀ i j, gInv i j * sphereHeightOneForm x (fun _ : Fin 1 => basis i)
        * sphereHeightOneForm x (fun _ : Fin 1 => basis j)
      = gInv i j * (sphereHeightOneForm x (fun _ : Fin 1 => basis i)
          * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (basis j)
              (gradFun (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
                sphereHeight x)) := by
    intro i j
    rw [show sphereHeightOneForm x (fun _ : Fin 1 => basis j)
        = (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (basis j)
            (gradFun (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
              sphereHeight x) from by
      rw [sphereOneForm_eq_inner_grad]
      exact (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).symm x _ _]
    ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hstep i j))]
  rw [trace_oneform_metric (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
    basis gInv hinv (sphereHeightOneForm x)
    (gradFun (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
      sphereHeight x)]
  exact sphereOneForm_gradZ x

private theorem sphereHeight_sq_le_one
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    sphereHeight x ^ 2 ≤ 1 := by
  have h := normSq0S_nonneg (I := 𝓡 2)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x 1 (sphereHeightOneForm x)
  rw [sphereNormSq_h] at h
  linarith

private def sphereP2fun (p : sphere (0 : EuclideanSpace Real (Fin 3)) 1) : Real :=
  (3 * sphereHeight p ^ 2 - 1) / 2

private theorem sphereP2fun_contMDiff :
    ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ sphereP2fun :=
  ((contMDiff_const.mul (sphereHeight_contMDiff.pow 2)).sub contMDiff_const).div_const 2

private theorem legendre_eq_smul_P2 (ε : Real) :
    legendreConformalFactor ε = fun p => ε * sphereP2fun p := rfl

private theorem extDeriv_sphereP2
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) (v : TangentSpace (𝓡 2) x) :
    extDerivFun (I := 𝓡 2) sphereP2fun x v
      = 3 * sphereHeight x * extDerivFun (I := 𝓡 2) sphereHeight x v := by
  have hz_at := sphereHeight_mdiffAt x
  have hzz : MDifferentiableAt (𝓡 2) 𝓘(Real, Real)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        sphereHeight p * sphereHeight p) x := hz_at.mul hz_at
  have hzz32 : MDifferentiableAt (𝓡 2) 𝓘(Real, Real)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        (3 / 2 : Real) * (sphereHeight p * sphereHeight p)) x :=
    (mdifferentiableAt_const (I := 𝓡 2) (I' := 𝓘(Real, Real)) (c := (3 / 2 : Real))).mul hzz
  have hfun : sphereP2fun = fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
      (3 / 2 : Real) * (sphereHeight p * sphereHeight p) - (1 / 2 : Real) := by
    funext p
    rw [sphereP2fun]
    ring
  rw [hfun, extDerivFun_sub_at (I := 𝓡 2) v hzz32
    (mdifferentiableAt_const (I := 𝓡 2) (I' := 𝓘(Real, Real)) (c := (1 / 2 : Real)))]
  have hconst : extDerivFun (I := 𝓡 2)
      (fun _ : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => (1 / 2 : Real)) x v = 0 := by
    rw [extDerivFun_real_eq_mfderiv, mfderiv_const]
    rfl
  have hmul : extDerivFun (I := 𝓡 2)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        (3 / 2 : Real) * (sphereHeight p * sphereHeight p)) x v
      = (3 / 2 : Real) * extDerivFun (I := 𝓡 2)
          (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
            sphereHeight p * sphereHeight p) x v := by
    rw [extDerivFun_const_mul (𝓡 2) (3 / 2 : Real) hzz,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hprod := extDerivFun_mul_at (I := 𝓡 2) (f := sphereHeight) (g := sphereHeight)
    (x := x) v hz_at hz_at
  rw [hconst, hmul, hprod]
  ring

private theorem gradFun_legendre (ε : Real)
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    gradFun (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
        (legendreConformalFactor ε) x
      = (ε * (3 * sphereHeight x)) •
          gradFun (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
            sphereHeight x := by
  set g0 : SmoothRiemannianMetric (𝓡 2) (sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
    roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2) with hg0
  refine SmoothRiemannianMetric.eq_of_inner_eq_gen g0 (fun ζ => ?_)
  have hP2_at : MDifferentiableAt (𝓡 2) 𝓘(Real, Real) sphereP2fun x :=
    sphereP2fun_contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  calc g0.inner x (gradFun (I := 𝓡 2) g0 (legendreConformalFactor ε) x) ζ
      = extDerivFun (I := 𝓡 2) (legendreConformalFactor ε) x ζ := by
        rw [extDerivFun_real_eq_mfderiv]
        exact inner_gradFun (I := 𝓡 2) g0 (legendreConformalFactor ε) x ζ
    _ = extDerivFun (I := 𝓡 2)
          (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => ε * sphereP2fun p) x ζ := by
        rw [← legendre_eq_smul_P2]
    _ = ε * extDerivFun (I := 𝓡 2) sphereP2fun x ζ := by
        rw [extDerivFun_const_mul (𝓡 2) ε hP2_at, ContinuousLinearMap.smul_apply, smul_eq_mul]
    _ = ε * (3 * sphereHeight x * extDerivFun (I := 𝓡 2) sphereHeight x ζ) := by
        rw [extDeriv_sphereP2]
    _ = ε * (3 * sphereHeight x *
          g0.inner x (gradFun (I := 𝓡 2) g0 sphereHeight x) ζ) := by
        rw [extDerivFun_real_eq_mfderiv, inner_gradFun]
    _ = g0.inner x ((ε * (3 * sphereHeight x)) •
          gradFun (I := 𝓡 2) g0 sphereHeight x) ζ := by
        rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
        ring

private theorem sphereConnDiff_apply (ε : Real)
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (w v : TangentSpace (𝓡 2) x) :
    CovariantDerivative.difference
        (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
        (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x w v
      = (ε * (3 * sphereHeight x)) •
          (extDerivFun (I := 𝓡 2) sphereHeight x v • w
            + extDerivFun (I := 𝓡 2) sphereHeight x w • v
            - (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x w v
              • gradFun (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
                  sphereHeight x) := by
  have hcd : CovariantDerivative.difference
        (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
        (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x w v
      = DifferentialGeometry.PDE.DeTurck.connDiff (I := 𝓡 2)
          (conformalMetric (legendreConformalFactor ε) (legendreConformalFactor_contMDiff ε)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x w v := rfl
  rw [hcd, connDiff_conformalMetric_apply (I := 𝓡 2) (legendreConformalFactor ε)
    (legendreConformalFactor_contMDiff ε)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x w v]
  have hin : ∀ u : TangentSpace (𝓡 2) x,
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
          (gradFun (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
            (legendreConformalFactor ε) x) u
        = ε * (3 * sphereHeight x) * extDerivFun (I := 𝓡 2) sphereHeight x u := by
    intro u
    rw [gradFun_legendre ε x, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
      inner_gradFun, ← extDerivFun_real_eq_mfderiv]
  rw [hin v, hin w, gradFun_legendre ε x]
  module

private theorem duSec_val (φ : sphere (0 : EuclideanSpace Real (Fin 3)) 1 -> Real)
    (hφ : ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞) φ)
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) (v : TangentSpace (𝓡 2) x) :
    duSec (I := 𝓡 2) φ hφ x (fun _ : Fin 1 => v) = extDerivFun (I := 𝓡 2) φ x v := by
  rw [duSec_apply]
  exact differential1FormFun_apply_eq_extDerivFun (I := 𝓡 2) φ x v

private def oneFormProd
    (α β : OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)) :
    TwoTensorSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
  MultilinearSection.product (𝕜 := Real) (F := EuclideanSpace Real (Fin 2)) (IB := 𝓡 2)
    (E := TangentSpace (𝓡 2)) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 1) α β

private theorem oneFormProd_cons
    (α β : OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (u : TangentSpace (𝓡 2) x) (w : Fin 1 → TangentSpace (𝓡 2) x) :
    oneFormProd α β x (Fin.cons u w)
      = α x (fun _ : Fin 1 => u) * β x w := by
  change (Bundle.continuousMultilinearMap.product_fun (𝕜 := Real)
      (F := EuclideanSpace Real (Fin 2)) (E := TangentSpace (𝓡 2)) (s := 1) (q := 1)
      (α x) (β x)) (Fin.cons u w) = _
  rw [Bundle.continuousMultilinearMap.product_fun_apply]
  have hleft : Fin.cons u w ∘ Fin.castAdd 1 = fun _ : Fin 1 => u := by
    funext a
    fin_cases a
    rfl
  have hright : Fin.cons u w ∘ Fin.natAdd 1 = w := by
    funext a
    fin_cases a
    rfl
  rw [hleft, hright]
  rfl

private theorem oneFormProd_pair
    (α β : OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (v : Fin 2 → TangentSpace (𝓡 2) x) :
    oneFormProd α β x v
      = α x (fun _ : Fin 1 => v 0) * β x (fun _ : Fin 1 => v 1) := by
  have hv : v = Fin.cons (v 0) (fun _ : Fin 1 => v 1) := by
    funext a
    fin_cases a <;> rfl
  conv_lhs => rw [hv]
  rw [oneFormProd_cons]

private def smulLeibnizCand1
    (φ : sphere (0 : EuclideanSpace Real (Fin 3)) 1 -> Real)
    (hφ : ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞) φ)
    (T : OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (DT : TwoTensorSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)) :
    TwoTensorSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
  let P : TwoTensorSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
    MultilinearSection.product (𝕜 := Real) (F := EuclideanSpace Real (Fin 2)) (IB := 𝓡 2)
      (E := TangentSpace (𝓡 2)) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 1)
      (duSec (I := 𝓡 2) φ hφ) T
  P + tensor0SField_smulByFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
        (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) (s := 2) φ hφ DT

private theorem smulLeibnizCand1_cons
    (φ : sphere (0 : EuclideanSpace Real (Fin 3)) 1 -> Real)
    (hφ : ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞) φ)
    (T : OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (DT : TwoTensorSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (u : TangentSpace (𝓡 2) x) (w : Fin 1 → TangentSpace (𝓡 2) x) :
    smulLeibnizCand1 φ hφ T DT x (Fin.cons u w)
      = extDerivFun (I := 𝓡 2) φ x u * T x w + φ x * DT x (Fin.cons u w) := by
  change (Bundle.continuousMultilinearMap.product_fun (𝕜 := Real)
      (F := EuclideanSpace Real (Fin 2)) (E := TangentSpace (𝓡 2)) (s := 1) (q := 1)
      ((duSec (I := 𝓡 2) φ hφ) x) (T x)) (Fin.cons u w)
      + φ x * DT x (Fin.cons u w)
    = extDerivFun (I := 𝓡 2) φ x u * T x w + φ x * DT x (Fin.cons u w)
  rw [Bundle.continuousMultilinearMap.product_fun_apply]
  have hleft : Fin.cons u w ∘ Fin.castAdd 1 = fun _ : Fin 1 => u := by
    funext a
    fin_cases a
    rfl
  have hright : Fin.cons u w ∘ Fin.natAdd 1 = w := by
    funext a
    fin_cases a
    rfl
  rw [hleft, hright]
  exact congrArg (fun t => t * T x w + φ x * DT x (Fin.cons u w)) (duSec_val φ hφ x u)

private def smulLeibnizCand2
    (φ : sphere (0 : EuclideanSpace Real (Fin 3)) 1 -> Real)
    (hφ : ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞) φ)
    (T : TwoTensorSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (DT : Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3) :
    Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3 :=
  let P : Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3 :=
    MultilinearSection.product (𝕜 := Real) (F := EuclideanSpace Real (Fin 2)) (IB := 𝓡 2)
      (E := TangentSpace (𝓡 2)) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
      (duSec (I := 𝓡 2) φ hφ) T
  P + tensor0SField_smulByFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
        (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) (s := 3) φ hφ DT

private theorem smulLeibnizCand2_cons
    (φ : sphere (0 : EuclideanSpace Real (Fin 3)) 1 -> Real)
    (hφ : ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞) φ)
    (T : TwoTensorSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (DT : Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3)
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (u : TangentSpace (𝓡 2) x) (w : Fin 2 → TangentSpace (𝓡 2) x) :
    smulLeibnizCand2 φ hφ T DT x (Fin.cons u w)
      = extDerivFun (I := 𝓡 2) φ x u * T x w + φ x * DT x (Fin.cons u w) := by
  change (Bundle.continuousMultilinearMap.product_fun (𝕜 := Real)
      (F := EuclideanSpace Real (Fin 2)) (E := TangentSpace (𝓡 2)) (s := 1) (q := 2)
      ((duSec (I := 𝓡 2) φ hφ) x) (T x)) (Fin.cons u w)
      + φ x * DT x (Fin.cons u w)
    = extDerivFun (I := 𝓡 2) φ x u * T x w + φ x * DT x (Fin.cons u w)
  rw [Bundle.continuousMultilinearMap.product_fun_apply]
  have hleft : Fin.cons u w ∘ Fin.castAdd 2 = fun _ : Fin 1 => u := by
    funext a
    fin_cases a
    rfl
  have hright : Fin.cons u w ∘ Fin.natAdd 1 = w := by
    funext a
    fin_cases a <;> rfl
  rw [hleft, hright]
  exact congrArg (fun t => t * T x w + φ x * DT x (Fin.cons u w)) (duSec_val φ hφ x u)

private def prodLeibnizCand
    (α β : OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (Dα Dβ : TwoTensorSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)) :
    Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3 :=
  let P : Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3 :=
    MultilinearSection.product (𝕜 := Real) (F := EuclideanSpace Real (Fin 2)) (IB := 𝓡 2)
      (E := TangentSpace (𝓡 2)) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 1) Dα β
  let Q : Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3 :=
    MultilinearSection.domDomCongr (𝕜 := Real) (F := EuclideanSpace Real (Fin 2))
      (IB := 𝓡 2) (E := TangentSpace (𝓡 2)) (∞ : WithTop ℕ∞)
      (Equiv.swap (0 : Fin 3) 1)
      (MultilinearSection.product (𝕜 := Real) (F := EuclideanSpace Real (Fin 2))
        (IB := 𝓡 2) (E := TangentSpace (𝓡 2)) (n := (∞ : WithTop ℕ∞))
        (s := 1) (q := 2) α Dβ)
  P + Q

private theorem prodLeibnizCand_cons
    (α β : OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (Dα Dβ : TwoTensorSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (u : TangentSpace (𝓡 2) x) (w : Fin 2 → TangentSpace (𝓡 2) x) :
    prodLeibnizCand α β Dα Dβ x (Fin.cons u w)
      = Dα x (Fin.cons u (fun _ : Fin 1 => w 0)) * β x (fun _ : Fin 1 => w 1)
        + α x (fun _ : Fin 1 => w 0) * Dβ x (Fin.cons u (fun _ : Fin 1 => w 1)) := by
  have h1 : (Bundle.continuousMultilinearMap.product_fun (𝕜 := Real)
      (F := EuclideanSpace Real (Fin 2)) (E := TangentSpace (𝓡 2)) (s := 2) (q := 1)
      (Dα x) (β x)) (Fin.cons u w)
      = Dα x (Fin.cons u (fun _ : Fin 1 => w 0)) * β x (fun _ : Fin 1 => w 1) := by
    rw [Bundle.continuousMultilinearMap.product_fun_apply]
    have hleft : Fin.cons u w ∘ Fin.castAdd 1 = Fin.cons u (fun _ : Fin 1 => w 0) := by
      funext a
      fin_cases a <;> rfl
    have hright : Fin.cons u w ∘ Fin.natAdd 2 = fun _ : Fin 1 => w 1 := by
      funext a
      fin_cases a
      rfl
    rw [hleft, hright]
    rfl
  have h2 : (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 3) 1)
        (Bundle.continuousMultilinearMap.product_fun (𝕜 := Real)
          (F := EuclideanSpace Real (Fin 2)) (E := TangentSpace (𝓡 2)) (s := 1) (q := 2)
          (α x) (Dβ x))) (Fin.cons u w)
      = α x (fun _ : Fin 1 => w 0) * Dβ x (Fin.cons u (fun _ : Fin 1 => w 1)) := by
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [Bundle.continuousMultilinearMap.product_fun_apply]
    have hleft : (fun i : Fin 3 =>
          (Fin.cons u w : Fin 3 → TangentSpace (𝓡 2) x) ((Equiv.swap (0 : Fin 3) 1) i))
          ∘ Fin.castAdd 2
        = fun _ : Fin 1 => w 0 := by
      funext a
      fin_cases a
      rfl
    have hright : (fun i : Fin 3 =>
          (Fin.cons u w : Fin 3 → TangentSpace (𝓡 2) x) ((Equiv.swap (0 : Fin 3) 1) i))
          ∘ Fin.natAdd 1
        = Fin.cons u (fun _ : Fin 1 => w 1) := by
      funext a
      fin_cases a <;> rfl
    rw [hleft, hright]
    rfl
  calc prodLeibnizCand α β Dα Dβ x (Fin.cons u w)
      = (Bundle.continuousMultilinearMap.product_fun (𝕜 := Real)
          (F := EuclideanSpace Real (Fin 2)) (E := TangentSpace (𝓡 2)) (s := 2) (q := 1)
          (Dα x) (β x)) (Fin.cons u w)
        + (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 3) 1)
            (Bundle.continuousMultilinearMap.product_fun (𝕜 := Real)
              (F := EuclideanSpace Real (Fin 2)) (E := TangentSpace (𝓡 2)) (s := 1) (q := 2)
              (α x) (Dβ x))) (Fin.cons u w) := rfl
    _ = Dα x (Fin.cons u (fun _ : Fin 1 => w 0)) * β x (fun _ : Fin 1 => w 1)
        + α x (fun _ : Fin 1 => w 0) * Dβ x (Fin.cons u (fun _ : Fin 1 => w 1)) := by
      rw [h1, h2]

private theorem realize_smulByFun_one
    (cov : CovariantDerivative (𝓡 2) (EuclideanSpace Real (Fin 2))
      (TangentSpace (𝓡 2) : sphere (0 : EuclideanSpace Real (Fin 3)) 1 -> Type _))
    (φ : sphere (0 : EuclideanSpace Real (Fin 3)) 1 -> Real)
    (hφ : ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞) φ)
    (T : OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (DT : TwoTensorSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (hT : TotalNabla0SRealizes (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
      (I := 𝓡 2) 1 cov T DT) :
    TotalNabla0SRealizes (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
      (I := 𝓡 2) 1 cov
      (tensor0SField_smulByFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
        (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) (s := 1) φ hφ T)
      (smulLeibnizCand1 φ hφ T DT) := by
  intro X x slots
  classical
  obtain ⟨σ, hσx⟩ := ContMDiffSection.exists_eq_at (I := 𝓡 2) (n := (⊤ : ℕ∞))
    (F := EuclideanSpace Real (Fin 2))
    (V := (TangentSpace (𝓡 2) : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → Type _))
    x (slots 0)
  set Vs : Fin 1 -> ContMDiffSection (𝓡 2) (EuclideanSpace Real (Fin 2)) (∞ : WithTop ℕ∞)
      (TangentSpace (𝓡 2) : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → Type _) :=
    fun _ => σ with hVs
  have hslots : (fun a : Fin 1 => Vs a x) = slots := by
    funext a
    fin_cases a
    exact hσx
  rw [← hslots]
  have hφm : MDifferentiableAt (𝓡 2) 𝓘(Real, Real) φ x :=
    hφ.contMDiffAt.mdifferentiableAt (by simp)
  have hTm : MDifferentiableAt (𝓡 2) 𝓘(Real, Real)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        T p (fun a : Fin 1 => Vs a p)) x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := Real)
      (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2) T Vs x).mdifferentiableAt (by simp)
  have heval := nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
    (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) cov X Vs
    (tensor0SField_smulByFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
      (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) (s := 1) φ hφ T) x
  have hTeval := TotalNabla0SRealizes.eval_smooth_slots (I := 𝓡 2) hT X Vs x
  have hfun : (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        (tensor0SField_smulByFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
          (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) (s := 1) φ hφ T) p (fun a : Fin 1 => Vs a p))
      = fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
          φ p * T p (fun a : Fin 1 => Vs a p) := by
    funext p
    rfl
  have hprod : extDerivFun (I := 𝓡 2)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        φ p * T p (fun a : Fin 1 => Vs a p)) x (X x)
      = φ x * extDerivFun (I := 𝓡 2)
          (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
            T p (fun a : Fin 1 => Vs a p)) x (X x)
        + T x (fun a : Fin 1 => Vs a x) * extDerivFun (I := 𝓡 2) φ x (X x) :=
    extDerivFun_mul_at (I := 𝓡 2) (X x) hφm hTm
  have hcorr : (∑ a : Fin 1,
        (tensor0SField_smulByFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
          (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) (s := 1) φ hφ T) x
          (Function.update (fun b : Fin 1 => Vs b x) a
            ((cov (fun p => Vs a p) x) (X x))))
      = φ x * ∑ a : Fin 1, T x
          (Function.update (fun b : Fin 1 => Vs b x) a
            ((cov (fun p => Vs a p) x) (X x))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rfl
  rw [smulLeibnizCand1_cons, heval, hfun, hprod, hcorr, hTeval]
  ring

private theorem realize_smulByFun_two
    (cov : CovariantDerivative (𝓡 2) (EuclideanSpace Real (Fin 2))
      (TangentSpace (𝓡 2) : sphere (0 : EuclideanSpace Real (Fin 3)) 1 -> Type _))
    (φ : sphere (0 : EuclideanSpace Real (Fin 3)) 1 -> Real)
    (hφ : ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞) φ)
    (T : TwoTensorSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (DT : Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3)
    (hT : TotalNabla0SRealizes (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
      (I := 𝓡 2) 2 cov T DT) :
    TotalNabla0SRealizes (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
      (I := 𝓡 2) 2 cov
      (tensor0SField_smulByFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
        (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) (s := 2) φ hφ T)
      (smulLeibnizCand2 φ hφ T DT) := by
  intro X x slots
  classical
  set Vs : Fin 2 -> ContMDiffSection (𝓡 2) (EuclideanSpace Real (Fin 2)) (∞ : WithTop ℕ∞)
      (TangentSpace (𝓡 2) : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → Type _) :=
    fun a => (ContMDiffSection.exists_eq_at (I := 𝓡 2) (n := (⊤ : ℕ∞))
      (F := EuclideanSpace Real (Fin 2))
      (V := (TangentSpace (𝓡 2) : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → Type _))
      x (slots a)).choose with hVs
  have hslots : (fun a : Fin 2 => Vs a x) = slots := by
    funext a
    exact (ContMDiffSection.exists_eq_at (I := 𝓡 2) (n := (⊤ : ℕ∞))
      (F := EuclideanSpace Real (Fin 2))
      (V := (TangentSpace (𝓡 2) : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → Type _))
      x (slots a)).choose_spec
  rw [← hslots]
  have hφm : MDifferentiableAt (𝓡 2) 𝓘(Real, Real) φ x :=
    hφ.contMDiffAt.mdifferentiableAt (by simp)
  have hTm : MDifferentiableAt (𝓡 2) 𝓘(Real, Real)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        T p (fun a : Fin 2 => Vs a p)) x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := Real)
      (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2) T Vs x).mdifferentiableAt (by simp)
  have heval := nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
    (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) cov X Vs
    (tensor0SField_smulByFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
      (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) (s := 2) φ hφ T) x
  have hTeval := TotalNabla0SRealizes.eval_smooth_slots (I := 𝓡 2) hT X Vs x
  have hfun : (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        (tensor0SField_smulByFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
          (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) (s := 2) φ hφ T) p (fun a : Fin 2 => Vs a p))
      = fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
          φ p * T p (fun a : Fin 2 => Vs a p) := by
    funext p
    rfl
  have hprod : extDerivFun (I := 𝓡 2)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        φ p * T p (fun a : Fin 2 => Vs a p)) x (X x)
      = φ x * extDerivFun (I := 𝓡 2)
          (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
            T p (fun a : Fin 2 => Vs a p)) x (X x)
        + T x (fun a : Fin 2 => Vs a x) * extDerivFun (I := 𝓡 2) φ x (X x) :=
    extDerivFun_mul_at (I := 𝓡 2) (X x) hφm hTm
  have hcorr : (∑ a : Fin 2,
        (tensor0SField_smulByFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
          (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) (s := 2) φ hφ T) x
          (Function.update (fun b : Fin 2 => Vs b x) a
            ((cov (fun p => Vs a p) x) (X x))))
      = φ x * ∑ a : Fin 2, T x
          (Function.update (fun b : Fin 2 => Vs b x) a
            ((cov (fun p => Vs a p) x) (X x))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rfl
  rw [smulLeibnizCand2_cons, heval, hfun, hprod, hcorr, hTeval]
  ring

set_option maxHeartbeats 1600000 in
private theorem realize_product_oneForm
    (cov : CovariantDerivative (𝓡 2) (EuclideanSpace Real (Fin 2))
      (TangentSpace (𝓡 2) : sphere (0 : EuclideanSpace Real (Fin 3)) 1 -> Type _))
    (α β : OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (Dα Dβ : TwoTensorSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (hα : TotalNabla0SRealizes (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
      (I := 𝓡 2) 1 cov α Dα)
    (hβ : TotalNabla0SRealizes (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
      (I := 𝓡 2) 1 cov β Dβ) :
    TotalNabla0SRealizes (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
      (I := 𝓡 2) 2 cov (oneFormProd α β) (prodLeibnizCand α β Dα Dβ) := by
  intro X x slots
  classical
  set Vs : Fin 2 -> ContMDiffSection (𝓡 2) (EuclideanSpace Real (Fin 2)) (∞ : WithTop ℕ∞)
      (TangentSpace (𝓡 2) : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → Type _) :=
    fun a => (ContMDiffSection.exists_eq_at (I := 𝓡 2) (n := (⊤ : ℕ∞))
      (F := EuclideanSpace Real (Fin 2))
      (V := (TangentSpace (𝓡 2) : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → Type _))
      x (slots a)).choose with hVs
  have hslots : (fun a : Fin 2 => Vs a x) = slots := by
    funext a
    exact (ContMDiffSection.exists_eq_at (I := 𝓡 2) (n := (⊤ : ℕ∞))
      (F := EuclideanSpace Real (Fin 2))
      (V := (TangentSpace (𝓡 2) : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → Type _))
      x (slots a)).choose_spec
  rw [← hslots]
  have hαm : MDifferentiableAt (𝓡 2) 𝓘(Real, Real)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        α p (fun _ : Fin 1 => Vs 0 p)) x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := Real)
      (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2) α (fun _ : Fin 1 => Vs 0)
      x).mdifferentiableAt (by simp)
  have hβm : MDifferentiableAt (𝓡 2) 𝓘(Real, Real)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        β p (fun _ : Fin 1 => Vs 1 p)) x :=
    (tensor0SField_eval_smooth_slots_contMDiffAt (𝕜 := Real)
      (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2) β (fun _ : Fin 1 => Vs 1)
      x).mdifferentiableAt (by simp)
  have heval := nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
    (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) cov X Vs
    (oneFormProd α β) x
  have hαeval := TotalNabla0SRealizes.eval_smooth_slots (I := 𝓡 2) hα X
    (fun _ : Fin 1 => Vs 0) x
  have hβeval := TotalNabla0SRealizes.eval_smooth_slots (I := 𝓡 2) hβ X
    (fun _ : Fin 1 => Vs 1) x
  have htuple : ∀ p : sphere (0 : EuclideanSpace Real (Fin 3)) 1,
      (fun a : Fin 2 => Vs a p) = Fin.cons (Vs 0 p) (fun _ : Fin 1 => Vs 1 p) := by
    intro p
    funext a
    fin_cases a <;> rfl
  have hfun : (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        oneFormProd α β p (fun a : Fin 2 => Vs a p))
      = fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
          α p (fun _ : Fin 1 => Vs 0 p) * β p (fun _ : Fin 1 => Vs 1 p) := by
    funext p
    rw [htuple p, oneFormProd_cons]
  have hprod : extDerivFun (I := 𝓡 2)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        α p (fun _ : Fin 1 => Vs 0 p) * β p (fun _ : Fin 1 => Vs 1 p)) x (X x)
      = α x (fun _ : Fin 1 => Vs 0 x) * extDerivFun (I := 𝓡 2)
          (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
            β p (fun _ : Fin 1 => Vs 1 p)) x (X x)
        + β x (fun _ : Fin 1 => Vs 1 x) * extDerivFun (I := 𝓡 2)
            (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
              α p (fun _ : Fin 1 => Vs 0 p)) x (X x) :=
    extDerivFun_mul_at (I := 𝓡 2) (X x) hαm hβm
  have hupdate0 : Function.update (fun b : Fin 2 => Vs b x) (0 : Fin 2)
        ((cov (fun p => Vs 0 p) x) (X x))
      = Fin.cons ((cov (fun p => Vs 0 p) x) (X x)) (fun _ : Fin 1 => Vs 1 x) := by
    funext a
    fin_cases a <;> simp
  have hupdate1 : Function.update (fun b : Fin 2 => Vs b x) (1 : Fin 2)
        ((cov (fun p => Vs 1 p) x) (X x))
      = Fin.cons (Vs 0 x) (fun _ : Fin 1 => (cov (fun p => Vs 1 p) x) (X x)) := by
    funext a
    fin_cases a <;> simp
  have hsingleupdate : ∀ (c : TangentSpace (𝓡 2) x) (a : Fin 1)
      (w : Fin 1 → TangentSpace (𝓡 2) x),
      Function.update w a c = fun _ : Fin 1 => c := by
    intro c a w
    funext b
    fin_cases b
    fin_cases a
    simp
  have hαd : extDerivFun (I := 𝓡 2)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        α p (fun _ : Fin 1 => Vs 0 p)) x (X x)
      = Dα x (Fin.cons (X x) (fun _ : Fin 1 => Vs 0 x))
        + α x (fun _ : Fin 1 => (cov (fun p => Vs 0 p) x) (X x)) := by
    rw [hαeval, Fin.sum_univ_one, hsingleupdate]
    ring
  have hβd : extDerivFun (I := 𝓡 2)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        β p (fun _ : Fin 1 => Vs 1 p)) x (X x)
      = Dβ x (Fin.cons (X x) (fun _ : Fin 1 => Vs 1 x))
        + β x (fun _ : Fin 1 => (cov (fun p => Vs 1 p) x) (X x)) := by
    rw [hβeval, Fin.sum_univ_one, hsingleupdate]
    ring
  have hcorrsum : (∑ a : Fin 2,
        oneFormProd α β x
          (Function.update (fun b : Fin 2 => Vs b x) a
            ((cov (fun p => Vs a p) x) (X x))))
      = α x (fun _ : Fin 1 => (cov (fun p => Vs 0 p) x) (X x)) * β x (fun _ : Fin 1 => Vs 1 x)
        + α x (fun _ : Fin 1 => Vs 0 x)
            * β x (fun _ : Fin 1 => (cov (fun p => Vs 1 p) x) (X x)) := by
    rw [Fin.sum_univ_two, hupdate0, hupdate1, oneFormProd_cons, oneFormProd_cons]
  rw [prodLeibnizCand_cons, heval, hfun, hprod, hαd, hβd, hcorrsum]
  ring

private theorem oneFormSlot_eq_clm (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (A : Tensor0SSpace (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) 1 x) (v : TangentSpace (𝓡 2) x) :
    A (fun _ : Fin 1 => v)
      = continuousMultilinearCurryFin1 Real (TangentSpace (𝓡 2) x) Real A v := by
  rw [continuousMultilinearCurryFin1_apply]
  exact congrArg (⇑A) (Fin.snoc_zero _ v).symm

private theorem oneFormSlot_smul (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (A : Tensor0SSpace (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) 1 x)
    (c : Real) (u : TangentSpace (𝓡 2) x) :
    A (fun _ : Fin 1 => c • u) = c * A (fun _ : Fin 1 => u) := by
  rw [oneFormSlot_eq_clm, oneFormSlot_eq_clm, map_smul, smul_eq_mul]

private theorem oneFormSlot_comb3 (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (A : Tensor0SSpace (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) 1 x)
    (a b c : Real) (u v w : TangentSpace (𝓡 2) x) :
    A (fun _ : Fin 1 => a • u + b • v - c • w)
      = a * A (fun _ : Fin 1 => u) + b * A (fun _ : Fin 1 => v)
        - c * A (fun _ : Fin 1 => w) := by
  rw [oneFormSlot_eq_clm, oneFormSlot_eq_clm, oneFormSlot_eq_clm, oneFormSlot_eq_clm,
    map_sub, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]

private theorem gInner_smul_left (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (c : Real) (u t : TangentSpace (𝓡 2) x) :
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (c • u) t
      = c * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x u t := by
  rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

private theorem gInner_comb3_left (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (a b c : Real) (u v w t : TangentSpace (𝓡 2) x) :
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (a • u + b • v - c • w) t
      = a * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x u t
        + b * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x v t
        - c * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x w t := by
  rw [map_sub, map_add, map_smul, map_smul, map_smul]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

private theorem gInner_comb3_right (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (a b c : Real) (t u v w : TangentSpace (𝓡 2) x) :
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x t (a • u + b • v - c • w)
      = a * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x t u
        + b * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x t v
        - c * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x t w := by
  rw [map_sub, map_add, map_smul, map_smul, map_smul]
  simp only [smul_eq_mul]

private theorem updateFinOne (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (c : TangentSpace (𝓡 2) x) (a : Fin 1) (w : Fin 1 → TangentSpace (𝓡 2) x) :
    Function.update w a c = fun _ : Fin 1 => c := by
  funext b
  fin_cases b
  fin_cases a
  simp

private theorem sphere6z_contMDiff :
    ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => 6 * sphereHeight p) :=
  contMDiff_const.mul sphereHeight_contMDiff

private theorem sphereBcoef_contMDiff :
    ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        -(3 * sphereHeight p * (1 - sphereHeight p ^ 2))) :=
  ((contMDiff_const.mul sphereHeight_contMDiff).mul
    (contMDiff_const.sub (sphereHeight_contMDiff.pow 2))).neg

private def sphereDzDz :
    TwoTensorSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
  oneFormProd sphereHeightOneForm sphereHeightOneForm

private def sphereBField :
    TwoTensorSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
  tensor0SField_smulByFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
      (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) (s := 2)
      (fun p => 6 * sphereHeight p) sphere6z_contMDiff sphereDzDz
    + tensor0SField_smulByFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
        (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) (s := 2)
        (fun p => -(3 * sphereHeight p * (1 - sphereHeight p ^ 2))) sphereBcoef_contMDiff
        (metricTensorField (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))

private theorem sphereBField_apply (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (v : Fin 2 → TangentSpace (𝓡 2) x) :
    sphereBField x v
      = 6 * sphereHeight x * (sphereHeightOneForm x (fun _ : Fin 1 => v 0)
          * sphereHeightOneForm x (fun _ : Fin 1 => v 1))
        - 3 * sphereHeight x * (1 - sphereHeight x ^ 2)
          * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (v 0) (v 1) := by
  have hsplit : sphereBField x v
      = (6 * sphereHeight x) * sphereDzDz x v
        + (-(3 * sphereHeight x * (1 - sphereHeight x ^ 2)))
          * (metricTensorField (I := 𝓡 2)
              (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x v := rfl
  rw [hsplit, metricTensorField_apply]
  rw [show sphereDzDz x v = oneFormProd sphereHeightOneForm sphereHeightOneForm x v from rfl,
    oneFormProd_pair]
  ring

private theorem sphereCovZeroEq :
    metricCov (I := 𝓡 2) (sphereConformalMetric 0)
      = metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) :=
  congrArg (metricCov (I := 𝓡 2)) sphereConformalMetric_zero_eq

private theorem sphereRealizeZero_first :
    TotalNabla0SRealizes (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2) 1
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      sphereHeightOneForm ((sphereConformalDerivs 0).nablaA) := by
  rw [← sphereCovZeroEq]
  exact (sphereConformalDerivs 0).first

private theorem sphereRealizeZero_second :
    TotalNabla0SRealizes (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2) 2
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      ((sphereConformalDerivs 0).nablaA) ((sphereConformalDerivs 0).nabla2A) := by
  rw [← sphereCovZeroEq]
  exact (sphereConformalDerivs 0).second

private theorem sphereNablaAZero_val (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (v : Fin 2 → TangentSpace (𝓡 2) x) :
    (sphereConformalDerivs 0).nablaA x v
      = -(sphereHeight x)
        * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (v 0) (v 1) := by
  rw [sphereNablaA_eq x]
  rw [show ((-(sphereHeight x)) •
        metricTensor0S (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x) v
      = -(sphereHeight x) * (metricTensor0S (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x) v from rfl,
    metricTensor0S_apply]

set_option maxHeartbeats 800000 in
private theorem sphereNablaA_expansion (ε : Real) :
    (sphereConformalDerivs ε).nablaA
      = (sphereConformalDerivs 0).nablaA + (-ε) • sphereBField := by
  refine totalNabla0SRealizes_unique
    (cov := metricCov (I := 𝓡 2) (sphereConformalMetric ε))
    (α := sphereHeightOneForm)
    (sphereConformalDerivs ε).first ?_
  intro X x slots
  classical
  obtain ⟨σ, hσx⟩ := ContMDiffSection.exists_eq_at (I := 𝓡 2) (n := (⊤ : ℕ∞))
    (F := EuclideanSpace Real (Fin 2))
    (V := (TangentSpace (𝓡 2) : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → Type _))
    x (slots 0)
  set Vs : Fin 1 -> ContMDiffSection (𝓡 2) (EuclideanSpace Real (Fin 2)) (∞ : WithTop ℕ∞)
      (TangentSpace (𝓡 2) : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → Type _) :=
    fun _ => σ with hVs
  have hslots : (fun a : Fin 1 => Vs a x) = slots := by
    funext a
    fin_cases a
    exact hσx
  rw [← hslots]
  have hsub' : nabla0SFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) 1
      (metricCov (I := 𝓡 2) (sphereConformalMetric ε)) X sphereHeightOneForm x
      (fun a : Fin 1 => Vs a x)
      - nabla0SFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
        (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) 1
        (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
        X sphereHeightOneForm x (fun a : Fin 1 => Vs a x)
      = -∑ a : Fin 1, sphereHeightOneForm x
          (Function.update (fun b : Fin 1 => Vs b x) a
            ((CovariantDerivative.difference
                (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
                (metricCov (I := 𝓡 2)
                  (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x)
              (Vs a x) (X x))) :=
    nabla0SFun_sub_cov (I := 𝓡 2)
      (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      X Vs sphereHeightOneForm x
  have hbase := sphereRealizeZero_first X x (fun a : Fin 1 => Vs a x)
  have hEps : nabla0SFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) 1
      (metricCov (I := 𝓡 2) (sphereConformalMetric ε)) X sphereHeightOneForm x
      (fun a : Fin 1 => Vs a x)
      = (sphereConformalDerivs 0).nablaA x (Fin.cons (X x) (fun a : Fin 1 => Vs a x))
        - ∑ a : Fin 1, sphereHeightOneForm x
            (Function.update (fun b : Fin 1 => Vs b x) a
              ((CovariantDerivative.difference
                  (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
                  (metricCov (I := 𝓡 2)
                    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x)
                (Vs a x) (X x))) := by
    linarith [hsub', hbase]
  have hcorr : (∑ a : Fin 1, sphereHeightOneForm x
        (Function.update (fun b : Fin 1 => Vs b x) a
          ((CovariantDerivative.difference
              (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
              (metricCov (I := 𝓡 2)
                (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x)
            (Vs a x) (X x))))
      = ε * (6 * sphereHeight x
            * (sphereHeightOneForm x (fun _ : Fin 1 => X x)
                * sphereHeightOneForm x (fun _ : Fin 1 => Vs 0 x))
          - 3 * sphereHeight x * (1 - sphereHeight x ^ 2)
            * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (X x)
                (Vs 0 x)) := by
    rw [Fin.sum_univ_one, updateFinOne, sphereConnDiff_apply ε x (Vs 0 x) (X x)]
    rw [oneFormSlot_smul, oneFormSlot_comb3]
    rw [show sphereHeightOneForm x (fun _ : Fin 1 =>
          gradFun (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
            sphereHeight x) = 1 - sphereHeight x ^ 2 from sphereOneForm_gradZ x]
    rw [show extDerivFun (I := 𝓡 2) sphereHeight x (X x)
        = sphereHeightOneForm x (fun _ : Fin 1 => X x) from
      (sphereHeightOneForm_apply x (X x)).symm]
    rw [show extDerivFun (I := 𝓡 2) sphereHeight x (Vs 0 x)
        = sphereHeightOneForm x (fun _ : Fin 1 => Vs 0 x) from
      (sphereHeightOneForm_apply x (Vs 0 x)).symm]
    rw [(roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).symm x (Vs 0 x) (X x)]
    ring
  have hLHS : ((sphereConformalDerivs 0).nablaA + (-ε) • sphereBField) x
        (Fin.cons (X x) (fun a : Fin 1 => Vs a x))
      = (sphereConformalDerivs 0).nablaA x (Fin.cons (X x) (fun a : Fin 1 => Vs a x))
        + (-ε) * sphereBField x (Fin.cons (X x) (fun a : Fin 1 => Vs a x)) := rfl
  have hcons0 : (Fin.cons (X x) (fun a : Fin 1 => Vs a x) : Fin 2 → TangentSpace (𝓡 2) x) 0
      = X x := rfl
  have hcons1 : (Fin.cons (X x) (fun a : Fin 1 => Vs a x) : Fin 2 → TangentSpace (𝓡 2) x) 1
      = Vs 0 x := by
    rw [← Fin.succ_zero_eq_one, Fin.cons_succ]
  have hBval := sphereBField_apply x (Fin.cons (X x) (fun a : Fin 1 => Vs a x))
  rw [hcons0, hcons1] at hBval
  rw [hLHS, hBval, hEps, hcorr]
  ring

private theorem gInner_smul_right (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (c : Real) (t u : TangentSpace (𝓡 2) x) :
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x t (c • u)
      = c * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x t u := by
  rw [map_smul, smul_eq_mul]

private theorem sphereE1coef_contMDiff :
    ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        -(6 * sphereHeight p ^ 2)) :=
  (contMDiff_const.mul (sphereHeight_contMDiff.pow 2)).neg

private theorem sphere72coef_contMDiff :
    ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        72 * sphereHeight p ^ 2) :=
  contMDiff_const.mul (sphereHeight_contMDiff.pow 2)

private theorem sphereE2coef_contMDiff :
    ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        -(18 * sphereHeight p ^ 2 * (1 - sphereHeight p ^ 2))) :=
  ((contMDiff_const.mul (sphereHeight_contMDiff.pow 2)).mul
    (contMDiff_const.sub (sphereHeight_contMDiff.pow 2))).neg

private def oneFormMetricProd
    (α : OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)) :
    Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3 :=
  let P : Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3 :=
    MultilinearSection.product (𝕜 := Real) (F := EuclideanSpace Real (Fin 2)) (IB := 𝓡 2)
      (E := TangentSpace (𝓡 2)) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2) α
      (metricTensorField (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
  P

private theorem oneFormMetricProd_cons
    (α : OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (u : TangentSpace (𝓡 2) x) (w : Fin 2 → TangentSpace (𝓡 2) x) :
    oneFormMetricProd α x (Fin.cons u w)
      = α x (fun _ : Fin 1 => u)
        * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (w 0) (w 1) := by
  have hstep : oneFormMetricProd α x (Fin.cons u w)
      = (Bundle.continuousMultilinearMap.product_fun (𝕜 := Real)
          (F := EuclideanSpace Real (Fin 2)) (E := TangentSpace (𝓡 2)) (s := 1) (q := 2)
          (α x)
          ((metricTensorField (I := 𝓡 2)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x))
          (Fin.cons u w) := rfl
  rw [hstep, Bundle.continuousMultilinearMap.product_fun_apply]
  have hleft : Fin.cons u w ∘ Fin.castAdd 2 = fun _ : Fin 1 => u := by
    funext a
    fin_cases a
    rfl
  have hright : Fin.cons u w ∘ Fin.natAdd 1 = w := by
    funext a
    fin_cases a <;> rfl
  rw [hleft, hright]
  exact congrArg (fun t => α x (fun _ : Fin 1 => u) * t)
    (metricTensorField_apply (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x w)

private def metricOneFormProd
    (α : OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)) :
    Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3 :=
  let P : Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3 :=
    MultilinearSection.product (𝕜 := Real) (F := EuclideanSpace Real (Fin 2)) (IB := 𝓡 2)
      (E := TangentSpace (𝓡 2)) (n := (∞ : WithTop ℕ∞)) (s := 2) (q := 1)
      (metricTensorField (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) α
  P

private theorem metricOneFormProd_cons
    (α : OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (u : TangentSpace (𝓡 2) x) (w : Fin 2 → TangentSpace (𝓡 2) x) :
    metricOneFormProd α x (Fin.cons u w)
      = (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x u (w 0)
        * α x (fun _ : Fin 1 => w 1) := by
  have hstep : metricOneFormProd α x (Fin.cons u w)
      = (Bundle.continuousMultilinearMap.product_fun (𝕜 := Real)
          (F := EuclideanSpace Real (Fin 2)) (E := TangentSpace (𝓡 2)) (s := 2) (q := 1)
          ((metricTensorField (I := 𝓡 2)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x)
          (α x)) (Fin.cons u w) := rfl
  rw [hstep, Bundle.continuousMultilinearMap.product_fun_apply]
  have hleft : Fin.cons u w ∘ Fin.castAdd 1
      = Fin.cons u (fun _ : Fin 1 => w 0) := by
    funext a
    fin_cases a <;> rfl
  have hright : Fin.cons u w ∘ Fin.natAdd 2 = fun _ : Fin 1 => w 1 := by
    funext a
    fin_cases a
    rfl
  rw [hleft, hright]
  have hm : metricTensorField (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
        (Fin.cons u (fun _ : Fin 1 => w 0))
      = (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x u (w 0) := by
    rw [metricTensorField_apply,
      show (Fin.cons u (fun _ : Fin 1 => w 0) : Fin 2 → TangentSpace (𝓡 2) x) 1 = w 0 from by
        rw [← Fin.succ_zero_eq_one, Fin.cons_succ]]
    rfl
  exact congrArg (fun t => t * α x (fun _ : Fin 1 => w 1)) hm

private def oneFormMetricProdSwap
    (α : OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)) :
    Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3 :=
  MultilinearSection.domDomCongr (𝕜 := Real) (F := EuclideanSpace Real (Fin 2))
    (IB := 𝓡 2) (E := TangentSpace (𝓡 2)) (∞ : WithTop ℕ∞) (Equiv.swap (0 : Fin 3) 1)
    (MultilinearSection.product (𝕜 := Real) (F := EuclideanSpace Real (Fin 2)) (IB := 𝓡 2)
      (E := TangentSpace (𝓡 2)) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2) α
      (metricTensorField (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))))

private theorem oneFormMetricProdSwap_cons
    (α : OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (u : TangentSpace (𝓡 2) x) (w : Fin 2 → TangentSpace (𝓡 2) x) :
    oneFormMetricProdSwap α x (Fin.cons u w)
      = α x (fun _ : Fin 1 => w 0)
        * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x u (w 1) := by
  have hstep : oneFormMetricProdSwap α x (Fin.cons u w)
      = (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 3) 1)
          (Bundle.continuousMultilinearMap.product_fun (𝕜 := Real)
            (F := EuclideanSpace Real (Fin 2)) (E := TangentSpace (𝓡 2)) (s := 1) (q := 2)
            (α x)
            ((metricTensorField (I := 𝓡 2)
              (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x)))
          (Fin.cons u w) := rfl
  rw [hstep, ContinuousMultilinearMap.domDomCongr_apply,
    Bundle.continuousMultilinearMap.product_fun_apply]
  have hleft : (fun i : Fin 3 =>
        (Fin.cons u w : Fin 3 → TangentSpace (𝓡 2) x) ((Equiv.swap (0 : Fin 3) 1) i))
        ∘ Fin.castAdd 2
      = fun _ : Fin 1 => w 0 := by
    funext a
    fin_cases a
    rfl
  have hright : (fun i : Fin 3 =>
        (Fin.cons u w : Fin 3 → TangentSpace (𝓡 2) x) ((Equiv.swap (0 : Fin 3) 1) i))
        ∘ Fin.natAdd 1
      = Fin.cons u (fun _ : Fin 1 => w 1) := by
    funext a
    fin_cases a <;> rfl
  rw [hleft, hright]
  have hm : metricTensorField (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
        (Fin.cons u (fun _ : Fin 1 => w 1))
      = (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x u (w 1) := by
    rw [metricTensorField_apply,
      show (Fin.cons u (fun _ : Fin 1 => w 1) : Fin 2 → TangentSpace (𝓡 2) x) 1 = w 1 from by
        rw [← Fin.succ_zero_eq_one, Fin.cons_succ]]
    rfl
  exact congrArg (fun t => α x (fun _ : Fin 1 => w 0) * t) hm

private def tripleDz :
    Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3 :=
  let P : Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3 :=
    MultilinearSection.product (𝕜 := Real) (F := EuclideanSpace Real (Fin 2)) (IB := 𝓡 2)
      (E := TangentSpace (𝓡 2)) (n := (∞ : WithTop ℕ∞)) (s := 1) (q := 2)
      sphereHeightOneForm sphereDzDz
  P

private theorem tripleDz_cons
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (u : TangentSpace (𝓡 2) x) (w : Fin 2 → TangentSpace (𝓡 2) x) :
    tripleDz x (Fin.cons u w)
      = sphereHeightOneForm x (fun _ : Fin 1 => u)
        * (sphereHeightOneForm x (fun _ : Fin 1 => w 0)
            * sphereHeightOneForm x (fun _ : Fin 1 => w 1)) := by
  have hstep : tripleDz x (Fin.cons u w)
      = (Bundle.continuousMultilinearMap.product_fun (𝕜 := Real)
          (F := EuclideanSpace Real (Fin 2)) (E := TangentSpace (𝓡 2)) (s := 1) (q := 2)
          (sphereHeightOneForm x) (sphereDzDz x)) (Fin.cons u w) := rfl
  rw [hstep, Bundle.continuousMultilinearMap.product_fun_apply]
  have hleft : Fin.cons u w ∘ Fin.castAdd 2 = fun _ : Fin 1 => u := by
    funext a
    fin_cases a
    rfl
  have hright : Fin.cons u w ∘ Fin.natAdd 1 = w := by
    funext a
    fin_cases a <;> rfl
  rw [hleft, hright]
  have hdz : sphereDzDz x w
      = sphereHeightOneForm x (fun _ : Fin 1 => w 0)
        * sphereHeightOneForm x (fun _ : Fin 1 => w 1) :=
    oneFormProd_pair sphereHeightOneForm sphereHeightOneForm x w
  exact congrArg (fun t => sphereHeightOneForm x (fun _ : Fin 1 => u) * t) hdz

private def sphereE1Field :
    Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3 :=
  tensor0SField_smulByFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
    (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) (s := 3)
    (fun p => -(6 * sphereHeight p ^ 2)) sphereE1coef_contMDiff
    (oneFormMetricProd sphereHeightOneForm)

private def sphereE2Field :
    Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3 :=
  tensor0SField_smulByFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
      (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) (s := 3)
      (fun p => 72 * sphereHeight p ^ 2) sphere72coef_contMDiff tripleDz
    + tensor0SField_smulByFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
        (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) (s := 3)
        (fun p => -(18 * sphereHeight p ^ 2 * (1 - sphereHeight p ^ 2)))
        sphereE2coef_contMDiff
        (oneFormMetricProd sphereHeightOneForm + oneFormMetricProdSwap sphereHeightOneForm
          + metricOneFormProd sphereHeightOneForm)

private def sphereDzDzDeriv :
    Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3 :=
  prodLeibnizCand sphereHeightOneForm sphereHeightOneForm
    ((sphereConformalDerivs 0).nablaA) ((sphereConformalDerivs 0).nablaA)

private def sphereDBField :
    Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3 :=
  smulLeibnizCand2 (fun p => 6 * sphereHeight p) sphere6z_contMDiff sphereDzDz sphereDzDzDeriv
    + smulLeibnizCand2 (fun p => -(3 * sphereHeight p * (1 - sphereHeight p ^ 2)))
        sphereBcoef_contMDiff
        (metricTensorField (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
        0

private theorem sphereRealize_dzdz :
    TotalNabla0SRealizes (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2) 2
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      sphereDzDz sphereDzDzDeriv :=
  realize_product_oneForm
    (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
    sphereHeightOneForm sphereHeightOneForm
    ((sphereConformalDerivs 0).nablaA) ((sphereConformalDerivs 0).nablaA)
    sphereRealizeZero_first sphereRealizeZero_first

private theorem sphereRealize_B :
    TotalNabla0SRealizes (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2) 2
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      sphereBField sphereDBField :=
  TotalNabla0SRealizes.add
    (realize_smulByFun_two
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      (fun p => 6 * sphereHeight p) sphere6z_contMDiff sphereDzDz sphereDzDzDeriv
      sphereRealize_dzdz)
    (realize_smulByFun_two
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      (fun p => -(3 * sphereHeight p * (1 - sphereHeight p ^ 2))) sphereBcoef_contMDiff
      (metricTensorField (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      0
      (zero_realizes_metric (I := 𝓡 2)
        (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
        (leviCivitaConnectionOfMetric_isMetricCompatible (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))))

set_option maxHeartbeats 3200000 in
private theorem sphereNabla2A_expansion (ε : Real) :
    (sphereConformalDerivs ε).nabla2A
      = (sphereConformalDerivs 0).nabla2A
        + (-ε) • (sphereDBField + sphereE1Field) + (ε * ε) • sphereE2Field := by
  have hfirst : TotalNabla0SRealizes (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
      (I := 𝓡 2) 2 (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
      ((sphereConformalDerivs 0).nablaA + (-ε) • sphereBField)
      ((sphereConformalDerivs ε).nabla2A) := by
    rw [← sphereNablaA_expansion ε]
    exact (sphereConformalDerivs ε).second
  refine totalNabla0SRealizes_unique hfirst ?_
  intro X x slots
  classical
  set Vs : Fin 2 -> ContMDiffSection (𝓡 2) (EuclideanSpace Real (Fin 2)) (∞ : WithTop ℕ∞)
      (TangentSpace (𝓡 2) : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → Type _) :=
    fun a => (ContMDiffSection.exists_eq_at (I := 𝓡 2) (n := (⊤ : ℕ∞))
      (F := EuclideanSpace Real (Fin 2))
      (V := (TangentSpace (𝓡 2) : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → Type _))
      x (slots a)).choose with hVs
  have hslots : (fun a : Fin 2 => Vs a x) = slots := by
    funext a
    exact (ContMDiffSection.exists_eq_at (I := 𝓡 2) (n := (⊤ : ℕ∞))
      (F := EuclideanSpace Real (Fin 2))
      (V := (TangentSpace (𝓡 2) : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → Type _))
      x (slots a)).choose_spec
  rw [← hslots]
  have hsub' : nabla0SFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) 2
      (metricCov (I := 𝓡 2) (sphereConformalMetric ε)) X
      ((sphereConformalDerivs 0).nablaA + (-ε) • sphereBField) x
      (fun a : Fin 2 => Vs a x)
      - nabla0SFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
        (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) 2
        (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
        X ((sphereConformalDerivs 0).nablaA + (-ε) • sphereBField) x
        (fun a : Fin 2 => Vs a x)
      = -∑ a : Fin 2, ((sphereConformalDerivs 0).nablaA + (-ε) • sphereBField) x
          (Function.update (fun b : Fin 2 => Vs b x) a
            ((CovariantDerivative.difference
                (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
                (metricCov (I := 𝓡 2)
                  (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x)
              (Vs a x) (X x))) :=
    nabla0SFun_sub_cov (I := 𝓡 2)
      (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      X Vs ((sphereConformalDerivs 0).nablaA + (-ε) • sphereBField) x
  have hlin : nabla0SFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) 2
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      X ((sphereConformalDerivs 0).nablaA + (-ε) • sphereBField) x
      (fun a : Fin 2 => Vs a x)
      = nabla0SFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) 2
          (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
          X ((sphereConformalDerivs 0).nablaA) x (fun a : Fin 2 => Vs a x)
        + (-ε) * nabla0SFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
            (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) 2
            (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
            X sphereBField x (fun a : Fin 2 => Vs a x) := by
    rw [nabla0SFun_add (I := 𝓡 2)
        (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
        X ((sphereConformalDerivs 0).nablaA) ((-ε) • sphereBField) x,
      nabla0SFun_smul (I := 𝓡 2)
        (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
        X (-ε) sphereBField x]
    rfl
  have hbaseN := sphereRealizeZero_second X x (fun a : Fin 2 => Vs a x)
  have hbaseB := sphereRealize_B X x (fun a : Fin 2 => Vs a x)
  have hdiff0 := sphereConnDiff_apply ε x (Vs 0 x) (X x)
  have hdiff1 := sphereConnDiff_apply ε x (Vs 1 x) (X x)
  set gz : TangentSpace (𝓡 2) x :=
    gradFun (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
      sphereHeight x with hgz
  set dzX : Real := extDerivFun (I := 𝓡 2) sphereHeight x (X x) with hdzX
  set dz0 : Real := extDerivFun (I := 𝓡 2) sphereHeight x (Vs 0 x) with hdz0
  set dz1 : Real := extDerivFun (I := 𝓡 2) sphereHeight x (Vs 1 x) with hdz1
  have hgradInner : ∀ t : TangentSpace (𝓡 2) x,
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x gz t
        = extDerivFun (I := 𝓡 2) sphereHeight x t := by
    intro t
    rw [hgz, inner_gradFun, ← extDerivFun_real_eq_mfderiv]
  have hgradInner' : ∀ t : TangentSpace (𝓡 2) x,
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x t gz
        = extDerivFun (I := 𝓡 2) sphereHeight x t := by
    intro t
    rw [(roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).symm x t gz]
    exact hgradInner t
  have hOneFormVal : ∀ t : TangentSpace (𝓡 2) x,
      sphereHeightOneForm x (fun _ : Fin 1 => t)
        = extDerivFun (I := 𝓡 2) sphereHeight x t :=
    fun t => sphereHeightOneForm_apply x t
  have hgg : (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x gz gz
      = 1 - sphereHeight x ^ 2 := by
    rw [hgz]
    exact sphereGradZ_normSq x
  have hcorr0 : ((sphereConformalDerivs 0).nablaA + (-ε) • sphereBField) x
        (Function.update (fun b : Fin 2 => Vs b x) 0
          ((CovariantDerivative.difference
              (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
              (metricCov (I := 𝓡 2)
                (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x)
            (Vs 0 x) (X x)))
      = (-(sphereHeight x)
            - (-ε) * (3 * sphereHeight x * (1 - sphereHeight x ^ 2)))
          * (ε * (3 * sphereHeight x))
          * (dzX * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
                (Vs 0 x) (Vs 1 x)
              + dz0 * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
                  (X x) (Vs 1 x)
              - (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
                  (Vs 0 x) (X x) * dz1)
        + (-ε) * (6 * sphereHeight x
            * ((ε * (3 * sphereHeight x))
                * (dzX * dz0 + dz0 * dzX
                  - (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
                      (Vs 0 x) (X x) * (1 - sphereHeight x ^ 2))
                * dz1)) := by
    have hupd : ∀ b : Fin 2, b = 0 ∨ b = 1 := by decide
    have hval : ((sphereConformalDerivs 0).nablaA + (-ε) • sphereBField) x
          (Function.update (fun b : Fin 2 => Vs b x) 0
            ((CovariantDerivative.difference
                (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
                (metricCov (I := 𝓡 2)
                  (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x)
              (Vs 0 x) (X x)))
        = (sphereConformalDerivs 0).nablaA x
            (Function.update (fun b : Fin 2 => Vs b x) 0
              ((CovariantDerivative.difference
                  (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
                  (metricCov (I := 𝓡 2)
                    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x)
                (Vs 0 x) (X x)))
          + (-ε) * sphereBField x
              (Function.update (fun b : Fin 2 => Vs b x) 0
                ((CovariantDerivative.difference
                    (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
                    (metricCov (I := 𝓡 2)
                      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x)
                  (Vs 0 x) (X x))) := rfl
    rw [hval, sphereNablaAZero_val, sphereBField_apply]
    simp only [Function.update_self,
      Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
    rw [hdiff0]
    rw [gInner_smul_left, gInner_comb3_left]
    rw [oneFormSlot_smul, oneFormSlot_comb3]
    rw [hgradInner (Vs 1 x)]
    simp only [hOneFormVal, ← hdzX, ← hdz0, ← hdz1]
    rw [show extDerivFun (I := 𝓡 2) sphereHeight x gz
        = (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x gz gz from
      (hgradInner gz).symm]
    rw [hgg]
    ring
  have hcorr1 : ((sphereConformalDerivs 0).nablaA + (-ε) • sphereBField) x
        (Function.update (fun b : Fin 2 => Vs b x) 1
          ((CovariantDerivative.difference
              (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
              (metricCov (I := 𝓡 2)
                (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x)
            (Vs 1 x) (X x)))
      = (-(sphereHeight x)
            - (-ε) * (3 * sphereHeight x * (1 - sphereHeight x ^ 2)))
          * (ε * (3 * sphereHeight x))
          * (dzX * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
                (Vs 0 x) (Vs 1 x)
              + dz1 * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
                  (Vs 0 x) (X x)
              - (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
                  (Vs 1 x) (X x) * dz0)
        + (-ε) * (6 * sphereHeight x
            * (dz0 * ((ε * (3 * sphereHeight x))
                * (dzX * dz1 + dz1 * dzX
                  - (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
                      (Vs 1 x) (X x) * (1 - sphereHeight x ^ 2))))) := by
    have hval : ((sphereConformalDerivs 0).nablaA + (-ε) • sphereBField) x
          (Function.update (fun b : Fin 2 => Vs b x) 1
            ((CovariantDerivative.difference
                (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
                (metricCov (I := 𝓡 2)
                  (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x)
              (Vs 1 x) (X x)))
        = (sphereConformalDerivs 0).nablaA x
            (Function.update (fun b : Fin 2 => Vs b x) 1
              ((CovariantDerivative.difference
                  (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
                  (metricCov (I := 𝓡 2)
                    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x)
                (Vs 1 x) (X x)))
          + (-ε) * sphereBField x
              (Function.update (fun b : Fin 2 => Vs b x) 1
                ((CovariantDerivative.difference
                    (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
                    (metricCov (I := 𝓡 2)
                      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x)
                  (Vs 1 x) (X x))) := rfl
    rw [hval, sphereNablaAZero_val, sphereBField_apply]
    simp only [Function.update_self,
      Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
    rw [hdiff1]
    rw [gInner_smul_right, gInner_comb3_right]
    rw [oneFormSlot_smul, oneFormSlot_comb3]
    rw [hgradInner' (Vs 0 x)]
    simp only [hOneFormVal, ← hdzX, ← hdz0, ← hdz1]
    rw [show extDerivFun (I := 𝓡 2) sphereHeight x gz
        = (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x gz gz from
      (hgradInner gz).symm]
    rw [hgg]
    ring
  have hE1val : sphereE1Field x (Fin.cons (X x) (fun a : Fin 2 => Vs a x))
      = -(6 * sphereHeight x ^ 2) * (dzX
          * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
              (Vs 0 x) (Vs 1 x)) := by
    have hval : sphereE1Field x (Fin.cons (X x) (fun a : Fin 2 => Vs a x))
        = -(6 * sphereHeight x ^ 2)
          * oneFormMetricProd sphereHeightOneForm x
              (Fin.cons (X x) (fun a : Fin 2 => Vs a x)) := rfl
    rw [hval, oneFormMetricProd_cons, hOneFormVal, ← hdzX]
  have hE2val : sphereE2Field x (Fin.cons (X x) (fun a : Fin 2 => Vs a x))
      = 72 * sphereHeight x ^ 2 * (dzX * (dz0 * dz1))
        - 18 * sphereHeight x ^ 2 * (1 - sphereHeight x ^ 2)
          * (dzX * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
                (Vs 0 x) (Vs 1 x)
            + dz0 * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
                (X x) (Vs 1 x)
            + (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
                (X x) (Vs 0 x) * dz1) := by
    have hval : sphereE2Field x (Fin.cons (X x) (fun a : Fin 2 => Vs a x))
        = 72 * sphereHeight x ^ 2
            * tripleDz x (Fin.cons (X x) (fun a : Fin 2 => Vs a x))
          + -(18 * sphereHeight x ^ 2 * (1 - sphereHeight x ^ 2))
            * (oneFormMetricProd sphereHeightOneForm x
                  (Fin.cons (X x) (fun a : Fin 2 => Vs a x))
                + oneFormMetricProdSwap sphereHeightOneForm x
                    (Fin.cons (X x) (fun a : Fin 2 => Vs a x))
                + metricOneFormProd sphereHeightOneForm x
                    (Fin.cons (X x) (fun a : Fin 2 => Vs a x))) := rfl
    rw [hval, tripleDz_cons, oneFormMetricProd_cons, oneFormMetricProdSwap_cons,
      metricOneFormProd_cons]
    simp only [hOneFormVal, ← hdzX, ← hdz0, ← hdz1]
    ring
  have hLHS : ((sphereConformalDerivs 0).nabla2A
        + (-ε) • (sphereDBField + sphereE1Field) + (ε * ε) • sphereE2Field) x
        (Fin.cons (X x) (fun a : Fin 2 => Vs a x))
      = (sphereConformalDerivs 0).nabla2A x (Fin.cons (X x) (fun a : Fin 2 => Vs a x))
        + (-ε) * (sphereDBField x (Fin.cons (X x) (fun a : Fin 2 => Vs a x))
            + sphereE1Field x (Fin.cons (X x) (fun a : Fin 2 => Vs a x)))
        + (ε * ε) * sphereE2Field x (Fin.cons (X x) (fun a : Fin 2 => Vs a x)) := rfl
  have hsum2 : (∑ a : Fin 2, ((sphereConformalDerivs 0).nablaA + (-ε) • sphereBField) x
        (Function.update (fun b : Fin 2 => Vs b x) a
          ((CovariantDerivative.difference
              (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
              (metricCov (I := 𝓡 2)
                (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x)
            (Vs a x) (X x))))
      = ((sphereConformalDerivs 0).nablaA + (-ε) • sphereBField) x
          (Function.update (fun b : Fin 2 => Vs b x) 0
            ((CovariantDerivative.difference
                (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
                (metricCov (I := 𝓡 2)
                  (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x)
              (Vs 0 x) (X x)))
        + ((sphereConformalDerivs 0).nablaA + (-ε) • sphereBField) x
            (Function.update (fun b : Fin 2 => Vs b x) 1
              ((CovariantDerivative.difference
                  (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
                  (metricCov (I := 𝓡 2)
                    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x)
                (Vs 1 x) (X x))) := Fin.sum_univ_two _
  have hsym1 : (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
        (Vs 0 x) (X x)
      = (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (X x) (Vs 0 x) :=
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).symm x (Vs 0 x) (X x)
  have hsym2 : (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
        (Vs 1 x) (X x)
      = (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (X x) (Vs 1 x) :=
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).symm x (Vs 1 x) (X x)
  rw [hLHS, hE1val, hE2val]
  rw [show nabla0SFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) 2
      (metricCov (I := 𝓡 2) (sphereConformalMetric ε)) X
      ((sphereConformalDerivs 0).nablaA + (-ε) • sphereBField) x
      (fun a : Fin 2 => Vs a x)
      = nabla0SFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) 2
          (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
          X ((sphereConformalDerivs 0).nablaA + (-ε) • sphereBField) x
          (fun a : Fin 2 => Vs a x)
        - ∑ a : Fin 2, ((sphereConformalDerivs 0).nablaA + (-ε) • sphereBField) x
            (Function.update (fun b : Fin 2 => Vs b x) a
              ((CovariantDerivative.difference
                  (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
                  (metricCov (I := 𝓡 2)
                    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x)
                (Vs a x) (X x))) from by linarith [hsub']]
  rw [hlin, ← hbaseN, ← hbaseB, hsum2, hcorr0, hcorr1, hsym1, hsym2]
  ring

private theorem finTwoCons_one (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (u : TangentSpace (𝓡 2) x) (w : Fin 1 → TangentSpace (𝓡 2) x) :
    (Fin.cons u w : Fin 2 → TangentSpace (𝓡 2) x) 1 = w 0 := by
  rw [← Fin.succ_zero_eq_one, Fin.cons_succ]

private theorem trace_oneform_metric_flip
    (g : SmoothRiemannianMetric (𝓡 2) (sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {x : sphere (0 : EuclideanSpace Real (Fin 3)) 1}
    (basis : Module.Basis Idx Real (TangentSpace (𝓡 2) x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis_gen (I := 𝓡 2) g x basis gInv)
    (A : Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) 1 x)
    (w : TangentSpace (𝓡 2) x) :
    (∑ i : Idx, ∑ j : Idx,
        gInv i j * (g.inner x (basis i) w * A (fun _ : Fin 1 => basis j)))
      = A (fun _ : Fin 1 => w) := by
  classical
  set L : TangentSpace (𝓡 2) x →L[Real] Real :=
    continuousMultilinearCurryFin1 Real (TangentSpace (𝓡 2) x) Real A with hLdef
  have hLA : ∀ v : TangentSpace (𝓡 2) x, A (fun _ : Fin 1 => v) = L v := by
    intro v
    rw [hLdef, continuousMultilinearCurryFin1_apply]
    exact congrArg (⇑A) (Fin.snoc_zero _ v).symm
  have hexp : ∀ i : Idx,
      g.inner x (basis i) w = ∑ k : Idx, basis.repr w k * g.inner x (basis i) (basis k) := by
    intro i
    conv_lhs => rw [← basis.sum_repr w]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [map_smul, smul_eq_mul]
  have hcoord : ∀ j : Idx,
      (∑ i : Idx, gInv i j * g.inner x (basis i) w) = basis.repr w j := by
    intro j
    calc
      (∑ i : Idx, gInv i j * g.inner x (basis i) w)
          = ∑ i : Idx, ∑ k : Idx,
              basis.repr w k * (gInv i j * g.inner x (basis i) (basis k)) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hexp i, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = ∑ k : Idx, basis.repr w k *
              (∑ i : Idx, g.inner x (basis k) (basis i) * gInv i j) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [g.symm x (basis i) (basis k)]
            ring
      _ = ∑ k : Idx, basis.repr w k * (if k = j then (1 : Real) else 0) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [(hinv k j).2]
      _ = basis.repr w j := by
            rw [Finset.sum_congr rfl (fun k _ => by rw [mul_ite, mul_one, mul_zero])]
            rw [Finset.sum_ite_eq' Finset.univ j (fun k => basis.repr w k)]
            simp
  calc
    (∑ i : Idx, ∑ j : Idx,
        gInv i j * (g.inner x (basis i) w * A (fun _ : Fin 1 => basis j)))
        = ∑ j : Idx, ∑ i : Idx,
            gInv i j * (g.inner x (basis i) w * A (fun _ : Fin 1 => basis j)) :=
          Finset.sum_comm
    _ = ∑ j : Idx, A (fun _ : Fin 1 => basis j) *
          (∑ i : Idx, gInv i j * g.inner x (basis i) w) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ j : Idx, basis.repr w j • L (basis j) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hcoord j, hLA (basis j), smul_eq_mul]
          ring
    _ = L (∑ j : Idx, basis.repr w j • basis j) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [map_smul]
    _ = L w := by rw [basis.sum_repr w]
    _ = A (fun _ : Fin 1 => w) := (hLA w).symm

private theorem extDeriv_six_z
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) (u : TangentSpace (𝓡 2) x) :
    extDerivFun (I := 𝓡 2)
        (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => 6 * sphereHeight p) x u
      = 6 * extDerivFun (I := 𝓡 2) sphereHeight x u := by
  rw [extDerivFun_const_mul (𝓡 2) (6 : Real) (sphereHeight_mdiffAt x),
    ContinuousLinearMap.smul_apply, smul_eq_mul]

private theorem extDeriv_Bcoef2
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) (u : TangentSpace (𝓡 2) x) :
    extDerivFun (I := 𝓡 2)
        (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
          -(3 * sphereHeight p * (1 - sphereHeight p ^ 2))) x u
      = (9 * sphereHeight x ^ 2 - 3) * extDerivFun (I := 𝓡 2) sphereHeight x u := by
  have hz_at := sphereHeight_mdiffAt x
  have hzz : MDifferentiableAt (𝓡 2) 𝓘(Real, Real)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        sphereHeight p * sphereHeight p) x := hz_at.mul hz_at
  have hzzz : MDifferentiableAt (𝓡 2) 𝓘(Real, Real)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        sphereHeight p * (sphereHeight p * sphereHeight p)) x := hz_at.mul hzz
  have h3zzz : MDifferentiableAt (𝓡 2) 𝓘(Real, Real)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        (3 : Real) * (sphereHeight p * (sphereHeight p * sphereHeight p))) x :=
    (mdifferentiableAt_const (I := 𝓡 2) (I' := 𝓘(Real, Real)) (c := (3 : Real))).mul hzzz
  have h3z : MDifferentiableAt (𝓡 2) 𝓘(Real, Real)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        (3 : Real) * sphereHeight p) x :=
    (mdifferentiableAt_const (I := 𝓡 2) (I' := 𝓘(Real, Real)) (c := (3 : Real))).mul hz_at
  have hfun : (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        -(3 * sphereHeight p * (1 - sphereHeight p ^ 2)))
      = fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
          (3 : Real) * (sphereHeight p * (sphereHeight p * sphereHeight p))
            - (3 : Real) * sphereHeight p := by
    funext p
    ring
  rw [hfun, extDerivFun_sub_at (I := 𝓡 2) u h3zzz h3z]
  have h1 : extDerivFun (I := 𝓡 2)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        (3 : Real) * (sphereHeight p * (sphereHeight p * sphereHeight p))) x u
      = 3 * extDerivFun (I := 𝓡 2)
          (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
            sphereHeight p * (sphereHeight p * sphereHeight p)) x u := by
    rw [extDerivFun_const_mul (𝓡 2) (3 : Real) hzzz,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
  have h2 : extDerivFun (I := 𝓡 2)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        (3 : Real) * sphereHeight p) x u
      = 3 * extDerivFun (I := 𝓡 2) sphereHeight x u := by
    rw [extDerivFun_const_mul (𝓡 2) (3 : Real) hz_at,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
  have h3 : extDerivFun (I := 𝓡 2)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        sphereHeight p * (sphereHeight p * sphereHeight p)) x u
      = sphereHeight x * extDerivFun (I := 𝓡 2)
          (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
            sphereHeight p * sphereHeight p) x u
        + (sphereHeight x * sphereHeight x) * extDerivFun (I := 𝓡 2) sphereHeight x u :=
    extDerivFun_mul_at (I := 𝓡 2) u hz_at hzz
  have h4 : extDerivFun (I := 𝓡 2)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        sphereHeight p * sphereHeight p) x u
      = sphereHeight x * extDerivFun (I := 𝓡 2) sphereHeight x u
        + sphereHeight x * extDerivFun (I := 𝓡 2) sphereHeight x u :=
    extDerivFun_mul_at (I := 𝓡 2) u hz_at hz_at
  rw [h1, h2, h3, h4]
  ring

private theorem nablaZero_pair (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (u t : TangentSpace (𝓡 2) x) :
    (sphereConformalDerivs 0).nablaA x (Fin.cons u (fun _ : Fin 1 => t))
      = -(sphereHeight x)
        * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x u t := by
  rw [sphereNablaAZero_val, finTwoCons_one]
  rfl

private theorem dzdz_pair (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (u t : TangentSpace (𝓡 2) x) :
    sphereDzDz x (Fin.cons u (fun _ : Fin 1 => t))
      = sphereHeightOneForm x (fun _ : Fin 1 => u)
        * sphereHeightOneForm x (fun _ : Fin 1 => t) :=
  oneFormProd_cons sphereHeightOneForm sphereHeightOneForm x u (fun _ : Fin 1 => t)

private theorem sphereRoughLap_conformal (ε : Real)
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (T : Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) 3 x)
    (ww : Fin 1 → TangentSpace (𝓡 2) x) :
    roughLap0STensor (I := 𝓡 2) (sphereConformalMetric ε) (s := 1) T ww
      = Real.exp (-(2 * legendreConformalFactor ε x))
        * roughLap0STensor (I := 𝓡 2)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (s := 1) T ww := by
  classical
  rw [roughLap0STensor_apply, roughLap0STensor_apply]
  set basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := 𝓡 2) x
    with hbasis
  set gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
        (EuclideanSpace Real (Fin 2))
      → DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
          (EuclideanSpace Real (Fin 2)) → Real :=
    fun k l => DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x k l
      (extChartAt (𝓡 2) x x) with hgInv
  have hinv : MetricInverseInBasis_gen (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x basis gInv :=
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
  have hinvε : MetricInverseInBasis_gen (I := 𝓡 2)
      (conformalMetric (legendreConformalFactor ε) (legendreConformalFactor_contMDiff ε)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x basis
      (fun i j => Real.exp (-(2 * legendreConformalFactor ε x)) * gInv i j) :=
    metricInvBasis_conformal (I := 𝓡 2) (legendreConformalFactor ε)
      (legendreConformalFactor_contMDiff ε)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) basis gInv hinv
  rw [show sphereConformalMetric ε
      = conformalMetric (legendreConformalFactor ε) (legendreConformalFactor_contMDiff ε)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) from rfl]
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := 𝓡 2)
      (conformalMetric (legendreConformalFactor ε) (legendreConformalFactor_contMDiff ε)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) basis
      (fun i j => Real.exp (-(2 * legendreConformalFactor ε x)) * gInv i j) hinvε T ww,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) basis gInv hinv T ww]
  unfold metricTrace0S2InBasis
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem sphereTracePair_conformal (ε : Real)
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (B : Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) 2 x) :
    metricTracePair0SAt (I := 𝓡 2) (sphereConformalMetric ε) B
      = Real.exp (-(2 * legendreConformalFactor ε x))
        * metricTracePair0SAt (I := 𝓡 2)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) B := by
  classical
  set basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := 𝓡 2) x
    with hbasis
  set gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
        (EuclideanSpace Real (Fin 2))
      → DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
          (EuclideanSpace Real (Fin 2)) → Real :=
    fun k l => DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x k l
      (extChartAt (𝓡 2) x x) with hgInv
  have hinv : MetricInverseInBasis_gen (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x basis gInv :=
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
  have hinvε : MetricInverseInBasis_gen (I := 𝓡 2)
      (conformalMetric (legendreConformalFactor ε) (legendreConformalFactor_contMDiff ε)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) x basis
      (fun i j => Real.exp (-(2 * legendreConformalFactor ε x)) * gInv i j) :=
    metricInvBasis_conformal (I := 𝓡 2) (legendreConformalFactor ε)
      (legendreConformalFactor_contMDiff ε)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) basis gInv hinv
  rw [show sphereConformalMetric ε
      = conformalMetric (legendreConformalFactor ε) (legendreConformalFactor_contMDiff ε)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) from rfl]
  rw [metricTracePair0SAt_eq_sum_basis (I := 𝓡 2)
      (conformalMetric (legendreConformalFactor ε) (legendreConformalFactor_contMDiff ε)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) basis
      (fun i j => Real.exp (-(2 * legendreConformalFactor ε x)) * gInv i j) hinvε B,
    metricTracePair0SAt_eq_sum_basis (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) basis gInv hinv B]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem sphereAhlfors_conformal (ε : Real)
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (T : Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) 2 x) :
    ahlforsOperator (I := 𝓡 2) (sphereConformalMetric ε) T
      = ahlforsOperator (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) T := by
  unfold ahlforsOperator traceFreePart0S
  rw [sphereTracePair_conformal ε x]
  have hmet : metricTensor0S (I := 𝓡 2) (sphereConformalMetric ε) x
      = Real.exp (2 * legendreConformalFactor ε x) •
        metricTensor0S (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x := by
    rw [show sphereConformalMetric ε
        = conformalMetric (legendreConformalFactor ε) (legendreConformalFactor_contMDiff ε)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) from rfl]
    exact metricTensor0S_conformal (I := 𝓡 2) (legendreConformalFactor ε)
      (legendreConformalFactor_contMDiff ε)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
  rw [hmet, smul_smul]
  congr 2
  have hcancel : Real.exp (-(2 * legendreConformalFactor ε x))
      * Real.exp (2 * legendreConformalFactor ε x) = 1 := by
    rw [← Real.exp_add]
    norm_num
  linear_combination ((↑(Module.finrank Real (EuclideanSpace Real (Fin 2))) : Real)⁻¹
    * metricTracePair0SAt (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
        (symmetricPart0S (I := 𝓡 2) T)) * hcancel

private theorem sphereRoughLap_linear
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) (a b : Real)
    (T₀ T₁ T₂ : Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) 3 x)
    (ww : Fin 1 → TangentSpace (𝓡 2) x) :
    roughLap0STensor (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (s := 1)
        (T₀ + a • T₁ + b • T₂) ww
      = roughLap0STensor (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (s := 1) T₀ ww
        + a * roughLap0STensor (I := 𝓡 2)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (s := 1) T₁ ww
        + b * roughLap0STensor (I := 𝓡 2)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (s := 1) T₂ ww := by
  classical
  rw [roughLap0STensor_apply, roughLap0STensor_apply, roughLap0STensor_apply,
    roughLap0STensor_apply]
  set basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := 𝓡 2) x
    with hbasis
  set gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
        (EuclideanSpace Real (Fin 2))
      → DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
          (EuclideanSpace Real (Fin 2)) → Real :=
    fun k l => DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x k l
      (extChartAt (𝓡 2) x x) with hgInv
  have hinv : MetricInverseInBasis_gen (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x basis gInv :=
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) basis gInv hinv
      (T₀ + a • T₁ + b • T₂) ww,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) basis gInv hinv T₀ ww,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) basis gInv hinv T₁ ww,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) basis gInv hinv T₂ ww]
  unfold metricTrace0S2InBasis
  have hpt : ∀ i j, gInv i j * ((T₀ + a • T₁ + b • T₂)
        (metricTraceInput (I := 𝓡 2) (basis i) (basis j) ww))
      = gInv i j * T₀ (metricTraceInput (I := 𝓡 2) (basis i) (basis j) ww)
        + a * (gInv i j * T₁ (metricTraceInput (I := 𝓡 2) (basis i) (basis j) ww))
        + b * (gInv i j * T₂ (metricTraceInput (I := 𝓡 2) (basis i) (basis j) ww)) := by
    intro i j
    rw [show (T₀ + a • T₁ + b • T₂)
          (metricTraceInput (I := 𝓡 2) (basis i) (basis j) ww)
        = T₀ (metricTraceInput (I := 𝓡 2) (basis i) (basis j) ww)
          + a * T₁ (metricTraceInput (I := 𝓡 2) (basis i) (basis j) ww)
          + b * T₂ (metricTraceInput (I := 𝓡 2) (basis i) (basis j) ww) from rfl]
    ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib),
    Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib),
    Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun i _ => (Finset.mul_sum _ _ _).symm), ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i _ => (Finset.mul_sum _ _ _).symm), ← Finset.mul_sum]

section TraceSums

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : sphere (0 : EuclideanSpace Real (Fin 3)) 1}
variable (basis : Module.Basis Idx Real (TangentSpace (𝓡 2) x))
variable (gInv : Idx → Idx → Real)

private theorem sum_dz_dz
    (hinv : MetricInverseInBasis_gen (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x basis gInv) :
    (∑ i : Idx, ∑ j : Idx, gInv i j
        * (sphereHeightOneForm x (fun _ : Fin 1 => basis i)
            * sphereHeightOneForm x (fun _ : Fin 1 => basis j)))
      = 1 - sphereHeight x ^ 2 := by
  have hpt : ∀ i j : Idx, gInv i j
        * (sphereHeightOneForm x (fun _ : Fin 1 => basis i)
            * sphereHeightOneForm x (fun _ : Fin 1 => basis j))
      = gInv i j * (sphereHeightOneForm x (fun _ : Fin 1 => basis i)
          * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (basis j)
              (gradFun (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
                sphereHeight x)) := by
    intro i j
    rw [show sphereHeightOneForm x (fun _ : Fin 1 => basis j)
        = (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (basis j)
            (gradFun (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
              sphereHeight x) from by
      rw [sphereOneForm_eq_inner_grad]
      exact (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).symm x _ _]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))]
  rw [trace_oneform_metric (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
    basis gInv hinv (sphereHeightOneForm x)
    (gradFun (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
      sphereHeight x)]
  exact sphereOneForm_gradZ x

private theorem sum_g_g
    (hinv : MetricInverseInBasis_gen (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x basis gInv)
    (hcard : Fintype.card Idx = 2) :
    (∑ i : Idx, ∑ j : Idx, gInv i j
        * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (basis i) (basis j))
      = 2 := by
  have hpt : ∀ i j : Idx, gInv i j
        * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (basis i) (basis j)
      = gInv i j
        * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (basis j) (basis i) := by
    intro i j
    rw [(roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).symm x (basis i) (basis j)]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))]
  have hrow : ∀ i : Idx, (∑ j : Idx, gInv i j
        * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (basis j) (basis i))
      = 1 := by
    intro i
    rw [(hinv i i).1]
    simp
  rw [Finset.sum_congr rfl (fun i _ => hrow i)]
  rw [Finset.sum_const, Finset.card_univ, hcard]
  norm_num

end TraceSums

set_option maxHeartbeats 3200000 in
private theorem sphereTrace_DBE1
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (ww : Fin 1 → TangentSpace (𝓡 2) x) :
    roughLap0STensor (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (s := 1)
        ((sphereDBField + sphereE1Field) x) ww
      = (3 - 21 * sphereHeight x ^ 2) * sphereHeightOneForm x ww := by
  classical
  rw [roughLap0STensor_apply]
  set basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := 𝓡 2) x
    with hbasis
  set gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
        (EuclideanSpace Real (Fin 2))
      → DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
          (EuclideanSpace Real (Fin 2)) → Real :=
    fun k l => DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x k l
      (extChartAt (𝓡 2) x x) with hgInv
  have hinv : MetricInverseInBasis_gen (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x basis gInv :=
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
  have hcard : Fintype.card
      (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
        (EuclideanSpace Real (Fin 2))) = 2 := by
    rw [← Module.finrank_eq_card_basis basis]
    exact finrank_euclideanSpace_fin
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := 𝓡 2)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) basis gInv hinv
    ((sphereDBField + sphereE1Field) x) ww]
  unfold metricTrace0S2InBasis
  have hval : ∀ i j, (sphereDBField + sphereE1Field) x
        (metricTraceInput (I := 𝓡 2) (basis i) (basis j) ww)
      = (extDerivFun (I := 𝓡 2)
            (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => 6 * sphereHeight p) x
            (basis i))
          * (sphereDzDz x (Fin.cons (basis j) ww))
        + (6 * sphereHeight x)
          * ((sphereConformalDerivs 0).nablaA x
                (Fin.cons (basis i) (fun _ : Fin 1 => (Fin.cons (basis j) ww :
                  Fin 2 → TangentSpace (𝓡 2) x) 0))
              * sphereHeightOneForm x (fun _ : Fin 1 => (Fin.cons (basis j) ww :
                  Fin 2 → TangentSpace (𝓡 2) x) 1)
            + sphereHeightOneForm x (fun _ : Fin 1 => (Fin.cons (basis j) ww :
                Fin 2 → TangentSpace (𝓡 2) x) 0)
              * (sphereConformalDerivs 0).nablaA x
                  (Fin.cons (basis i) (fun _ : Fin 1 => (Fin.cons (basis j) ww :
                    Fin 2 → TangentSpace (𝓡 2) x) 1)))
        + ((extDerivFun (I := 𝓡 2)
              (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
                -(3 * sphereHeight p * (1 - sphereHeight p ^ 2))) x (basis i))
            * (metricTensorField (I := 𝓡 2)
                (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
                (Fin.cons (basis j) ww))
          + (-(3 * sphereHeight x * (1 - sphereHeight x ^ 2))) * 0)
        + (-(6 * sphereHeight x ^ 2))
          * (sphereHeightOneForm x (fun _ : Fin 1 => basis i)
              * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
                  ((Fin.cons (basis j) ww : Fin 2 → TangentSpace (𝓡 2) x) 0)
                  ((Fin.cons (basis j) ww : Fin 2 → TangentSpace (𝓡 2) x) 1)) := by
    intro i j
    have hsplit : (sphereDBField + sphereE1Field) x
          (metricTraceInput (I := 𝓡 2) (basis i) (basis j) ww)
        = smulLeibnizCand2 (fun p => 6 * sphereHeight p) sphere6z_contMDiff sphereDzDz
            sphereDzDzDeriv x (Fin.cons (basis i) (Fin.cons (basis j) ww))
          + smulLeibnizCand2
              (fun p => -(3 * sphereHeight p * (1 - sphereHeight p ^ 2)))
              sphereBcoef_contMDiff
              (metricTensorField (I := 𝓡 2)
                (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) 0 x
              (Fin.cons (basis i) (Fin.cons (basis j) ww))
          + sphereE1Field x (Fin.cons (basis i) (Fin.cons (basis j) ww)) := rfl
    rw [hsplit, smulLeibnizCand2_cons, smulLeibnizCand2_cons]
    rw [show sphereDzDzDeriv x (Fin.cons (basis i) (Fin.cons (basis j) ww))
        = (sphereConformalDerivs 0).nablaA x
            (Fin.cons (basis i) (fun _ : Fin 1 => (Fin.cons (basis j) ww :
              Fin 2 → TangentSpace (𝓡 2) x) 0))
          * sphereHeightOneForm x (fun _ : Fin 1 => (Fin.cons (basis j) ww :
              Fin 2 → TangentSpace (𝓡 2) x) 1)
        + sphereHeightOneForm x (fun _ : Fin 1 => (Fin.cons (basis j) ww :
            Fin 2 → TangentSpace (𝓡 2) x) 0)
          * (sphereConformalDerivs 0).nablaA x
              (Fin.cons (basis i) (fun _ : Fin 1 => (Fin.cons (basis j) ww :
                Fin 2 → TangentSpace (𝓡 2) x) 1)) from
      prodLeibnizCand_cons sphereHeightOneForm sphereHeightOneForm
        ((sphereConformalDerivs 0).nablaA) ((sphereConformalDerivs 0).nablaA) x
        (basis i) (Fin.cons (basis j) ww)]
    rw [show sphereE1Field x (Fin.cons (basis i) (Fin.cons (basis j) ww))
        = (-(6 * sphereHeight x ^ 2))
          * (sphereHeightOneForm x (fun _ : Fin 1 => basis i)
              * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
                  ((Fin.cons (basis j) ww : Fin 2 → TangentSpace (𝓡 2) x) 0)
                  ((Fin.cons (basis j) ww : Fin 2 → TangentSpace (𝓡 2) x) 1)) from by
      rw [show sphereE1Field x (Fin.cons (basis i) (Fin.cons (basis j) ww))
          = (-(6 * sphereHeight x ^ 2))
            * oneFormMetricProd sphereHeightOneForm x
                (Fin.cons (basis i) (Fin.cons (basis j) ww)) from rfl,
        oneFormMetricProd_cons]]
    rw [show ((0 : Tensor0SField (𝕜 := Real) (E := EuclideanSpace Real (Fin 2)) (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (n := (∞ : WithTop ℕ∞)) 3) x)
          (Fin.cons (basis i) (Fin.cons (basis j) ww)) = 0 from rfl]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    congrArg (fun t => gInv i j * t) (hval i j)))]
  have hww : (fun _ : Fin 1 => ww 0) = ww := by
    funext a
    fin_cases a
    rfl
  have hval2 : ∀ i j, gInv i j
        * ((extDerivFun (I := 𝓡 2)
              (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => 6 * sphereHeight p) x
              (basis i))
            * (sphereDzDz x (Fin.cons (basis j) ww))
          + (6 * sphereHeight x)
            * ((sphereConformalDerivs 0).nablaA x
                  (Fin.cons (basis i) (fun _ : Fin 1 => (Fin.cons (basis j) ww :
                    Fin 2 → TangentSpace (𝓡 2) x) 0))
                * sphereHeightOneForm x (fun _ : Fin 1 => (Fin.cons (basis j) ww :
                    Fin 2 → TangentSpace (𝓡 2) x) 1)
              + sphereHeightOneForm x (fun _ : Fin 1 => (Fin.cons (basis j) ww :
                  Fin 2 → TangentSpace (𝓡 2) x) 0)
                * (sphereConformalDerivs 0).nablaA x
                    (Fin.cons (basis i) (fun _ : Fin 1 => (Fin.cons (basis j) ww :
                      Fin 2 → TangentSpace (𝓡 2) x) 1)))
          + ((extDerivFun (I := 𝓡 2)
                (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
                  -(3 * sphereHeight p * (1 - sphereHeight p ^ 2))) x (basis i))
              * (metricTensorField (I := 𝓡 2)
                  (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
                  (Fin.cons (basis j) ww))
            + (-(3 * sphereHeight x * (1 - sphereHeight x ^ 2))) * 0)
          + (-(6 * sphereHeight x ^ 2))
            * (sphereHeightOneForm x (fun _ : Fin 1 => basis i)
                * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
                    ((Fin.cons (basis j) ww : Fin 2 → TangentSpace (𝓡 2) x) 0)
                    ((Fin.cons (basis j) ww : Fin 2 → TangentSpace (𝓡 2) x) 1)))
      = (6 * sphereHeightOneForm x ww)
          * (gInv i j * (sphereHeightOneForm x (fun _ : Fin 1 => basis i)
              * sphereHeightOneForm x (fun _ : Fin 1 => basis j)))
        + (-(6 * sphereHeight x ^ 2) * sphereHeightOneForm x ww)
          * (gInv i j * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
              (basis i) (basis j))
        + (-(6 * sphereHeight x ^ 2))
          * (gInv i j * ((roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
                (basis i) (ww 0)
              * sphereHeightOneForm x (fun _ : Fin 1 => basis j)))
        + (3 * sphereHeight x ^ 2 - 3)
          * (gInv i j * (sphereHeightOneForm x (fun _ : Fin 1 => basis i)
              * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
                  (basis j) (ww 0))) := by
    intro i j
    rw [Fin.cons_zero, finTwoCons_one x (basis j) ww]
    have hdz : sphereDzDz x (Fin.cons (basis j) ww)
        = sphereHeightOneForm x (fun _ : Fin 1 => basis j)
          * sphereHeightOneForm x (fun _ : Fin 1 => ww 0) := by
      have h1 := oneFormProd_pair sphereHeightOneForm sphereHeightOneForm x
        (Fin.cons (basis j) ww)
      rw [Fin.cons_zero, finTwoCons_one x (basis j) ww] at h1
      exact h1
    have hmet : metricTensorField (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
          (Fin.cons (basis j) ww)
        = (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (basis j)
            (ww 0) := by
      have h1 := metricTensorField_apply (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x (Fin.cons (basis j) ww)
      rw [Fin.cons_zero, finTwoCons_one x (basis j) ww] at h1
      exact h1
    rw [hdz, hmet, extDeriv_six_z, extDeriv_Bcoef2,
      nablaZero_pair x (basis i) (basis j), nablaZero_pair x (basis i) (ww 0)]
    rw [show extDerivFun (I := 𝓡 2) sphereHeight x (basis i)
        = sphereHeightOneForm x (fun _ : Fin 1 => basis i) from
      (sphereHeightOneForm_apply x (basis i)).symm]
    rw [show sphereHeightOneForm x (fun _ : Fin 1 => ww 0)
        = sphereHeightOneForm x ww from congrArg _ hww]
    rw [(roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).symm x (basis i) (ww 0)]
    rw [show (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (ww 0) (basis i)
        = (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (basis i) (ww 0)
        from (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).symm x (ww 0) (basis i)]
    ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hval2 i j))]
  have hsplit4 : ∀ (c₁ c₂ c₃ c₄ : Real)
      (s₁ s₂ s₃ s₄ : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
          (EuclideanSpace Real (Fin 2))
        → DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
            (EuclideanSpace Real (Fin 2)) → Real),
      (∑ i, ∑ j, (c₁ * s₁ i j + c₂ * s₂ i j + c₃ * s₃ i j + c₄ * s₄ i j))
        = c₁ * (∑ i, ∑ j, s₁ i j) + c₂ * (∑ i, ∑ j, s₂ i j)
          + c₃ * (∑ i, ∑ j, s₃ i j) + c₄ * (∑ i, ∑ j, s₄ i j) := by
    intro c₁ c₂ c₃ c₄ s₁ s₂ s₃ s₄
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit4]
  rw [sum_dz_dz basis gInv hinv, sum_g_g basis gInv hinv hcard,
    trace_oneform_metric_flip (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
      basis gInv hinv (sphereHeightOneForm x) (ww 0),
    trace_oneform_metric (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
      basis gInv hinv (sphereHeightOneForm x) (ww 0)]
  rw [show sphereHeightOneForm x (fun _ : Fin 1 => ww 0)
      = sphereHeightOneForm x ww from congrArg _ hww]
  ring

set_option maxHeartbeats 3200000 in
private theorem sphereTrace_E2
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (ww : Fin 1 → TangentSpace (𝓡 2) x) :
    roughLap0STensor (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (s := 1)
        (sphereE2Field x) ww
      = 0 := by
  classical
  rw [roughLap0STensor_apply]
  set basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := 𝓡 2) x
    with hbasis
  set gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
        (EuclideanSpace Real (Fin 2))
      → DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
          (EuclideanSpace Real (Fin 2)) → Real :=
    fun k l => DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x k l
      (extChartAt (𝓡 2) x x) with hgInv
  have hinv : MetricInverseInBasis_gen (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x basis gInv :=
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
  have hcard : Fintype.card
      (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
        (EuclideanSpace Real (Fin 2))) = 2 := by
    rw [← Module.finrank_eq_card_basis basis]
    exact finrank_euclideanSpace_fin
  rw [metricTraceFirstTwo0SAt_eq_sum_basis (I := 𝓡 2)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) basis gInv hinv
    (sphereE2Field x) ww]
  unfold metricTrace0S2InBasis
  have hww : (fun _ : Fin 1 => ww 0) = ww := by
    funext a
    fin_cases a
    rfl
  have hval2 : ∀ i j, gInv i j
        * sphereE2Field x (metricTraceInput (I := 𝓡 2) (basis i) (basis j) ww)
      = (72 * sphereHeight x ^ 2 * sphereHeightOneForm x ww)
          * (gInv i j * (sphereHeightOneForm x (fun _ : Fin 1 => basis i)
              * sphereHeightOneForm x (fun _ : Fin 1 => basis j)))
        + (-(18 * sphereHeight x ^ 2 * (1 - sphereHeight x ^ 2))
            * sphereHeightOneForm x ww)
          * (gInv i j * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
              (basis i) (basis j))
        + (-(18 * sphereHeight x ^ 2 * (1 - sphereHeight x ^ 2)))
          * (gInv i j * ((roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
                (basis i) (ww 0)
              * sphereHeightOneForm x (fun _ : Fin 1 => basis j)))
        + (-(18 * sphereHeight x ^ 2 * (1 - sphereHeight x ^ 2)))
          * (gInv i j * (sphereHeightOneForm x (fun _ : Fin 1 => basis i)
              * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
                  (basis j) (ww 0))) := by
    intro i j
    have hsplit : sphereE2Field x
          (metricTraceInput (I := 𝓡 2) (basis i) (basis j) ww)
        = (72 * sphereHeight x ^ 2)
            * tripleDz x (Fin.cons (basis i) (Fin.cons (basis j) ww))
          + (-(18 * sphereHeight x ^ 2 * (1 - sphereHeight x ^ 2)))
            * (oneFormMetricProd sphereHeightOneForm x
                  (Fin.cons (basis i) (Fin.cons (basis j) ww))
                + oneFormMetricProdSwap sphereHeightOneForm x
                    (Fin.cons (basis i) (Fin.cons (basis j) ww))
                + metricOneFormProd sphereHeightOneForm x
                    (Fin.cons (basis i) (Fin.cons (basis j) ww))) := rfl
    rw [hsplit, tripleDz_cons, oneFormMetricProd_cons, oneFormMetricProdSwap_cons,
      metricOneFormProd_cons]
    rw [Fin.cons_zero, finTwoCons_one x (basis j) ww]
    rw [show sphereHeightOneForm x (fun _ : Fin 1 => ww 0)
        = sphereHeightOneForm x ww from congrArg _ hww]
    rw [(roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).symm x (basis i) (ww 0)]
    rw [show (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (ww 0) (basis i)
        = (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x (basis i) (ww 0)
        from (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).symm x (ww 0) (basis i)]
    ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hval2 i j))]
  have hsplit4 : ∀ (c₁ c₂ c₃ c₄ : Real)
      (s₁ s₂ s₃ s₄ : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
          (EuclideanSpace Real (Fin 2))
        → DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
            (EuclideanSpace Real (Fin 2)) → Real),
      (∑ i, ∑ j, (c₁ * s₁ i j + c₂ * s₂ i j + c₃ * s₃ i j + c₄ * s₄ i j))
        = c₁ * (∑ i, ∑ j, s₁ i j) + c₂ * (∑ i, ∑ j, s₂ i j)
          + c₃ * (∑ i, ∑ j, s₃ i j) + c₄ * (∑ i, ∑ j, s₄ i j) := by
    intro c₁ c₂ c₃ c₄ s₁ s₂ s₃ s₄
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit4]
  rw [sum_dz_dz basis gInv hinv, sum_g_g basis gInv hinv hcard,
    trace_oneform_metric_flip (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
      basis gInv hinv (sphereHeightOneForm x) (ww 0),
    trace_oneform_metric (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
      basis gInv hinv (sphereHeightOneForm x) (ww 0)]
  rw [show sphereHeightOneForm x (fun _ : Fin 1 => ww 0)
      = sphereHeightOneForm x ww from congrArg _ hww]
  ring

private theorem sphereRoughLapEps (ε : Real)
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (ww : Fin 1 → TangentSpace (𝓡 2) x) :
    roughLap0STensor (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (s := 1)
        ((sphereConformalDerivs ε).nabla2A x) ww
      = (-1 + (-ε) * (3 - 21 * sphereHeight x ^ 2)) * sphereHeightOneForm x ww := by
  rw [sphereNabla2A_expansion ε]
  have hval : ((sphereConformalDerivs 0).nabla2A
        + (-ε) • (sphereDBField + sphereE1Field) + (ε * ε) • sphereE2Field) x
      = (sphereConformalDerivs 0).nabla2A x
        + (-ε) • ((sphereDBField + sphereE1Field) x)
        + (ε * ε) • (sphereE2Field x) := rfl
  rw [hval, sphereRoughLap_linear]
  have hzero : roughLap0STensor (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (s := 1)
      ((sphereConformalDerivs 0).nabla2A x) ww
      = -(sphereHeightOneForm x ww) := by
    rw [sphereConformalDerivs_zero_nabla2A_roughLap x]
    rfl
  rw [hzero, sphereTrace_DBE1, sphereTrace_E2]
  ring

private theorem inner0S_add_right''
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Nat)
    (A B C : Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) s x) :
    inner0S (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x s A (B + C)
      = inner0S (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x s A B
        + inner0S (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x s A C := by
  let D := tensor0SMetricData (I := 𝓡 2)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x s
  change D.flat A (B + C) = D.flat A B + D.flat A C
  rw [(D.flat A).map_add]

private theorem swapSlots_linear
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) (c : Real)
    (A B : Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) 2 x) :
    swapSlots0S (I := 𝓡 2) (A + c • B)
      = swapSlots0S (I := 𝓡 2) A + c • swapSlots0S (I := 𝓡 2) B := by
  ext vv
  rw [swapSlots0S_apply']
  have hL : (A + c • B) (fun i => vv (Equiv.swap (0 : Fin 2) 1 i))
      = A (fun i => vv (Equiv.swap (0 : Fin 2) 1 i))
        + c * B (fun i => vv (Equiv.swap (0 : Fin 2) 1 i)) := rfl
  rw [hL]
  have hR : (swapSlots0S (I := 𝓡 2) A + c • swapSlots0S (I := 𝓡 2) B) vv
      = swapSlots0S (I := 𝓡 2) A vv + c * swapSlots0S (I := 𝓡 2) B vv := rfl
  rw [hR, swapSlots0S_apply', swapSlots0S_apply']

private theorem symPart_linear
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) (c : Real)
    (A B : Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) 2 x) :
    symmetricPart0S (I := 𝓡 2) (A + c • B)
      = symmetricPart0S (I := 𝓡 2) A + c • symmetricPart0S (I := 𝓡 2) B := by
  unfold symmetricPart0S
  rw [swapSlots_linear x c A B]
  module

private theorem tracePair_linear
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) (c : Real)
    (A B : Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) 2 x) :
    metricTracePair0SAt (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (A + c • B)
      = metricTracePair0SAt (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) A
        + c * metricTracePair0SAt (I := 𝓡 2)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) B := by
  unfold metricTracePair0SAt
  rw [inner0S_add_right'' x 2 _ A (c • B), inner0S_smul_right]

private theorem sphereAhlfors_linear
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) (c : Real)
    (A B : Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) 2 x) :
    ahlforsOperator (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (A + c • B)
      = ahlforsOperator (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) A
        + c • ahlforsOperator (I := 𝓡 2)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) B := by
  unfold ahlforsOperator traceFreePart0S
  rw [symPart_linear x c A B, tracePair_linear x c
    (symmetricPart0S (I := 𝓡 2) A) (symmetricPart0S (I := 𝓡 2) B)]
  rw [mul_add, add_smul]
  module

private theorem sphereB_symm (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    swapSlots0S (I := 𝓡 2) (sphereBField x) = sphereBField x := by
  ext vv
  rw [swapSlots0S_apply']
  have h1 := sphereBField_apply x (fun i => vv (Equiv.swap (0 : Fin 2) 1 i))
  have h2 := sphereBField_apply x vv
  rw [h1, h2]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [(roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).symm x (vv 1) (vv 0)]
  ring

private theorem sphereB_traceFree (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    metricTracePair0SAt (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (sphereBField x) = 0 := by
  classical
  set basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := 𝓡 2) x
    with hbasis
  set gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
        (EuclideanSpace Real (Fin 2))
      → DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
          (EuclideanSpace Real (Fin 2)) → Real :=
    fun k l => DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x k l
      (extChartAt (𝓡 2) x x) with hgInv
  have hinv : MetricInverseInBasis_gen (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x basis gInv :=
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
  have hcard : Fintype.card
      (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
        (EuclideanSpace Real (Fin 2))) = 2 := by
    rw [← Module.finrank_eq_card_basis basis]
    exact finrank_euclideanSpace_fin
  rw [metricTracePair0SAt_eq_sum_basis (I := 𝓡 2)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) basis gInv hinv
    (sphereBField x)]
  have hval : ∀ i j, gInv i j * sphereBField x (vec2 (I := 𝓡 2) (basis i) (basis j))
      = (6 * sphereHeight x)
          * (gInv i j * (sphereHeightOneForm x (fun _ : Fin 1 => basis i)
              * sphereHeightOneForm x (fun _ : Fin 1 => basis j)))
        + (-(3 * sphereHeight x * (1 - sphereHeight x ^ 2)))
          * (gInv i j * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
              (basis i) (basis j)) := by
    intro i j
    have h1 := sphereBField_apply x (vec2 (I := 𝓡 2) (basis i) (basis j))
    rw [show (vec2 (I := 𝓡 2) (basis i) (basis j) : Fin 2 → TangentSpace (𝓡 2) x) 0
        = basis i from rfl,
      show (vec2 (I := 𝓡 2) (basis i) (basis j) : Fin 2 → TangentSpace (𝓡 2) x) 1
        = basis j from rfl] at h1
    rw [h1]
    ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hval i j))]
  have hsplit2 : ∀ (c₁ c₂ : Real)
      (s₁ s₂ : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
          (EuclideanSpace Real (Fin 2))
        → DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
            (EuclideanSpace Real (Fin 2)) → Real),
      (∑ i, ∑ j, (c₁ * s₁ i j + c₂ * s₂ i j))
        = c₁ * (∑ i, ∑ j, s₁ i j) + c₂ * (∑ i, ∑ j, s₂ i j) := by
    intro c₁ c₂ s₁ s₂
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit2]
  rw [sum_dz_dz basis gInv hinv, sum_g_g basis gInv hinv hcard]
  ring

private theorem sphereAhlfors_B (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    ahlforsOperator (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (sphereBField x)
      = sphereBField x := by
  unfold ahlforsOperator traceFreePart0S
  have hsym : symmetricPart0S (I := 𝓡 2) (sphereBField x) = sphereBField x := by
    unfold symmetricPart0S
    rw [sphereB_symm x]
    module
  rw [hsym, sphereB_traceFree x]
  rw [mul_zero, zero_smul]
  abel

private theorem sphereAhlforsEps (ε : Real)
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    ahlforsOperator (I := 𝓡 2) (sphereConformalMetric ε)
        ((sphereConformalDerivs ε).nablaA x)
      = (-ε) • sphereBField x := by
  rw [sphereAhlfors_conformal ε x, sphereNablaA_expansion ε]
  have hval : ((sphereConformalDerivs 0).nablaA + (-ε) • sphereBField) x
      = (sphereConformalDerivs 0).nablaA x + (-ε) • sphereBField x := rfl
  rw [hval, sphereAhlfors_linear x (-ε) ((sphereConformalDerivs 0).nablaA x) (sphereBField x),
    sphereConformalDerivs_zero_nablaA_ahlfors x, sphereAhlfors_B x]
  abel

private theorem extDeriv_zonal_chain (G G' : Real → Real)
    (hd : ∀ t : Real, HasDerivAt G (G' t) t)
    (y : sphere (0 : EuclideanSpace Real (Fin 3)) 1) (u : TangentSpace (𝓡 2) y) :
    extDerivFun (I := 𝓡 2)
        (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => G (sphereHeight p)) y u
      = G' (sphereHeight y) * extDerivFun (I := 𝓡 2) sphereHeight y u := by
  rw [extDerivFun_real_eq_mfderiv, extDerivFun_real_eq_mfderiv]
  have hzm : MDifferentiableAt (𝓡 2) 𝓘(Real, Real) sphereHeight y := sphereHeight_mdiffAt y
  have hGm : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Real) G (sphereHeight y) := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact (hd (sphereHeight y)).differentiableAt
  have hcomp := mfderiv_comp (I := 𝓡 2) (I' := 𝓘(Real, Real)) (I'' := 𝓘(Real, Real))
    y hGm hzm
  have h1 : mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => G (sphereHeight p)) y u
      = ((mfderiv 𝓘(Real, Real) 𝓘(Real, Real) G (sphereHeight y)).comp
          (mfderiv (𝓡 2) 𝓘(Real, Real) sphereHeight y)) u :=
    congrArg (fun L : TangentSpace (𝓡 2) y →L[Real] Real => L u) hcomp
  rw [h1, ContinuousLinearMap.comp_apply]
  rw [show mfderiv 𝓘(Real, Real) 𝓘(Real, Real) G (sphereHeight y)
      = fderiv Real G (sphereHeight y) from mfderiv_eq_fderiv]
  rw [(hd (sphereHeight y)).hasFDerivAt.fderiv]
  exact mul_comm (G := Real) ((mfderiv (𝓡 2) 𝓘(Real, Real) sphereHeight y) u)
    (G' (sphereHeight y))

private theorem formLaplacianScalar_congr
    {f₁ f₂ : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → Real} (h : f₁ = f₂)
    (h₁ : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ f₁) (h₂ : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ f₂)
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    formLaplacianScalar (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) h₁ x
      = formLaplacianScalar (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) h₂ x := by
  subst h
  rfl

set_option maxHeartbeats 1600000 in
private theorem formLaplacianScalar_zonal
    (F F' F'' : Real → Real)
    (hφ : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F (sphereHeight p)))
    (hφ' : ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F' (sphereHeight p)))
    (hd1 : ∀ t : Real, HasDerivAt F (F' t) t)
    (hd2 : ∀ t : Real, HasDerivAt F' (F'' t) t)
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    formLaplacianScalar (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) hφ x
      = -(F'' (sphereHeight x) * (1 - sphereHeight x ^ 2))
        + 2 * sphereHeight x * F' (sphereHeight x) := by
  classical
  have hduChain : duSec (I := 𝓡 2)
        (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F (sphereHeight p)) hφ
      = tensor0SField_smulByFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
          (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) (s := 1)
          (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F' (sphereHeight p)) hφ'
          sphereHeightOneForm := by
    refine DFunLike.ext _ _ fun y => ?_
    refine ContinuousMultilinearMap.ext fun vv => ?_
    have hvv : vv = fun _ : Fin 1 => vv 0 := by
      funext a
      fin_cases a
      rfl
    rw [hvv]
    have hL : duSec (I := 𝓡 2)
          (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F (sphereHeight p)) hφ y
          (fun _ : Fin 1 => vv 0)
        = extDerivFun (I := 𝓡 2)
            (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F (sphereHeight p)) y
            (vv 0) := duSec_val _ hφ y (vv 0)
    have hR : (tensor0SField_smulByFun (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
          (I := 𝓡 2) (n := (∞ : WithTop ℕ∞)) (s := 1)
          (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F' (sphereHeight p)) hφ'
          sphereHeightOneForm) y (fun _ : Fin 1 => vv 0)
        = F' (sphereHeight y) * sphereHeightOneForm y (fun _ : Fin 1 => vv 0) := rfl
    have hmid : extDerivFun (I := 𝓡 2)
        (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F (sphereHeight p)) y (vv 0)
        = F' (sphereHeight y) * sphereHeightOneForm y (fun _ : Fin 1 => vv 0) := by
      rw [extDeriv_zonal_chain F F' hd1 y (vv 0), sphereHeightOneForm_apply]
    exact hL.trans (hmid.trans hR.symm)
  have hmc : DifferentialGeometry.Integral.Connection.IsMetricCompatible_gen
      (I := 𝓡 2)
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) :=
    leviCivitaConnectionOfMetric_isMetricCompatible (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
  have hcovsm := metricCov_smooth (I := 𝓡 2)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
  have hreal : TotalNabla0SRealizes (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
      (I := 𝓡 2) 1
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      (duSec (I := 𝓡 2)
        (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F (sphereHeight p)) hφ)
      (hessianSec (I := 𝓡 2)
        (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
        hcovsm
        (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F (sphereHeight p)) hφ) :=
    totalNabla0S_realizes 1
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      (duSec (I := 𝓡 2)
        (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F (sphereHeight p)) hφ)
      (totalNabla0S_reg 1
        (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
        hcovsm
        (duSec (I := 𝓡 2)
          (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F (sphereHeight p)) hφ))
  have hrealCand : TotalNabla0SRealizes (𝕜 := Real) (E := EuclideanSpace Real (Fin 2))
      (I := 𝓡 2) 1
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      (duSec (I := 𝓡 2)
        (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F (sphereHeight p)) hφ)
      (smulLeibnizCand1
        (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F' (sphereHeight p)) hφ'
        sphereHeightOneForm ((sphereConformalDerivs 0).nablaA)) := by
    rw [hduChain]
    exact realize_smulByFun_one
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F' (sphereHeight p)) hφ'
      sphereHeightOneForm ((sphereConformalDerivs 0).nablaA) sphereRealizeZero_first
  have hfield : hessianSec (I := 𝓡 2)
        (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
        hcovsm
        (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F (sphereHeight p)) hφ
      = smulLeibnizCand1
          (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F' (sphereHeight p)) hφ'
          sphereHeightOneForm ((sphereConformalDerivs 0).nablaA) :=
    totalNabla0SRealizes_unique hreal hrealCand
  have hlapeq : formLaplacianScalar (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) hφ x
      = -(laplacian (I := 𝓡 2)
          (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
          (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F (sphereHeight p)) x) := by
    rw [formLaplacianScalar_eq_neg_Δ_g (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) hφ x]
    rw [← laplacian_levi_eq (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) hφ x]
    rfl
  rw [hlapeq]
  have htrace : laplacian (I := 𝓡 2)
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F (sphereHeight p)) x
      = scalarLapTraceAt (I := 𝓡 2)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
          (hessianSec (I := 𝓡 2)
            (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
            hcovsm
            (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F (sphereHeight p)) hφ x) :=
    ScalarLaplacianRealizesTraceAt.eq_trace (I := 𝓡 2)
      (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F (sphereHeight p)) _
      (scalarLap_smooth (I := 𝓡 2)
        (metricCov (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
        hcovsm (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) hmc
        (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F (sphereHeight p)) hφ)
  rw [htrace, hfield]
  classical
  set basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := 𝓡 2) x
    with hbasis
  set gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
        (EuclideanSpace Real (Fin 2))
      → DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
          (EuclideanSpace Real (Fin 2)) → Real :=
    fun k l => DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x k l
      (extChartAt (𝓡 2) x x) with hgInv
  have hinv : MetricInverseInBasis_gen (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x basis gInv :=
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
  have hcard : Fintype.card
      (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
        (EuclideanSpace Real (Fin 2))) = 2 := by
    rw [← Module.finrank_eq_card_basis basis]
    exact finrank_euclideanSpace_fin
  rw [scalarLapTraceAt_eq_pair, metricTracePair0SAt_eq_sum_basis (I := 𝓡 2)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) basis gInv hinv]
  have hval : ∀ i j, gInv i j
        * (smulLeibnizCand1
            (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => F' (sphereHeight p)) hφ'
            sphereHeightOneForm ((sphereConformalDerivs 0).nablaA)) x
            (vec2 (I := 𝓡 2) (basis i) (basis j))
      = (F'' (sphereHeight x))
          * (gInv i j * (sphereHeightOneForm x (fun _ : Fin 1 => basis i)
              * sphereHeightOneForm x (fun _ : Fin 1 => basis j)))
        + (-(sphereHeight x) * F' (sphereHeight x))
          * (gInv i j * (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x
              (basis i) (basis j)) := by
    intro i j
    have hvec : (vec2 (I := 𝓡 2) (basis i) (basis j) : Fin 2 → TangentSpace (𝓡 2) x)
        = Fin.cons (basis i) (fun _ : Fin 1 => basis j) := by
      funext a
      fin_cases a <;> rfl
    rw [hvec, smulLeibnizCand1_cons, extDeriv_zonal_chain F' F'' hd2 x (basis i),
      nablaZero_pair x (basis i) (basis j)]
    rw [show extDerivFun (I := 𝓡 2) sphereHeight x (basis i)
        = sphereHeightOneForm x (fun _ : Fin 1 => basis i) from
      (sphereHeightOneForm_apply x (basis i)).symm]
    ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hval i j))]
  have hsplit2 : ∀ (c₁ c₂ : Real)
      (s₁ s₂ : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
          (EuclideanSpace Real (Fin 2))
        → DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
            (EuclideanSpace Real (Fin 2)) → Real),
      (∑ i, ∑ j, (c₁ * s₁ i j + c₂ * s₂ i j))
        = c₁ * (∑ i, ∑ j, s₁ i j) + c₂ * (∑ i, ∑ j, s₂ i j) := by
    intro c₁ c₂ s₁ s₂
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit2, sum_dz_dz basis gInv hinv, sum_g_g basis gInv hinv hcard]
  ring

private theorem sphereK_eq (ε : Real) (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    gaussCurvature (I := 𝓡 2) (sphereConformalMetric ε) x
      = Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
        * (1 + 3 * (ε * (3 * sphereHeight x ^ 2 - 1))) := by
  have hdim : Module.finrank Real (EuclideanSpace Real (Fin 2)) = 2 :=
    finrank_euclideanSpace_fin
  have hd1 : ∀ t : Real, HasDerivAt (fun s : Real => ε * ((3 * s ^ 2 - 1) / 2))
      (ε * (3 * t)) t := by
    intro t
    have hp : HasDerivAt (fun s : Real => s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h := (((hp.const_mul 3).sub_const 1).div_const 2).const_mul ε
    convert h using 1
    ring
  have hd2 : ∀ t : Real, HasDerivAt (fun s : Real => ε * (3 * s)) (ε * 3) t := by
    intro t
    have h := ((hasDerivAt_id t).const_mul 3).const_mul ε
    convert h using 1
    ring
  have hφ' : ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        ε * (3 * sphereHeight p)) :=
    contMDiff_const.mul (contMDiff_const.mul sphereHeight_contMDiff)
  have hlapval : formLaplacianScalar (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
      (legendreConformalFactor_contMDiff ε) x
      = -(ε * 3 * (1 - sphereHeight x ^ 2))
        + 2 * sphereHeight x * (ε * (3 * sphereHeight x)) := by
    have hcongr := formLaplacianScalar_congr (f₁ := legendreConformalFactor ε)
      (f₂ := fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        (fun t : Real => ε * ((3 * t ^ 2 - 1) / 2)) (sphereHeight p)) rfl
      (legendreConformalFactor_contMDiff ε) (legendreConformalFactor_contMDiff ε) x
    rw [hcongr]
    have hz := formLaplacianScalar_zonal (fun t : Real => ε * ((3 * t ^ 2 - 1) / 2))
      (fun t : Real => ε * (3 * t)) (fun _ : Real => ε * 3)
      (legendreConformalFactor_contMDiff ε) hφ' hd1 hd2 x
    rw [hz]
  rw [show sphereConformalMetric ε
      = conformalMetric (legendreConformalFactor ε) (legendreConformalFactor_contMDiff ε)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) from rfl]
  rw [gaussCurvature_conformalMetric (I := 𝓡 2) hdim (legendreConformalFactor ε)
    (legendreConformalFactor_contMDiff ε)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x]
  rw [roundMetric_gaussCurvature_eq_one x, hlapval]
  rw [show legendreConformalFactor ε x
      = ε * ((3 * sphereHeight x ^ 2 - 1) / 2) from rfl]
  rw [show -(2 * (ε * ((3 * sphereHeight x ^ 2 - 1) / 2)))
      = -(ε * (3 * sphereHeight x ^ 2 - 1)) from by ring]
  ring

private theorem sphereKsm (ε : Real) :
    ContMDiff (𝓡 2) 𝓘(Real, Real) ∞
      (gaussCurvature (I := 𝓡 2) (sphereConformalMetric ε)) := by
  have hdim : Module.finrank Real (EuclideanSpace Real (Fin 2)) = 2 :=
    finrank_euclideanSpace_fin
  have hK1 : ∀ x, gaussCurvature (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x = 1 :=
    roundMetric_gaussCurvature_eq_one
  have hK : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞
      (gaussCurvature (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) := by
    rw [funext hK1]
    exact contMDiff_const
  rw [show sphereConformalMetric ε
      = conformalMetric (legendreConformalFactor ε) (legendreConformalFactor_contMDiff ε)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) from rfl]
  exact gaussCurvature_conformalMetric_contMDiff (I := 𝓡 2) hdim
    (legendreConformalFactor ε) (legendreConformalFactor_contMDiff ε)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) hK

set_option maxHeartbeats 1600000 in
private theorem sphereLapK_eq (ε : Real) (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    formLaplacianScalar (I := 𝓡 2)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (sphereKsm ε) x
      = -(Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
            * (ε * (6 * (2 - 3 * (ε * (3 * sphereHeight x ^ 2 - 1)))
              - 36 * ε * sphereHeight x ^ 2
                * (5 - 3 * (ε * (3 * sphereHeight x ^ 2 - 1)))))
          * (1 - sphereHeight x ^ 2))
        + 2 * sphereHeight x
          * (Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
            * (6 * ε * sphereHeight x
              * (2 - 3 * (ε * (3 * sphereHeight x ^ 2 - 1))))) := by
  have hfun : gaussCurvature (I := 𝓡 2) (sphereConformalMetric ε)
      = fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
          (fun t : Real => Real.exp (-(ε * (3 * t ^ 2 - 1)))
            * (1 + 3 * (ε * (3 * t ^ 2 - 1)))) (sphereHeight p) := by
    funext p
    exact sphereK_eq ε p
  have hinner : ∀ t : Real, HasDerivAt (fun s : Real => -(ε * (3 * s ^ 2 - 1)))
      (-(ε * (6 * t))) t := by
    intro t
    have hp : HasDerivAt (fun s : Real => s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h := (((hp.const_mul 3).sub_const 1).const_mul ε).neg
    convert h using 1
    ring
  have hexpD : ∀ t : Real, HasDerivAt
      (fun s : Real => Real.exp (-(ε * (3 * s ^ 2 - 1))))
      (Real.exp (-(ε * (3 * t ^ 2 - 1))) * (-(ε * (6 * t)))) t := by
    intro t
    exact (hinner t).exp
  have hd1 : ∀ t : Real, HasDerivAt
      (fun s : Real => Real.exp (-(ε * (3 * s ^ 2 - 1))) * (1 + 3 * (ε * (3 * s ^ 2 - 1))))
      (Real.exp (-(ε * (3 * t ^ 2 - 1)))
        * (6 * ε * t * (2 - 3 * (ε * (3 * t ^ 2 - 1))))) t := by
    intro t
    have hp : HasDerivAt (fun s : Real => s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have hlin : HasDerivAt (fun s : Real => 1 + 3 * (ε * (3 * s ^ 2 - 1)))
        (3 * (ε * (6 * t))) t := by
      have h := (((hp.const_mul 3).sub_const 1).const_mul ε).const_mul 3 |>.const_add 1
      convert h using 1
      ring
    have h := (hexpD t).mul hlin
    convert h using 1
    ring
  have hd2 : ∀ t : Real, HasDerivAt
      (fun s : Real => Real.exp (-(ε * (3 * s ^ 2 - 1)))
        * (6 * ε * s * (2 - 3 * (ε * (3 * s ^ 2 - 1)))))
      (Real.exp (-(ε * (3 * t ^ 2 - 1)))
        * (ε * (6 * (2 - 3 * (ε * (3 * t ^ 2 - 1)))
          - 36 * ε * t ^ 2 * (5 - 3 * (ε * (3 * t ^ 2 - 1)))))) t := by
    intro t
    have hp : HasDerivAt (fun s : Real => s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have hG : HasDerivAt (fun s : Real => 6 * ε * s * (2 - 3 * (ε * (3 * s ^ 2 - 1))))
        (6 * ε * (2 - 3 * (ε * (3 * t ^ 2 - 1)))
          + 6 * ε * t * (-(3 * (ε * (6 * t))))) t := by
      have hlin1 : HasDerivAt (fun s : Real => 6 * ε * s) (6 * ε) t := by
        have h := (hasDerivAt_id t).const_mul (6 * ε)
        convert h using 1
        ring
      have hlin2 : HasDerivAt (fun s : Real => 2 - 3 * (ε * (3 * s ^ 2 - 1)))
          (-(3 * (ε * (6 * t)))) t := by
        have h := (((hp.const_mul 3).sub_const 1).const_mul ε).const_mul 3 |>.neg.const_add 2
        convert h using 1
        ring
      have h := hlin1.mul hlin2
      convert h using 1
    have h := (hexpD t).mul hG
    convert h using 1
    ring
  have hφF : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        (fun t : Real => Real.exp (-(ε * (3 * t ^ 2 - 1)))
          * (1 + 3 * (ε * (3 * t ^ 2 - 1)))) (sphereHeight p)) := by
    rw [← hfun]
    exact sphereKsm ε
  have hφ' : ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        Real.exp (-(ε * (3 * sphereHeight p ^ 2 - 1)))
          * (6 * ε * sphereHeight p * (2 - 3 * (ε * (3 * sphereHeight p ^ 2 - 1))))) := by
    have hbase : ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
          3 * sphereHeight p ^ 2 - 1) :=
      (contMDiff_const.mul (sphereHeight_contMDiff.pow 2)).sub contMDiff_const
    have hin0 : ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
          ε * (3 * sphereHeight p ^ 2 - 1)) := contMDiff_const.mul hbase
    have hin : ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
          -(ε * (3 * sphereHeight p ^ 2 - 1))) := hin0.neg
    have hexp : ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
          Real.exp (-(ε * (3 * sphereHeight p ^ 2 - 1)))) :=
      Real.contDiff_exp.comp_contMDiff hin
    have hin1 : ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
          2 - 3 * (ε * (3 * sphereHeight p ^ 2 - 1))) :=
      contMDiff_const.sub (contMDiff_const.mul hin0)
    have hin2 : ContMDiff (𝓡 2) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
          6 * ε * sphereHeight p * (2 - 3 * (ε * (3 * sphereHeight p ^ 2 - 1)))) :=
      (contMDiff_const.mul sphereHeight_contMDiff).mul hin1
    exact hexp.mul hin2
  have hcongr := formLaplacianScalar_congr hfun (sphereKsm ε) hφF x
  rw [hcongr]
  exact formLaplacianScalar_zonal
    (fun t : Real => Real.exp (-(ε * (3 * t ^ 2 - 1))) * (1 + 3 * (ε * (3 * t ^ 2 - 1))))
    (fun t : Real => Real.exp (-(ε * (3 * t ^ 2 - 1)))
      * (6 * ε * t * (2 - 3 * (ε * (3 * t ^ 2 - 1)))))
    (fun t : Real => Real.exp (-(ε * (3 * t ^ 2 - 1)))
      * (ε * (6 * (2 - 3 * (ε * (3 * t ^ 2 - 1)))
        - 36 * ε * t ^ 2 * (5 - 3 * (ε * (3 * t ^ 2 - 1))))))
    hφF hφ' hd1 hd2 x

private theorem sphereVtensor (ε : Real) (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    roughLap0STensor (I := 𝓡 2) (sphereConformalMetric ε) (s := 1)
        ((sphereConformalDerivs ε).nabla2A x)
      + gaussCurvature (I := 𝓡 2) (sphereConformalMetric ε) x • sphereHeightOneForm x
      = (ε * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
          * (30 * sphereHeight x ^ 2 - 6)) • sphereHeightOneForm x := by
  refine ContinuousMultilinearMap.ext fun ww => ?_
  have hexp : Real.exp (-(2 * legendreConformalFactor ε x))
      = Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1))) := by
    refine congrArg Real.exp ?_
    rw [show legendreConformalFactor ε x = ε * ((3 * sphereHeight x ^ 2 - 1) / 2) from rfl]
    ring
  have hL : (roughLap0STensor (I := 𝓡 2) (sphereConformalMetric ε) (s := 1)
        ((sphereConformalDerivs ε).nabla2A x)
      + gaussCurvature (I := 𝓡 2) (sphereConformalMetric ε) x • sphereHeightOneForm x) ww
      = roughLap0STensor (I := 𝓡 2) (sphereConformalMetric ε) (s := 1)
          ((sphereConformalDerivs ε).nabla2A x) ww
        + gaussCurvature (I := 𝓡 2) (sphereConformalMetric ε) x
          * sphereHeightOneForm x ww := rfl
  have hR : ((ε * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
        * (30 * sphereHeight x ^ 2 - 6)) • sphereHeightOneForm x) ww
      = (ε * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
          * (30 * sphereHeight x ^ 2 - 6)) * sphereHeightOneForm x ww := rfl
  refine hL.trans (Eq.trans ?_ hR.symm)
  rw [sphereRoughLap_conformal ε x ((sphereConformalDerivs ε).nabla2A x) ww,
    sphereRoughLapEps ε x ww, sphereK_eq ε x, hexp]
  ring

private theorem sphereNormSq_smul
    (g : SmoothRiemannianMetric (𝓡 2) (sphere (0 : EuclideanSpace Real (Fin 3)) 1))
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Nat) (c : Real)
    (A : Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) s x) :
    normSq0S (I := 𝓡 2) g x s (c • A) = c ^ 2 * normSq0S (I := 𝓡 2) g x s A := by
  rw [normSq0S_eq_inner, normSq0S_eq_inner, inner0S_smul_left, inner0S_smul_right]
  ring

private theorem sphereNormSq_h_eps (ε : Real)
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    normSq0S (I := 𝓡 2) (sphereConformalMetric ε) x 1 (sphereHeightOneForm x)
      = Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1))) * (1 - sphereHeight x ^ 2) := by
  rw [show sphereConformalMetric ε
      = conformalMetric (legendreConformalFactor ε) (legendreConformalFactor_contMDiff ε)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) from rfl]
  rw [normSq0S_conformal (I := 𝓡 2) (legendreConformalFactor ε)
    (legendreConformalFactor_contMDiff ε)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) 1 (sphereHeightOneForm x)]
  rw [sphereNormSq_h]
  refine congrArg (fun t => t * (1 - sphereHeight x ^ 2)) (congrArg Real.exp ?_)
  rw [show legendreConformalFactor ε x = ε * ((3 * sphereHeight x ^ 2 - 1) / 2) from rfl]
  push_cast
  ring

private theorem sphereNormSq_conf_two (ε : Real)
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (A : Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) 2 x) :
    normSq0S (I := 𝓡 2) (sphereConformalMetric ε) x 2 A
      = Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1))))
        * normSq0S (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x 2 A := by
  rw [show sphereConformalMetric ε
      = conformalMetric (legendreConformalFactor ε) (legendreConformalFactor_contMDiff ε)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) from rfl]
  rw [normSq0S_conformal (I := 𝓡 2) (legendreConformalFactor ε)
    (legendreConformalFactor_contMDiff ε)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) 2 A]
  refine congrArg (fun t => t * normSq0S (I := 𝓡 2)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x 2 A) (congrArg Real.exp ?_)
  rw [show legendreConformalFactor ε x = ε * ((3 * sphereHeight x ^ 2 - 1) / 2) from rfl]
  push_cast
  ring

private local instance sphereMeasurableSpace :
    MeasurableSpace (sphere (0 : EuclideanSpace Real (Fin 3)) 1) := borel _

private local instance sphereBorelSpace :
    BorelSpace (sphere (0 : EuclideanSpace Real (Fin 3)) 1) := ⟨rfl⟩

private theorem sphereIntegral_conformal (ε : Real)
    (f : sphere (0 : EuclideanSpace Real (Fin 3)) 1 → Real) :
    (∫ x, f x ∂(riemannianVolumeMeasure (I := 𝓡 2)
        (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (sphereConformalMetric ε)))
      = ∫ x, Real.exp (ε * (3 * sphereHeight x ^ 2 - 1)) * f x
          ∂(riemannianVolumeMeasure (I := 𝓡 2)
            (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) := by
  rw [show sphereConformalMetric ε
      = conformalMetric (legendreConformalFactor ε) (legendreConformalFactor_contMDiff ε)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) from rfl]
  rw [volume_conformal (I := 𝓡 2) (legendreConformalFactor ε)
    (legendreConformalFactor_contMDiff ε)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))]
  rw [integral_withDensity_eq_integral_toReal_smul
    (μ := riemannianVolumeMeasure (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
    (measurable_conformalDensity (I := 𝓡 2) (legendreConformalFactor ε)
      (legendreConformalFactor_contMDiff ε))
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) f]
  refine congrArg (MeasureTheory.integral _) (funext fun x => ?_)
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
  refine congrArg (fun t => t * f x) (congrArg Real.exp ?_)
  rw [show legendreConformalFactor ε x = ε * ((3 * sphereHeight x ^ 2 - 1) / 2) from rfl]
  have hfr : ((Module.finrank Real (EuclideanSpace Real (Fin 2)) : ℕ) : Real) = 2 := by
    rw [finrank_euclideanSpace_fin]
    norm_num
  rw [hfr]
  ring

private def sphereT1 (ε : Real) : Real :=
  ∫ x, normSq0S (I := 𝓡 2) (sphereConformalMetric ε) x 1
      (roughLap0STensor (I := 𝓡 2) (sphereConformalMetric ε) (s := 1)
          ((sphereConformalDerivs ε).nabla2A x)
        + gaussCurvature (I := 𝓡 2) (sphereConformalMetric ε) x • sphereHeightOneForm x)
    ∂(riemannianVolumeMeasure (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (sphereConformalMetric ε))

private def sphereT2 (ε : Real) : Real :=
  ∫ x, gaussCurvature (I := 𝓡 2) (sphereConformalMetric ε) x
      * normSq0S (I := 𝓡 2) (sphereConformalMetric ε) x 2
          (ahlforsOperator (I := 𝓡 2) (sphereConformalMetric ε)
            ((sphereConformalDerivs ε).nablaA x))
    ∂(riemannianVolumeMeasure (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (sphereConformalMetric ε))

private def sphereT3 (ε : Real) : Real :=
  ∫ x, formLaplacianScalar (I := 𝓡 2) (sphereConformalMetric ε) (sphereKsm ε) x
      * normSq0S (I := 𝓡 2) (sphereConformalMetric ε) x 1 (sphereHeightOneForm x)
    ∂(riemannianVolumeMeasure (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) (sphereConformalMetric ε))

private theorem sphereQ_decomp (ε : Real) :
    sphereCurvatureEnergy ε = sphereT1 ε + 2 * sphereT2 ε + 2⁻¹ * sphereT3 ε := by
  have hdim : Module.finrank Real (EuclideanSpace Real (Fin 2)) = 2 :=
    finrank_euclideanSpace_fin
  have hR2 : ∀ x, Nabla2OneFormRealizesAt (I := 𝓡 2)
      (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
      sphereHeightOneForm ((sphereConformalDerivs ε).nablaA) x
      ((sphereConformalDerivs ε).nabla2A x) :=
    fun x => nabla2OneFormRealizesAt_of_totalNabla
      (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
      sphereHeightOneForm ((sphereConformalDerivs ε).nablaA)
      ((sphereConformalDerivs ε).nabla2A)
      (sphereConformalDerivs ε).first (sphereConformalDerivs ε).second x
  have hR1 : NablaOneFormSectionRealizes (I := 𝓡 2)
      (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
      sphereHeightOneForm ((sphereConformalDerivs ε).nablaA) :=
    fun x => (hR2 x).1 x
  have hid := curvatureEnergyIdentity_twoDim hdim (sphereConformalMetric ε)
    sphereHeightOneForm ((sphereConformalDerivs ε).nablaA)
    (fun x => (sphereConformalDerivs ε).nabla2A x) (sphereKsm ε) hR1 hR2
  exact hid

private def zonalA (ε t : Real) : Real :=
  -((6 * (2 - 3 * (ε * (3 * t ^ 2 - 1)))
      - 36 * ε * t ^ 2 * (5 - 3 * (ε * (3 * t ^ 2 - 1)))) * (1 - t ^ 2))
    + 12 * t ^ 2 * (2 - 3 * (ε * (3 * t ^ 2 - 1)))

private def zonalR (ε t : Real) : Real :=
  324 * ε * t ^ 6 - 432 * ε * t ^ 4 + 108 * ε * t ^ 2 - 342 * t ^ 4 + 288 * t ^ 2 - 18

private theorem zonalA_split (ε t : Real) :
    zonalA ε t = (36 * t ^ 2 - 12) + ε * zonalR ε t := by
  rw [zonalA, zonalR]
  ring

private theorem zonalR_bound (ε t : Real) (hε : |ε| ≤ 1) (ht : t ^ 2 ≤ 1) :
    |zonalR ε t| ≤ 1512 := by
  rw [zonalR]
  have h1 : -1 ≤ ε := by
    have := abs_le.mp hε
    linarith [this.1]
  have h2 : ε ≤ 1 := (abs_le.mp hε).2
  have ht0 : 0 ≤ t ^ 2 := sq_nonneg t
  have ht4 : t ^ 4 ≤ 1 := by nlinarith
  have ht40 : 0 ≤ t ^ 4 := by positivity
  have ht6 : t ^ 6 ≤ 1 := by nlinarith
  have ht60 : 0 ≤ t ^ 6 := by positivity
  rw [abs_le]
  constructor <;> nlinarith [mul_le_one₀ h2 ht60 ht6, mul_le_one₀ h2 ht40 ht4,
    mul_le_one₀ h2 ht0 ht]

private theorem zonalA_bound (ε t : Real) (hε : |ε| ≤ 1) (ht : t ^ 2 ≤ 1) :
    |zonalA ε t| ≤ 1560 := by
  rw [zonalA_split]
  have h1 := zonalR_bound ε t hε ht
  have h2 : |36 * t ^ 2 - 12| ≤ 48 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg t]
  calc |36 * t ^ 2 - 12 + ε * zonalR ε t|
      ≤ |36 * t ^ 2 - 12| + |ε * zonalR ε t| := abs_add_le _ _
    _ ≤ 48 + |ε| * |zonalR ε t| := by rw [abs_mul]; linarith
    _ ≤ 48 + 1 * 1512 := by
        have := abs_nonneg (zonalR ε t)
        have h3 : |ε| * |zonalR ε t| ≤ 1 * 1512 := by
          apply mul_le_mul hε h1 (abs_nonneg _) (by norm_num)
        linarith
    _ ≤ 1560 := by norm_num

private theorem hasDerivAt_of_sq_bound (f : Real → Real) (D C δ : Real)
    (hδ : 0 < δ) (hC : 0 ≤ C)
    (hb : ∀ ε : Real, |ε| ≤ δ → |f ε - f 0 - ε * D| ≤ C * ε ^ 2) :
    HasDerivAt f D 0 := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  rw [Metric.eventually_nhds_iff]
  refine ⟨min δ (c / (C + 1)), lt_min hδ (by positivity), fun y hy => ?_⟩
  have hy' : |y| < min δ (c / (C + 1)) := by
    rw [Real.dist_eq, sub_zero] at hy
    exact hy
  have h1 : |y| ≤ δ := le_of_lt (lt_of_lt_of_le hy' (min_le_left _ _))
  have h2 : |y| ≤ c / (C + 1) := le_of_lt (lt_of_lt_of_le hy' (min_le_right _ _))
  have hb' := hb y h1
  have h3 : |y| * (C + 1) ≤ c := by
    rw [le_div_iff₀ (by positivity : (0 : Real) < C + 1)] at h2
    exact h2
  simp only [sub_zero, Real.norm_eq_abs, smul_eq_mul]
  calc |f y - f 0 - y * D| ≤ C * y ^ 2 := hb'
    _ = C * |y| * |y| := by
        rw [← sq_abs y]
        ring
    _ ≤ c * |y| := by
        have h4 : C * |y| ≤ c := by nlinarith [abs_nonneg y]
        have h5 : 0 ≤ |y| := abs_nonneg y
        nlinarith

private theorem inner0S_symm''
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Nat)
    (A B : Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) s x) :
    inner0S (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x s A B
      = inner0S (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x s B A := by
  unfold inner0S MetricFiberData.inner
  exact (tensor0SMetricData (I := 𝓡 2)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x s).symm A B

private theorem sphereQabs (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    |3 * sphereHeight x ^ 2 - 1| ≤ 2 := by
  have h := sphereHeight_sq_le_one x
  have h0 := sq_nonneg (sphereHeight x)
  rw [abs_le]
  constructor <;> nlinarith

private theorem sphereExpBound (ε : Real) (hε : |ε| ≤ 1)
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) (c : Real) (hc : |c| ≤ 2) :
    Real.exp (c * (ε * (3 * sphereHeight x ^ 2 - 1))) ≤ Real.exp 4 := by
  apply Real.exp_le_exp.mpr
  have hq := sphereQabs x
  have h1 : |c * (ε * (3 * sphereHeight x ^ 2 - 1))| ≤ 4 := by
    rw [abs_mul, abs_mul]
    have h2 : |ε| * |3 * sphereHeight x ^ 2 - 1| ≤ 1 * 2 :=
      mul_le_mul hε hq (abs_nonneg _) (by norm_num)
    have h3 : |c| * (|ε| * |3 * sphereHeight x ^ 2 - 1|) ≤ 2 * (1 * 2) :=
      mul_le_mul hc (by linarith) (by positivity) (by norm_num)
    linarith
  linarith [(abs_le.mp h1).2]

set_option maxHeartbeats 1600000 in
private theorem sphereNormSqB (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    normSq0S (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x 2
        (sphereBField x)
      = 18 * sphereHeight x ^ 2 * (1 - sphereHeight x ^ 2) ^ 2 := by
  classical
  set g0 : SmoothRiemannianMetric (𝓡 2) (sphere (0 : EuclideanSpace Real (Fin 3)) 1) :=
    roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2) with hg0
  set P : Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) 2 x := sphereDzDz x with hP
  set Q : Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) 2 x :=
    metricTensorField (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x with hQ
  have hsplit : sphereBField x
      = (6 * sphereHeight x) • P
        + (-(3 * sphereHeight x * (1 - sphereHeight x ^ 2))) • Q := rfl
  set a : Real := 6 * sphereHeight x with ha
  set b : Real := -(3 * sphereHeight x * (1 - sphereHeight x ^ 2)) with hb
  have hexpand : normSq0S (I := 𝓡 2) g0 x 2 (a • P + b • Q)
      = a ^ 2 * inner0S (I := 𝓡 2) g0 x 2 P P
        + 2 * (a * b) * inner0S (I := 𝓡 2) g0 x 2 P Q
        + b ^ 2 * inner0S (I := 𝓡 2) g0 x 2 Q Q := by
    rw [normSq0S_eq_inner, inner0S_add_right'' x 2 (a • P + b • Q) (a • P) (b • Q)]
    rw [show inner0S (I := 𝓡 2) g0 x 2 (a • P + b • Q) (a • P)
        = inner0S (I := 𝓡 2) g0 x 2 (a • P) (a • P)
          + inner0S (I := 𝓡 2) g0 x 2 (b • Q) (a • P) from by
      rw [inner0S_symm'' x 2 (a • P + b • Q) (a • P),
        inner0S_add_right'' x 2 (a • P) (a • P) (b • Q)]
      rw [inner0S_symm'' x 2 (a • P) (a • P)]
      rw [show inner0S (I := 𝓡 2) g0 x 2 (a • P) (b • Q)
          = inner0S (I := 𝓡 2) g0 x 2 (b • Q) (a • P) from inner0S_symm'' x 2 _ _]]
    rw [show inner0S (I := 𝓡 2) g0 x 2 (a • P + b • Q) (b • Q)
        = inner0S (I := 𝓡 2) g0 x 2 (a • P) (b • Q)
          + inner0S (I := 𝓡 2) g0 x 2 (b • Q) (b • Q) from by
      rw [inner0S_symm'' x 2 (a • P + b • Q) (b • Q),
        inner0S_add_right'' x 2 (b • Q) (a • P) (b • Q)]
      rw [show inner0S (I := 𝓡 2) g0 x 2 (b • Q) (a • P)
          = inner0S (I := 𝓡 2) g0 x 2 (a • P) (b • Q) from inner0S_symm'' x 2 _ _]]
    rw [inner0S_smul_left, inner0S_smul_right, inner0S_smul_left, inner0S_smul_right,
      inner0S_smul_left, inner0S_smul_right, inner0S_smul_left, inner0S_smul_right]
    rw [show inner0S (I := 𝓡 2) g0 x 2 Q P
        = inner0S (I := 𝓡 2) g0 x 2 P Q from inner0S_symm'' x 2 _ _]
    ring
  set basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := 𝓡 2) x
    with hbasis
  set gInv : DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
        (EuclideanSpace Real (Fin 2))
      → DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
          (EuclideanSpace Real (Fin 2)) → Real :=
    fun k l => DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x k l
      (extChartAt (𝓡 2) x x) with hgInv
  have hinv : MetricInverseInBasis_gen (I := 𝓡 2)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x basis gInv :=
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := 𝓡 2) (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) x
  have hcard : Fintype.card
      (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real)
        (EuclideanSpace Real (Fin 2))) = 2 := by
    rw [← Module.finrank_eq_card_basis basis]
    exact finrank_euclideanSpace_fin
  have hPP : inner0S (I := 𝓡 2) g0 x 2 P P = (1 - sphereHeight x ^ 2) ^ 2 := by
    letI : NormedAddCommGroup (TangentSpace (𝓡 2) x) :=
      @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace (𝓡 2) x) _ _ _
        (tangentMetricData_gen (I := 𝓡 2) g0 x).metric.toCore
    letI : InnerProductSpace Real (TangentSpace (𝓡 2) x) :=
      @InnerProductSpace.ofCore Real (TangentSpace (𝓡 2) x) _ _ _
        (tangentMetricData_gen (I := 𝓡 2) g0 x).metric.toCore.toCore
    set ob := stdOrthonormalBasis Real (TangentSpace (𝓡 2) x) with hob
    have hON : ∀ i j, g0.inner x (ob i) (ob j)
        = if i = j then (1 : Real) else 0 := by
      intro i j
      have hinner : Inner.inner Real (ob i) (ob j)
          = (tangentMetricData_gen (I := 𝓡 2) g0 x).metric.inner (ob i) (ob j) :=
        MetricFiberData.toCore_inner (tangentMetricData_gen (I := 𝓡 2) g0 x).metric (ob i) (ob j)
      have hob' := ob.inner_eq_ite i j
      rw [← TangentMetricData_gen.inner_eq_gen (tangentMetricData_gen (I := 𝓡 2) g0 x)
        (ob i) (ob j)]
      change (tangentMetricData_gen (I := 𝓡 2) g0 x).metric.inner (ob i) (ob j)
        = if i = j then (1 : Real) else 0
      rw [← hinner]
      exact hob'
    have hinvON : MetricInverseInBasis_gen (I := 𝓡 2) g0 x ob.toBasis
        (identityInvMetric (Idx := Fin (Module.finrank Real
          (TangentSpace (𝓡 2) x)))) := by
      intro i j
      constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
    have hprod := normSq0S_product (I := 𝓡 2) g0 x ob.toBasis hinvON
      sphereHeightOneForm sphereHeightOneForm
    rw [show inner0S (I := 𝓡 2) g0 x 2 P P
        = normSq0S (I := 𝓡 2) g0 x 2 P from (normSq0S_eq_inner (I := 𝓡 2) g0 x 2 P).symm]
    rw [show normSq0S (I := 𝓡 2) g0 x 2 P
        = normSq0S (I := 𝓡 2) g0 x 1 (sphereHeightOneForm x)
          * normSq0S (I := 𝓡 2) g0 x 1 (sphereHeightOneForm x) from hprod]
    rw [sphereNormSq_h]
    ring
  have hPQ : inner0S (I := 𝓡 2) g0 x 2 P Q = 1 - sphereHeight x ^ 2 := by
    rw [show inner0S (I := 𝓡 2) g0 x 2 P Q
        = inner0S (I := 𝓡 2) g0 x 2 Q P from inner0S_symm'' x 2 _ _]
    rw [show Q = metricTensor0S (I := 𝓡 2) g0 x from
      metricTrace_metricField_eq0S (I := 𝓡 2) g0 x]
    rw [show inner0S (I := 𝓡 2) g0 x 2 (metricTensor0S (I := 𝓡 2) g0 x) P
        = metricTracePair0SAt (I := 𝓡 2) g0 P from rfl]
    rw [metricTracePair0SAt_eq_sum_basis (I := 𝓡 2) g0 basis gInv hinv P]
    have hval : ∀ i j, gInv i j * P (vec2 (I := 𝓡 2) (basis i) (basis j))
        = gInv i j * (sphereHeightOneForm x (fun _ : Fin 1 => basis i)
            * sphereHeightOneForm x (fun _ : Fin 1 => basis j)) := by
      intro i j
      have h1 := oneFormProd_pair sphereHeightOneForm sphereHeightOneForm x
        (vec2 (I := 𝓡 2) (basis i) (basis j))
      rw [show (vec2 (I := 𝓡 2) (basis i) (basis j) : Fin 2 → TangentSpace (𝓡 2) x) 0
          = basis i from rfl,
        show (vec2 (I := 𝓡 2) (basis i) (basis j) : Fin 2 → TangentSpace (𝓡 2) x) 1
          = basis j from rfl] at h1
      rw [show P (vec2 (I := 𝓡 2) (basis i) (basis j))
          = sphereHeightOneForm x (fun _ : Fin 1 => basis i)
            * sphereHeightOneForm x (fun _ : Fin 1 => basis j) from h1]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hval i j))]
    exact sum_dz_dz basis gInv hinv
  have hQQ : inner0S (I := 𝓡 2) g0 x 2 Q Q = 2 := by
    rw [show Q = metricTensor0S (I := 𝓡 2) g0 x from
      metricTrace_metricField_eq0S (I := 𝓡 2) g0 x]
    rw [show inner0S (I := 𝓡 2) g0 x 2 (metricTensor0S (I := 𝓡 2) g0 x)
          (metricTensor0S (I := 𝓡 2) g0 x)
        = normSq0S (I := 𝓡 2) g0 x 2 (metricTensor0S (I := 𝓡 2) g0 x) from
      (normSq0S_eq_inner (I := 𝓡 2) g0 x 2 _).symm]
    rw [normSq0S_metricTensor0S_eq_card (I := 𝓡 2) g0 basis gInv hinv, hcard]
    norm_num
  rw [hsplit, hexpand, hPP, hPQ, hQQ]
  rw [ha, hb]
  ring

private theorem sphereVolFinite :
    IsFiniteMeasure (riemannianVolumeMeasure (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) := by
  constructor
  haveI := riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := 𝓡 2)
    (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
  exact IsCompact.measure_lt_top isCompact_univ

private theorem sphereT1_nonneg (ε : Real) : 0 ≤ sphereT1 ε :=
  MeasureTheory.integral_nonneg fun x =>
    normSq0S_nonneg (I := 𝓡 2) (sphereConformalMetric ε) x 1 _

private theorem sphereT1_le (ε : Real) (hε : |ε| ≤ 1) :
    sphereT1 ε ≤ (1296 * Real.exp 4 ^ 4
        * (riemannianVolumeMeasure (I := 𝓡 2)
            (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).real Set.univ)
      * ε ^ 2 := by
  haveI := sphereVolFinite
  have hpt : (fun x : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        normSq0S (I := 𝓡 2) (sphereConformalMetric ε) x 1
          (roughLap0STensor (I := 𝓡 2) (sphereConformalMetric ε) (s := 1)
              ((sphereConformalDerivs ε).nabla2A x)
            + gaussCurvature (I := 𝓡 2) (sphereConformalMetric ε) x • sphereHeightOneForm x))
      = fun x : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
          (ε * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
              * (30 * sphereHeight x ^ 2 - 6)) ^ 2
            * (Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
              * (1 - sphereHeight x ^ 2)) := by
    funext x
    rw [sphereVtensor ε x, sphereNormSq_smul, sphereNormSq_h_eps]
  have hstep1 : sphereT1 ε
      = ∫ x, Real.exp (ε * (3 * sphereHeight x ^ 2 - 1))
          * ((ε * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
              * (30 * sphereHeight x ^ 2 - 6)) ^ 2
            * (Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
              * (1 - sphereHeight x ^ 2)))
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) := by
    rw [show sphereT1 ε = ∫ x, (fun y : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        normSq0S (I := 𝓡 2) (sphereConformalMetric ε) y 1
          (roughLap0STensor (I := 𝓡 2) (sphereConformalMetric ε) (s := 1)
              ((sphereConformalDerivs ε).nabla2A y)
            + gaussCurvature (I := 𝓡 2) (sphereConformalMetric ε) y • sphereHeightOneForm y)) x
      ∂(riemannianVolumeMeasure (I := 𝓡 2)
        (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
        (sphereConformalMetric ε)) from rfl]
    rw [show (fun y : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        normSq0S (I := 𝓡 2) (sphereConformalMetric ε) y 1
          (roughLap0STensor (I := 𝓡 2) (sphereConformalMetric ε) (s := 1)
              ((sphereConformalDerivs ε).nabla2A y)
            + gaussCurvature (I := 𝓡 2) (sphereConformalMetric ε) y • sphereHeightOneForm y))
      = fun x : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
          (ε * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
              * (30 * sphereHeight x ^ 2 - 6)) ^ 2
            * (Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
              * (1 - sphereHeight x ^ 2)) from hpt]
    exact sphereIntegral_conformal ε _
  rw [hstep1]
  have hbound : ∀ x : sphere (0 : EuclideanSpace Real (Fin 3)) 1,
      Real.exp (ε * (3 * sphereHeight x ^ 2 - 1))
          * ((ε * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
              * (30 * sphereHeight x ^ 2 - 6)) ^ 2
            * (Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
              * (1 - sphereHeight x ^ 2)))
        ≤ 1296 * Real.exp 4 ^ 4 * ε ^ 2 := by
    intro x
    have hE1 : Real.exp (ε * (3 * sphereHeight x ^ 2 - 1)) ≤ Real.exp 4 := by
      have h := sphereExpBound ε hε x 1 (by norm_num)
      rw [one_mul] at h
      exact h
    have hE2 : Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1))) ≤ Real.exp 4 := by
      have h := sphereExpBound ε hε x (-1) (by norm_num)
      rw [show (-1 : Real) * (ε * (3 * sphereHeight x ^ 2 - 1))
          = -(ε * (3 * sphereHeight x ^ 2 - 1)) from by ring] at h
      exact h
    have hz := sphereHeight_sq_le_one x
    have hz0 := sq_nonneg (sphereHeight x)
    have hW : (30 * sphereHeight x ^ 2 - 6) ^ 2 ≤ 1296 := by nlinarith
    have hN0 : (0 : Real) ≤ 1 - sphereHeight x ^ 2 := by linarith
    have hN1 : 1 - sphereHeight x ^ 2 ≤ 1 := by linarith
    have hcalc : Real.exp (ε * (3 * sphereHeight x ^ 2 - 1))
        * ((ε * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
            * (30 * sphereHeight x ^ 2 - 6)) ^ 2
          * (Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
            * (1 - sphereHeight x ^ 2)))
        = ((30 * sphereHeight x ^ 2 - 6) ^ 2 * (1 - sphereHeight x ^ 2))
          * (Real.exp (ε * (3 * sphereHeight x ^ 2 - 1))
            * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1))) ^ 3) * ε ^ 2 := by
      ring
    rw [hcalc]
    have h1 : (30 * sphereHeight x ^ 2 - 6) ^ 2 * (1 - sphereHeight x ^ 2) ≤ 1296 * 1 := by
      apply mul_le_mul hW hN1 hN0 (by norm_num)
    have h2 : Real.exp (ε * (3 * sphereHeight x ^ 2 - 1))
        * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1))) ^ 3
        ≤ Real.exp 4 * Real.exp 4 ^ 3 := by
      apply mul_le_mul hE1 (pow_le_pow_left₀ (Real.exp_nonneg _) hE2 3)
        (by positivity) (Real.exp_nonneg _)
    calc ((30 * sphereHeight x ^ 2 - 6) ^ 2 * (1 - sphereHeight x ^ 2))
          * (Real.exp (ε * (3 * sphereHeight x ^ 2 - 1))
            * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1))) ^ 3) * ε ^ 2
        ≤ (1296 * 1) * (Real.exp 4 * Real.exp 4 ^ 3) * ε ^ 2 := by
          apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg ε)
          apply mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 1296 * Real.exp 4 ^ 4 * ε ^ 2 := by ring
  have hle := MeasureTheory.integral_mono_of_nonneg
    (f := fun x : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
      Real.exp (ε * (3 * sphereHeight x ^ 2 - 1))
        * ((ε * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
            * (30 * sphereHeight x ^ 2 - 6)) ^ 2
          * (Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
            * (1 - sphereHeight x ^ 2))))
    (g := fun _ : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
      1296 * Real.exp 4 ^ 4 * ε ^ 2)
    (μ := riemannianVolumeMeasure (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
    (Filter.Eventually.of_forall fun x => by
      have hz := sphereHeight_sq_le_one x
      have hN0 : (0 : Real) ≤ 1 - sphereHeight x ^ 2 := by linarith
      exact mul_nonneg (Real.exp_nonneg _)
        (mul_nonneg (sq_nonneg _) (mul_nonneg (Real.exp_nonneg _) hN0)))
    (MeasureTheory.integrable_const _)
    (Filter.Eventually.of_forall hbound)
  calc (∫ x, Real.exp (ε * (3 * sphereHeight x ^ 2 - 1))
        * ((ε * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
            * (30 * sphereHeight x ^ 2 - 6)) ^ 2
          * (Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
            * (1 - sphereHeight x ^ 2)))
      ∂(riemannianVolumeMeasure (I := 𝓡 2)
        (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))))
      ≤ ∫ _, 1296 * Real.exp 4 ^ 4 * ε ^ 2
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) := hle
    _ = (1296 * Real.exp 4 ^ 4
          * (riemannianVolumeMeasure (I := 𝓡 2)
              (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
              (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).real Set.univ)
        * ε ^ 2 := by
        rw [MeasureTheory.integral_const, smul_eq_mul]
        ring

private theorem sphereT1_deriv : HasDerivAt sphereT1 0 0 := by
  have hC : (0 : Real) ≤ 1296 * Real.exp 4 ^ 4
      * (riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).real Set.univ := by
    positivity
  refine hasDerivAt_of_sq_bound sphereT1 0 _ 1 one_pos hC (fun ε hε => ?_)
  have h1 := sphereT1_le ε hε
  have h2 := sphereT1_nonneg ε
  have h0 : sphereT1 0 = 0 := by
    have ha := sphereT1_le 0 (by norm_num)
    have hb := sphereT1_nonneg 0
    have : sphereT1 0 ≤ 0 := by
      calc sphereT1 0 ≤ _ * (0 : Real) ^ 2 := ha
        _ = 0 := by ring
    linarith
  rw [h0, sub_zero, mul_zero, sub_zero, abs_of_nonneg h2]
  exact h1

private theorem sphereT2_abs_le (ε : Real) (hε : |ε| ≤ 1) :
    |sphereT2 ε| ≤ (126 * Real.exp 4 ^ 3
        * (riemannianVolumeMeasure (I := 𝓡 2)
            (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).real Set.univ)
      * ε ^ 2 := by
  haveI := sphereVolFinite
  have hpt : (fun x : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        gaussCurvature (I := 𝓡 2) (sphereConformalMetric ε) x
          * normSq0S (I := 𝓡 2) (sphereConformalMetric ε) x 2
              (ahlforsOperator (I := 𝓡 2) (sphereConformalMetric ε)
                ((sphereConformalDerivs ε).nablaA x)))
      = fun x : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
          (Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
              * (1 + 3 * (ε * (3 * sphereHeight x ^ 2 - 1))))
            * ((-ε) ^ 2 * (Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1))))
              * (18 * sphereHeight x ^ 2 * (1 - sphereHeight x ^ 2) ^ 2))) := by
    funext x
    rw [sphereAhlforsEps ε x, sphereNormSq_smul, sphereNormSq_conf_two, sphereNormSqB,
      sphereK_eq ε x]
  have hstep1 : sphereT2 ε
      = ∫ x, Real.exp (ε * (3 * sphereHeight x ^ 2 - 1))
          * ((Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
              * (1 + 3 * (ε * (3 * sphereHeight x ^ 2 - 1))))
            * ((-ε) ^ 2 * (Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1))))
              * (18 * sphereHeight x ^ 2 * (1 - sphereHeight x ^ 2) ^ 2))))
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) := by
    rw [show sphereT2 ε = ∫ x, (fun y : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
        gaussCurvature (I := 𝓡 2) (sphereConformalMetric ε) y
          * normSq0S (I := 𝓡 2) (sphereConformalMetric ε) y 2
              (ahlforsOperator (I := 𝓡 2) (sphereConformalMetric ε)
                ((sphereConformalDerivs ε).nablaA y))) x
      ∂(riemannianVolumeMeasure (I := 𝓡 2)
        (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
        (sphereConformalMetric ε)) from rfl]
    rw [hpt]
    exact sphereIntegral_conformal ε _
  rw [hstep1]
  have hbound : ∀ x : sphere (0 : EuclideanSpace Real (Fin 3)) 1,
      |Real.exp (ε * (3 * sphereHeight x ^ 2 - 1))
          * ((Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
              * (1 + 3 * (ε * (3 * sphereHeight x ^ 2 - 1))))
            * ((-ε) ^ 2 * (Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1))))
              * (18 * sphereHeight x ^ 2 * (1 - sphereHeight x ^ 2) ^ 2))))|
        ≤ 126 * Real.exp 4 ^ 3 * ε ^ 2 := by
    intro x
    have hE1 : Real.exp (ε * (3 * sphereHeight x ^ 2 - 1)) ≤ Real.exp 4 := by
      have h := sphereExpBound ε hε x 1 (by norm_num)
      rw [one_mul] at h
      exact h
    have hE2 : Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1))) ≤ Real.exp 4 := by
      have h := sphereExpBound ε hε x (-1) (by norm_num)
      rw [show (-1 : Real) * (ε * (3 * sphereHeight x ^ 2 - 1))
          = -(ε * (3 * sphereHeight x ^ 2 - 1)) from by ring] at h
      exact h
    have hE3 : Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1)))) ≤ Real.exp 4 := by
      have h := sphereExpBound ε hε x (-2) (by norm_num)
      rw [show (-2 : Real) * (ε * (3 * sphereHeight x ^ 2 - 1))
          = -(2 * (ε * (3 * sphereHeight x ^ 2 - 1))) from by ring] at h
      exact h
    have hz := sphereHeight_sq_le_one x
    have hz0 := sq_nonneg (sphereHeight x)
    have hq := sphereQabs x
    have hK : |1 + 3 * (ε * (3 * sphereHeight x ^ 2 - 1))| ≤ 7 := by
      have h1 : |ε * (3 * sphereHeight x ^ 2 - 1)| ≤ 2 := by
        rw [abs_mul]
        calc |ε| * |3 * sphereHeight x ^ 2 - 1| ≤ 1 * 2 :=
            mul_le_mul hε hq (abs_nonneg _) (by norm_num)
          _ = 2 := by norm_num
      have h2 := abs_le.mp h1
      rw [abs_le]
      constructor <;> nlinarith [h2.1, h2.2]
    have hG0 : (0 : Real) ≤ 18 * sphereHeight x ^ 2 * (1 - sphereHeight x ^ 2) ^ 2 := by
      positivity
    have hG1 : 18 * sphereHeight x ^ 2 * (1 - sphereHeight x ^ 2) ^ 2 ≤ 18 := by
      nlinarith [sq_nonneg (1 - sphereHeight x ^ 2), sq_nonneg (sphereHeight x)]
    have hrest0 : (0 : Real) ≤ Real.exp (ε * (3 * sphereHeight x ^ 2 - 1))
        * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
        * Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1))))
        * (18 * sphereHeight x ^ 2 * (1 - sphereHeight x ^ 2) ^ 2) * ε ^ 2 := by
      positivity
    have harr : Real.exp (ε * (3 * sphereHeight x ^ 2 - 1))
        * ((Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
            * (1 + 3 * (ε * (3 * sphereHeight x ^ 2 - 1))))
          * ((-ε) ^ 2 * (Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1))))
            * (18 * sphereHeight x ^ 2 * (1 - sphereHeight x ^ 2) ^ 2))))
        = (1 + 3 * (ε * (3 * sphereHeight x ^ 2 - 1)))
          * (Real.exp (ε * (3 * sphereHeight x ^ 2 - 1))
            * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
            * Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1))))
            * (18 * sphereHeight x ^ 2 * (1 - sphereHeight x ^ 2) ^ 2) * ε ^ 2) := by
      ring
    rw [harr, abs_mul, abs_of_nonneg hrest0]
    have hEprod : Real.exp (ε * (3 * sphereHeight x ^ 2 - 1))
        * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
        * Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1))))
        ≤ Real.exp 4 * Real.exp 4 * Real.exp 4 := by
      apply mul_le_mul (mul_le_mul hE1 hE2 (Real.exp_nonneg _) (Real.exp_nonneg _)) hE3
        (Real.exp_nonneg _) (by positivity)
    calc |1 + 3 * (ε * (3 * sphereHeight x ^ 2 - 1))|
          * (Real.exp (ε * (3 * sphereHeight x ^ 2 - 1))
            * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
            * Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1))))
            * (18 * sphereHeight x ^ 2 * (1 - sphereHeight x ^ 2) ^ 2) * ε ^ 2)
        ≤ 7 * (Real.exp 4 * Real.exp 4 * Real.exp 4 * 18 * ε ^ 2) := by
          apply mul_le_mul hK ?_ hrest0 (by norm_num)
          apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg ε)
          apply mul_le_mul hEprod hG1 hG0 (by positivity)
      _ = 126 * Real.exp 4 ^ 3 * ε ^ 2 := by ring
  calc |∫ x, Real.exp (ε * (3 * sphereHeight x ^ 2 - 1))
        * ((Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
            * (1 + 3 * (ε * (3 * sphereHeight x ^ 2 - 1))))
          * ((-ε) ^ 2 * (Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1))))
            * (18 * sphereHeight x ^ 2 * (1 - sphereHeight x ^ 2) ^ 2))))
      ∂(riemannianVolumeMeasure (I := 𝓡 2)
        (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))|
      ≤ ∫ x, |Real.exp (ε * (3 * sphereHeight x ^ 2 - 1))
          * ((Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
              * (1 + 3 * (ε * (3 * sphereHeight x ^ 2 - 1))))
            * ((-ε) ^ 2 * (Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1))))
              * (18 * sphereHeight x ^ 2 * (1 - sphereHeight x ^ 2) ^ 2))))|
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ _, 126 * Real.exp 4 ^ 3 * ε ^ 2
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => abs_nonneg _)
          (MeasureTheory.integrable_const _)
          (Filter.Eventually.of_forall hbound)
    _ = (126 * Real.exp 4 ^ 3
          * (riemannianVolumeMeasure (I := 𝓡 2)
              (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
              (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).real Set.univ)
        * ε ^ 2 := by
        rw [MeasureTheory.integral_const, smul_eq_mul]
        ring

private theorem sphereT2_deriv : HasDerivAt sphereT2 0 0 := by
  have hC : (0 : Real) ≤ 126 * Real.exp 4 ^ 3
      * (riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).real Set.univ := by
    positivity
  refine hasDerivAt_of_sq_bound sphereT2 0 _ 1 one_pos hC (fun ε hε => ?_)
  have h1 := sphereT2_abs_le ε hε
  have h0 : sphereT2 0 = 0 := by
    have ha := sphereT2_abs_le 0 (by norm_num)
    have : |sphereT2 0| ≤ 0 := by
      calc |sphereT2 0| ≤ _ * (0 : Real) ^ 2 := ha
        _ = 0 := by ring
    have := abs_nonneg (sphereT2 0)
    have habs : |sphereT2 0| = 0 := le_antisymm ‹|sphereT2 0| ≤ 0› this
    exact abs_eq_zero.mp habs
  rw [h0, sub_zero, mul_zero, sub_zero]
  exact h1

private theorem sphereT3_pointwise (ε : Real)
    (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    Real.exp (ε * (3 * sphereHeight x ^ 2 - 1))
      * (formLaplacianScalar (I := 𝓡 2) (sphereConformalMetric ε) (sphereKsm ε) x
        * normSq0S (I := 𝓡 2) (sphereConformalMetric ε) x 1 (sphereHeightOneForm x))
    = ε * zonalA ε (sphereHeight x) * (1 - sphereHeight x ^ 2)
        * Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1)))) := by
  have hdim : Module.finrank Real (EuclideanSpace Real (Fin 2)) = 2 :=
    finrank_euclideanSpace_fin
  rw [sphereNormSq_h_eps ε x]
  have hconf : formLaplacianScalar (I := 𝓡 2) (sphereConformalMetric ε) (sphereKsm ε) x
      = Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
        * formLaplacianScalar (I := 𝓡 2)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) (sphereKsm ε) x := by
    have h := formLaplacianScalar_conformalMetric_twoDim (I := 𝓡 2) hdim
      (legendreConformalFactor ε) (legendreConformalFactor_contMDiff ε)
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
      (gaussCurvature (I := 𝓡 2) (sphereConformalMetric ε)) (sphereKsm ε) x
    rw [show Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
        = Real.exp (-(2 * legendreConformalFactor ε x)) from congrArg Real.exp (by
      rw [show legendreConformalFactor ε x
          = ε * ((3 * sphereHeight x ^ 2 - 1) / 2) from rfl]
      ring)]
    exact h
  rw [hconf, sphereLapK_eq ε x]
  have hone : Real.exp (ε * (3 * sphereHeight x ^ 2 - 1))
      * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1))) = 1 := by
    rw [← Real.exp_add]
    simp
  have hsq : Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
      * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
      = Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1)))) := by
    rw [← Real.exp_add]
    refine congrArg Real.exp ?_
    ring
  rw [zonalA, ← hsq]
  linear_combination (ε * (-((6 * (2 - 3 * (ε * (3 * sphereHeight x ^ 2 - 1)))
      - 36 * ε * sphereHeight x ^ 2 * (5 - 3 * (ε * (3 * sphereHeight x ^ 2 - 1))))
        * (1 - sphereHeight x ^ 2))
      + 12 * sphereHeight x ^ 2 * (2 - 3 * (ε * (3 * sphereHeight x ^ 2 - 1))))
    * (1 - sphereHeight x ^ 2)
    * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))
    * Real.exp (-(ε * (3 * sphereHeight x ^ 2 - 1)))) * hone

private theorem sphereT3_eq (ε : Real) :
    sphereT3 ε
      = ∫ x, ε * zonalA ε (sphereHeight x) * (1 - sphereHeight x ^ 2)
          * Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1))))
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) := by
  rw [show sphereT3 ε = ∫ x, (fun y : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
      formLaplacianScalar (I := 𝓡 2) (sphereConformalMetric ε) (sphereKsm ε) y
        * normSq0S (I := 𝓡 2) (sphereConformalMetric ε) y 1 (sphereHeightOneForm y)) x
    ∂(riemannianVolumeMeasure (I := 𝓡 2)
      (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
      (sphereConformalMetric ε)) from rfl]
  rw [sphereIntegral_conformal ε _]
  refine congrArg (MeasureTheory.integral _) (funext fun x => ?_)
  exact sphereT3_pointwise ε x

private theorem sphereT3_zero : sphereT3 0 = 0 := by
  rw [sphereT3_eq 0]
  have hpt : (fun x : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
      (0 : Real) * zonalA 0 (sphereHeight x) * (1 - sphereHeight x ^ 2)
        * Real.exp (-(2 * ((0 : Real) * (3 * sphereHeight x ^ 2 - 1)))))
      = fun _ : sphere (0 : EuclideanSpace Real (Fin 3)) 1 => (0 : Real) := by
    funext x
    ring
  rw [hpt, MeasureTheory.integral_zero]

private theorem sphereD_eq :
    (∫ x, (36 * sphereHeight x ^ 2 - 12) * (1 - sphereHeight x ^ 2)
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))))
      = -(64 * Real.pi / 5) := by
  have hpt : (fun x : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
      (36 * sphereHeight x ^ 2 - 12) * (1 - sphereHeight x ^ 2))
      = fun x : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
          24 * (((3 * sphereHeight x ^ 2 - 1) / 2) * (1 - sphereHeight x ^ 2)) := by
    funext x
    ring
  rw [show (∫ x, (36 * sphereHeight x ^ 2 - 12) * (1 - sphereHeight x ^ 2)
      ∂(riemannianVolumeMeasure (I := 𝓡 2)
        (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))))
    = ∫ x, 24 * (((3 * sphereHeight x ^ 2 - 1) / 2) * (1 - sphereHeight x ^ 2))
      ∂(riemannianVolumeMeasure (I := 𝓡 2)
        (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))
    from congrArg (MeasureTheory.integral _) hpt]
  rw [MeasureTheory.integral_const_mul]
  have hzonal : (∫ x, ((3 * sphereHeight x ^ 2 - 1) / 2) * (1 - sphereHeight x ^ 2)
      ∂(riemannianVolumeMeasure (I := 𝓡 2)
        (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))))
      = -(8 * Real.pi / 15) :=
    DifferentialGeometry.Geometry.integral_legendreTwo_height_roundMetric
  rw [hzonal]
  ring

private theorem sphereT3_deriv : HasDerivAt sphereT3 (-(64 * Real.pi / 5)) 0 := by
  have hC : (0 : Real) ≤ 13992
      * (riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).real Set.univ := by
    positivity
  haveI := sphereVolFinite
  refine hasDerivAt_of_sq_bound sphereT3 (-(64 * Real.pi / 5)) _ (1 / 4)
    (by norm_num) hC (fun ε hε => ?_)
  have hε1 : |ε| ≤ 1 := le_trans hε (by norm_num)
  rw [sphereT3_zero, sub_zero, sphereT3_eq ε]
  have hcont1 : Continuous (fun x : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
      ε * zonalA ε (sphereHeight x) * (1 - sphereHeight x ^ 2)
        * Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1))))) := by
    have hz : Continuous sphereHeight := sphereHeight_contMDiff.continuous
    unfold zonalA
    fun_prop
  have hcont2 : Continuous (fun x : sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
      ε * ((36 * sphereHeight x ^ 2 - 12) * (1 - sphereHeight x ^ 2))) := by
    have hz : Continuous sphereHeight := sphereHeight_contMDiff.continuous
    fun_prop
  have hint1 := DifferentialGeometry.Integral.L2.integrable_of_continuous_compactSpace (I := 𝓡 2)
    (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) hcont1
  have hint2 := DifferentialGeometry.Integral.L2.integrable_of_continuous_compactSpace (I := 𝓡 2)
    (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) hcont2
  have hD : ε * -(64 * Real.pi / 5)
      = ∫ x, ε * ((36 * sphereHeight x ^ 2 - 12) * (1 - sphereHeight x ^ 2))
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) := by
    rw [MeasureTheory.integral_const_mul, sphereD_eq]
  rw [hD, ← MeasureTheory.integral_sub hint1 hint2]
  have hbound : ∀ x : sphere (0 : EuclideanSpace Real (Fin 3)) 1,
      |ε * zonalA ε (sphereHeight x) * (1 - sphereHeight x ^ 2)
          * Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1))))
        - ε * ((36 * sphereHeight x ^ 2 - 12) * (1 - sphereHeight x ^ 2))|
        ≤ 13992 * ε ^ 2 := by
    intro x
    have hz := sphereHeight_sq_le_one x
    have hq := sphereQabs x
    have hN0 : (0 : Real) ≤ 1 - sphereHeight x ^ 2 := by linarith
    have hN1 : 1 - sphereHeight x ^ 2 ≤ 1 := by nlinarith [sq_nonneg (sphereHeight x)]
    have hA := zonalA_bound ε (sphereHeight x) hε1 hz
    have hR := zonalR_bound ε (sphereHeight x) hε1 hz
    have hxe : |(-(2 * (ε * (3 * sphereHeight x ^ 2 - 1))))| ≤ 1 := by
      rw [abs_neg, abs_mul, abs_mul]
      have h1 : |ε| * |3 * sphereHeight x ^ 2 - 1| ≤ (1 / 4) * 2 :=
        mul_le_mul hε hq (abs_nonneg _) (by norm_num)
      have h2 : |(2 : Real)| = 2 := by norm_num
      rw [h2]
      nlinarith [abs_nonneg ε, abs_nonneg (3 * sphereHeight x ^ 2 - 1)]
    have hexp1 := Real.abs_exp_sub_one_le hxe
    have harr : ε * zonalA ε (sphereHeight x) * (1 - sphereHeight x ^ 2)
          * Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1))))
        - ε * ((36 * sphereHeight x ^ 2 - 12) * (1 - sphereHeight x ^ 2))
        = ε * ((1 - sphereHeight x ^ 2)
            * (zonalA ε (sphereHeight x)
                * (Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1)))) - 1)
              + (zonalA ε (sphereHeight x) - (36 * sphereHeight x ^ 2 - 12)))) := by
      ring
    rw [harr, abs_mul]
    have hinner : |(1 - sphereHeight x ^ 2)
          * (zonalA ε (sphereHeight x)
              * (Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1)))) - 1)
            + (zonalA ε (sphereHeight x) - (36 * sphereHeight x ^ 2 - 12)))|
        ≤ 13992 * |ε| := by
      rw [abs_mul]
      have hsplit : |zonalA ε (sphereHeight x)
            * (Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1)))) - 1)
          + (zonalA ε (sphereHeight x) - (36 * sphereHeight x ^ 2 - 12))|
          ≤ |zonalA ε (sphereHeight x)|
              * |Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1)))) - 1|
            + |zonalA ε (sphereHeight x) - (36 * sphereHeight x ^ 2 - 12)| := by
        calc |zonalA ε (sphereHeight x)
              * (Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1)))) - 1)
            + (zonalA ε (sphereHeight x) - (36 * sphereHeight x ^ 2 - 12))|
            ≤ |zonalA ε (sphereHeight x)
                * (Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1)))) - 1)|
              + |zonalA ε (sphereHeight x) - (36 * sphereHeight x ^ 2 - 12)| :=
              abs_add_le _ _
          _ = |zonalA ε (sphereHeight x)|
                * |Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1)))) - 1|
              + |zonalA ε (sphereHeight x) - (36 * sphereHeight x ^ 2 - 12)| := by
              rw [abs_mul]
      have hexpb : |Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1)))) - 1|
          ≤ 8 * |ε| := by
        calc |Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1)))) - 1|
            ≤ 2 * |(-(2 * (ε * (3 * sphereHeight x ^ 2 - 1))))| := hexp1
          _ ≤ 8 * |ε| := by
              rw [abs_neg, abs_mul, abs_mul]
              have h2 : |(2 : Real)| = 2 := by norm_num
              rw [h2]
              nlinarith [abs_nonneg ε, hq, abs_nonneg (3 * sphereHeight x ^ 2 - 1)]
      have hdiffA : |zonalA ε (sphereHeight x) - (36 * sphereHeight x ^ 2 - 12)|
          ≤ 1512 * |ε| := by
        rw [zonalA_split]
        rw [show 36 * sphereHeight x ^ 2 - 12 + ε * zonalR ε (sphereHeight x)
            - (36 * sphereHeight x ^ 2 - 12) = ε * zonalR ε (sphereHeight x) from by ring]
        rw [abs_mul]
        nlinarith [abs_nonneg ε, abs_nonneg (zonalR ε (sphereHeight x))]
      have hterm1 : |zonalA ε (sphereHeight x)|
            * |Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1)))) - 1|
          ≤ 1560 * (8 * |ε|) := by
        apply mul_le_mul hA hexpb (abs_nonneg _) (by norm_num)
      have hN : |1 - sphereHeight x ^ 2| ≤ 1 := by
        rw [abs_of_nonneg hN0]
        exact hN1
      calc |1 - sphereHeight x ^ 2|
            * |zonalA ε (sphereHeight x)
                * (Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1)))) - 1)
              + (zonalA ε (sphereHeight x) - (36 * sphereHeight x ^ 2 - 12))|
          ≤ 1 * (1560 * (8 * |ε|) + 1512 * |ε|) := by
            apply mul_le_mul hN (le_trans hsplit (by linarith)) (abs_nonneg _) (by norm_num)
        _ = 13992 * |ε| := by ring
    calc |ε| * |(1 - sphereHeight x ^ 2)
          * (zonalA ε (sphereHeight x)
              * (Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1)))) - 1)
            + (zonalA ε (sphereHeight x) - (36 * sphereHeight x ^ 2 - 12)))|
        ≤ |ε| * (13992 * |ε|) :=
          mul_le_mul_of_nonneg_left hinner (abs_nonneg ε)
      _ = 13992 * (|ε| * |ε|) := by ring
      _ = 13992 * ε ^ 2 := by
          rw [← abs_mul, ← sq, abs_of_nonneg (sq_nonneg ε)]
  calc |∫ x, (ε * zonalA ε (sphereHeight x) * (1 - sphereHeight x ^ 2)
        * Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1))))
        - ε * ((36 * sphereHeight x ^ 2 - 12) * (1 - sphereHeight x ^ 2)))
      ∂(riemannianVolumeMeasure (I := 𝓡 2)
        (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)))|
      ≤ ∫ x, |ε * zonalA ε (sphereHeight x) * (1 - sphereHeight x ^ 2)
          * Real.exp (-(2 * (ε * (3 * sphereHeight x ^ 2 - 1))))
          - ε * ((36 * sphereHeight x ^ 2 - 12) * (1 - sphereHeight x ^ 2))|
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ _, 13992 * ε ^ 2
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => abs_nonneg _)
          (MeasureTheory.integrable_const _)
          (Filter.Eventually.of_forall hbound)
    _ = (13992 * (riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
          (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).real Set.univ)
        * ε ^ 2 := by
        rw [MeasureTheory.integral_const, smul_eq_mul]
        ring

end SharpnessDerivative

theorem sphereCurvatureEnergy_hasDerivAt :
    HasDerivAt sphereCurvatureEnergy (-(32 * Real.pi / 5)) 0 := by
  have hfun : sphereCurvatureEnergy
      = fun ε => sphereT1 ε + 2 * sphereT2 ε + 2⁻¹ * sphereT3 ε :=
    funext sphereQ_decomp
  rw [hfun]
  have h := (sphereT1_deriv.add (sphereT2_deriv.const_mul 2)).add
    (sphereT3_deriv.const_mul 2⁻¹)
  convert h using 1
  ring

theorem sphereCurvatureEnergy_neg :
    ∃ ε₀ : Real, 0 < ε₀ ∧
      ∀ ε ∈ Set.Ioo (0 : Real) ε₀, sphereCurvatureEnergy ε < 0 := by
  have hd := sphereCurvatureEnergy_hasDerivAt
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  have hneg : (-(32 * Real.pi / 5)) < 0 := by
    have := Real.pi_pos
    linarith
  have hev : ∀ᶠ y in nhdsWithin (0 : Real) {x | x ≠ 0},
      slope sphereCurvatureEnergy 0 y < 0 :=
    hslope.eventually_lt_const hneg
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hδprop⟩ := hev
  refine ⟨δ, hδ, fun ε hε => ?_⟩
  have hεpos := hε.1
  have hεlt := hε.2
  have hdist : dist ε 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hεpos]
    exact hεlt
  have hs := hδprop hdist (ne_of_gt hεpos)
  rw [slope_def_field, sphereCurvatureEnergy_zero, sub_zero, sub_zero] at hs
  rcases div_neg_iff.mp hs with ⟨_, hb⟩ | ⟨ha, _⟩
  · linarith
  · exact ha

theorem curvatureEnergyInequality_fails_unrestricted :
    ∃ g : SmoothRiemannianMetric (𝓡 2) (sphere (0 : EuclideanSpace Real (Fin 3)) 1),
    ∃ h : OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1),
    ∃ nablaH : TwoTensorSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1),
    ∃ nabla2H : (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) ->
      Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) 3 x,
      NablaOneFormSectionRealizes (I := 𝓡 2)
        (metricCov (I := 𝓡 2) g) h nablaH ∧
      (∀ x, Nabla2OneFormRealizesAt (I := 𝓡 2)
        (metricCov (I := 𝓡 2) g) h nablaH x (nabla2H x)) ∧
      (∫ x, normSq0S (I := 𝓡 2) g x 1
            (roughLap0STensor (I := 𝓡 2) g (s := 1) (nabla2H x))
          ∂(riemannianVolumeMeasure (I := 𝓡 2)
            (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) g))
        < (∫ x, gaussCurvature (I := 𝓡 2) g x * normSq0S (I := 𝓡 2) g x 2 (nablaH x)
            ∂(riemannianVolumeMeasure (I := 𝓡 2)
              (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) g))
          + (∫ x, inner0S (I := 𝓡 2) g x 2
                (oneFormReaction2D (I := 𝓡 2) g (h x)) (nablaH x)
              ∂(riemannianVolumeMeasure (I := 𝓡 2)
                (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) g)) := by
  obtain ⟨ε₀, hε₀, hneg⟩ := sphereCurvatureEnergy_neg
  refine ⟨sphereConformalMetric (ε₀ / 2), sphereHeightOneForm,
    (sphereConformalDerivs (ε₀ / 2)).nablaA,
    fun x => (sphereConformalDerivs (ε₀ / 2)).nabla2A x, ?_, ?_, ?_⟩
  · exact fun x =>
      (nabla2OneFormRealizesAt_of_totalNabla
        (metricCov (I := 𝓡 2) (sphereConformalMetric (ε₀ / 2)))
        sphereHeightOneForm ((sphereConformalDerivs (ε₀ / 2)).nablaA)
        ((sphereConformalDerivs (ε₀ / 2)).nabla2A)
        (sphereConformalDerivs (ε₀ / 2)).first
        (sphereConformalDerivs (ε₀ / 2)).second x).1 x
  · exact fun x =>
      nabla2OneFormRealizesAt_of_totalNabla
        (metricCov (I := 𝓡 2) (sphereConformalMetric (ε₀ / 2)))
        sphereHeightOneForm ((sphereConformalDerivs (ε₀ / 2)).nablaA)
        ((sphereConformalDerivs (ε₀ / 2)).nabla2A)
        (sphereConformalDerivs (ε₀ / 2)).first
        (sphereConformalDerivs (ε₀ / 2)).second x
  · have hval : sphereCurvatureEnergy (ε₀ / 2) < 0 :=
      hneg (ε₀ / 2) ⟨by linarith, by linarith⟩
    have hval' : (∫ x, normSq0S (I := 𝓡 2) (sphereConformalMetric (ε₀ / 2)) x 1
          (roughLap0STensor (I := 𝓡 2) (sphereConformalMetric (ε₀ / 2)) (s := 1)
            ((sphereConformalDerivs (ε₀ / 2)).nabla2A x))
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
          (sphereConformalMetric (ε₀ / 2))))
        - (∫ x, gaussCurvature (I := 𝓡 2) (sphereConformalMetric (ε₀ / 2)) x
            * normSq0S (I := 𝓡 2) (sphereConformalMetric (ε₀ / 2)) x 2
                ((sphereConformalDerivs (ε₀ / 2)).nablaA x)
          ∂(riemannianVolumeMeasure (I := 𝓡 2)
            (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
            (sphereConformalMetric (ε₀ / 2))))
        - (∫ x, inner0S (I := 𝓡 2) (sphereConformalMetric (ε₀ / 2)) x 2
            (oneFormReaction2D (I := 𝓡 2) (sphereConformalMetric (ε₀ / 2))
              (sphereHeightOneForm x))
            ((sphereConformalDerivs (ε₀ / 2)).nablaA x)
          ∂(riemannianVolumeMeasure (I := 𝓡 2)
            (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
            (sphereConformalMetric (ε₀ / 2)))) < 0 := hval
    beta_reduce
    linarith [hval']

theorem curvatureEnergyInequality_fails_positively_curved :
    ∃ g : SmoothRiemannianMetric (𝓡 2) (sphere (0 : EuclideanSpace Real (Fin 3)) 1),
    ∃ h : OneFormSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1),
    ∃ nablaH : TwoTensorSection (I := 𝓡 2) (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1),
    ∃ nabla2H : (x : sphere (0 : EuclideanSpace Real (Fin 3)) 1) ->
      Tensor0SSpace (𝕜 := Real) (I := 𝓡 2) 3 x,
      NablaOneFormSectionRealizes (I := 𝓡 2)
        (metricCov (I := 𝓡 2) g) h nablaH ∧
      (∀ x, Nabla2OneFormRealizesAt (I := 𝓡 2)
        (metricCov (I := 𝓡 2) g) h nablaH x (nabla2H x)) ∧
      (∀ x, 0 < gaussCurvature (I := 𝓡 2) g x) ∧
      (∫ x, normSq0S (I := 𝓡 2) g x 1
            (roughLap0STensor (I := 𝓡 2) g (s := 1) (nabla2H x))
          ∂(riemannianVolumeMeasure (I := 𝓡 2)
            (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) g))
        < (∫ x, gaussCurvature (I := 𝓡 2) g x * normSq0S (I := 𝓡 2) g x 2 (nablaH x)
            ∂(riemannianVolumeMeasure (I := 𝓡 2)
              (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) g))
          + (∫ x, inner0S (I := 𝓡 2) g x 2
                (oneFormReaction2D (I := 𝓡 2) g (h x)) (nablaH x)
              ∂(riemannianVolumeMeasure (I := 𝓡 2)
                (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) g)) := by
  obtain ⟨ε₀, hε₀, hneg⟩ := sphereCurvatureEnergy_neg
  set ε := min ε₀ (1 / 3) / 2 with hεdef
  have hminpos : 0 < min ε₀ (1 / 3) := lt_min hε₀ (by norm_num)
  have hεpos : 0 < ε := by rw [hεdef]; exact half_pos hminpos
  have hεltε₀ : ε < ε₀ := by
    have h1 : min ε₀ (1 / 3) ≤ ε₀ := min_le_left _ _
    rw [hεdef]; linarith
  have hεlt13 : ε < 1 / 3 := by
    have h2 : min ε₀ (1 / 3) ≤ 1 / 3 := min_le_right _ _
    rw [hεdef]; linarith
  refine ⟨sphereConformalMetric ε, sphereHeightOneForm,
    (sphereConformalDerivs ε).nablaA,
    fun x => (sphereConformalDerivs ε).nabla2A x, ?_, ?_, ?_, ?_⟩
  · exact fun x =>
      (nabla2OneFormRealizesAt_of_totalNabla
        (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
        sphereHeightOneForm ((sphereConformalDerivs ε).nablaA)
        ((sphereConformalDerivs ε).nabla2A)
        (sphereConformalDerivs ε).first
        (sphereConformalDerivs ε).second x).1 x
  · exact fun x =>
      nabla2OneFormRealizesAt_of_totalNabla
        (metricCov (I := 𝓡 2) (sphereConformalMetric ε))
        sphereHeightOneForm ((sphereConformalDerivs ε).nablaA)
        ((sphereConformalDerivs ε).nabla2A)
        (sphereConformalDerivs ε).first
        (sphereConformalDerivs ε).second x
  · intro x
    rw [sphereK_eq ε x]
    exact mul_pos (Real.exp_pos _)
      (by nlinarith [sphereHeight_sq_le_one x, hεpos, hεlt13,
        sq_nonneg (sphereHeight x)])
  · have hval : sphereCurvatureEnergy ε < 0 :=
      hneg ε ⟨hεpos, hεltε₀⟩
    have hval' : (∫ x, normSq0S (I := 𝓡 2) (sphereConformalMetric ε) x 1
          (roughLap0STensor (I := 𝓡 2) (sphereConformalMetric ε) (s := 1)
            ((sphereConformalDerivs ε).nabla2A x))
        ∂(riemannianVolumeMeasure (I := 𝓡 2)
          (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
          (sphereConformalMetric ε)))
        - (∫ x, gaussCurvature (I := 𝓡 2) (sphereConformalMetric ε) x
            * normSq0S (I := 𝓡 2) (sphereConformalMetric ε) x 2
                ((sphereConformalDerivs ε).nablaA x)
          ∂(riemannianVolumeMeasure (I := 𝓡 2)
            (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
            (sphereConformalMetric ε)))
        - (∫ x, inner0S (I := 𝓡 2) (sphereConformalMetric ε) x 2
            (oneFormReaction2D (I := 𝓡 2) (sphereConformalMetric ε)
              (sphereHeightOneForm x))
            ((sphereConformalDerivs ε).nablaA x)
          ∂(riemannianVolumeMeasure (I := 𝓡 2)
            (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1)
            (sphereConformalMetric ε))) < 0 := hval
    beta_reduce
    linarith [hval']

end Sphere

end DifferentialGeometry.Integral.Connection
