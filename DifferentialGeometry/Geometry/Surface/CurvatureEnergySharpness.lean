import DifferentialGeometry.Geometry.Surface.CurvatureEnergyIdentity
import DifferentialGeometry.Geometry.Metric.Conformal
import DifferentialGeometry.Geometry.Metric.Sphere.RoundProjConnLC
import DifferentialGeometry.Geometry.Metric.Sphere.RoundChartGram
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Operator.HessianTraceRealization
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.TotalNabla0S
import DifferentialGeometry.Geometry.Metric.Sphere.QuotientDescent
import DifferentialGeometry.Geometry.Curvature.Sphere.RoundGaussCurvature

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

theorem sphereCurvatureEnergy_hasDerivAt :
    HasDerivAt sphereCurvatureEnergy (-(32 * Real.pi / 5)) 0 := sorry

theorem sphereCurvatureEnergy_neg :
    ∃ ε₀ : Real, 0 < ε₀ ∧
      ∀ ε ∈ Set.Ioo (0 : Real) ε₀, sphereCurvatureEnergy ε < 0 := sorry

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
                (M := sphere (0 : EuclideanSpace Real (Fin 3)) 1) g)) := sorry

end Sphere

end DifferentialGeometry.Integral.Connection
