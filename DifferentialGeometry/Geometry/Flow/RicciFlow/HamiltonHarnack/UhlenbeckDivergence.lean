import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.ActualEvolution
import DifferentialGeometry.Geometry.Curvature.RicciPullbackDerivative
import DifferentialGeometry.Geometry.Operator.HessianPullback

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

theorem multilinear_pullback_hamiltonP_divergence_eq_hamiltonDivPAt
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gSource gTarget : SmoothRiemannianMetric I M)
    (φ : ∀ x : M, TangentSpace I x ≃L[Real] TangentSpace I x)
    (hφ : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ :
        TotalSpace (E →L[Real] E)
          (fun x => TangentSpace I x →L[Real] TangentSpace I x))))
    (x : M)
    (hiso : ∀ u v, gTarget.inner x (φ x u) (φ x v) = gSource.inner x u v)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis (I := I) gSource x basis gInv)
    (A B : TangentSpace I x) :
    let D := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map (metricCov gTarget)
    let fixedP := fun y => tensor0SPullbackCLE 3 (φ y).toLinearEquiv (hamiltonPField gTarget y)
    (∑ i : Idx, ∑ j : Idx,
      gInv i j * D.multilinear 3 fixedP x (φ x (basis i)) (vec3 (basis j) A B)) =
      tensor0SPullbackCLE 2 (φ x).toLinearEquiv
        (hamiltonDivPAt gTarget x) (vec2 A B) := by
  have hinv' : MetricInverseInBasis (I := I) gTarget x
      (basis.map (φ x).toLinearEquiv) gInv := by
    intro i j
    change (∑ k, gInv i k * gTarget.inner x (φ x (basis k)) (φ x (basis j)) = _) ∧
      (∑ k, gTarget.inner x (φ x (basis i)) (φ x (basis k)) * gInv k j = _)
    simpa only [hiso] using hinv i j
  have he (A B : TangentSpace I x) :
      (fun i => (φ x).toLinearEquiv (vec2 A B i)) = vec2 (φ x A) (φ x B) := by
    funext i
    fin_cases i <;> rfl
  have hv (A B C D : TangentSpace I x) :
      (fun i : Fin 4 => (φ x).toLinearEquiv
        ((Fin.cons A (vec3 (I := I) B C D) : Fin 4 → TangentSpace I x) i)) =
        vec4 (φ x A) (φ x B) (φ x C) (φ x D) := by
    funext i
    fin_cases i <;> rfl
  dsimp only
  simp_rw [multilinear_pullback_eq_totalNabla0SFun φ hφ]
  simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply, he, hv]
  exact (hamiltonDivPAt_apply_eq_trace_hamiltonNablaP gTarget
    (basis.map (φ x).toLinearEquiv) gInv hinv' (φ x A) (φ x B)).symm

theorem hamiltonMAt_tensor0SPullbackCLE_eq_divergence_add
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (clock : HarnackClock) (ht : clock.time ∈ D.regular)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gSource : SmoothRiemannianMetric I M)
    (φ : ∀ x : M, TangentSpace I x ≃L[Real] TangentSpace I x)
    (hφ : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ :
        TotalSpace (E →L[Real] E)
          (fun x => TangentSpace I x →L[Real] TangentSpace I x))))
    (x : M)
    (hiso : ∀ u v, (S.family.metric clock.time).inner x (φ x u) (φ x v) =
      gSource.inner x u v)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis (I := I) gSource x basis gInv)
    (A B : TangentSpace I x) :
    let D := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map
      (metricCov (S.family.metric clock.time))
    let fixedP := fun y => tensor0SPullbackCLE 3 (φ y).toLinearEquiv
      (hamiltonPField (S.family.metric clock.time) y)
    tensor0SPullbackCLE 2 (φ x).toLinearEquiv
        (hamiltonMAt clock (S.family.metric clock.time) x) (vec2 A B) =
      (∑ i : Idx, ∑ j : Idx,
        gInv i j * D.multilinear 3 fixedP x (φ x (basis i)) (vec3 (basis j) A B)) +
      tensor0SPullbackCLE 2 (φ x).toLinearEquiv
        (hamiltonCurvatureRicciAt (S.family.metric clock.time) x) (vec2 A B) +
      (1 / (2 * clock.elapsed) : Real) *
        tensor0SPullbackCLE 2 (φ x).toLinearEquiv
          (metricRicci (S.family.metric clock.time) x) (vec2 A B) := by
  dsimp only
  rw [multilinear_pullback_hamiltonP_divergence_eq_hamiltonDivPAt
    gSource (S.family.metric clock.time) φ hφ x hiso basis gInv hinv]
  rw [hamiltonMAt_eq_hamiltonDivPAt_add S hS clock ht]
  simp only [map_add, map_smul, Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply,
    smul_eq_mul]

theorem hamiltonScalarHessianAt_eq_hessianSec
    (g : SmoothRiemannianMetric I M) (x : M) :
    hamiltonScalarHessianAt g x =
      hessianSec (metricCov g) (metricCov_smooth g)
        (fun y => metricTracePair0SAt g (metricRicci g y))
        (trace02_smooth g (metricRicci g)) x := by
  classical
  let basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x
  let gInv := basisInvMetric g x basis
  have hinv := basisInvMetric_isInverse g x basis
  apply ext0S_basis (I := I) basis
  intro v
  have hv : (fun i => basis (v i)) = vec2 (basis (v 0)) (basis (v 1)) := by
    funext i
    fin_cases i <;> rfl
  change hamiltonScalarHessianAt g x (fun i => basis (v i)) =
    hessianSec (metricCov g) (metricCov_smooth g)
      (fun y => metricTracePair0SAt g (metricRicci g y))
      (trace02_smooth g (metricRicci g)) x (fun i => basis (v i))
  rw [hv]
  rw [hamiltonScalarHessianAt_apply g basis gInv hinv]
  exact (nabla2Trace02 (metricCov g) (metricCov_smooth g) g
    (leviCivitaConnectionOfMetric_isMetricCompatible g) (metricRicci g)
    basis gInv hinv (basis (v 0)) (basis (v 1))).symm

theorem hamiltonRicciSquareAt_tensor0SPullbackCLE_apply
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gSource gTarget : SmoothRiemannianMetric I M) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (hiso : ∀ u v, gTarget.inner y (e u) (e v) = gSource.inner x u v)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis (I := I) gSource x basis gInv)
    (A B : TangentSpace I x) :
    let Ric := tensor0SPullbackCLE 2 e (metricRicci gTarget y)
    tensor0SPullbackCLE 2 e (hamiltonRicciSquareAt gTarget y) (vec2 A B) =
      ∑ i, ∑ j, gInv i j * (Ric (vec2 A (basis i)) * Ric (vec2 (basis j) B)) := by
  have hinv' : MetricInverseInBasis (I := I) gTarget y (basis.map e) gInv := by
    intro i j
    simpa only [Module.Basis.map_apply, hiso] using hinv i j
  have he (A B : TangentSpace I x) :
      (fun i => e (vec2 A B i)) = vec2 (e A) (e B) := by
    funext i
    fin_cases i <;> rfl
  dsimp only
  simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply, he]
  exact hamiltonRicciSquareAt_apply gTarget (basis.map e) gInv hinv' (e A) (e B)

theorem hamiltonCurvatureRicciAt_tensor0SPullbackCLE_apply
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gSource gTarget : SmoothRiemannianMetric I M) {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (hiso : ∀ u v, gTarget.inner y (e u) (e v) = gSource.inner x u v)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis (I := I) gSource x basis gInv)
    (A B : TangentSpace I x) :
    let Ric := tensor0SPullbackCLE 2 e (metricRicci gTarget y)
    let Rm := tensor0SPullbackCLE 4 e (metricRm04 gTarget y)
    tensor0SPullbackCLE 2 e (hamiltonCurvatureRicciAt gTarget y) (vec2 A B) =
      ∑ i, ∑ j, gInv i j *
        (∑ k, ∑ l, gInv k l * (Rm (vec4 A (basis k) (basis i) B) *
          Ric (vec2 (basis l) (basis j)))) := by
  have hinv' : MetricInverseInBasis (I := I) gTarget y (basis.map e) gInv := by
    intro i j
    simpa only [Module.Basis.map_apply, hiso] using hinv i j
  have he (A B : TangentSpace I x) :
      (fun i => e (vec2 A B i)) = vec2 (e A) (e B) := by
    funext i
    fin_cases i <;> rfl
  have hf (A B C D : TangentSpace I x) :
      (fun i => e (vec4 A B C D i)) = vec4 (e A) (e B) (e C) (e D) := by
    funext i
    fin_cases i <;> rfl
  dsimp only
  simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply, he, hf]
  exact hamiltonCurvatureRicciAt_apply gTarget (basis.map e) gInv hinv' (e A) (e B)

theorem multilinear_pullback_hamiltonP_divergence_eq_laplacian_hessian
    [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (t : D.RegularTime)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gSource : SmoothRiemannianMetric I M)
    (φ : ∀ x : M, TangentSpace I x ≃L[Real] TangentSpace I x)
    (hφ : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ :
        TotalSpace (E →L[Real] E)
          (fun x => TangentSpace I x →L[Real] TangentSpace I x))))
    (x : M)
    (hiso : ∀ u v, (S.family.metric t).inner x (φ x u) (φ x v) =
      gSource.inner x u v)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis (I := I) gSource x basis gInv)
    (A B : TangentSpace I x) :
    let g := S.family.metric t
    let D := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map (metricCov g)
    let fixedP := fun y => tensor0SPullbackCLE 3 (φ y).toLinearEquiv (hamiltonPField g y)
    let fixedRic := fun y => tensor0SPullbackCLE 2 (φ y).toLinearEquiv (metricRicci g y)
    (∑ i : Idx, ∑ j : Idx,
      gInv i j * D.multilinear 3 fixedP x (φ x (basis i)) (vec3 (basis j) A B)) =
      rawBundleConnLap g (D.multilinear 2) fixedRic x (vec2 A B) -
      (1 / 2 : Real) * tensor0SPullbackCLE 2 (φ x).toLinearEquiv
        (hessianSec (metricCov g) (metricCov_smooth g)
          (fun y => metricTracePair0SAt g (metricRicci g y))
          (trace02_smooth g (metricRicci g)) x) (vec2 A B) -
      tensor0SPullbackCLE 2 (φ x).toLinearEquiv
        (hamiltonRicciSquareAt g x) (vec2 A B) +
      tensor0SPullbackCLE 2 (φ x).toLinearEquiv
        (hamiltonCurvatureRicciAt g x) (vec2 A B) := by
  dsimp only
  rw [multilinear_pullback_hamiltonP_divergence_eq_hamiltonDivPAt
    gSource (S.family.metric t) φ hφ x hiso basis gInv hinv,
    rawBundleConnLap_pullback_metricRicci_eq_roughLap0STensor (S.family.metric t) φ hφ x,
    hamiltonDivPAt_eq_rough_laplacian S hS t x,
    hamiltonScalarHessianAt_eq_hessianSec]
  simp only [map_add, map_sub, map_smul, Tensor0SSpace.add_apply,
    Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply, smul_eq_mul]
  rfl

theorem multilinear_pullback_hamiltonP_divergence_eq_laplacian
    [BoundarylessManifold I M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (t : D.RegularTime)
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (gSource : SmoothRiemannianMetric I M)
    (φ : ∀ x : M, TangentSpace I x ≃L[Real] TangentSpace I x)
    (hφ : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ :
        TotalSpace (E →L[Real] E)
          (fun x => TangentSpace I x →L[Real] TangentSpace I x))))
    (x : M)
    (hiso : ∀ u v, (S.family.metric t).inner x (φ x u) (φ x v) =
      gSource.inner x u v)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx → Idx → Real)
    (hinv : MetricInverseInBasis (I := I) gSource x basis gInv)
    (A B : TangentSpace I x) :
    let g := S.family.metric t
    let D := CovariantDerivative.pullbackFiberwiseLinearEquiv
      (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map (metricCov g)
    let fixedP := fun y => tensor0SPullbackCLE 3 (φ y).toLinearEquiv (hamiltonPField g y)
    let fixedRic := fun y => tensor0SPullbackCLE 2 (φ y).toLinearEquiv (metricRicci g y)
    let fixedRm := tensor0SPullbackCLE 4 (φ x).toLinearEquiv (metricRm04 g x)
    let fixedDu := fun y => tensor0SPullbackCLE 1 (φ y).toLinearEquiv (scalarDuSec S t y)
    (∑ i : Idx, ∑ j : Idx,
      gInv i j * D.multilinear 3 fixedP x (φ x (basis i)) (vec3 (basis j) A B)) =
      rawBundleConnLap g (D.multilinear 2) fixedRic x (vec2 A B) -
      (1 / 2 : Real) * D.multilinear 1 fixedDu x (φ x A) (fun _ : Fin 1 => B) -
      (∑ i, ∑ j, gInv i j *
        (fixedRic x (vec2 A (basis i)) * fixedRic x (vec2 (basis j) B))) +
      ∑ i, ∑ j, gInv i j * (∑ k, ∑ l, gInv k l *
        (fixedRm (vec4 A (basis k) (basis i) B) * fixedRic x (vec2 (basis l) (basis j)))) := by
  have hH := multilinear_pullback_eq_hessianSec φ hφ
    (metricCov (S.family.metric t)) (metricCov_smooth (S.family.metric t))
    (fun y => metricTracePair0SAt (S.family.metric t) (metricRicci (S.family.metric t) y))
    (trace02_smooth (S.family.metric t) (metricRicci (S.family.metric t)))
    x A (fun _ : Fin 1 => B)
  have hv : Fin.cons A (fun _ : Fin 1 => B) = vec2 A B := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at hH
  have hcore := multilinear_pullback_hamiltonP_divergence_eq_laplacian_hessian
    S hS t gSource φ hφ x hiso basis gInv hinv A B
  dsimp only at hcore ⊢
  rw [hamiltonRicciSquareAt_tensor0SPullbackCLE_apply
      gSource (S.family.metric t) (φ x).toLinearEquiv hiso basis gInv hinv,
    hamiltonCurvatureRicciAt_tensor0SPullbackCLE_apply
      gSource (S.family.metric t) (φ x).toLinearEquiv hiso basis gInv hinv] at hcore
  rw [← hH] at hcore
  exact hcore

end DifferentialGeometry.PDE.RicciFlow
