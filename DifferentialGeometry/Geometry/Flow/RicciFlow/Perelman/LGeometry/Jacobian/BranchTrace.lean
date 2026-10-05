import DifferentialGeometry.Geometry.Operator.Laplacian.Rough
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.Basic
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false

noncomputable section

open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

private theorem trace_invGram_metricTensor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) {y : M}
    (basis : Module.Basis ι ℝ (TangentSpace I y))
    (B : Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H)
      (I := I) (M := M) 2 y) :
    Matrix.trace
      ((Matrix.of fun i j ↦ g.inner y (basis i) (basis j))⁻¹ *
        Matrix.of fun i j ↦
          B (vec2 (I := I) (basis i) (basis j))) =
      metricTracePair0SAt (I := I) g B := by
  classical
  let G : Matrix ι ι ℝ :=
    Matrix.of fun i j ↦ g.inner y (basis i) (basis j)
  let U : Matrix ι ι ℝ :=
    Matrix.of (basisInvMetric (I := I) g y basis)
  have hUG : U * G = 1 := by
    ext i j
    simpa only [Matrix.mul_apply, Matrix.one_apply,
      U, G, Matrix.of_apply] using
      (basisInvMetric_isInverse (I := I) g y basis i j).1
  have hGinv : G⁻¹ = U := Matrix.inv_eq_left_inv hUG
  change Matrix.trace
    (G⁻¹ * Matrix.of fun i j ↦
      B (vec2 (I := I) (basis i) (basis j))) =
    metricTracePair0SAt (I := I) g B
  rw [hGinv, metricTracePair0SAt_eq_sum_basis (I := I) g basis
    (basisInvMetric (I := I) g y basis)
    (basisInvMetric_isInverse (I := I) g y basis) B]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    U, Matrix.of_apply]
  calc
    (∑ i : ι, ∑ j : ι,
        basisInvMetric (I := I) g y basis i j *
          B (vec2 (I := I) (basis j) (basis i))) =
      ∑ j : ι, ∑ i : ι,
        basisInvMetric (I := I) g y basis i j *
          B (vec2 (I := I) (basis j) (basis i)) :=
      Finset.sum_comm
    _ = ∑ i : ι, ∑ j : ι,
        basisInvMetric (I := I) g y basis i j *
          B (vec2 (I := I) (basis i) (basis j)) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [basisInvMetric_symm (I := I) g y basis j i]

end DifferentialGeometry.PDE.RicciFlow
end

set_option autoImplicit false
noncomputable section
open Bundle Set DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}
private theorem lActBranch_hess_lExpField
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M) (Z : TangentSpace I x) (tau : ℝ)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hconj : ¬ IsLConjugate S T x Z tau)
    (V W : TangentSpace I x) :
    hessFun (S.base.metric (T - tau))
      (lActBranch S hS T x Z tau hdom hconj) (lExp S T x Z tau)
      (lExpField S T x Z V tau) (lExpField S T x Z W tau) =
      (2 * Real.sqrt tau) * (S.base.metric (T - tau)).inner
        (lExp S T x Z tau) (lExpFieldVelocity S T x Z V tau)
        (lExpField S T x Z W tau) := by
  let z : E := Z
  let hloc : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞
      (fun W : E ↦ lExp S T x W tau) z :=
    lExp_localDiffeo S hS T x Z tau hdom hconj
  let y : M := lExp S T x Z tau
  let YV : TangentSpace I y := lExpField S T x Z V tau
  let YW : TangentSpace I y := lExpField S T x Z W tau
  have hInv : mfderiv I 𝓘(ℝ, E) hloc.localInverse y YV = V := by
    have hleft := (hloc.mfderivToContinuousLinearEquiv (by simp)).left_inv V
    exact hleft
  have hbranch : hessFun (S.base.metric (T - tau))
      (lActBranch S hS T x Z tau hdom hconj) y YV YW =
      (S.base.metric (T - tau)).inner y (lRegularizedFieldVelocity S T x Z V tau) YW := by
    have hout : hessFun (S.base.metric (T - tau))
        (lActBranch S hS T x Z tau hdom hconj) y YV YW =
        (S.base.metric (T - tau)).inner y
          (lRegularizedFieldVelocity S T x Z
            (mfderiv I 𝓘(ℝ, E) hloc.localInverse y YV) tau) YW := by
      exact lActBranch_hess S hS T x Z tau hdom hconj YV YW
    exact hout.trans (congrArg (fun U : E ↦
      (S.base.metric (T - tau)).inner y
        (lRegularizedFieldVelocity S T x Z U tau) YW) hInv)
  exact hbranch.trans (lRegularizedJacobi_pair S hS T x Z V tau hdom YW)
end DifferentialGeometry.PDE.RicciFlow
end

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem lExpTrace_eq_branch
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M) (Z : TangentSpace I x) (tau : ℝ)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hnconj : ¬ IsLConjugate S T x Z tau) :
    (1 / 2 : ℝ) * Matrix.trace
        ((lExpGram S T x Z tau)⁻¹ * lExpGramDeriv S T x Z tau) =
      (1 / (2 * Real.sqrt tau)) *
        metricTracePair0SAt (I := I) (S.base.metric (T - tau))
          (hessTensorAt (I := I) (S.base.metric (T - tau))
            (lActBranch S hS T x Z tau hdom hnconj)
            (lExp S T x Z tau)) +
      S.scalar (T - tau) (lExp S T x Z tau) := by
  classical
  have htau : 0 < tau :=
    ((mem_lExpPosDom S T x Z tau).1 hdom).1
  let y : M := lExp S T x Z tau
  let g : SmoothRiemannianMetric I M := S.base.metric (T - tau)
  let F : M → ℝ := lActBranch S hS T x Z tau hdom hnconj
  let z : E := Z
  let L : E →ₗ[ℝ] TangentSpace I y :=
    { toFun := fun V ↦ lExpField S T x Z V tau
      map_add' := by
        intro V W
        exact (mfderiv 𝓘(ℝ, E) I
          (fun U : E ↦ lExp S T x U tau) z).map_add V W
      map_smul' := by
        intro c V
        exact (mfderiv 𝓘(ℝ, E) I
          (fun U : E ↦ lExp S T x U tau) z).map_smul c V }
  have hbij : Function.Bijective L := by
    constructor
    · intro V W hVW
      exact lExpDeriv_inj (I := I) S T x Z tau hdom hnconj hVW
    · intro Y
      obtain ⟨V, hV⟩ :=
        lExpDeriv_surj (I := I) S T x Z tau hdom hnconj Y
      exact ⟨V, hV⟩
  let e : E ≃ₗ[ℝ] TangentSpace I y :=
    LinearEquiv.ofBijective L hbij
  let basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ
      (TangentSpace I y) :=
    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).map e
  have hbasis (i : Fin (Module.finrank ℝ E)) :
      basis i = lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) tau := by
    change e ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) = _
    rfl
  let G := lExpGram S T x Z tau
  let V := lExpVelocityGram S T x Z tau
  let Hm : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.of fun i j ↦
      hessTensorAt (I := I) g F y
        (vec2 (I := I) (basis i) (basis j))
  have hGram :
      (Matrix.of fun i j ↦ g.inner y (basis i) (basis j)) = G := by
    ext i j
    simp only [G, lExpGram, lGram, Matrix.of_apply, g, y, hbasis]
  have hH : Hm = (2 * Real.sqrt tau) • V := by
    ext i j
    change hessTensorAt (I := I) g F y
        (vec2 (I := I) (basis i) (basis j)) =
      (2 * Real.sqrt tau) * g.inner y
        (lExpFieldVelocity S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) tau)
        (lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) tau)
    rw [hessTensorAt_apply, hbasis, hbasis]
    exact lActBranch_hess_lExpField (I := I) S hS T x Z tau
      hdom hnconj ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)
  have hTraceH :
      Matrix.trace (G⁻¹ * Hm) =
        metricTracePair0SAt (I := I) g
          (hessTensorAt (I := I) g F y) := by
    have h := trace_invGram_metricTensor (I := I) g basis
      (hessTensorAt (I := I) g F y)
    rw [hGram] at h
    exact h
  have hTraceRic :
      Matrix.trace (G⁻¹ * lExpRicci S T x Z tau) =
        S.scalar (T - tau) y := by
    have h := trace_invGram_metricTensor (I := I) g basis
      (S.ricciAt (T - tau) y)
    rw [hGram] at h
    have h' :
        Matrix.trace (G⁻¹ * lExpRicci S T x Z tau) =
          metricTracePair0SAt (I := I) g
            (S.ricciAt (T - tau) y) := by
      simpa only [lExpRicci, Matrix.of_apply, hbasis, g, y] using h
    apply h'.trans
    simpa only [g, SolutionOn.family_metric] using
      (S.scalar_eq_metricTrace (I := I) (T - tau) y).symm
  have hGT : G.transpose = G := by
    ext i j
    simp only [Matrix.transpose_apply, G, lExpGram, lGram, Matrix.of_apply]
    exact (S.base.metric (T - tau)).symm (lExp S T x Z tau)
      (lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) tau)
      (lExpField S T x Z ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) tau)
  have hGinvT : (G⁻¹).transpose = G⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hGT]
  have htrans :
      Matrix.trace (G⁻¹ * V.transpose) =
        Matrix.trace (G⁻¹ * V) := by
    simpa only [hGinvT] using Matrix.trace_transpose_mul G⁻¹ V
  have hscaled :
      (2 * Real.sqrt tau) * Matrix.trace (G⁻¹ * V) =
        metricTracePair0SAt (I := I) g
          (hessTensorAt (I := I) g F y) := by
    rw [hH] at hTraceH
    simpa only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] using hTraceH
  have hden : 2 * Real.sqrt tau ≠ 0 :=
    mul_ne_zero (by norm_num) (Real.sqrt_pos.2 htau).ne'
  have hVel :
      Matrix.trace (G⁻¹ * V) =
        (1 / (2 * Real.sqrt tau)) *
          metricTracePair0SAt (I := I) g
            (hessTensorAt (I := I) g F y) := by
    calc
      Matrix.trace (G⁻¹ * V) =
          metricTracePair0SAt (I := I) g
            (hessTensorAt (I := I) g F y) / (2 * Real.sqrt tau) :=
        (eq_div_iff hden).2 ((mul_comm _ _).trans hscaled)
      _ = (1 / (2 * Real.sqrt tau)) *
          metricTracePair0SAt (I := I) g
            (hessTensorAt (I := I) g F y) := by ring
  rw [lExpGramDeriv_eq]
  change (1 / 2 : ℝ) * Matrix.trace
      (G⁻¹ * (V + V.transpose + 2 • lExpRicci S T x Z tau)) =
    (1 / (2 * Real.sqrt tau)) *
      metricTracePair0SAt (I := I) g
        (hessTensorAt (I := I) g F y) +
      S.scalar (T - tau) y
  simp only [Matrix.mul_add, Matrix.trace_add,
    Matrix.mul_smul, Matrix.trace_smul]
  rw [htrans, hVel, hTraceRic]
  ring

end DifferentialGeometry.PDE.RicciFlow
end
