import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentRiemannian
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SInnerBundleCLM
import DifferentialGeometry.Geometry.Metric.TensorInner.PosDefBilinBoundedUnitBall
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SChartLocalInner
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SChartLocalInnerCLM
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SInnerBridgeIdentity
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth Riemannian metric on the (0,s)-tensor bundle

This file assembles the continuity of the pointwise `(0, s)`-tensor inner
product on smooth sections, delivering the public theorem
`Tensor0SBundle.continuous_inner_of_smooth_sections`.

The pointwise inner product as a continuous bilinear pairing
(`innerModelCLM`/`innerBundleCLM`, with symmetry and positive-definiteness), the
bounded-unit-ball lemma `posDef_bilin_unit_ball_isBounded`, the chart-local
inner product `chartTensorInnerPointwise_0s` together with its CLM packaging,
and the bridge identity `tensorInnerPointwise_0s_bridge_identity` are developed
in the sibling files
`Tensor0SInnerBundleCLM`, `PosDefBilinBoundedUnitBall`,
`Tensor0SChartLocalInner`, `Tensor0SChartLocalInnerCLM`, and
`Tensor0SInnerBridgeIdentity`, all of which are re-exported here.

Using the bridge identity together with the chart-local smoothness/continuity
of the chart-local inner product on smooth tensor arguments, the inner product
on smooth `(0, s)`-tensor sections is shown to be continuous on each chart and
then, by gluing the chart cover, globally continuous.
-/

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap Bornology
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Tensor
namespace Tensor0SRiemannian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure (chartGramMatrix
  chartGramMatrix_apply chartGramMatrix_isHermitian
  chartGramMatrix_posDef chartGramMatrix_det_pos
  chartGramMatrix_entry_contMDiffOn chartGramMatrix_det_contMDiffOn
  chartBasisVecFiber chartBasisVec)

variable {n : ℕ}

/-! ### Continuity of `chartTensorInnerPointwise_0s` with smooth tensor arguments

We extend the smoothness lemma `chartTensorInnerPointwise_0s_contMDiffOn` (for fixed
tensor args) to the case where the tensor arguments themselves are smooth functions
of `b` on the chart base set. The proof is by induction on `s`. -/

-- File-local instance to ensure typeclass resolution finds NormedSpace on Tensor0SModel.
private instance tensor0SModelNormedSpace_local {s : ℕ} :
    NormedSpace ℝ (Tensor0SModel s ℝ E) :=
  Tensor0SBundle.tensor0SModel_normedSpace s

-- File-local instance for NormedAddCommGroup on Tensor0SModel.
private instance tensor0SModelNormedAddCommGroup_local {s : ℕ} :
    NormedAddCommGroup (Tensor0SModel s ℝ E) := inferInstance


/-! ### Continuity of `chartTensorInnerPointwise_0s` with smooth tensor arguments

We extend the smoothness lemma `chartTensorInnerPointwise_0s_contMDiffOn` (for fixed
tensor args) to the case where the tensor arguments themselves are smooth functions
of `b` on the chart base set. The proof is by induction on `s`, using
`curryLeftAtCLM` (a CLM, avoiding curryEquiv normed-instance issues) to extract the
arguments at each induction step. -/

/-- The chart-local inner product is continuous in `b` on the chart base set
when the tensor arguments are continuous functions of `b`. -/
lemma chartTensorInnerPointwise_0s_continuousOn_smooth_args
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ)
    (T S : M → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (_hT : ContinuousOn T (trivializationAt E (TangentSpace I) α).baseSet)
    (_hS : ContinuousOn S (trivializationAt E (TangentSpace I) α).baseSet),
      ContinuousOn (fun b : M =>
          chartTensorInnerPointwise_0s (I := I) (M := M) s g α b (T b) (S b))
        (trivializationAt E (TangentSpace I) α).baseSet := by
  intro s
  induction s with
  | zero =>
      intro T S hT hS
      have heval0 : Continuous
          (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ =>
            T (fun i => Fin.elim0 i)) :=
        continuous_id.eval_const _
      have heq : (fun b : M =>
          chartTensorInnerPointwise_0s (I := I) (M := M) 0 g α b (T b) (S b)) =
          fun b : M =>
            ((T b) (fun i => Fin.elim0 i)) * ((S b) (fun i => Fin.elim0 i)) := by
        funext b
        rw [chartTensorInnerPointwise_0s_zero]
      rw [heq]
      exact (heval0.comp_continuousOn hT).mul (heval0.comp_continuousOn hS)
  | succ s ih =>
      intro T S hT hS
      have heq : (fun b : M =>
          chartTensorInnerPointwise_0s (I := I) (M := M) (s + 1) g α b (T b) (S b)) =
          fun b : M =>
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                (chartGramMatrix g α b)⁻¹ i j *
                  chartTensorInnerPointwise_0s (I := I) (M := M) s g α b
                    ((T b).curryLeft ((chartModelBasis E) i))
                    ((S b).curryLeft ((chartModelBasis E) j)) := by
        funext b
        rw [chartTensorInnerPointwise_0s_succ]
      rw [heq]
      refine continuousOn_finset_sum _ (fun i _ => ?_)
      refine continuousOn_finset_sum _ (fun j _ => ?_)
      refine ContinuousOn.mul ?_ ?_
      · exact (chartGramMatrix_inv_entry_contMDiffOn (I := I) g α i j).continuousOn
      · -- Apply ih: need continuity of the curryLeft-applied tensors as functions of b.
        -- Use the existing `curryLeftAtCLM` (a CLM) for continuity.
        have hT_curry : ContinuousOn
            (fun b : M => (T b).curryLeft ((chartModelBasis E) i))
            (trivializationAt E (TangentSpace I) α).baseSet := by
          have hheq : (fun b : M => (T b).curryLeft ((chartModelBasis E) i)) =
              fun b : M => curryLeftAtCLM (E := E) s ((chartModelBasis E) i) (T b) := by
            funext b
            rw [curryLeftAtCLM_apply]
          rw [hheq]
          exact (curryLeftAtCLM (E := E) s ((chartModelBasis E) i)).continuous.comp_continuousOn hT
        have hS_curry : ContinuousOn
            (fun b : M => (S b).curryLeft ((chartModelBasis E) j))
            (trivializationAt E (TangentSpace I) α).baseSet := by
          have hheq : (fun b : M => (S b).curryLeft ((chartModelBasis E) j)) =
              fun b : M => curryLeftAtCLM (E := E) s ((chartModelBasis E) j) (S b) := by
            funext b
            rw [curryLeftAtCLM_apply]
          rw [hheq]
          exact (curryLeftAtCLM (E := E) s ((chartModelBasis E) j)).continuous.comp_continuousOn hS
        exact ih _ _ hT_curry hS_curry

/-- The chart-local inner product is smooth in `b` on the chart base set when
each basis-tuple evaluation of the two tensor arguments is a smooth scalar
function of `b`. This is the smoothness analog of
`chartTensorInnerPointwise_0s_continuousOn_smooth_args`. The hypothesis form
(scalar smoothness of every basis-tuple evaluation) is used directly because
the diamond between `ContinuousMultilinearMap.instModule` and
`NormedSpace.toModule` on `Tensor0SModel` makes a direct `ContMDiffOn`
hypothesis on a `Tensor0SModel`-valued function awkward. The proof is by
induction on `s`. -/
lemma chartTensorInnerPointwise_0s_contMDiffOn_smooth_args
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ)
    (T S : M → ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
    (_hT : ∀ φ : Fin s → Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (T b) (fun k : Fin s => (chartModelBasis E) (φ k)))
        (trivializationAt E (TangentSpace I) α).baseSet)
    (_hS : ∀ φ : Fin s → Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (S b) (fun k : Fin s => (chartModelBasis E) (φ k)))
        (trivializationAt E (TangentSpace I) α).baseSet),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M =>
          chartTensorInnerPointwise_0s (I := I) (M := M) s g α b (T b) (S b))
        (trivializationAt E (TangentSpace I) α).baseSet := by
  intro s
  induction s with
  | zero =>
      intro T S hT hS
      have heq : (fun b : M =>
          chartTensorInnerPointwise_0s (I := I) (M := M) 0 g α b (T b) (S b)) =
          fun b : M =>
            ((T b) (fun i => Fin.elim0 i)) * ((S b) (fun i => Fin.elim0 i)) := by
        funext b
        rw [chartTensorInnerPointwise_0s_zero]
      rw [heq]
      have hT0 := hT (fun i : Fin 0 => Fin.elim0 i)
      have hS0 := hS (fun i : Fin 0 => Fin.elim0 i)

      have hempty :
          (fun k : Fin 0 => (chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))
            = (fun i : Fin 0 => (Fin.elim0 i : E)) := by
        funext i
        exact Fin.elim0 i
      have hT_smooth :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M => (T b) (fun i => Fin.elim0 i))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        have : (fun b : M => (T b) (fun i : Fin 0 => Fin.elim0 i)) =
            (fun b : M => (T b)
              (fun k : Fin 0 =>
                (chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))) := by
          funext b
          congr 1
          rw [hempty]
        rw [this]
        exact hT0
      have hS_smooth :
          ContMDiffOn I 𝓘(ℝ) ∞
            (fun b : M => (S b) (fun i => Fin.elim0 i))
            (trivializationAt E (TangentSpace I) α).baseSet := by
        have : (fun b : M => (S b) (fun i : Fin 0 => Fin.elim0 i)) =
            (fun b : M => (S b)
              (fun k : Fin 0 =>
                (chartModelBasis E) ((fun i : Fin 0 => Fin.elim0 i) k))) := by
          funext b
          congr 1
          rw [hempty]
        rw [this]
        exact hS0
      exact hT_smooth.mul hS_smooth
  | succ s ih =>
      intro T S hT hS
      have heq : (fun b : M =>
          chartTensorInnerPointwise_0s (I := I) (M := M) (s + 1) g α b (T b) (S b)) =
          fun b : M =>
            ∑ i : Fin (Module.finrank ℝ E),
              ∑ j : Fin (Module.finrank ℝ E),
                (chartGramMatrix g α b)⁻¹ i j *
                  chartTensorInnerPointwise_0s (I := I) (M := M) s g α b
                    ((T b).curryLeft ((chartModelBasis E) i))
                    ((S b).curryLeft ((chartModelBasis E) j)) := by
        funext b
        rw [chartTensorInnerPointwise_0s_succ]
      rw [heq]
      refine contMDiffOn_finset_sum (fun i _ => ?_)
      refine contMDiffOn_finset_sum (fun j _ => ?_)
      refine ContMDiffOn.mul ?_ ?_
      · exact chartGramMatrix_inv_entry_contMDiffOn (I := I) g α i j
      · -- Apply the inductive hypothesis to the curryLeft-applied tensors.
        -- Each basis evaluation of the curryLeft tensor unfolds to a basis
        -- evaluation of the original tensor on the extended `Fin.cons`-tuple.
        refine ih
            (fun b : M => (T b).curryLeft ((chartModelBasis E) i))
            (fun b : M => (S b).curryLeft ((chartModelBasis E) j))
            ?_ ?_
        · intro ψ

          set ψ' : Fin (s + 1) → Fin (Module.finrank ℝ E) :=
            Fin.cons (α := fun _ => Fin (Module.finrank ℝ E)) i ψ with hψ'
          have hψ'_zero : ψ' 0 = i := by
            simp [hψ']
          have hψ'_succ : ∀ k : Fin s, ψ' k.succ = ψ k := by
            intro k
            simp [hψ']
          have heq' :
              (fun b : M => ((T b).curryLeft ((chartModelBasis E) i))
                  (fun k : Fin s => (chartModelBasis E) (ψ k)))
                = fun b : M =>
                    (T b) (fun k : Fin (s + 1) =>
                      (chartModelBasis E) (ψ' k)) := by
            funext b
            rw [ContinuousMultilinearMap.curryLeft_apply]
            congr 1
            funext k
            refine Fin.cases ?_ ?_ k
            · rw [hψ'_zero]

              simp
            · intro k'
              rw [hψ'_succ k']
              simp
          rw [heq']
          exact hT ψ'
        · intro ψ
          set ψ' : Fin (s + 1) → Fin (Module.finrank ℝ E) :=
            Fin.cons (α := fun _ => Fin (Module.finrank ℝ E)) j ψ with hψ'
          have hψ'_zero : ψ' 0 = j := by
            simp [hψ']
          have hψ'_succ : ∀ k : Fin s, ψ' k.succ = ψ k := by
            intro k
            simp [hψ']
          have heq' :
              (fun b : M => ((S b).curryLeft ((chartModelBasis E) j))
                  (fun k : Fin s => (chartModelBasis E) (ψ k)))
                = fun b : M =>
                    (S b) (fun k : Fin (s + 1) =>
                      (chartModelBasis E) (ψ' k)) := by
            funext b
            rw [ContinuousMultilinearMap.curryLeft_apply]
            congr 1
            funext k
            refine Fin.cases ?_ ?_ k
            · rw [hψ'_zero]; simp
            · intro k'
              rw [hψ'_succ k']; simp
          rw [heq']
          exact hS ψ'

/-! ### Public continuity theorem on each chart

Given the bridge identity and the chart-local smoothness, we obtain
chart-local continuity of the inner product on smooth tensor sections. The
caller supplies the continuity hypothesis on the chart-trivialised projection. -/

/-- On each chart α, given continuity of the chart-α-trivialised projections of
the tensor sections, the pointwise inner product is continuous in `b` on the
chart's base set. -/
theorem chartLocal_continuous_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T S : ∀ y : M, Tensor0SSpace s I y) (α : M)
    (hTα : ContinuousOn
      (fun b : M => (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (T b)).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b))
      (trivializationAt E (TangentSpace I) α).baseSet)
    (hSα : ContinuousOn
      (fun b : M => (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (S b)).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b))
      (trivializationAt E (TangentSpace I) α).baseSet) :
    ContinuousOn
      (fun b : M =>
        tensorInnerPointwise_0s (I := I) (M := M) s g b
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) (T b))
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) (S b)))
      (trivializationAt E (TangentSpace I) α).baseSet := by

  have hbridge : ∀ b ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      tensorInnerPointwise_0s (I := I) (M := M) s g b
        (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) (T b))
        (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) (S b)) =
      chartTensorInnerPointwise_0s (I := I) (M := M) s g α b
        ((Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (T b)).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b))
        ((Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (S b)).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b)) := by
    intro b hb
    exact tensorInnerPointwise_0s_bridge_identity (I := I) (M := M) g α s hb _ _
  refine ContinuousOn.congr ?_ hbridge
  exact chartTensorInnerPointwise_0s_continuousOn_smooth_args
    (I := I) (M := M) g α s _ _ hTα hSα

/-- Global continuity of the pointwise inner product on (0,s) tensor sections.

Given the chart-trivialised projection-continuity hypothesis at every point of
`M` (one chart-α centred at each point), the inner product is globally
continuous. The hypothesis says: for each `α ∈ M`, the chart-α-trivialised
projection of each tensor section is continuous on the chart's base set. -/
theorem _root_.Tensor0SBundle.continuous_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (T S : ∀ y : M, Tensor0SSpace s I y)
    (hT_charts : ∀ α : M, ContinuousOn
      (fun b : M => (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (T b)).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b))
      (trivializationAt E (TangentSpace I) α).baseSet)
    (hS_charts : ∀ α : M, ContinuousOn
      (fun b : M => (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
          (S b)).compContinuousLinearMap
          (fun _ : Fin s => chartJinv (I := I) (M := M) α b))
      (trivializationAt E (TangentSpace I) α).baseSet) :
    Continuous (fun b : M =>
      tensorInnerPointwise_0s (I := I) (M := M) s g b
        (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) (T b))
        (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) (S b))) := by
  rw [continuous_iff_continuousAt]
  intro b
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) b).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt _ _ b
  have hOpen : IsOpen (trivializationAt E (TangentSpace I) b).baseSet :=
    (trivializationAt E (TangentSpace I) b).open_baseSet
  have hLocal := chartLocal_continuous_inner_of_smooth_sections
    (I := I) (M := M) g s T S b (hT_charts b) (hS_charts b)
  exact hLocal.continuousAt (hOpen.mem_nhds hb_base)

end Tensor0SRiemannian
end Tensor
end DifferentialGeometry

end
