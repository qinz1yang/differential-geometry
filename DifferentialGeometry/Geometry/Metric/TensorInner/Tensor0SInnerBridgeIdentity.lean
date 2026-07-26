import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentRiemannian
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SChartLocalInner
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
# Bridge identity for the (0,s) pointwise inner product

This file relates the metric pointwise inner product
`tensorInnerPointwise_0s s g b` to its chart-local replacement
`chartTensorInnerPointwise_0s` from the sibling file. The chart-Jacobian of the
tangent trivialisation centred at `α` is packaged as continuous linear maps
`chartJ`/`chartJinv`, and the change-of-basis between the canonical model basis
and the chart-`α` frame is encoded by the matrices `chartJMatrix`/
`chartJinvMatrix`, which are mutually inverse on the trivialisation base set.

The Gram-matrix transformation `chartGramMatrix = chartJinvMatrixᵀ * gramMatrixAt
* chartJinvMatrix` and its inverse-entry consequence yield the main result
`tensorInnerPointwise_0s_bridge_identity`: on the base set, the metric inner
product of two tensors equals the chart-local inner product of the tensors
pre-composed with `chartJinv`. This is the algebraic bridge underpinning the
continuity of the inner product on smooth sections.
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

/-! ### Continuity of the inner product on smooth tensor sections

We deliver the public continuity theorem `Tensor0SBundle.continuous_inner_of_smooth_sections`
via the following strategy:

1. Define `chartTensorInnerPointwise_0s` as a chart-local version of the
   pointwise inner product, using `chartGramMatrix g α b` (smooth in `b`)
   in place of `gramMatrixAt g b`.
2. Establish a basis-invariance identity relating the two pointwise inner
   products: `tensorInnerPointwise_0s s g b S T = chartTensorInnerPointwise_0s s g α b S_α(b) T_α(b)`
   where `S_α(b) = S.compContinuousLinearMap (fun _ => (triv α).symmL b)`.
3. From this, on each chart, the inner product on smooth sections becomes
   a continuous function of `b` because:
   - The chart-local Gram matrix and its inverse are smooth in `b`.
   - The trivialised tensor sections are smooth (continuous) in `b`.
4. Glue via chart cover for global continuity. -/

/-! ### Auxiliary CLMs and their relations

We package the chart-Jacobian and its inverse as CLMs and establish the
basic identities (round-trip, basis-vector image, Gram-matrix expansion). -/

/-- The chart-Jacobian on the fibre at `b`: the forward map of the tangent
trivialisation centred at `α`. -/
noncomputable def chartJ (α : M) (b : M) : E →L[ℝ] E :=
  (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b

/-- The chart-Jacobian inverse on the fibre at `b`: the backward map of the
tangent trivialisation centred at `α`. -/
noncomputable def chartJinv (α : M) (b : M) : E →L[ℝ] E :=
  (trivializationAt E (TangentSpace I) α).symmL ℝ b

lemma chartJinv_apply (α : M) (b : M) (v : E) :
    chartJinv (I := I) (M := M) α b v =
      (trivializationAt E (TangentSpace I) α).symmL ℝ b v := rfl

lemma chartJ_apply (α : M) (b : M) (v : E) :
    chartJ (I := I) (M := M) α b v =
      (trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b v := rfl

/-- `chartJinv α b` images the model basis vector `(chartModelBasis E) i` to the
chart-α basis vector `chartBasisVecFiber α i b`. -/
private lemma chartJinv_basis (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    chartJinv (I := I) (M := M) α b ((chartModelBasis E) i) =
      chartBasisVecFiber (I := I) α i b := by
  unfold chartBasisVecFiber chartJinv
  rfl

/-- For `b` in the chart's base set, `chartJ α b ∘ chartJinv α b = id`. -/
lemma chartJ_chartJinv (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) (v : E) :
    chartJ (I := I) (M := M) α b
        (chartJinv (I := I) (M := M) α b v) = v := by
  unfold chartJ chartJinv
  exact (trivializationAt E (TangentSpace I) α).continuousLinearMapAt_symmL hb v

/-- For `b` in the chart's base set, `chartJinv α b ∘ chartJ α b = id` on `TangentSpace I b`. -/
lemma chartJinv_chartJ (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) (v : TangentSpace I b) :
    chartJinv (I := I) (M := M) α b
        (chartJ (I := I) (M := M) α b v) = v := by
  unfold chartJ chartJinv
  exact (trivializationAt E (TangentSpace I) α).symmL_continuousLinearMapAt hb v

/-- Alias for `chartJinv_chartJ`: useful as a rewrite target when the
type-synonym `TangentSpace I b = E` needs to be matched against `E` directly
in downstream files. -/
lemma chartJinv_chartJ_self (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) (v : E) :
    chartJinv (I := I) (M := M) α b
        (chartJ (I := I) (M := M) α b v) = v :=
  chartJinv_chartJ (I := I) (M := M) α hb v

/-! ### Gram matrix relationship

The chart-α Gram matrix is the Gram matrix of the metric on the
chart-α basis vectors `chartBasisVecFiber α i b = chartJinv α b ((chartModelBasis E) i)`.
This is equivalent to evaluating `g.inner b` on the corresponding model-basis
vectors after applying `chartJinv α b`. -/

/-- The chart-α Gram matrix entry expressed via `chartJinv α b`. -/
lemma chartGramMatrix_eq_innerJinv
    (g : SmoothRiemannianMetric I M) (α b : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix g α b i j =
      g.inner b
        (chartJinv (I := I) (M := M) α b ((chartModelBasis E) i))
        (chartJinv (I := I) (M := M) α b ((chartModelBasis E) j)) := by
  rw [chartGramMatrix_apply]
  rw [chartJinv_basis (I := I) (M := M), chartJinv_basis (I := I) (M := M)]

/-! ### Linearity of `curryLeft` in its argument

The curryLeft slot map satisfies `T.curryLeft (∑ a c_a v_a) = ∑ a c_a (T.curryLeft v_a)`. -/

private lemma curryLeft_sum {n : ℕ} {s : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
    (c : Fin n → ℝ) (v : Fin n → E) :
    T.curryLeft (∑ k : Fin n, c k • v k) =
      ∑ k : Fin n, c k • T.curryLeft (v k) := by
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [map_smul]

/-! ### Composition lemma for `compContinuousLinearMap` and `curryLeft`

Lemma: `(T \circ_ML L).curryLeft w = (T.curryLeft (L w)) \circ_ML L`. -/

private lemma compContinuousLinearMap_curryLeft {s : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
    (L : E →L[ℝ] E) (w : E) :
    (T.compContinuousLinearMap (fun _ : Fin (s + 1) => L)).curryLeft w =
      (T.curryLeft (L w)).compContinuousLinearMap (fun _ : Fin s => L) := by
  ext m
  simp only [ContinuousMultilinearMap.curryLeft_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]

  have hcons_eq : (fun i : Fin (s + 1) => L ((Fin.cons w m : Fin (s + 1) → E) i)) =
      (Fin.cons (L w) (fun i' : Fin s => L (m i')) : Fin (s + 1) → E) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro i'
      simp
  rw [hcons_eq]

/-! ### Bilinearity of `tensorInnerPointwise_0s` over a finite sum

For sums `S = ∑ k c_k S_k`, `T = ∑ l d_l T_l`, the tensor inner product
expands as `∑_{k,l} c_k d_l ⟨S_k, T_l⟩`. -/

private lemma tensorInnerPointwise_0s_sum_left
    (g : SmoothRiemannianMetric I M) (b : M) (s : ℕ) {n : ℕ}
    (c : Fin n → ℝ) (S : Fin n → Tensor0SModel s ℝ E)
    (T : Tensor0SModel s ℝ E) :
    tensorInnerPointwise_0s (I := I) (M := M) s g b
        (∑ k : Fin n, c k • S k) T =
      ∑ k : Fin n, c k *
        tensorInnerPointwise_0s (I := I) (M := M) s g b (S k) T := by
  classical
  induction n with
  | zero =>
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rw [show (0 : Tensor0SModel s ℝ E) =
        (0 : ℝ) • (0 : Tensor0SModel s ℝ E) from
        (zero_smul _ _).symm]
      rw [tensorInnerPointwise_0s_smul_left, zero_mul]
  | succ n ih =>

      have ih_app := ih (fun k : Fin n => c k.succ) (fun k : Fin n => S k.succ)
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      rw [tensorInnerPointwise_0s_add_left, tensorInnerPointwise_0s_smul_left]
      rw [ih_app]

private lemma tensorInnerPointwise_0s_sum_right
    (g : SmoothRiemannianMetric I M) (b : M) (s : ℕ) {n : ℕ}
    (S : Tensor0SModel s ℝ E)
    (d : Fin n → ℝ) (T : Fin n → Tensor0SModel s ℝ E) :
    tensorInnerPointwise_0s (I := I) (M := M) s g b S
        (∑ l : Fin n, d l • T l) =
      ∑ l : Fin n, d l *
        tensorInnerPointwise_0s (I := I) (M := M) s g b S (T l) := by
  classical
  induction n with
  | zero =>
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rw [show (0 : Tensor0SModel s ℝ E) =
        (0 : ℝ) • (0 : Tensor0SModel s ℝ E) from
        (zero_smul _ _).symm]
      rw [tensorInnerPointwise_0s_smul_right, zero_mul]
  | succ n ih =>
      have ih_app := ih (fun l : Fin n => d l.succ) (fun l : Fin n => T l.succ)
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      rw [tensorInnerPointwise_0s_add_right, tensorInnerPointwise_0s_smul_right]
      rw [ih_app]

/-! ### Helper for the bridge identity: a generalised inner-product formula

To avoid the matrix-level basis-change argument, we define a generalised
inner-product formula `tensorInnerOnFrame s b f Ginv T S`, parametric in
the basis `f` and the matrix `Ginv`. This is the same recursion as
`tensorInnerPointwise_0s` and `chartTensorInnerPointwise_0s` with the basis
`f` and matrix `Ginv` factored out. We prove that:

* `tensorInnerOnFrame s b (chartModelBasis E) (gramMatrixAt g b)⁻¹ T S =
   tensorInnerPointwise_0s s g b T S`.
* `tensorInnerOnFrame s b (chartBasisVecFiber α · b) (chartGramMatrix g α b)⁻¹ T S =
   tensorInnerPointwise_0s s g b T S` (basis-invariance for the same metric).
* The chart-α formula equals `chartTensorInnerPointwise_0s` precomposed with
   the trivialization. -/

/-- The generalised inner-product formula on a basis `f` with matrix `Ginv`. -/
private noncomputable def tensorInnerOnFrame :
    (s : ℕ) → (Fin (Module.finrank ℝ E) → E) →
      Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ →
      Tensor0SModel s ℝ E →
      Tensor0SModel s ℝ E → ℝ
  | 0, _, _, T, S => T (fun i => Fin.elim0 i) * S (fun i => Fin.elim0 i)
  | s + 1, f, Ginv, T, S =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        Ginv i j *
          tensorInnerOnFrame s f Ginv (T.curryLeft (f i)) (S.curryLeft (f j))

private lemma tensorInnerOnFrame_zero
    (f : Fin (Module.finrank ℝ E) → E)
    (Ginv : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (T S : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) :
    tensorInnerOnFrame (E := E) 0 f Ginv T S =
      T (fun i => Fin.elim0 i) * S (fun i => Fin.elim0 i) := rfl

private lemma tensorInnerOnFrame_succ (s : ℕ)
    (f : Fin (Module.finrank ℝ E) → E)
    (Ginv : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (T S : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    tensorInnerOnFrame (E := E) (s + 1) f Ginv T S =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        Ginv i j *
          tensorInnerOnFrame (E := E) s f Ginv (T.curryLeft (f i)) (S.curryLeft (f j)) := rfl

/-- `tensorInnerPointwise_0s s g b T S` agrees with `tensorInnerOnFrame s e G⁻¹` on
the model basis `e = chartModelBasis E` and `G = gramMatrixAt g b`. -/
private lemma tensorInnerPointwise_0s_eq_tensorInnerOnFrame
    (g : SmoothRiemannianMetric I M) (b : M) :
    ∀ (s : ℕ) (T S : Tensor0SModel s ℝ E),
      tensorInnerPointwise_0s (I := I) (M := M) s g b T S =
        tensorInnerOnFrame (E := E) s
          (fun i : Fin (Module.finrank ℝ E) => (chartModelBasis E) i)
          (gramMatrixAt (I := I) (M := M) g b)⁻¹ T S := by
  intro s
  induction s with
  | zero => intro T S; rfl
  | succ s ih =>
      intro T S
      rw [tensorInnerPointwise_0s_succ, tensorInnerOnFrame_succ]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [ih (T.curryLeft ((chartModelBasis E) i))
          (S.curryLeft ((chartModelBasis E) j))]

/-- `chartTensorInnerPointwise_0s g α s b T S` agrees with `tensorInnerOnFrame s e G⁻¹`
on the model basis `e = chartModelBasis E` and `G = chartGramMatrix g α b`. -/
private lemma chartTensorInnerPointwise_0s_eq_tensorInnerOnFrame
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) :
    ∀ (s : ℕ) (T S : Tensor0SModel s ℝ E),
      chartTensorInnerPointwise_0s (I := I) (M := M) s g α b T S =
        tensorInnerOnFrame (E := E) s
          (fun i : Fin (Module.finrank ℝ E) => (chartModelBasis E) i)
          (chartGramMatrix g α b)⁻¹ T S := by
  intro s
  induction s with
  | zero => intro T S; rfl
  | succ s ih =>
      intro T S
      rw [chartTensorInnerPointwise_0s_succ, tensorInnerOnFrame_succ]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [ih (T.curryLeft ((chartModelBasis E) i))
          (S.curryLeft ((chartModelBasis E) j))]

/-! ### Basis-change for `tensorInnerOnFrame`

The key fact: changing both the basis `f → h` and the matrix
`Ginv → Hinv` consistently with the gram-matrix transformation
preserves `tensorInnerOnFrame`. We don't formulate this in full
generality; instead, we prove the specific change-of-basis result
needed for the bridge identity. -/

/-! ### Frame-change strategy

For a basis `f`, an alternative basis `h_i = ∑_a A_{ai} f_a` expressed via a matrix `A`,
and the corresponding gram matrices `G_f` (on `f`), `G_h` (on `h`) satisfying
`G_h = Aᵀ G_f A`, we expect `tensorInnerOnFrame s h G_h⁻¹ T S = tensorInnerOnFrame s f G_f⁻¹ T S`.

We work in the special case where `f = chartModelBasis E`, `h_i = chartJinv α b (e_i)`,
`A = matrix of chartJinv`. Then `G_f = gramMatrixAt g b`, `G_h = chartGramMatrix g α b`.

We don't prove the abstract change-of-basis at the matrix level. Instead, we prove
the bridge identity DIRECTLY by induction on `s` using the recursion structure. -/

/-! ### The bridge identity, by direct induction

The bridge identity:
`tensorInnerPointwise_0s s g b T S = chartTensorInnerPointwise_0s g α s b T_α S_α`
where `T_α = T.compContinuousLinearMap (fun _ => chartJinv α b)`, on `b` in the chart
base set.

We prove this directly by induction on `s` using the basis-change argument:
the chart-α basis `chartBasisVecFiber α i b = chartJinv α b ((chartModelBasis E) i)`,
and the chart-α gram matrix `chartGramMatrix g α b` is the gram matrix of `g.inner b`
on this basis.

KEY OBSERVATION: An equivalent formulation is to prove the bridge in the form:
`tensorInnerPointwise_0s s g b T S = chartTensorInnerOnChartBasis s g α b T S`
where `chartTensorInnerOnChartBasis` uses the chart-α basis `chartBasisVecFiber` directly:
this is the "true basis-change" form. Then we can connect to
`chartTensorInnerPointwise_0s` (which uses the model basis) via the
`compContinuousLinearMap` substitution.

We follow this two-step path. -/

/-- An auxiliary inner product on the chart-α basis: same recursion as
`chartTensorInnerPointwise_0s` but using `chartBasisVecFiber α i b` (the chart-α basis)
instead of the fixed model basis. -/
private noncomputable def chartTensorInnerOnChartBasis :
    (s : ℕ) → SmoothRiemannianMetric I M → (α : M) → (b : M) →
      Tensor0SModel s ℝ E →
      Tensor0SModel s ℝ E → ℝ
  | 0, _g, _α, _b, T, S =>
      T (fun i => Fin.elim0 i) * S (fun i => Fin.elim0 i)
  | s + 1, g, α, b, T, S =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (chartGramMatrix g α b)⁻¹ i j *
          chartTensorInnerOnChartBasis s g α b
            (T.curryLeft (chartBasisVecFiber (I := I) α i b))
            (S.curryLeft (chartBasisVecFiber (I := I) α j b))

private lemma chartTensorInnerOnChartBasis_zero
    (g : SmoothRiemannianMetric I M) (α b : M)
    (T S : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) :
    chartTensorInnerOnChartBasis (I := I) (M := M) 0 g α b T S =
      T (fun i => Fin.elim0 i) * S (fun i => Fin.elim0 i) := rfl

private lemma chartTensorInnerOnChartBasis_succ
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (T S : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    chartTensorInnerOnChartBasis (I := I) (M := M) (s + 1) g α b T S =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (chartGramMatrix g α b)⁻¹ i j *
          chartTensorInnerOnChartBasis (I := I) (M := M) s g α b
            (T.curryLeft (chartBasisVecFiber (I := I) α i b))
            (S.curryLeft (chartBasisVecFiber (I := I) α j b)) := rfl

/-! ### Equality of the two chart-trivialised forms

We show `chartTensorInnerOnChartBasis s g α b T S =
   chartTensorInnerPointwise_0s g α s b T_α S_α`
where `T_α = T \circ_ML chartJinv α b`.

The proof uses the "compose-and-curry" identity
`(T \circ L).curryLeft (L w) = (T.curryLeft w) \circ L` slot-by-slot. -/

/-- The "compose-and-curry" relation, packaged for `chartJinv α b`:
given an arity-(s+1) tensor `T`, currying `T` at `chartJinv α b ((chartModelBasis E) i)`
in the slot, after composing with `chartJinv α b` in the remaining slots, equals the
result of currying first then composing with `chartJinv α b` in remaining slots. -/
private lemma chartJinv_compose_curry_chartBasis {s : ℕ} (α : M) (b : M)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
    (i : Fin (Module.finrank ℝ E)) :
    (T.compContinuousLinearMap (fun _ : Fin (s + 1) =>
        chartJinv (I := I) (M := M) α b)).curryLeft ((chartModelBasis E) i) =
      (T.curryLeft (chartBasisVecFiber (I := I) α i b)).compContinuousLinearMap
        (fun _ : Fin s => chartJinv (I := I) (M := M) α b) := by
  rw [compContinuousLinearMap_curryLeft]
  rw [chartJinv_basis (I := I) (M := M)]

/-- Bridge B: `chartTensorInnerOnChartBasis` (using chart-α basis)
equals `chartTensorInnerPointwise_0s` precomposed with `chartJinv α b`. -/
private theorem chartTensorInnerOnChartBasis_eq_chartTensorInnerPointwise_compose
    (g : SmoothRiemannianMetric I M) (α : M) (b : M) :
    ∀ (s : ℕ) (T S : Tensor0SModel s ℝ E),
      chartTensorInnerOnChartBasis (I := I) (M := M) s g α b T S =
        chartTensorInnerPointwise_0s (I := I) (M := M) s g α b
          (T.compContinuousLinearMap (fun _ : Fin s =>
            chartJinv (I := I) (M := M) α b))
          (S.compContinuousLinearMap (fun _ : Fin s =>
            chartJinv (I := I) (M := M) α b)) := by
  intro s
  induction s with
  | zero =>
      intro T S
      rw [chartTensorInnerOnChartBasis_zero, chartTensorInnerPointwise_0s_zero]

      simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
      congr 1 <;>
        · congr 1
          funext i
          exact i.elim0
  | succ s ih =>
      intro T S
      rw [chartTensorInnerOnChartBasis_succ, chartTensorInnerPointwise_0s_succ]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [chartJinv_compose_curry_chartBasis (I := I) (M := M) α b T i,
          chartJinv_compose_curry_chartBasis (I := I) (M := M) α b S j]
      rw [ih (T.curryLeft (chartBasisVecFiber (I := I) α i b))
          (S.curryLeft (chartBasisVecFiber (I := I) α j b))]

/-! ### Bridge A: `tensorInnerPointwise_0s s g b T S = chartTensorInnerOnChartBasis s g α b T S`

This is the basis-invariance fact. The proof uses the matrix identity
`(chartGramMatrix)⁻¹ = (chartJinvMatrix) (gramMatrixAt)⁻¹ (chartJinvMatrix)ᵀ` (applied to `b` on chart base set), where `chartJinvMatrix` is the matrix of `chartJinv α b` in
the model basis.

We approach this in stages, building up the matrix identities. -/

/-- The matrix of `chartJinv α b` in the model basis: `(JinvMat α b)_{ai}`
is the `a`-th coordinate of `chartJinv α b ((chartModelBasis E) i)` in the basis. -/
private noncomputable def chartJinvMatrix (α : M) (b : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun a i =>
    ((chartModelBasis E).repr
      (chartJinv (I := I) (M := M) α b ((chartModelBasis E) i))) a

@[simp] private lemma chartJinvMatrix_apply (α : M) (b : M)
    (a i : Fin (Module.finrank ℝ E)) :
    chartJinvMatrix (I := I) (M := M) α b a i =
      ((chartModelBasis E).repr
        (chartJinv (I := I) (M := M) α b ((chartModelBasis E) i))) a := rfl

/-- The chart-α basis vector `chartBasisVecFiber α i b` decomposes via `chartJinvMatrix`
in the model basis. -/
private lemma chartBasisVecFiber_eq_sum (α : M) (b : M)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := I) α i b =
      ∑ a : Fin (Module.finrank ℝ E),
        chartJinvMatrix (I := I) (M := M) α b a i • (chartModelBasis E) a := by
  rw [← chartJinv_basis (I := I) (M := M) α b i]
  exact ((chartModelBasis E).sum_repr
    (chartJinv (I := I) (M := M) α b ((chartModelBasis E) i))).symm

/-- The matrix of `chartJ α b` in the model basis. -/
private noncomputable def chartJMatrix (α : M) (b : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun a i =>
    ((chartModelBasis E).repr
      (chartJ (I := I) (M := M) α b ((chartModelBasis E) i))) a

@[simp] private lemma chartJMatrix_apply (α : M) (b : M)
    (a i : Fin (Module.finrank ℝ E)) :
    chartJMatrix (I := I) (M := M) α b a i =
      ((chartModelBasis E).repr
        (chartJ (I := I) (M := M) α b ((chartModelBasis E) i))) a := rfl

/-- For any `v : E`, `(chartJ α b v)_a = ∑_k (chartJMatrix)_{a,k} (v decomposed in basis)_k`. -/
private lemma chartJ_apply_repr (α : M) (b : M) (v : E)
    (a : Fin (Module.finrank ℝ E)) :
    ((chartModelBasis E).repr (chartJ (I := I) (M := M) α b v)) a =
      ∑ k : Fin (Module.finrank ℝ E),
        chartJMatrix (I := I) (M := M) α b a k *
          ((chartModelBasis E).repr v) k := by

  have hv : v = ∑ k : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr v) k • (chartModelBasis E) k :=
    ((chartModelBasis E).sum_repr v).symm
  conv_lhs => rw [hv]
  rw [map_sum, map_sum]
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [map_smul, map_smul]
  rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, chartJMatrix_apply]
  ring

/-- Similarly, `(chartJinv α b v)_a = ∑_k (chartJinvMatrix)_{a,k} (v decomposed)_k`. -/
private lemma chartJinv_apply_repr (α : M) (b : M) (v : E)
    (a : Fin (Module.finrank ℝ E)) :
    ((chartModelBasis E).repr (chartJinv (I := I) (M := M) α b v)) a =
      ∑ k : Fin (Module.finrank ℝ E),
        chartJinvMatrix (I := I) (M := M) α b a k *
          ((chartModelBasis E).repr v) k := by
  have hv : v = ∑ k : Fin (Module.finrank ℝ E),
      ((chartModelBasis E).repr v) k • (chartModelBasis E) k :=
    ((chartModelBasis E).sum_repr v).symm
  conv_lhs => rw [hv]
  rw [map_sum, map_sum]
  rw [Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [map_smul, map_smul]
  rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, chartJinvMatrix_apply]
  ring

/-- The Gram matrix relationship at the matrix level:
`chartGramMatrix g α b = (chartJinvMatrix α b)ᵀ * gramMatrixAt g b * chartJinvMatrix α b`. -/
private lemma chartGramMatrix_eq_matrix_form
    (g : SmoothRiemannianMetric I M) (α b : M) :
    chartGramMatrix g α b =
      (chartJinvMatrix (I := I) (M := M) α b)ᵀ *
        gramMatrixAt (I := I) (M := M) g b *
        chartJinvMatrix (I := I) (M := M) α b := by
  ext i j

  rw [chartGramMatrix_eq_innerJinv]

  have hi : chartJinv (I := I) (M := M) α b ((chartModelBasis E) i) =
      ∑ a, chartJinvMatrix (I := I) (M := M) α b a i • (chartModelBasis E) a := by
    rw [chartJinv_basis (I := I) (M := M) α b i]
    exact chartBasisVecFiber_eq_sum (I := I) (M := M) α b i
  have hj : chartJinv (I := I) (M := M) α b ((chartModelBasis E) j) =
      ∑ b', chartJinvMatrix (I := I) (M := M) α b b' j • (chartModelBasis E) b' := by
    rw [chartJinv_basis (I := I) (M := M) α b j]
    exact chartBasisVecFiber_eq_sum (I := I) (M := M) α b j
  rw [hi, hj]

  have hLHS_eq :
      (g.inner b (∑ a : Fin (Module.finrank ℝ E),
          chartJinvMatrix (I := I) (M := M) α b a i • (chartModelBasis E) a))
        (∑ b' : Fin (Module.finrank ℝ E),
          chartJinvMatrix (I := I) (M := M) α b b' j • (chartModelBasis E) b') =
      ∑ a : Fin (Module.finrank ℝ E),
        ∑ b' : Fin (Module.finrank ℝ E),
          chartJinvMatrix (I := I) (M := M) α b a i *
            chartJinvMatrix (I := I) (M := M) α b b' j *
            g.inner b ((chartModelBasis E) a) ((chartModelBasis E) b') := by

    have hL : g.inner b (∑ a : Fin (Module.finrank ℝ E),
          chartJinvMatrix (I := I) (M := M) α b a i • (chartModelBasis E) a) =
        ∑ a : Fin (Module.finrank ℝ E),
          chartJinvMatrix (I := I) (M := M) α b a i •
            g.inner b ((chartModelBasis E) a) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro a _
      exact ContinuousLinearMap.map_smul (g.inner b) _ _
    rw [hL, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]

    rw [show (g.inner b ((chartModelBasis E) a))
        (∑ b' : Fin (Module.finrank ℝ E),
          chartJinvMatrix (I := I) (M := M) α b b' j • (chartModelBasis E) b') =
        ∑ b' : Fin (Module.finrank ℝ E),
          chartJinvMatrix (I := I) (M := M) α b b' j *
            g.inner b ((chartModelBasis E) a) ((chartModelBasis E) b') from ?_]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro b' _
      ring
    · rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro b' _
      rw [show ((g.inner b) ((chartModelBasis E) a))
          (chartJinvMatrix (I := I) (M := M) α b b' j • (chartModelBasis E) b') =
          chartJinvMatrix (I := I) (M := M) α b b' j •
            ((g.inner b) ((chartModelBasis E) a)) ((chartModelBasis E) b') from ?_]
      · rw [smul_eq_mul]
      · exact ContinuousLinearMap.map_smul ((g.inner b) ((chartModelBasis E) a)) _ _
  refine hLHS_eq.trans ?_

  rw [Matrix.mul_apply]
  rw [show ∑ b' : Fin (Module.finrank ℝ E),
      ((chartJinvMatrix (I := I) (M := M) α b)ᵀ *
          gramMatrixAt (I := I) (M := M) g b) i b' *
        chartJinvMatrix (I := I) (M := M) α b b' j =
        ∑ b' : Fin (Module.finrank ℝ E),
          (∑ a : Fin (Module.finrank ℝ E),
            chartJinvMatrix (I := I) (M := M) α b a i *
              gramMatrixAt (I := I) (M := M) g b a b') *
            chartJinvMatrix (I := I) (M := M) α b b' j from ?_]
  · -- ∑ b' (∑ a J_{a,i} G_{a,b'}) * J_{b',j} = ∑ a ∑ b' J_{a,i} G_{a,b'} J_{b',j}.
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b' _
    rw [gramMatrixAt_apply]
    ring
  · refine Finset.sum_congr rfl ?_
    intro b' _
    rw [Matrix.mul_apply]

    refine congr_arg (· * chartJinvMatrix (I := I) (M := M) α b b' j) ?_
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [Matrix.transpose_apply]

/-- `chartJinvMatrix α b` is invertible on the chart base set, with inverse `chartJMatrix α b`. -/
private lemma chartJinvMatrix_mul_chartJMatrix (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartJinvMatrix (I := I) (M := M) α b *
        chartJMatrix (I := I) (M := M) α b = 1 := by
  ext a c
  rw [Matrix.mul_apply]

  have hsum_eq : ∑ k, chartJinvMatrix (I := I) (M := M) α b a k *
      chartJMatrix (I := I) (M := M) α b k c =
    ((chartModelBasis E).repr (chartJinv (I := I) (M := M) α b
      (chartJ (I := I) (M := M) α b ((chartModelBasis E) c)))) a := by
    rw [chartJinv_apply_repr (I := I) (M := M) α b
      (chartJ (I := I) (M := M) α b ((chartModelBasis E) c)) a]
    rfl
  rw [hsum_eq]
  rw [chartJinv_chartJ (I := I) (M := M) α hb]
  rw [Module.Basis.repr_self]
  rw [Finsupp.single_apply]
  rw [Matrix.one_apply]
  by_cases hac : c = a
  · rw [if_pos hac]
    rw [if_pos hac.symm]
  · rw [if_neg hac]
    have : ¬ a = c := fun h => hac h.symm
    rw [if_neg this]

/-- The other direction: `chartJMatrix α b * chartJinvMatrix α b = 1`. -/
private lemma chartJMatrix_mul_chartJinvMatrix (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartJMatrix (I := I) (M := M) α b *
        chartJinvMatrix (I := I) (M := M) α b = 1 := by
  ext a c
  rw [Matrix.mul_apply]

  have hsum_eq : ∑ k, chartJMatrix (I := I) (M := M) α b a k *
      chartJinvMatrix (I := I) (M := M) α b k c =
    ((chartModelBasis E).repr (chartJ (I := I) (M := M) α b
      (chartJinv (I := I) (M := M) α b ((chartModelBasis E) c)))) a := by
    rw [chartJ_apply_repr (I := I) (M := M) α b
      (chartJinv (I := I) (M := M) α b ((chartModelBasis E) c)) a]
    rfl
  rw [hsum_eq]
  rw [chartJ_chartJinv (I := I) (M := M) α hb]
  rw [Module.Basis.repr_self]
  rw [Finsupp.single_apply]
  rw [Matrix.one_apply]
  by_cases hac : c = a
  · rw [if_pos hac]
    rw [if_pos hac.symm]
  · rw [if_neg hac]
    have : ¬ a = c := fun h => hac h.symm
    rw [if_neg this]

/-- `chartJinvMatrix α b` is invertible on the chart base set, with inverse `chartJMatrix α b`. -/
private lemma chartJinvMatrix_inv (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (chartJinvMatrix (I := I) (M := M) α b)⁻¹ =
      chartJMatrix (I := I) (M := M) α b := by
  apply Matrix.inv_eq_left_inv
  exact chartJMatrix_mul_chartJinvMatrix (I := I) (M := M) α hb

/-- The Gram matrix `chartGramMatrix` is invertible on the chart base set: its determinant
is positive (hence nonzero). -/
private lemma chartGramMatrix_isUnit_det
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    IsUnit (chartGramMatrix g α b).det :=
  (chartGramMatrix_det_pos (I := I) g α hb).ne'.isUnit

private lemma chartGramMatrix_isUnit
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    IsUnit (chartGramMatrix g α b) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (chartGramMatrix_isUnit_det (I := I) (M := M) g α hb)

private lemma chartGramMatrix_inv_mul_self_at
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (chartGramMatrix g α b)⁻¹ *
        chartGramMatrix g α b = 1 :=
  Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (chartGramMatrix_isUnit (I := I) (M := M) g α hb))

private lemma chartGramMatrix_self_mul_inv_at
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartGramMatrix g α b *
        (chartGramMatrix g α b)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (chartGramMatrix_isUnit (I := I) (M := M) g α hb))

/-- The key matrix identity expressed in entry form.
`∑ ij (chartGramMatrix)⁻¹_{ij} (chartJinvMatrix)_{ai} (chartJinvMatrix)_{b'j} = (gramMatrixAt)⁻¹_{ab'}`.

This follows from `chartGramMatrix = chartJinvMatrixᵀ * gramMatrixAt * chartJinvMatrix`,
inverted to `chartGramMatrix⁻¹ = chartJinvMatrix⁻¹ * gramMatrixAt⁻¹ * (chartJinvMatrixᵀ)⁻¹`,
multiplied by `chartJinvMatrix * (·) * chartJinvMatrixᵀ` and using
`chartJinvMatrix * chartJinvMatrix⁻¹ = 1`. -/
private lemma chartJinv_chartGramInv_chartJinvT_eq_gramInv_entry
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (a c : Fin (Module.finrank ℝ E)) :
    ∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        (chartGramMatrix g α b)⁻¹ i j *
          (chartJinvMatrix (I := I) (M := M) α b a i *
            chartJinvMatrix (I := I) (M := M) α b c j) =
      (gramMatrixAt (I := I) (M := M) g b)⁻¹ a c := by

  have hLHS_form :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          (chartGramMatrix g α b)⁻¹ i j *
            (chartJinvMatrix (I := I) (M := M) α b a i *
              chartJinvMatrix (I := I) (M := M) α b c j)) =
      (chartJinvMatrix (I := I) (M := M) α b *
        (chartGramMatrix g α b)⁻¹ *
        (chartJinvMatrix (I := I) (M := M) α b)ᵀ) a c := by

    rw [Matrix.mul_apply]

    rw [show ∑ j : Fin (Module.finrank ℝ E),
        (chartJinvMatrix (I := I) (M := M) α b *
          (chartGramMatrix g α b)⁻¹) a j *
          (chartJinvMatrix (I := I) (M := M) α b)ᵀ j c =
        ∑ j : Fin (Module.finrank ℝ E),
          (∑ i : Fin (Module.finrank ℝ E),
            chartJinvMatrix (I := I) (M := M) α b a i *
            (chartGramMatrix g α b)⁻¹ i j) *
          chartJinvMatrix (I := I) (M := M) α b c j from ?_]
    · -- Now: LHS double sum = ∑ j (∑ i J_{a,i} G⁻¹_{i,j}) * J_{c,j}.
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    · refine Finset.sum_congr rfl ?_
      intro j _
      rw [Matrix.mul_apply, Matrix.transpose_apply]
  rw [hLHS_form]

  have hJinvMat_inv := chartJinvMatrix_inv (I := I) (M := M) α hb

  have hrhs : (chartJinvMatrix (I := I) (M := M) α b *
      (chartGramMatrix g α b)⁻¹ *
      (chartJinvMatrix (I := I) (M := M) α b)ᵀ) *
      gramMatrixAt (I := I) (M := M) g b = 1 := by

    have hGramEq := chartGramMatrix_eq_matrix_form (I := I) (M := M) g α b

    have hJinvMatT_mul_G :
        (chartJinvMatrix (I := I) (M := M) α b)ᵀ *
            gramMatrixAt (I := I) (M := M) g b =
          chartGramMatrix g α b *
            (chartJinvMatrix (I := I) (M := M) α b)⁻¹ := by

      rw [hGramEq, hJinvMat_inv]
      rw [Matrix.mul_assoc, Matrix.mul_assoc]
      rw [chartJinvMatrix_mul_chartJMatrix (I := I) (M := M) α hb]
      rw [Matrix.mul_one]

    rw [Matrix.mul_assoc, Matrix.mul_assoc,
      hJinvMatT_mul_G,
      ← Matrix.mul_assoc (chartGramMatrix g α b)⁻¹,
      chartGramMatrix_inv_mul_self_at (I := I) (M := M) g α hb,
      Matrix.one_mul,
      hJinvMat_inv,
      chartJinvMatrix_mul_chartJMatrix (I := I) (M := M) α hb]

  have hMain : chartJinvMatrix (I := I) (M := M) α b *
      (chartGramMatrix g α b)⁻¹ *
      (chartJinvMatrix (I := I) (M := M) α b)ᵀ =
      (gramMatrixAt (I := I) (M := M) g b)⁻¹ := by

    exact (Matrix.inv_eq_left_inv hrhs).symm
  rw [hMain]

/-! ### Bridge A: `tensorInnerPointwise_0s s g b T S = chartTensorInnerOnChartBasis s g α b T S`

This is the basis-invariance fact. We prove it by induction on `s`. -/

private theorem tensorInnerPointwise_0s_eq_chartTensorInnerOnChartBasis
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ) {b : M},
      b ∈ (trivializationAt E (TangentSpace I) α).baseSet →
      ∀ (T S : Tensor0SModel s ℝ E),
      tensorInnerPointwise_0s (I := I) (M := M) s g b T S =
        chartTensorInnerOnChartBasis (I := I) (M := M) s g α b T S := by
  intro s
  induction s with
  | zero =>
      intro b _ T S
      rw [tensorInnerPointwise_0s_zero_arity, chartTensorInnerOnChartBasis_zero]
  | succ s ih =>
      intro b hb T S
      rw [tensorInnerPointwise_0s_succ, chartTensorInnerOnChartBasis_succ]

      have step1 :
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (chartGramMatrix g α b)⁻¹ i j *
                chartTensorInnerOnChartBasis (I := I) (M := M) s g α b
                  (T.curryLeft (chartBasisVecFiber (I := I) α i b))
                  (S.curryLeft (chartBasisVecFiber (I := I) α j b)) =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (chartGramMatrix g α b)⁻¹ i j *
                tensorInnerPointwise_0s (I := I) (M := M) s g b
                  (T.curryLeft (chartBasisVecFiber (I := I) α i b))
                  (S.curryLeft (chartBasisVecFiber (I := I) α j b)) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [← ih hb _ _]
      rw [step1]

      have step2_T : ∀ i : Fin (Module.finrank ℝ E),
          T.curryLeft (chartBasisVecFiber (I := I) α i b) =
            ∑ a : Fin (Module.finrank ℝ E),
              chartJinvMatrix (I := I) (M := M) α b a i •
                T.curryLeft ((chartModelBasis E) a) := by
        intro i
        rw [chartBasisVecFiber_eq_sum (I := I) (M := M) α b i]
        exact curryLeft_sum (E := E) (s := s) T _ _
      have step2_S : ∀ j : Fin (Module.finrank ℝ E),
          S.curryLeft (chartBasisVecFiber (I := I) α j b) =
            ∑ b' : Fin (Module.finrank ℝ E),
              chartJinvMatrix (I := I) (M := M) α b b' j •
                S.curryLeft ((chartModelBasis E) b') := by
        intro j
        rw [chartBasisVecFiber_eq_sum (I := I) (M := M) α b j]
        exact curryLeft_sum (E := E) (s := s) S _ _

      have step3 : ∀ i j : Fin (Module.finrank ℝ E),
          tensorInnerPointwise_0s (I := I) (M := M) s g b
              (T.curryLeft (chartBasisVecFiber (I := I) α i b))
              (S.curryLeft (chartBasisVecFiber (I := I) α j b)) =
            ∑ a : Fin (Module.finrank ℝ E),
              ∑ b' : Fin (Module.finrank ℝ E),
                chartJinvMatrix (I := I) (M := M) α b a i *
                  chartJinvMatrix (I := I) (M := M) α b b' j *
                tensorInnerPointwise_0s (I := I) (M := M) s g b
                  (T.curryLeft ((chartModelBasis E) a))
                  (S.curryLeft ((chartModelBasis E) b')) := by
        intro i j
        rw [step2_T i, step2_S j]
        rw [tensorInnerPointwise_0s_sum_left]
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [tensorInnerPointwise_0s_sum_right]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro b' _
        ring

      have step4 :
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (chartGramMatrix g α b)⁻¹ i j *
                tensorInnerPointwise_0s (I := I) (M := M) s g b
                  (T.curryLeft (chartBasisVecFiber (I := I) α i b))
                  (S.curryLeft (chartBasisVecFiber (I := I) α j b)) =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ a : Fin (Module.finrank ℝ E),
                ∑ b' : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j) *
                    tensorInnerPointwise_0s (I := I) (M := M) s g b
                      (T.curryLeft ((chartModelBasis E) a))
                      (S.curryLeft ((chartModelBasis E) b')) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [step3 i j]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro b' _
        ring
      rw [step4]

      have step5_0 :
          ∀ (i : Fin (Module.finrank ℝ E)),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ a : Fin (Module.finrank ℝ E),
                ∑ b' : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j) *
                    tensorInnerPointwise_0s (I := I) (M := M) s g b
                      (T.curryLeft ((chartModelBasis E) a))
                      (S.curryLeft ((chartModelBasis E) b')) =
            ∑ a : Fin (Module.finrank ℝ E),
              ∑ b' : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j) *
                    tensorInnerPointwise_0s (I := I) (M := M) s g b
                      (T.curryLeft ((chartModelBasis E) a))
                      (S.curryLeft ((chartModelBasis E) b')) := by
        intro i

        rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ E))]
        refine Finset.sum_congr rfl ?_
        intro a _

        rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ E))]
      have step5_1 :
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ a : Fin (Module.finrank ℝ E),
                ∑ b' : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j) *
                    tensorInnerPointwise_0s (I := I) (M := M) s g b
                      (T.curryLeft ((chartModelBasis E) a))
                      (S.curryLeft ((chartModelBasis E) b')) =
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ a : Fin (Module.finrank ℝ E),
              ∑ b' : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j) *
                    tensorInnerPointwise_0s (I := I) (M := M) s g b
                      (T.curryLeft ((chartModelBasis E) a))
                      (S.curryLeft ((chartModelBasis E) b')) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        exact step5_0 i
      have step5 :
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              ∑ a : Fin (Module.finrank ℝ E),
                ∑ b' : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j) *
                    tensorInnerPointwise_0s (I := I) (M := M) s g b
                      (T.curryLeft ((chartModelBasis E) a))
                      (S.curryLeft ((chartModelBasis E) b')) =
          ∑ a : Fin (Module.finrank ℝ E),
            ∑ b' : Fin (Module.finrank ℝ E),
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j) *
                    tensorInnerPointwise_0s (I := I) (M := M) s g b
                      (T.curryLeft ((chartModelBasis E) a))
                      (S.curryLeft ((chartModelBasis E) b')) := by
        rw [step5_1]

        rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ E))]
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [Finset.sum_comm (γ := Fin (Module.finrank ℝ E))]
      rw [step5]

      have step6 :
          ∑ a : Fin (Module.finrank ℝ E),
            ∑ b' : Fin (Module.finrank ℝ E),
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j) *
                    tensorInnerPointwise_0s (I := I) (M := M) s g b
                      (T.curryLeft ((chartModelBasis E) a))
                      (S.curryLeft ((chartModelBasis E) b')) =
          ∑ a : Fin (Module.finrank ℝ E),
            ∑ b' : Fin (Module.finrank ℝ E),
              (∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j)) *
                tensorInnerPointwise_0s (I := I) (M := M) s g b
                  (T.curryLeft ((chartModelBasis E) a))
                  (S.curryLeft ((chartModelBasis E) b')) := by
        refine Finset.sum_congr rfl ?_
        intro a _
        refine Finset.sum_congr rfl ?_
        intro b' _

        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.sum_mul]
      rw [step6]

      have step7 : ∀ (a c : Fin (Module.finrank ℝ E)),
          ∑ i : Fin (Module.finrank ℝ E),
            ∑ j : Fin (Module.finrank ℝ E),
              (chartGramMatrix g α b)⁻¹ i j *
                (chartJinvMatrix (I := I) (M := M) α b a i *
                  chartJinvMatrix (I := I) (M := M) α b c j) =
            (gramMatrixAt (I := I) (M := M) g b)⁻¹ a c := fun a c =>
        chartJinv_chartGramInv_chartJinvT_eq_gramInv_entry
          (I := I) (M := M) g α hb a c
      have step8 :
          ∑ a : Fin (Module.finrank ℝ E),
            ∑ b' : Fin (Module.finrank ℝ E),
              (∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    (chartJinvMatrix (I := I) (M := M) α b a i *
                      chartJinvMatrix (I := I) (M := M) α b b' j)) *
                tensorInnerPointwise_0s (I := I) (M := M) s g b
                  (T.curryLeft ((chartModelBasis E) a))
                  (S.curryLeft ((chartModelBasis E) b')) =
          ∑ a : Fin (Module.finrank ℝ E),
            ∑ b' : Fin (Module.finrank ℝ E),
              (gramMatrixAt (I := I) (M := M) g b)⁻¹ a b' *
                tensorInnerPointwise_0s (I := I) (M := M) s g b
                  (T.curryLeft ((chartModelBasis E) a))
                  (S.curryLeft ((chartModelBasis E) b')) := by
        refine Finset.sum_congr rfl ?_
        intro a _
        refine Finset.sum_congr rfl ?_
        intro b' _
        rw [step7 a b']

      symm
      exact step8

/-! ### Combining bridges: the main bridge identity -/

/-- **The bridge identity**, formal version.

For any tensors `T, S : MLF s`, on `b ∈ (chartAt H α).source` (= the trivialisation base set):
$$\text{tensorInnerPointwise\_0s s g b T S = chartTensorInnerPointwise\_0s g α s b T_α S_α}$$
where $T_α = T \circ_\text{ML} \text{chartJinv α b}$ and similarly for $S_α$. -/
theorem tensorInnerPointwise_0s_bridge_identity
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ) {b : M},
      b ∈ (trivializationAt E (TangentSpace I) α).baseSet →
      ∀ (T S : Tensor0SModel s ℝ E),
      tensorInnerPointwise_0s (I := I) (M := M) s g b T S =
        chartTensorInnerPointwise_0s (I := I) (M := M) s g α b
          (T.compContinuousLinearMap (fun _ : Fin s =>
            chartJinv (I := I) (M := M) α b))
          (S.compContinuousLinearMap (fun _ : Fin s =>
            chartJinv (I := I) (M := M) α b)) := by
  intro s b hb T S
  rw [tensorInnerPointwise_0s_eq_chartTensorInnerOnChartBasis
      (I := I) (M := M) g α s hb T S]
  rw [chartTensorInnerOnChartBasis_eq_chartTensorInnerPointwise_compose
      (I := I) (M := M) g α b s T S]

end Tensor0SRiemannian
end Tensor
end DifferentialGeometry

end
