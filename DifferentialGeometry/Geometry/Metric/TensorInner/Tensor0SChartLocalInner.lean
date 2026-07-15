import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentRiemannian
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Geometry.Metric.ChartGram
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
# Chart-local pointwise (0,s) inner product

The pointwise inner product `tensorInnerPointwise_0s s g b` is defined through
the canonical-basis Gram matrix `gramMatrixAt g b`, whose smoothness in `b` is
not directly accessible. To prepare for the smoothness arguments, this file
introduces `chartTensorInnerPointwise_0s`, a chart-local replacement built from
the chart-local Gram matrix `chartGramMatrix g α b`, whose entries (and whose
inverse-matrix entries, `chartGramMatrix_inv_entry_contMDiffOn`) are smooth on
the trivialisation base set.

The chart-local inner product is shown to be smooth in `b` for fixed tensor
arguments (`chartTensorInnerPointwise_0s_contMDiffOn`) and bilinear in its two
tensor arguments. These facts feed the CLM packaging and the bridge identity
developed in the sibling files.
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

/-! ## Bundle smoothness of the inner-product section

We assemble `innerBundleCLM g s` into a smooth section of the Hom bundle
`Hom(Tensor0S(s), Hom(Tensor0S(s), ℝ))` on `M`. The argument proceeds by
chart-localising and using the fact that the inner product, viewed in
trivialised coordinates, is a polynomial expression in the entries of the
chart-local Gram matrix and its inverse — both of which are smooth. The
chart-local representation of the inner-product section is constructed
by induction on `s` and then transferred to the bundle level.

The chart-local approach: in the trivialisation at `α : M`, the bilinear form
`innerBundleCLM g s b` (acting on bundle-fibre tensors) corresponds to a
bilinear form on the model fibre `Tensor0SModel s ℝ E`. The dependence on
`b ∈ chartAt(α).source` is smooth because the chart-local Gram matrix
`chartGramMatrix g α b` and its determinant inverse are smooth.
-/

open DifferentialGeometry.Integral.Measure (chartGramMatrix
  chartGramMatrix_apply chartGramMatrix_isHermitian
  chartGramMatrix_posDef chartGramMatrix_det_pos
  chartGramMatrix_entry_contMDiffOn chartGramMatrix_det_contMDiffOn
  chartBasisVecFiber chartBasisVec)

variable {n : ℕ}

/-! ### Smoothness of the inverse Gram matrix entries

The chart-local Gram matrix `chartGramMatrix g α b` is symmetric
positive-definite with strictly positive determinant on `chartAt(α).source`,
hence invertible. Its inverse is given by `(det)⁻¹ • adjugate`, both factors
being smooth in `b`. We expose entrywise smoothness, which is what the
inductive step of the bilinear-form smoothness proof needs. -/

/-- The adjugate matrix entries are smooth on the trivialisation base set.
We expand via `adjugate_apply` (giving a determinant of a row-update matrix)
and then via the permutation-sum formula for `det`, after which each
summand is a finite product of either constants (the `Pi.single` entry) or
smooth Gram-matrix entries. -/
private lemma chartGramMatrix_adjugate_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (chartGramMatrix g α b).adjugate i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical

  have hexp :
      (fun b : M => (chartGramMatrix g α b).adjugate i j)
        = (fun b : M =>
            ((chartGramMatrix g α b).updateRow j (Pi.single i 1)).det) := by
    funext b
    rw [Matrix.adjugate_apply]
  rw [hexp]

  have hexp2 :
      (fun b : M =>
          ((chartGramMatrix g α b).updateRow j (Pi.single i 1)).det)
        = (fun b : M =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ k,
                  ((chartGramMatrix g α b).updateRow j (Pi.single i 1))
                    (σ k) k) := by
    funext b
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp2]
  refine contMDiffOn_finset_sum (fun σ _ => ?_)
  refine ContMDiffOn.mul (contMDiffOn_const) ?_
  refine contMDiffOn_finset_prod (fun k _ => ?_)

  by_cases hσkj : σ k = j
  · -- Row replaced: entry is `(Pi.single i 1) k`, a constant in `b`.
    have heq :
        (fun b : M =>
            ((chartGramMatrix g α b).updateRow j (Pi.single i 1)) (σ k) k)
          = (fun _ : M => (Pi.single i 1 : Fin (Module.finrank ℝ E) → ℝ) k) := by
      funext b
      rw [hσkj, Matrix.updateRow_self]
    rw [heq]
    exact contMDiffOn_const
  · -- Row not replaced: entry is `A (σ k) k`, smooth in `b`.
    have heq :
        (fun b : M =>
            ((chartGramMatrix g α b).updateRow j (Pi.single i 1)) (σ k) k)
          = (fun b : M => chartGramMatrix g α b (σ k) k) := by
      funext b
      rw [Matrix.updateRow_ne hσkj]
    rw [heq]
    exact chartGramMatrix_entry_contMDiffOn (I := I) g α (σ k) k

/-- The inverse Gram matrix entries are smooth on the trivialisation base
set. The inverse formula is `A⁻¹ = (det A)⁻¹ • adjugate A`, valid because the
determinant is strictly positive (hence nonzero) on the chart base set. -/
lemma chartGramMatrix_inv_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => (chartGramMatrix g α b)⁻¹ i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by

  have hexp :
      (fun b : M => (chartGramMatrix g α b)⁻¹ i j)
        = (fun b : M => (chartGramMatrix g α b).det⁻¹ *
              (chartGramMatrix g α b).adjugate i j) := by
    funext b
    rw [Matrix.inv_def]
    simp [Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [hexp]

  intro b hb
  have hdet := chartGramMatrix_det_contMDiffOn (I := I) g α b hb
  have hadj := chartGramMatrix_adjugate_entry_contMDiffOn (I := I) g α i j b hb
  have hpos : 0 < (chartGramMatrix g α b).det :=
    chartGramMatrix_det_pos (I := I) g α hb
  have hpos_ne : (chartGramMatrix g α b).det ≠ 0 := ne_of_gt hpos
  have hinv : ContMDiffWithinAt I 𝓘(ℝ) ∞
      (fun b' : M => (chartGramMatrix g α b').det⁻¹)
      (trivializationAt E (TangentSpace I) α).baseSet b :=
    ContMDiffWithinAt.inv₀ hdet hpos_ne
  exact hinv.mul hadj

/-! ### From `chartGramMatrix` to a chart-local replacement for the inner
product

The pointwise inner product `tensorInnerPointwise_0s s g b S T` is defined
via the canonical-basis Gram matrix `gramMatrixAt g b`, whose smoothness in
`b` is not immediately accessible through Mathlib's standard tools (the
canonical model-fibre basis vectors do not yield smooth tangent-bundle
sections in general). To bypass this we replace `gramMatrixAt g b` by the
chart-local Gram matrix `chartGramMatrix g α b`, whose entries are smooth on
`chartAt(α).source`. The two are related by the change-of-basis matrix
coming from the trivialisation, and we will see below that the resulting
chart-local inner product, after suitable change-of-coordinates, equals the
bundle-trivialised form of `innerBundleCLM g s b`. -/

/-- A chart-local replacement for `tensorInnerPointwise_0s`, defined using
`chartGramMatrix g α b` in place of `gramMatrixAt g b`. -/
noncomputable def chartTensorInnerPointwise_0s :
    (s : ℕ) → SmoothRiemannianMetric I M → (α : M) → (b : M) →
      Tensor0SModel s ℝ E →
      Tensor0SModel s ℝ E → ℝ
  | 0, _g, _α, _b, S, T =>
      S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i)
  | s + 1, g, α, b, S, T =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (chartGramMatrix g α b)⁻¹ i j *
          chartTensorInnerPointwise_0s s g α b
            (S.curryLeft ((chartModelBasis E) i))
            (T.curryLeft ((chartModelBasis E) j))

lemma chartTensorInnerPointwise_0s_zero
    (g : SmoothRiemannianMetric I M) (α b : M)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) ℝ) :
    chartTensorInnerPointwise_0s (I := I) (M := M) 0 g α b S T =
      S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i) := rfl

lemma chartTensorInnerPointwise_0s_succ
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    chartTensorInnerPointwise_0s (I := I) (M := M) (s + 1) g α b S T =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (chartGramMatrix g α b)⁻¹ i j *
          chartTensorInnerPointwise_0s (I := I) (M := M) s g α b
            (S.curryLeft ((chartModelBasis E) i))
            (T.curryLeft ((chartModelBasis E) j)) := rfl

/-! ### Smoothness of the chart-local inner product

The chart-local inner product is smooth in `b` on the chart base set. The
proof is by induction on `s`. The base case is constant; the inductive step
uses smoothness of the inverse Gram matrix and the inductive hypothesis. -/

lemma chartTensorInnerPointwise_0s_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∀ (s : ℕ) (S T : Tensor0SModel s ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M =>
          chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T)
        (trivializationAt E (TangentSpace I) α).baseSet := by
  intro s
  induction s with
  | zero =>
      intro S T

      have heq :
          (fun b : M =>
              chartTensorInnerPointwise_0s (I := I) (M := M) 0 g α b S T)
            = fun _ : M =>
              S (fun i => Fin.elim0 i) * T (fun i => Fin.elim0 i) := by
        funext b
        rw [chartTensorInnerPointwise_0s_zero]
      rw [heq]
      exact contMDiffOn_const
  | succ s ih =>
      intro S T
      have heq :
          (fun b : M =>
              chartTensorInnerPointwise_0s (I := I) (M := M) (s + 1) g α b S T)
            = fun b : M =>
              ∑ i : Fin (Module.finrank ℝ E),
                ∑ j : Fin (Module.finrank ℝ E),
                  (chartGramMatrix g α b)⁻¹ i j *
                    chartTensorInnerPointwise_0s (I := I) (M := M) s g α b
                      (S.curryLeft ((chartModelBasis E) i))
                      (T.curryLeft ((chartModelBasis E) j)) := by
        funext b
        rw [chartTensorInnerPointwise_0s_succ]
      rw [heq]
      refine contMDiffOn_finset_sum (fun i _ => ?_)
      refine contMDiffOn_finset_sum (fun j _ => ?_)
      refine ContMDiffOn.mul ?_ ?_
      · exact chartGramMatrix_inv_entry_contMDiffOn (I := I) g α i j
      · exact ih
          (S.curryLeft ((chartModelBasis E) i))
          (T.curryLeft ((chartModelBasis E) j))

/-! ### Bilinearity of `chartTensorInnerPointwise_0s`

The chart-local inner product is bilinear in the two tensor arguments. We
prove the four bilinearity properties by induction on `s` (mirroring the
proofs of `tensorInnerPointwise_0s_*` in the project's `PointwiseInner`
files). -/

lemma chartTensorInnerPointwise_0s_add_left
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (S₁ S₂ T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0s (I := I) (M := M) s g α b (S₁ + S₂) T =
      chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S₁ T +
        chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S₂ T := by
  induction s with
  | zero =>
      change (S₁ + S₂) _ * T _ = S₁ _ * T _ + S₂ _ * T _
      rw [ContinuousMultilinearMap.add_apply]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (S₁ + S₂).curryLeft ((chartModelBasis E) i) =
            S₁.curryLeft ((chartModelBasis E) i) +
              S₂.curryLeft ((chartModelBasis E) i) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousMultilinearMap.add_apply]
      rw [hcurry, ih]
      ring

lemma chartTensorInnerPointwise_0s_smul_left
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (c : ℝ) (S T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0s (I := I) (M := M) s g α b (c • S) T =
      c * chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T := by
  induction s with
  | zero =>
      change (c • S) _ * T _ = c * (S _ * T _)
      rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (c • S).curryLeft ((chartModelBasis E) i) =
            c • S.curryLeft ((chartModelBasis E) i) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousMultilinearMap.smul_apply]
      rw [hcurry, ih]
      ring

lemma chartTensorInnerPointwise_0s_add_right
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (S T₁ T₂ : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S (T₁ + T₂) =
      chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T₁ +
        chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T₂ := by
  induction s with
  | zero =>
      change S _ * (T₁ + T₂) _ = S _ * T₁ _ + S _ * T₂ _
      rw [ContinuousMultilinearMap.add_apply]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (T₁ + T₂).curryLeft ((chartModelBasis E) j) =
            T₁.curryLeft ((chartModelBasis E) j) +
              T₂.curryLeft ((chartModelBasis E) j) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousMultilinearMap.add_apply]
      rw [hcurry, ih]
      ring

lemma chartTensorInnerPointwise_0s_smul_right
    (g : SmoothRiemannianMetric I M) (α b : M) (s : ℕ)
    (c : ℝ) (S T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S (c • T) =
      c * chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T := by
  induction s with
  | zero =>
      change S _ * (c • T) _ = c * (S _ * T _)
      rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul]; ring
  | succ s ih =>
      rw [chartTensorInnerPointwise_0s_succ,
          chartTensorInnerPointwise_0s_succ,
          Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      have hcurry :
          (c • T).curryLeft ((chartModelBasis E) j) =
            c • T.curryLeft ((chartModelBasis E) j) := by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousMultilinearMap.smul_apply]
      rw [hcurry, ih]
      ring

end Tensor0SRiemannian
end Tensor
end DifferentialGeometry

end
