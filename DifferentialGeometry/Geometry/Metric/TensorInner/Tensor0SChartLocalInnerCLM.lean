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
# CLM-valued chart-local (0,s) inner product

This file packages the chart-local inner product
`chartTensorInnerPointwise_0s` as a continuous bilinear pairing
`chartTensorInnerPointwise_0sCLM`, valued in the fixed normed space
`MLF →L MLF →L ℝ` and indexed by the base point `b`. It also records the
"curry one slot at a fixed vector" map as a continuous linear map
`curryLeftAtCLM`, the slot-composition map `composeCurryAtIJ`, and the explicit
finite-sum recursion identity `chartTensorInnerPointwise_0sCLM_succ_eq` that
exposes the inductive structure of the CLM-valued inner product.
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

/-! ### CLM-valued chart-local inner product

We package the chart-local inner product as a `MLF →L MLF →L ℝ`-valued
function of `b`, and prove it is smooth as a map into the fixed normed
space `MLF →L MLF →L ℝ`. This is the form needed by the
trivialisation-section iff lemma. -/

/-- The bilinear `LinearMap` underlying `chartTensorInnerPointwise_0s`. -/
def chartTensorInnerPointwise_0sBilin
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α b : M) :
    Tensor0SModel s ℝ E →ₗ[ℝ]
      Tensor0SModel s ℝ E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun S T => chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T)
    (fun S₁ S₂ T =>
      chartTensorInnerPointwise_0s_add_left (I := I) (M := M) g α b s S₁ S₂ T)
    (fun c S T =>
      chartTensorInnerPointwise_0s_smul_left (I := I) (M := M) g α b s c S T)
    (fun S T₁ T₂ =>
      chartTensorInnerPointwise_0s_add_right (I := I) (M := M) g α b s S T₁ T₂)
    (fun c S T =>
      chartTensorInnerPointwise_0s_smul_right (I := I) (M := M) g α b s c S T)

@[simp] lemma chartTensorInnerPointwise_0sBilin_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α b : M)
    (S T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0sBilin (I := I) (M := M) g s α b S T =
      chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T := rfl

/-- CLM-valued chart-local inner product as a continuous bilinear pairing
on the model fibre, indexed by `b : M`. We use that the model fibre is
finite-dimensional, so any bilinear LinearMap is automatically continuous. -/
noncomputable def chartTensorInnerPointwise_0sCLM
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α b : M) :
    Tensor0SModel s ℝ E →L[ℝ]
      Tensor0SModel s ℝ E →L[ℝ] ℝ :=
  let bilin := chartTensorInnerPointwise_0sBilin (I := I) (M := M) g s α b
  LinearMap.toContinuousLinearMap
    { toFun := fun S => LinearMap.toContinuousLinearMap (bilin S)
      map_add' := fun S₁ S₂ => by
        refine ContinuousLinearMap.ext ?_
        intro T
        change chartTensorInnerPointwise_0s (I := I) (M := M) s g α b (S₁ + S₂) T =
          chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S₁ T +
            chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S₂ T
        exact chartTensorInnerPointwise_0s_add_left
          (I := I) (M := M) g α b s S₁ S₂ T
      map_smul' := fun c S => by
        refine ContinuousLinearMap.ext ?_
        intro T
        change chartTensorInnerPointwise_0s (I := I) (M := M) s g α b (c • S) T =
          c • chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T
        rw [chartTensorInnerPointwise_0s_smul_left]
        rfl }

@[simp] lemma chartTensorInnerPointwise_0sCLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α b : M)
    (S T : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0sCLM (I := I) (M := M) g s α b S T =
      chartTensorInnerPointwise_0s (I := I) (M := M) s g α b S T := rfl

/-! ### Explicit recursion structure for the CLM-valued chart-local inner
product

We rewrite `chartTensorInnerPointwise_0sCLM g (s+1) α b` as an explicit
finite-sum of `((chartGramMatrix g α b)⁻¹ i j) • (constant CLM ∘ s-step CLM)`,
where the constant CLM is the "compose with `curryLeft eᵢ`" map, used to
slot the inductive `s`-step into the recursive formula. This factorisation is
what enables the smoothness induction. -/

/-- The `S ↦ S.curryLeft v` map as a CLM `MLF (s+1) →L MLF s`. We bound the
norm directly using the CMLM operator-norm formula: for any tuple
`m : Fin s → E`, `(S.curryLeft v) m = S (cons v m)` and
`‖S (cons v m)‖ ≤ ‖S‖ * ‖v‖ * ∏ ‖m i‖` by `S.norm_map_cons_le`. -/
noncomputable def curryLeftAtCLM (s : ℕ) (v : E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ →L[ℝ]
      Tensor0SModel s ℝ E :=
  LinearMap.mkContinuous
    { toFun := fun S => S.curryLeft v
      map_add' := fun S₁ S₂ => by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousMultilinearMap.add_apply]
      map_smul' := fun c S => by
        ext m
        simp [ContinuousMultilinearMap.curryLeft_apply,
              ContinuousMultilinearMap.smul_apply] }
    ‖v‖
    (fun S => by
      change ‖S.curryLeft v‖ ≤ _

      refine (ContinuousMultilinearMap.opNorm_le_bound
        (M := ‖S‖ * ‖v‖) ?_ ?_).trans (by ring_nf; rfl)
      · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
      · intro m
        rw [ContinuousMultilinearMap.curryLeft_apply]
        have := S.norm_map_cons_le v m
        calc ‖S (Fin.cons v m)‖
            ≤ ‖S‖ * ‖v‖ * ∏ i, ‖m i‖ := this
          _ = ‖S‖ * ‖v‖ * ∏ i, ‖m i‖ := rfl)

lemma curryLeftAtCLM_apply (s : ℕ) (v : E)
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    curryLeftAtCLM (E := E) s v S = S.curryLeft v := rfl

/-- Pre-composition of a CLM `MLF s →L MLF s →L ℝ` with `curryLeftAtCLM s eᵢ`
on the source side, and `curryLeftAtCLM s eⱼ` on the second argument. This
gives a CLM `MLF (s+1) →L MLF (s+1) →L ℝ`.

The construction: `composeCurryAtIJ B S T = B (S.curryLeft eᵢ) (T.curryLeft eⱼ)`.
We use `compL.flip CLj` (post-compose with `CLj`) on the inner CLM, and
`B.comp CLi` (pre-compose with `CLi`) on the outer. -/
private noncomputable def composeCurryAtIJ (s : ℕ)
    (i j : Fin (Module.finrank ℝ E))
    (B : Tensor0SModel s ℝ E →L[ℝ]
      Tensor0SModel s ℝ E →L[ℝ] ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ →L[ℝ] ℝ :=
  let CLi := curryLeftAtCLM (E := E) s ((chartModelBasis E) i)
  let CLj := curryLeftAtCLM (E := E) s ((chartModelBasis E) j)

  let postCompCLj :
      (Tensor0SModel s ℝ E →L[ℝ] ℝ) →L[ℝ]
        (ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ
      (ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ)
      (Tensor0SModel s ℝ E) ℝ).flip CLj
  postCompCLj.comp (B.comp CLi)

@[simp] private lemma composeCurryAtIJ_apply (s : ℕ)
    (i j : Fin (Module.finrank ℝ E))
    (B : Tensor0SModel s ℝ E →L[ℝ]
      Tensor0SModel s ℝ E →L[ℝ] ℝ)
    (S T : ContinuousMultilinearMap ℝ (fun _ : Fin (s + 1) => E) ℝ) :
    composeCurryAtIJ (E := E) s i j B S T =
      B (S.curryLeft ((chartModelBasis E) i))
        (T.curryLeft ((chartModelBasis E) j)) := by
  rfl

/-- The factorisation of `chartTensorInnerPointwise_0sCLM g (s+1) α b` as a
`Finset.sum` of `smul`s of `composeCurryAtIJ`-transformed s-step CLMs. This
identity is the basis for the smoothness induction. -/
private lemma chartTensorInnerPointwise_0sCLM_succ_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α b : M) :
    chartTensorInnerPointwise_0sCLM (I := I) (M := M) g (s + 1) α b
      = ∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            (chartGramMatrix g α b)⁻¹ i j •
              composeCurryAtIJ (E := E) s i j
                (chartTensorInnerPointwise_0sCLM (I := I) (M := M) g s α b) := by
  refine ContinuousLinearMap.ext ?_
  intro S
  refine ContinuousLinearMap.ext ?_
  intro T
  rw [chartTensorInnerPointwise_0sCLM_apply, chartTensorInnerPointwise_0s_succ]

  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply,
    composeCurryAtIJ_apply, smul_eq_mul,
    chartTensorInnerPointwise_0sCLM_apply]

/-! ### Smoothness of the CLM-valued chart-local inner product

Using the explicit factorisation, we prove smoothness of
`chartTensorInnerPointwise_0sCLM g s α b` as a function of `b ∈ chartAt α`,
viewed as a map into the fixed normed space `MLF →L MLF →L ℝ`. The induction
is on `s`, with the inductive step using `ContMDiffOn.smul` and the bilinear
"compose with constant" maps (which act on smooth-in-`b` CLMs via continuous
linear pre/post-composition). -/

end Tensor0SRiemannian
end Tensor
end DifferentialGeometry

end
