import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0SRiemannian
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Defs
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Algebra
import DifferentialGeometry.Geometry.Metric.ChartGram
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Continuity of the metric inner product on `(r, s)`-tensor sections

Given a smooth Riemannian metric `g` on a manifold `M`, this file establishes
continuity of the pointwise inner product `tensorInnerPointwise g r s b T S` on
mixed `(r, s)`-tensor sections via reduction to the covariant `(0, r + s)` case.

The reduction follows the definitional decomposition
`tensorInnerPointwise g r s b T S =
  tensorInnerPointwise_0s (r + s) g b
    (lowerAllUpperIndices g r s b T)
    (lowerAllUpperIndices g r s b S)`
already provided in `Integral.L2.PointwiseInner.Defs`.

Composing the lowering with the chart-trivialisation `chartJinv α b` of the
tangent bundle on each of the `r + s` slots, we obtain a chart-α-trivialised
fully-covariant model tensor whose pointwise inner product is computed via
`chartTensorInnerPointwise_0s` on the chart-Gram matrix. The continuity hypothesis
on each chart α is therefore phrased on this composed object.

The main public theorem is `TensorRSBundle.continuous_inner_of_smooth_sections`,
mirroring the corresponding `(0, s)`-statement.
-/

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap Bornology
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Tensor
namespace TensorRSRiemannian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Chart-α version of the `(r, s)` pointwise inner product

The mixed `(r, s)` pointwise inner product is defined via index-lowering followed
by the covariant `(0, r + s)` inner product. We define the chart-α analog by
applying the same lowering and replacing `tensorInnerPointwise_0s` with
`chartTensorInnerPointwise_0s` (which uses `chartGramMatrix g α b` in place of
`gramMatrixAt g b`).

For the chart bridge identity, the natural pairing arises from also composing the
lowered tensor with the chart-trivialisation `chartJinv α b` on each of the
`r + s` slots: this transforms the model basis into the chart-α basis and matches
the (0, r + s) bridge identity. -/

/-- Composed lowering: lower the `r` upper indices via `g.inner b`, then compose
with `chartJinv α b` on each of the resulting `r + s` slots. The result is the
fully-covariant model `(0, r + s)`-tensor whose chart-α-basis evaluation matches
the chart-α-trivialised image. -/
noncomputable def loweredCompose
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T : TensorRSModel r s ℝ E) : Tensor0SModel (r + s) ℝ E :=
  (lowerAllUpperIndices (I := I) (M := M) g r s b T).compContinuousLinearMap
    (fun _ : Fin (r + s) =>
      DifferentialGeometry.Tensor.Tensor0SRiemannian.chartJinv
        (I := I) (M := M) α b)

@[simp] lemma loweredCompose_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T : TensorRSModel r s ℝ E) (v : Fin (r + s) → E) :
    loweredCompose (I := I) (M := M) g r s α b T v =
      lowerAllUpperIndices (I := I) (M := M) g r s b T
        (fun i =>
          DifferentialGeometry.Tensor.Tensor0SRiemannian.chartJinv
            (I := I) (M := M) α b (v i)) := by
  unfold loweredCompose
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- The composed-lowering map is linear in `T`: it sends sums of mixed tensors
to sums of the corresponding lowered+composed model `(0, r + s)`-tensors. -/
lemma loweredCompose_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (T₁ T₂ : TensorRSModel r s ℝ E) :
    loweredCompose (I := I) (M := M) g r s α b (T₁ + T₂) =
      loweredCompose (I := I) (M := M) g r s α b T₁ +
        loweredCompose (I := I) (M := M) g r s α b T₂ := by
  unfold loweredCompose
  rw [ContinuousLinearMap.map_add]
  rfl

/-- The composed-lowering map is `ℝ`-homogeneous in `T`. -/
lemma loweredCompose_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (c : ℝ) (T : TensorRSModel r s ℝ E) :
    loweredCompose (I := I) (M := M) g r s α b (c • T) =
      c • loweredCompose (I := I) (M := M) g r s α b T := by
  unfold loweredCompose
  rw [ContinuousLinearMap.map_smul]
  rfl

/-- The composed-lowering map sends the zero `(r, s)`-tensor to the zero
`(0, r + s)`-tensor. -/
lemma loweredCompose_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M) :
    loweredCompose (I := I) (M := M) g r s α b (0 : TensorRSModel r s ℝ E) =
      (0 : Tensor0SModel (r + s) ℝ E) := by
  unfold loweredCompose
  rw [ContinuousLinearMap.map_zero]
  rfl

/-- The chart-α version of `tensorInnerPointwise` on `(r, s)`-tensors. We
implement it by lowering the `r` upper indices, composing with the chart-α
trivialisation `chartJinv α b`, and pairing the resulting `(0, r + s)`-tensors
through `chartTensorInnerPointwise_0s g α (r + s) b`.

This mirrors how `chartTensorInnerPointwise_0s` mirrors `tensorInnerPointwise_0s`
in `Tensor0SRiemannian`. -/
noncomputable def chartTensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (T S : TensorRSModel r s ℝ E) : ℝ :=
  chartTensorInnerPointwise_0s (I := I) (M := M) (r + s) g α b
    (loweredCompose (I := I) (M := M) g r s α b T)
    (loweredCompose (I := I) (M := M) g r s α b S)

@[simp] lemma chartTensorInnerPointwise_apply
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (T S : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b T S =
      chartTensorInnerPointwise_0s (I := I) (M := M) (r + s) g α b
        (loweredCompose (I := I) (M := M) g r s α b T)
        (loweredCompose (I := I) (M := M) g r s α b S) := rfl

/-! ### Algebraic properties of `chartTensorInnerPointwise`

The chart-α `(r, s)` inner product is bilinear and symmetric, inheriting these
properties from the underlying `chartTensorInnerPointwise_0s` together with
linearity of the composed-lowering map. -/

/-- Left additivity of the chart-α `(r, s)` inner product. -/
lemma chartTensorInnerPointwise_add_left
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (T₁ T₂ S : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b (T₁ + T₂) S =
      chartTensorInnerPointwise (I := I) (M := M) g α r s b T₁ S +
        chartTensorInnerPointwise (I := I) (M := M) g α r s b T₂ S := by
  rw [chartTensorInnerPointwise_apply, chartTensorInnerPointwise_apply,
    chartTensorInnerPointwise_apply, loweredCompose_add]
  exact chartTensorInnerPointwise_0s_add_left
    (I := I) (M := M) g α b (r + s) _ _ _

/-- Right additivity of the chart-α `(r, s)` inner product. -/
lemma chartTensorInnerPointwise_add_right
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (T S₁ S₂ : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b T (S₁ + S₂) =
      chartTensorInnerPointwise (I := I) (M := M) g α r s b T S₁ +
        chartTensorInnerPointwise (I := I) (M := M) g α r s b T S₂ := by
  rw [chartTensorInnerPointwise_apply, chartTensorInnerPointwise_apply,
    chartTensorInnerPointwise_apply, loweredCompose_add]
  exact chartTensorInnerPointwise_0s_add_right
    (I := I) (M := M) g α b (r + s) _ _ _

/-- Left `ℝ`-homogeneity of the chart-α `(r, s)` inner product. -/
lemma chartTensorInnerPointwise_smul_left
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (c : ℝ) (T S : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b (c • T) S =
      c * chartTensorInnerPointwise (I := I) (M := M) g α r s b T S := by
  rw [chartTensorInnerPointwise_apply, chartTensorInnerPointwise_apply,
    loweredCompose_smul]
  exact chartTensorInnerPointwise_0s_smul_left
    (I := I) (M := M) g α b (r + s) c _ _

/-- Right `ℝ`-homogeneity of the chart-α `(r, s)` inner product. -/
lemma chartTensorInnerPointwise_smul_right
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (c : ℝ) (T S : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b T (c • S) =
      c * chartTensorInnerPointwise (I := I) (M := M) g α r s b T S := by
  rw [chartTensorInnerPointwise_apply, chartTensorInnerPointwise_apply,
    loweredCompose_smul]
  exact chartTensorInnerPointwise_0s_smul_right
    (I := I) (M := M) g α b (r + s) c _ _

/-- Left zero of the chart-α `(r, s)` inner product. -/
lemma chartTensorInnerPointwise_zero_left
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (S : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b 0 S = 0 := by
  rw [chartTensorInnerPointwise_apply, loweredCompose_zero]

  have h := chartTensorInnerPointwise_0s_add_left
    (I := I) (M := M) g α b (r + s) (0 : Tensor0SModel (r + s) ℝ E) 0
    (loweredCompose (I := I) (M := M) g r s α b S)
  have h₀ : (0 : Tensor0SModel (r + s) ℝ E) + 0 = 0 := add_zero _
  rw [h₀] at h
  linarith

/-- Right zero of the chart-α `(r, s)` inner product. -/
lemma chartTensorInnerPointwise_zero_right
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) (b : M)
    (T : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b T 0 = 0 := by
  rw [chartTensorInnerPointwise_apply, loweredCompose_zero]
  have h := chartTensorInnerPointwise_0s_add_right
    (I := I) (M := M) g α b (r + s)
    (loweredCompose (I := I) (M := M) g r s α b T)
    (0 : Tensor0SModel (r + s) ℝ E) 0
  have h₀ : (0 : Tensor0SModel (r + s) ℝ E) + 0 = 0 := add_zero _
  rw [h₀] at h
  linarith

/-! ## Bridge identity for the `(r, s)` inner product

The bridge identity relates the model-basis `(r, s)` inner product
`tensorInnerPointwise` to its chart-α counterpart `chartTensorInnerPointwise`,
on points `b` in the chart base set. The proof reduces to the `(0, r + s)`
bridge identity already proven in `Tensor0SRiemannian`. -/

/-- **The bridge identity**, formal version.

For any pair of model `(r, s)`-tensors `T, S` and any base point `b` in the
trivialisation base set at `α`, the model-basis pointwise inner product agrees
with its chart-α counterpart. -/
theorem tensorInnerPointwise_bridge_identity
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T S : TensorRSModel r s ℝ E) :
    tensorInnerPointwise (I := I) (M := M) g r s b T S =
      chartTensorInnerPointwise (I := I) (M := M) g α r s b T S := by
  unfold tensorInnerPointwise chartTensorInnerPointwise loweredCompose
  exact tensorInnerPointwise_0s_bridge_identity
    (I := I) (M := M) g α (r + s) hb _ _

/-- Symmetry of the chart-α `(r, s)` inner product on the trivialisation base set:
follows from the bridge identity and the symmetry of `tensorInnerPointwise`. -/
lemma chartTensorInnerPointwise_symm
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T S : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise (I := I) (M := M) g α r s b T S =
      chartTensorInnerPointwise (I := I) (M := M) g α r s b S T := by
  rw [← tensorInnerPointwise_bridge_identity (I := I) (M := M) g α r s hb T S,
    ← tensorInnerPointwise_bridge_identity (I := I) (M := M) g α r s hb S T]
  exact tensorInnerPointwise_symm (I := I) (M := M) g r s b T S

/-! ## Continuity of the chart-α `(r, s)` inner product on continuous arguments

The chart-α `(r, s)` inner product, applied to two continuous functions
`T, S : M → TensorRSModel r s ℝ E` of the model fibre, is continuous on the
chart base set provided the lowered+composed images
`loweredCompose g r s α b (T b)` and similarly for `S` are continuous on the
chart base set.

The proof reduces to the `(0, r + s)` chart-local continuity lemma
`chartTensorInnerPointwise_0s_continuousOn_smooth_args`. -/

/-- The chart-α `(r, s)` inner product is continuous in `b` when its inputs
admit continuous lowered+composed representatives. -/
theorem chartTensorInnerPointwise_continuousOn
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ)
    (T S : M → TensorRSModel r s ℝ E)
    (hT : ContinuousOn (fun b : M => loweredCompose
        (I := I) (M := M) g r s α b (T b))
      (trivializationAt E (TangentSpace I) α).baseSet)
    (hS : ContinuousOn (fun b : M => loweredCompose
        (I := I) (M := M) g r s α b (S b))
      (trivializationAt E (TangentSpace I) α).baseSet) :
    ContinuousOn
      (fun b : M => chartTensorInnerPointwise
        (I := I) (M := M) g α r s b (T b) (S b))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hcont :
      ContinuousOn (fun b : M => chartTensorInnerPointwise_0s
        (I := I) (M := M) (r + s) g α b
          (loweredCompose (I := I) (M := M) g r s α b (T b))
          (loweredCompose (I := I) (M := M) g r s α b (S b)))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartTensorInnerPointwise_0s_continuousOn_smooth_args
      (I := I) (M := M) g α (r + s)
      (fun b => loweredCompose (I := I) (M := M) g r s α b (T b))
      (fun b => loweredCompose (I := I) (M := M) g r s α b (S b)) hT hS
  exact hcont

/-! ## Chart-local continuity of the `(r, s)` inner product on smooth sections

Given two `C^∞` `(r, s)`-tensor sections `T, S`, the bridge identity reduces
chart-local continuity of the inner product to the chart-α inner product, which
in turn reduces to the `(0, r + s)` chart-local statement. The hypothesis on the
caller's side is the continuity of the lowered+composed model-fibre
representations. -/

/-- Chart-local continuity of the `(r, s)` pointwise inner product on tensor
sections, given the continuity hypothesis on the chart-trivialised lowered
representations. -/
theorem chartLocal_continuous_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T S : ∀ y : M, TensorRSSpace r s I y) (α : M)
    (hTα : ContinuousOn
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b)))
      (trivializationAt E (TangentSpace I) α).baseSet)
    (hSα : ContinuousOn
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b)))
      (trivializationAt E (TangentSpace I) α).baseSet) :
    ContinuousOn
      (fun b : M =>
        tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
            (T b))
          (TensorRSSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
            (S b)))
      (trivializationAt E (TangentSpace I) α).baseSet := by

  have hbridge : ∀ b ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b))
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b)) =
      chartTensorInnerPointwise (I := I) (M := M) g α r s b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b))
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b)) := by
    intro b hb
    exact tensorInnerPointwise_bridge_identity
      (I := I) (M := M) g α r s hb _ _
  refine ContinuousOn.congr ?_ hbridge
  exact chartTensorInnerPointwise_continuousOn
    (I := I) (M := M) g α r s
    (fun b : M => TensorRSSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
        (T b))
    (fun b : M => TensorRSSpace.toModel
        (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
        (S b))
    hTα hSα

end TensorRSRiemannian
end Tensor
end DifferentialGeometry

/-! ## Public theorem on the `(r, s)`-tensor bundle

The chart-local continuity statement is glued into a global continuity
statement via the chart cover, mirroring the `(0, s)`-statement
`Tensor0SBundle.continuous_inner_of_smooth_sections`. -/

namespace TensorRSBundle

open scoped Manifold Topology Bundle BigOperators
open Tensor0SBundle Bundle Set
open DifferentialGeometry.Tensor.TensorRSRiemannian
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Global continuity of the pointwise inner product on `(r, s)`-tensor
sections. The hypothesis at each `α : M` is the continuity of the
lowered+composed model-fibre representation on the chart base set at `α`. -/
theorem continuous_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T S : ∀ y : M, TensorRSSpace r s I y)
    (hT_charts : ∀ α : M, ContinuousOn
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b)))
      (trivializationAt E (TangentSpace I) α).baseSet)
    (hS_charts : ∀ α : M, ContinuousOn
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b)))
      (trivializationAt E (TangentSpace I) α).baseSet) :
    Continuous (fun b : M =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b))
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b))) := by
  rw [continuous_iff_continuousAt]
  intro b
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) b).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt _ _ b
  have hOpen : IsOpen (trivializationAt E (TangentSpace I) b).baseSet :=
    (trivializationAt E (TangentSpace I) b).open_baseSet
  have hLocal :=
    DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_continuous_inner_of_smooth_sections
      (I := I) (M := M) g r s T S b (hT_charts b) (hS_charts b)
  exact hLocal.continuousAt (hOpen.mem_nhds hb_base)

end TensorRSBundle
