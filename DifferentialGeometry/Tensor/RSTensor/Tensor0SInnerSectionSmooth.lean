import DifferentialGeometry.Tensor.RSTensor.TensorRSRiemannian
import DifferentialGeometry.Tensor.Multilinear.MetricLowering
import DifferentialGeometry.Integral.L2.SmoothSections.Defs
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Smoothness of the pointwise tensor inner product on smooth `(r, s)`-tensor sections

Given a smooth Riemannian metric `g` on a manifold `M`, the pointwise
metric-induced inner product `tensorInnerPointwise g r s b T S` of two smooth
mixed `(r, s)`-tensor sections is a `C^∞` scalar function of the base point `b`.

This is the smoothness upgrade of the continuity statement
`TensorRSBundle.continuous_inner_of_smooth_sections`
(`Tensor/RSTensor/TensorRSRiemannian.lean`). The proof mirrors the continuity
argument verbatim, replacing `ContinuousOn` by `ContMDiffOn` throughout:

1. On each chart `α`, the chart-frame `(r, s)` inner product is smooth in `b`
   when its inputs admit smooth lowered+composed model-fibre representatives.
   This reduces, via the `(0, r + s)` chart-local smoothness lemma
   `chartTensorInnerPointwise_0s_contMDiffOn_smooth_args`, to per-basis-tuple
   scalar smoothness of the lowered+composed representatives, which is supplied
   by `TensorMetricLowering.contMDiffOn_loweredCompose` after evaluating at each
   basis tuple.

2. The chart-frame inner product is identified with the global pointwise inner
   product on the chart base set via `tensorInnerPointwise_bridge_identity`.

3. The chart-local smoothness statements are glued into a global smoothness
   statement via the chart cover.

The headline `tensorInnerPointwise_contMDiff` packages this for
`SmoothCcTensor g r s` arguments, the form needed by `L²` / Sobolev consumers.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Tensor
namespace TensorRSRiemannian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open TensorMetricLowering

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

-- File-local instances to ensure typeclass resolution finds the normed structure on
-- the model fibres `Tensor0SModel`/`TensorRSModel` (the project-registered operator-norm
-- instances), mirroring the pattern in `Tensor0SRiemannian.lean`.
private instance tensor0SModelNormedSpace_local {n : ℕ} :
    NormedSpace ℝ (Tensor0SModel n ℝ E) :=
  Tensor0SBundle.tensor0SModel_normedSpace n

private instance tensor0SModelNormedAddCommGroup_local {n : ℕ} :
    NormedAddCommGroup (Tensor0SModel n ℝ E) := inferInstance

private instance tensorRSModelNormedSpace_local {r s : ℕ} :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedSpace r s

private instance tensorRSModelNormedAddCommGroup_local {r s : ℕ} :
    NormedAddCommGroup (TensorRSModel r s ℝ E) := inferInstance

/-! ## Per-basis-tuple scalar smoothness from smoothness into the model fibre

The chart-local `(0, r + s)` smoothness lemma
`chartTensorInnerPointwise_0s_contMDiffOn_smooth_args` takes its arguments in the
form of per-basis-tuple scalar smoothness. We derive that form from a single
`ContMDiffOn` statement into `Tensor0SModel n ℝ E` by composing with the
continuous-linear evaluation map at each fixed basis tuple. -/

set_option linter.unusedSectionVars false in
/-- From smoothness of a `Tensor0SModel n ℝ E`-valued function on a set, the
scalar evaluation at any fixed basis tuple is smooth on that set. The evaluation
`T ↦ T m` at a fixed tuple `m` is the continuous linear map
`ContinuousMultilinearMap.apply ℝ _ ℝ m`, so smoothness is preserved by
composition. -/
lemma contMDiffOn_eval_basisTuple_of_into_tensor0SModel
    {n : ℕ} {U : Set M} {Φ : M → Tensor0SModel n ℝ E}
    (hΦ : ContMDiffOn I 𝓘(ℝ, Tensor0SModel n ℝ E) ∞ Φ U)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => Φ b (fun k : Fin n => (chartModelBasis E) (φ k))) U := by
  -- `T ↦ T (e_φ)` is a continuous linear map `Tensor0SModel n ℝ E →L[ℝ] ℝ`.
  set evalCLM :
      Tensor0SModel n ℝ E →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) ℝ
      (fun k : Fin n => (chartModelBasis E) (φ k)) with hevalCLM
  -- `fun b => Φ b (e_φ) = evalCLM ∘ Φ`.
  have heq : (fun b : M => Φ b (fun k : Fin n => (chartModelBasis E) (φ k)))
      = fun b : M => evalCLM (Φ b) := by
    funext b
    rfl
  rw [heq]
  exact evalCLM.contMDiff.comp_contMDiffOn hΦ

/-! ## Chart-frame smoothness of the `(r, s)` inner product

The chart-`α` `(r, s)` inner product `chartTensorInnerPointwise g α r s b (T b) (S b)`
is smooth in `b` on the chart base set when its inputs admit smooth lowered+composed
representatives `loweredCompose g r s α b (T b)`, `loweredCompose g r s α b (S b)`. -/

set_option linter.unusedSectionVars false in
/-- The chart-`α` `(r, s)` inner product is smooth in `b` on the chart base set
when its inputs admit smooth lowered+composed representatives. -/
theorem chartTensorInnerPointwise_contMDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) (r s : ℕ)
    (T S : M → TensorRSModel r s ℝ E)
    (hT : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b (T b))
      (trivializationAt E (TangentSpace I) α).baseSet)
    (hS : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b (S b))
      (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M => chartTensorInnerPointwise
        (I := I) (M := M) g α r s b (T b) (S b))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  -- `chartTensorInnerPointwise g α r s b T S = chartTensorInnerPointwise_0s (r+s) g α b
  --   (loweredCompose ... T) (loweredCompose ... S)` definitionally.
  have hsmooth :
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => chartTensorInnerPointwise_0s
          (I := I) (M := M) (r + s) g α b
            (loweredCompose (I := I) (M := M) g r s α b (T b))
            (loweredCompose (I := I) (M := M) g r s α b (S b)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
    chartTensorInnerPointwise_0s_contMDiffOn_smooth_args
      (I := I) (M := M) g α (r + s)
      (fun b => loweredCompose (I := I) (M := M) g r s α b (T b))
      (fun b => loweredCompose (I := I) (M := M) g r s α b (S b))
      (fun φ => contMDiffOn_eval_basisTuple_of_into_tensor0SModel
        (I := I) (M := M) hT φ)
      (fun φ => contMDiffOn_eval_basisTuple_of_into_tensor0SModel
        (I := I) (M := M) hS φ)
  exact hsmooth

/-! ## Chart-local smoothness of the `(r, s)` inner product on smooth sections

Given two smooth `(r, s)`-tensor sections `T, S`, the bridge identity reduces
chart-local smoothness of the inner product to the chart-`α` inner product, which
in turn reduces to the `(0, r + s)` chart-local statement. The hypothesis on the
caller's side is the smoothness of the lowered+composed model-fibre
representations. -/

set_option linter.unusedSectionVars false in
/-- Chart-local smoothness of the `(r, s)` pointwise inner product on tensor
sections, given the smoothness hypothesis on the chart-trivialised lowered
representations. -/
theorem chartLocal_contMDiff_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T S : ∀ y : M, TensorRSSpace r s I y) (α : M)
    (hTα : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b)))
      (trivializationAt E (TangentSpace I) α).baseSet)
    (hSα : ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b)))
      (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
            (T b))
          (TensorRSSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
            (S b)))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  -- Use the bridge identity to convert to `chartTensorInnerPointwise`, then
  -- apply `chartTensorInnerPointwise_contMDiffOn`.
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
  refine ContMDiffOn.congr ?_ hbridge
  exact chartTensorInnerPointwise_contMDiffOn
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

/-! ## Public smoothness theorem on the `(r, s)`-tensor bundle

The chart-local smoothness statement is glued into a global smoothness
statement via the chart cover, mirroring `TensorRSBundle.continuous_inner_of_smooth_sections`. -/

namespace TensorRSBundle

open scoped Manifold Topology Bundle BigOperators
open Tensor0SBundle Bundle Set
open DifferentialGeometry.Tensor.TensorRSRiemannian
open TensorMetricLowering
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private instance tensor0SModelNormedSpace_local {n : ℕ} :
    NormedSpace ℝ (Tensor0SModel n ℝ E) :=
  Tensor0SBundle.tensor0SModel_normedSpace n

private instance tensorRSModelNormedSpace_local {r s : ℕ} :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedSpace r s

set_option linter.unusedSectionVars false in
/-- Global smoothness of the pointwise inner product on `(r, s)`-tensor
sections. The hypothesis at each `α : M` is the smoothness of the
lowered+composed model-fibre representation on the chart base set at `α`. -/
theorem contMDiff_inner_of_smooth_sections
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T S : ∀ y : M, TensorRSSpace r s I y)
    (hT_charts : ∀ α : M, ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b)))
      (trivializationAt E (TangentSpace I) α).baseSet)
    (hS_charts : ∀ α : M, ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => loweredCompose (I := I) (M := M) g r s α b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b)))
      (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiff I 𝓘(ℝ) ∞ (fun b : M =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (T b))
        (TensorRSSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (r := r) (s := s) (x := b)
          (S b))) := by
  intro b
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) b).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt _ _ b
  have hOpen : IsOpen (trivializationAt E (TangentSpace I) b).baseSet :=
    (trivializationAt E (TangentSpace I) b).open_baseSet
  have hLocal :=
    DifferentialGeometry.Tensor.TensorRSRiemannian.chartLocal_contMDiff_inner_of_smooth_sections
      (I := I) (M := M) g r s T S b (hT_charts b) (hS_charts b)
  exact hLocal.contMDiffAt (hOpen.mem_nhds hb_base)

end TensorRSBundle

/-! ## Headline: smoothness of the inner product on `SmoothCcTensor` arguments -/

namespace DifferentialGeometry
namespace Tensor

open scoped Manifold Topology Bundle
open Tensor0SBundle Bundle Set
open TensorMetricLowering
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private instance tensorRSModelNormedSpace_local {r s : ℕ} :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedSpace r s

set_option linter.unusedSectionVars false in
/-- **Smoothness of the pointwise tensor inner product on smooth tensor sections.**
For two smooth `(r, s)`-tensor sections `T, S`, the map
`b ↦ tensorInnerPointwise g r s b (toModel (T b)) (toModel (S b))` is `C^∞`.

The hypotheses are smoothness of the section values into the model fibre, the
form produced by `ContMDiffSection` coercions; consumers holding a smooth
section pass its `.contMDiff` field through the chart-local lowered
representative smoothness `TensorMetricLowering.contMDiffOn_loweredCompose`. -/
theorem tensorInnerPointwise_contMDiff_of_mdiff
    [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T S : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
      (fun x : M => TensorRSSpace r s I x)⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (fun b : M =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel (T b))
        (TensorRSSpace.toModel (S b))) :=
  TensorRSBundle.contMDiff_inner_of_smooth_sections
    (I := I) (M := M) g r s
    (fun b : M => T b) (fun b : M => S b)
    (fun α : M =>
      TensorMetricLowering.contMDiffOn_loweredCompose
        (I := I) (M := M) g r s T α)
    (fun α : M =>
      TensorMetricLowering.contMDiffOn_loweredCompose
        (I := I) (M := M) g r s S α)

set_option linter.unusedSectionVars false in
/-- **Smoothness of the pointwise tensor inner product on `SmoothCcTensor` arguments.**
For two smooth, compactly-supported `(r, s)`-tensor sections `S, T`, the map
`b ↦ tensorInnerPointwise g r s b (toModel (S b)) (toModel (T b))` is `C^∞`.
This is the form consumed by the `L²` / Sobolev layer. -/
theorem tensorInnerPointwise_contMDiff
    [InnerProductSpace ℝ E]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) :
    ContMDiff I 𝓘(ℝ) ∞ (fun b : M =>
      tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel (S.toSection b))
        (TensorRSSpace.toModel (T.toSection b))) :=
  tensorInnerPointwise_contMDiff_of_mdiff
    (I := I) (M := M) g r s S.toSection T.toSection

end Tensor
end DifferentialGeometry

end
