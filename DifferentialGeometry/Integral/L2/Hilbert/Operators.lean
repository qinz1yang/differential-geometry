import DifferentialGeometry.Integral.L2.Hilbert.Defs
import DifferentialGeometry.Integral.L2.Hilbert.Inherited
import DifferentialGeometry.Integral.L2.Hilbert.DenseSubset
import DifferentialGeometry.Integral.L2.Hilbert.SimpLemmas
import DifferentialGeometry.Integral.L2.SmoothSections.Defs
import DifferentialGeometry.Integral.L2.SmoothSections.PreHilbert
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Lifting continuous linear operators to the metric `L²` Hilbert space

The metric `L²` Hilbert space `TensorL2 r s g` is the Hausdorff
completion of the seminormed space of compactly-supported smooth
`(r, s)`-tensor sections. Continuous linear operators acting on those
smooth sections extend uniquely by continuity to the completion. This
file packages the two extensions needed by downstream spectral theory:

* **Lift to a complete codomain** (`SmoothCcTensor.extendL2`). Given a
  continuous linear map `T : SmoothCcTensor g r s →L[ℝ] F` to a
  complete normed space `F`, produce its unique continuous linear
  extension `extendL2 T : TensorL2 r s g →L[ℝ] F` such that
  `extendL2 T (S.toL2) = T S` for every compactly-supported smooth
  section `S`. This is the standard mechanism for lifting linear
  functionals (`F = ℝ`), evaluation at a fixed test field, or any
  Banach-space-valued operator from the smooth side to `L²`.
* **Lift between completions of different `(r, s)`-orders**
  (`SmoothCcTensor.mapL2`). Given a continuous linear map
  `T : SmoothCcTensor g r₁ s₁ →L[ℝ] SmoothCcTensor g r₂ s₂` between
  spaces of compactly-supported smooth sections of different
  multilinear orders, produce its unique continuous linear extension
  `mapL2 T : TensorL2 r₁ s₁ g →L[ℝ] TensorL2 r₂ s₂ g`. This is the
  standard mechanism for lifting bundle morphisms (raising / lowering
  of indices, contraction with a fixed smooth tensor field, …) to the
  corresponding `L²` spaces.

Both constructions wrap existing Mathlib API: `extendL2` is a thin
wrapper around `ContinuousLinearMap.extend` along the dense
uniform-inducing embedding `toL2`, and `mapL2` is a thin wrapper around
`ContinuousLinearMap.completion`.

## Main definitions and theorems

* `SmoothCcTensor.extendL2 T` — the continuous linear extension of `T`
  to `TensorL2 r s g`.
* `SmoothCcTensor.extendL2_apply_toL2` — the extension agrees with `T`
  on the embedded smooth sections.
* `SmoothCcTensor.extendL2_unique` — uniqueness: any continuous linear
  map agreeing with `T` on the embedded smooth sections coincides with
  `extendL2 T`.
* `SmoothCcTensor.mapL2 T` — the continuous linear lift of `T` between
  the two `L²` Hilbert spaces.
* `SmoothCcTensor.mapL2_apply_toL2` — the lift commutes with the dense
  embedding: `mapL2 T (S.toL2) = (T S).toL2`.
* `SmoothCcTensor.mapL2_unique` — uniqueness: any continuous linear map
  intertwining `T` with the dense embedding equals `mapL2 T`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Manifold MeasureTheory Set Filter Bundle Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Integral
namespace L2

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace SmoothCcTensor

section UniformInducing

variable [T2Space M] [SigmaCompactSpace M] [InnerProductSpace ℝ E]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

set_option linter.unusedSectionVars false in
/-- The dense embedding `toL2` of the seminormed space of
compactly-supported smooth tensor sections into the metric `L²`
Hilbert space is uniform-inducing.

This is the inducing property of the canonical coercion
`SmoothCcTensor g r s → UniformSpace.Completion (SmoothCcTensor g r s)`,
transferred along `coe_toComplL`. It is the key analytic input for the
Mathlib `ContinuousLinearMap.extend` extension API used to define
`extendL2` below. -/
theorem isUniformInducing_toL2 :
    IsUniformInducing (toL2 (g := g) (r := r) (s := s)) := by
  have hcoe : (toL2 (g := g) (r := r) (s := s) :
        SmoothCcTensor g r s → TensorL2 r s g) =
      ((↑) : SmoothCcTensor g r s →
        UniformSpace.Completion (SmoothCcTensor g r s)) := by
    funext S
    exact toL2_apply (g := g) (r := r) (s := s) S
  rw [show (toL2 (g := g) (r := r) (s := s) :
        SmoothCcTensor g r s → TensorL2 r s g) =
      ((↑) : SmoothCcTensor g r s →
        UniformSpace.Completion (SmoothCcTensor g r s)) from hcoe]
  exact UniformSpace.Completion.isUniformInducing_coe _

end UniformInducing

section ExtendL2

variable [T2Space M] [SigmaCompactSpace M] [InnerProductSpace ℝ E]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

set_option linter.unusedSectionVars false in
/-- The unique continuous linear extension of a continuous linear map
`T : SmoothCcTensor g r s →L[ℝ] F` from the seminormed space of
compactly-supported smooth `(r, s)`-tensor sections to the metric `L²`
Hilbert space `TensorL2 r s g`, when the codomain `F` is a complete
normed space.

The extension is characterised by the relation `extendL2 T (S.toL2) =
T S` for every compactly-supported smooth section `S`, see
`extendL2_apply_toL2`, and is unique with this property among
continuous linear maps, see `extendL2_unique`. -/
def extendL2 (T : SmoothCcTensor g r s →L[ℝ] F) :
    TensorL2 r s g →L[ℝ] F :=
  T.extend (toL2 (g := g) (r := r) (s := s))

set_option linter.unusedSectionVars false in
/-- The extension of `T` agrees with `T` on the dense subspace of
compactly-supported smooth sections, embedded via `toL2`. -/
@[simp] theorem extendL2_apply_toL2 (T : SmoothCcTensor g r s →L[ℝ] F)
    (S : SmoothCcTensor g r s) :
    extendL2 T ((toL2 (g := g) (r := r) (s := s)) S) = T S :=
  ContinuousLinearMap.extend_eq T denseRange_toL2 isUniformInducing_toL2 S

set_option linter.unusedSectionVars false in
/-- Uniqueness of the extension: any continuous linear map
`U : TensorL2 r s g →L[ℝ] F` whose composition with the dense embedding
`toL2` equals `T` coincides with `extendL2 T`. -/
theorem extendL2_unique (T : SmoothCcTensor g r s →L[ℝ] F)
    (U : TensorL2 r s g →L[ℝ] F)
    (h : U.comp (toL2 (g := g) (r := r) (s := s)) = T) :
    extendL2 T = U :=
  ContinuousLinearMap.extend_unique T denseRange_toL2 isUniformInducing_toL2 U h

end ExtendL2

section MapL2

variable [T2Space M] [SigmaCompactSpace M] [InnerProductSpace ℝ E]
variable {g : SmoothRiemannianMetric I M} {r₁ s₁ r₂ s₂ : ℕ}

set_option linter.unusedSectionVars false in
/-- The continuous linear lift of a continuous linear map
`T : SmoothCcTensor g r₁ s₁ →L[ℝ] SmoothCcTensor g r₂ s₂` between the
seminormed spaces of compactly-supported smooth tensor sections to the
corresponding metric `L²` Hilbert spaces.

The lift is characterised by the intertwining relation `mapL2 T
(S.toL2) = (T S).toL2` for every compactly-supported smooth section
`S`, see `mapL2_apply_toL2`, and is unique with this property among
continuous linear maps, see `mapL2_unique`. -/
def mapL2
    (T : SmoothCcTensor g r₁ s₁ →L[ℝ] SmoothCcTensor g r₂ s₂) :
    TensorL2 r₁ s₁ g →L[ℝ] TensorL2 r₂ s₂ g :=
  T.completion

set_option linter.unusedSectionVars false in
/-- The lift `mapL2 T` intertwines the dense embedding `toL2` with the
operator `T`: applied to an embedded smooth section it returns the
embedding of the image. -/
@[simp] theorem mapL2_apply_toL2
    (T : SmoothCcTensor g r₁ s₁ →L[ℝ] SmoothCcTensor g r₂ s₂)
    (S : SmoothCcTensor g r₁ s₁) :
    mapL2 T ((toL2 (g := g) (r := r₁) (s := s₁)) S) =
      (toL2 (g := g) (r := r₂) (s := s₂)) (T S) := by
  have hS := toL2_apply (g := g) (r := r₁) (s := s₁) S
  have hTS := toL2_apply (g := g) (r := r₂) (s := s₂) (T S)
  rw [hS, hTS]
  change T.completion (S : UniformSpace.Completion (SmoothCcTensor g r₁ s₁)) =
    (T S : UniformSpace.Completion (SmoothCcTensor g r₂ s₂))
  exact T.completion_apply_coe S

set_option linter.unusedSectionVars false in
/-- Uniqueness of the lift: any continuous linear map
`U : TensorL2 r₁ s₁ g →L[ℝ] TensorL2 r₂ s₂ g` whose composition with
the dense embedding `toL2` equals the composition `toL2 ∘ T` coincides
with `mapL2 T`. -/
theorem mapL2_unique
    (T : SmoothCcTensor g r₁ s₁ →L[ℝ] SmoothCcTensor g r₂ s₂)
    (U : TensorL2 r₁ s₁ g →L[ℝ] TensorL2 r₂ s₂ g)
    (h : U.comp (toL2 (g := g) (r := r₁) (s := s₁)) =
      (toL2 (g := g) (r := r₂) (s := s₂)).comp T) :
    mapL2 T = U := by
  refine ContinuousLinearMap.ext fun x => ?_
  refine UniformSpace.Completion.induction_on (α := SmoothCcTensor g r₁ s₁)
      (p := fun y => (mapL2 T) y = U y) x ?_ ?_
  · exact isClosed_eq (mapL2 T).continuous U.continuous
  · intro a
    have hcoe :
        (a : UniformSpace.Completion (SmoothCcTensor g r₁ s₁)) =
          (toL2 (g := g) (r := r₁) (s := s₁)) a :=
      (toL2_apply (g := g) (r := r₁) (s := s₁) a).symm
    have hU : U ((toL2 (g := g) (r := r₁) (s := s₁)) a) =
        (toL2 (g := g) (r := r₂) (s := s₂)) (T a) := by
      have := congrArg (fun (φ : _ →L[ℝ] _) => φ a) h
      simpa using this
    have hM : (mapL2 T) ((toL2 (g := g) (r := r₁) (s := s₁)) a) =
        (toL2 (g := g) (r := r₂) (s := s₂)) (T a) :=
      mapL2_apply_toL2 (g := g) (r₁ := r₁) (s₁ := s₁)
        (r₂ := r₂) (s₂ := s₂) T a
    rw [hcoe, hM, ← hU]

end MapL2

end SmoothCcTensor

end L2
end Integral
end DifferentialGeometry

end
