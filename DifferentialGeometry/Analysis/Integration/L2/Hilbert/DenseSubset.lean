import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Defs
import DifferentialGeometry.Analysis.Integration.L2.Hilbert.Inherited
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.PreHilbert
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# Dense embedding of smooth tensor sections into the `L²` Hilbert space

This file packages the canonical embedding of compactly-supported smooth
`(r, s)`-tensor sections into the metric `L²` Hilbert space
`TensorL2 r s g` and records its key analytic properties:

* **Continuous linearity.** The embedding is given by
  `UniformSpace.Completion.toComplL`, the canonical embedding of a
  normed space into its Hausdorff completion as a continuous linear map.
* **Dense range.** Every element of `TensorL2 r s g` is a limit of
  embedded smooth sections.
* **Norm preservation.** `‖S.toL2‖ = ‖S‖`, where the right-hand side is
  the global metric `L²` (semi-)norm of `S`.
* **Inner-product preservation.** `⟪S.toL2, T.toL2⟫_ℝ = ⟪S, T⟫_ℝ`,
  where the right-hand side is the global metric `L²` pairing of `S`
  and `T`.

These four properties are the cornerstone of every density argument
extending an identity from smooth tensor fields to general `L²`
elements.

## Main definitions and theorems

* `SmoothCcTensor.toL2 : SmoothCcTensor g r s →L[ℝ] TensorL2 r s g`
* `SmoothCcTensor.toL2_apply` — `S.toL2` coincides with the canonical
  coercion `SmoothCcTensor g r s → TensorL2 r s g`.
* `SmoothCcTensor.denseRange_toL2` — the embedding has dense range.
* `SmoothCcTensor.norm_toL2` — the embedding is an isometry on
  representatives.
* `SmoothCcTensor.inner_toL2` — the embedding preserves inner products
  on representatives.
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

section DenseEmbedding

variable [T2Space M] [SigmaCompactSpace M] [InnerProductSpace ℝ E]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

set_option linter.unusedSectionVars false in
/-- The canonical continuous linear embedding of compactly-supported
smooth `(r, s)`-tensor sections into the metric `L²` Hilbert space.

This is `UniformSpace.Completion.toComplL`, the embedding of a normed
space into its Hausdorff completion as a continuous linear map.
Composed with the canonical fibrewise coercion
`SmoothCcTensor g r s → TensorL2 r s g`, it provides the standard
inclusion of smooth, compactly-supported sections as a dense subspace
of `L²`. -/
def toL2 : SmoothCcTensor g r s →L[ℝ] TensorL2 r s g :=
  UniformSpace.Completion.toComplL

set_option linter.unusedSectionVars false in
/-- Unfolding lemma: the embedding `toL2` agrees with the canonical
coercion from a normed space to its Hausdorff completion. -/
@[simp] theorem toL2_apply (S : SmoothCcTensor g r s) :
    (toL2 (g := g) (r := r) (s := s) S : TensorL2 r s g) =
      (S : UniformSpace.Completion (SmoothCcTensor g r s)) := by
  change (UniformSpace.Completion.toComplL S : TensorL2 r s g) =
    (S : UniformSpace.Completion (SmoothCcTensor g r s))
  rw [UniformSpace.Completion.coe_toComplL]

set_option linter.unusedSectionVars false in
/-- The image of the smooth, compactly-supported sections is dense in
the metric `L²` Hilbert space: a textbook density statement. -/
theorem denseRange_toL2 :
    DenseRange (toL2 (g := g) (r := r) (s := s)) := by
  have hcoe : (toL2 (g := g) (r := r) (s := s) :
        SmoothCcTensor g r s → TensorL2 r s g) =
      ((↑) : SmoothCcTensor g r s →
        UniformSpace.Completion (SmoothCcTensor g r s)) := by
    funext S
    exact toL2_apply (g := g) (r := r) (s := s) S
  rw [hcoe]
  exact UniformSpace.Completion.denseRange_coe

set_option linter.unusedSectionVars false in
/-- The embedding `toL2` preserves norms on representatives:
`‖S.toL2‖` equals the global metric `L²` (semi-)norm of `S`. This is
the textbook fact that the inclusion of smooth, compactly-supported
sections into `L²` is an isometry on representatives. -/
@[simp] theorem norm_toL2 (S : SmoothCcTensor g r s) :
    ‖toL2 (g := g) (r := r) (s := s) S‖ = ‖S‖ := by
  have h := toL2_apply (g := g) (r := r) (s := s) S
  rw [show ‖toL2 (g := g) (r := r) (s := s) S‖ =
        ‖(S : UniformSpace.Completion (SmoothCcTensor g r s))‖ from
      congrArg norm h]
  exact UniformSpace.Completion.norm_coe S

set_option linter.unusedSectionVars false in
/-- The embedding `toL2` preserves inner products on representatives.
This is the textbook fact that the inclusion of smooth,
compactly-supported sections into the metric `L²` Hilbert space is an
inner-product isometry on representatives. -/
@[simp] theorem inner_toL2 (S T : SmoothCcTensor g r s) :
    ⟪toL2 (g := g) (r := r) (s := s) S,
        toL2 (g := g) (r := r) (s := s) T⟫_ℝ = ⟪S, T⟫_ℝ := by
  have hS := toL2_apply (g := g) (r := r) (s := s) S
  have hT := toL2_apply (g := g) (r := r) (s := s) T
  rw [show (⟪toL2 (g := g) (r := r) (s := s) S,
            toL2 (g := g) (r := r) (s := s) T⟫_ℝ : ℝ) =
        ⟪(S : UniformSpace.Completion (SmoothCcTensor g r s)),
          (T : UniformSpace.Completion (SmoothCcTensor g r s))⟫_ℝ from by
      rw [hS, hT]]
  exact UniformSpace.Completion.inner_coe S T

set_option linter.unusedSectionVars false in
/-- The embedding `toL2` is injective on representatives: two
compactly-supported smooth sections with the same `L²` class are equal.

Although the `L²` (semi-)norm on `SmoothCcTensor g r s` is only a
seminorm — its kernel a priori contains sections vanishing almost
everywhere — every representative is *continuous*, so a representative of
zero `L²` norm vanishes everywhere against the full-support Riemannian
volume measure. Concretely, `toL2 S = toL2 T` forces the diagonal `L²`
norm of `S - T` to vanish, hence the nonnegative continuous integrand
`x ↦ ⟨(S - T)(x), (S - T)(x)⟩_{g(x)}` is zero almost everywhere; being
continuous against an `IsOpenPosMeasure`, it is zero *everywhere*, and
pointwise positive-definiteness then forces `(S - T)(x) = 0` for every
`x`, so `S = T`. -/
theorem smoothCcTensor_eq_of_toL2_eq (S T : SmoothCcTensor g r s)
    (h : toL2 (g := g) (r := r) (s := s) S =
      toL2 (g := g) (r := r) (s := s) T) : S = T := by
  have hsub : S - T = 0 := by
    have hnorm0 : ‖S - T‖ = 0 := by
      have hmap : toL2 (g := g) (r := r) (s := s) (S - T) = 0 := by
        rw [map_sub, h, sub_self]
      have := congrArg norm hmap
      rwa [norm_toL2 (g := g) (r := r) (s := s) (S - T), norm_zero] at this
    have hinner0 :
        tensorL2Inner (I := I) (M := M) g r s (S - T).toFun (S - T).toFun = 0 := by
      have hsqrt : tensorL2Norm (I := I) (M := M) g r s (S - T).toFun = 0 := by
        rw [← SmoothCcTensor.norm_def (I := I) (M := M) (S - T)]
        exact hnorm0
      rw [tensorL2Norm_def] at hsqrt
      exact (Real.sqrt_eq_zero
        (tensorL2Inner_nonneg (I := I) (M := M) g r s (S - T).toFun)).mp hsqrt
    have hae :
        (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
            ((S - T).toFun x) ((S - T).toFun x))
          =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg
        (fun x : M => tensorInnerPointwise_nonneg (I := I) (M := M) g r s x
          ((S - T).toFun x))
        (SmoothCcTensor.memL2_toFun (I := I) (M := M) (S - T))).mp hinner0
    haveI : (riemannianVolumeMeasure (I := I) (M := M) g).IsOpenPosMeasure :=
      riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
    have heq :
        (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
            ((S - T).toFun x) ((S - T).toFun x)) = 0 :=
      (Continuous.ae_eq_iff_eq (riemannianVolumeMeasure (I := I) (M := M) g)
        (SmoothCcTensor.continuous_inner_self (I := I) (M := M) (S - T))
        continuous_const).mp hae
    have hsection : (S - T).toSection = 0 := by
      refine ContMDiffSection.ext (fun x => ?_)
      have hx : tensorInnerPointwise (I := I) (M := M) g r s x
          ((S - T).toFun x) ((S - T).toFun x) = 0 := congrFun heq x
      have hfun : (S - T).toFun x = 0 :=
        (tensorInnerPointwise_eq_zero_iff (I := I) (M := M) g r s x
          ((S - T).toFun x)).mp hx
      have hmodel : TensorRSSpace.toModel ((S - T).toSection x) = 0 := hfun
      have hzero : TensorRSSpace.toModel
          ((0 : Cₛ^∞⟮I; TensorRSModel r s ℝ E,
            (fun x : M => TensorRSSpace r s I x)⟯) x) = 0 := by
        rw [ContMDiffSection.coe_zero, Pi.zero_apply, TensorRSSpace.toModel_zero]
      exact TensorRSSpace.toModel_injective (𝕜 := ℝ) (E := E) (I := I) (M := M)
        (hmodel.trans hzero.symm)
    refine SmoothCcTensor.ext ?_
    rw [SmoothCcTensor.toSection_zero]
    exact hsection
  exact sub_eq_zero.mp hsub

end DenseEmbedding

end SmoothCcTensor

end L2
end Integral
end DifferentialGeometry

end
