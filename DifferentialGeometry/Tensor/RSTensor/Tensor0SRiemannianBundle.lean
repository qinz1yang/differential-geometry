import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian
import DifferentialGeometry.Integral.L2.PointwiseInner.Defs
import DifferentialGeometry.Integral.L2.PointwiseInner.Algebra
import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Tensor.Multilinear.Basis
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Riemannian-metric data for the `(0, s)`-tensor bundle

Given a smooth Riemannian metric `g` on a manifold `M` (encoded as a
`SmoothRiemannianMetric I M`), this file consolidates the fiberwise inner
product `innerBundleCLM g s b` from `Tensor0SRiemannian.lean` and its algebraic
properties (symmetry, positive-definiteness on the diagonal, bilinearity,
diagonal continuity) into a single API that can be consumed by downstream
substeps that wish to package the data as a Mathlib
`Bundle.RiemannianMetric` / `Bundle.RiemannianBundle` instance.

The public exports are:

* `tensor0SRiemannianInnerCLM g s b` — alias for `innerBundleCLM g s b`,
  the bundle-fibre inner product as a continuous bilinear `→L[ℝ] →L[ℝ] ℝ`.
* `tensor0SRiemannianInner_symm`, `tensor0SRiemannianInner_pos`,
  `tensor0SRiemannianInner_smul_left`, `tensor0SRiemannianInner_smul_right`:
  symmetry, positivity, and bilinearity.
* `tensor0SRiemannianInner_diagonal_continuous`: continuity of
  `v ↦ inner b v v` on the bundle fibre, used for the `RiemannianMetric.continuousAt`
  field.

The actual `Bundle.RiemannianMetric` / `Bundle.RiemannianBundle` /
`IsContinuousRiemannianBundle` packaging requires careful management of the
diamond between the bundle topology (`instTopologicalSpaceContinuousMultilinearMap`)
and the norm topology (from `NormedAddCommGroup`) on the bundle fibre, and is
deferred to a follow-up step that registers the instance under controlled
local instance disables.
-/

noncomputable section

open Bundle Set IsManifold ContinuousLinearMap Bornology
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Tensor
namespace Tensor0SRiemannianBundle

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- File-local instance mirroring `Tensor0SRiemannian.bundleDualTopologicalSpace`:
install the strong CLM topology on `Tensor0SSpace s I b →L[ℝ] ℝ`. This makes
typeclass synthesis on nested `→L[ℝ]` types involving the bundle fibre
deterministic. -/
private instance bundleDualTopologicalSpace (s : ℕ) (b : M) :
    TopologicalSpace (Tensor0SSpace s I b →L[ℝ] ℝ) :=
  ContinuousLinearMap.topologicalSpace
    (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := Tensor0SSpace s I b) (F := ℝ)

/-! ## Public alias for the bundle-fibre inner product as a CLM -/

/-- The bundle-fibre `(0, s)` pointwise inner product as a continuous bilinear
pairing on `Tensor0SSpace s I b`. This is `Tensor0SRiemannian.innerBundleCLM`,
re-exported here under a name reflecting its role as the Riemannian metric of
the `(0, s)`-tensor bundle. -/
noncomputable def tensor0SRiemannianInnerCLM
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Tensor0SSpace s I b →L[ℝ] Tensor0SSpace s I b →L[ℝ] ℝ :=
  innerBundleCLM (I := I) (M := M) g s b

@[simp] lemma tensor0SRiemannianInnerCLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SSpace s I b) :
    tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T S =
      innerBundleCLM (I := I) (M := M) g s b T S := rfl

/-! ## Algebraic properties: symmetry, positive-definiteness, bilinearity -/

/-- Symmetry of the bundle-fibre inner product. -/
theorem tensor0SRiemannianInner_symm
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T S : Tensor0SSpace s I b) :
    tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T S =
      tensor0SRiemannianInnerCLM (I := I) (M := M) g s b S T :=
  innerBundleCLM_symm (I := I) (M := M) g s b T S

/-- Positive-definiteness of the bundle-fibre inner product on the diagonal:
`inner b T T > 0` for `T ≠ 0`. -/
theorem tensor0SRiemannianInner_pos
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T : Tensor0SSpace s I b) (hT : T ≠ 0) :
    0 < tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T T :=
  innerBundleCLM_pos (I := I) (M := M) g s b T hT

/-- Left scalar-homogeneity of the bundle-fibre inner product. -/
theorem tensor0SRiemannianInner_smul_left
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (c : ℝ) (T S : Tensor0SSpace s I b) :
    tensor0SRiemannianInnerCLM (I := I) (M := M) g s b (c • T) S =
      c * tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T S := by
  have h := ContinuousLinearMap.map_smul
    (innerBundleCLM (I := I) (M := M) g s b) c T
  -- `(innerBundleCLM g s b) (c • T) = c • (innerBundleCLM g s b T)` as CLMs.
  change innerBundleCLM (I := I) (M := M) g s b (c • T) S = _
  rw [h]
  rfl

/-- Right scalar-homogeneity of the bundle-fibre inner product. -/
theorem tensor0SRiemannianInner_smul_right
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (c : ℝ) (T S : Tensor0SSpace s I b) :
    tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T (c • S) =
      c * tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T S := by
  have h := ContinuousLinearMap.map_smul
    ((innerBundleCLM (I := I) (M := M) g s b) T) c S
  change (innerBundleCLM (I := I) (M := M) g s b T) (c • S) = _
  rw [h]
  rfl

/-! ## Diagonal continuity

We prove that `v ↦ tensor0SRiemannianInnerCLM g s b v v` is continuous on
the bundle fibre `Tensor0SSpace s I b`. The argument transports through the
continuous coercion `Tensor0SSpace.toModel` to the model fibre, where the
bilinear CLM `innerModelCLM g s b` has straightforward continuity. -/

/-- The model-fibre diagonal `T ↦ tensorInnerPointwise_0s s g b T T` is
continuous in the model fibre's norm topology. -/
lemma innerModel_diagonal_continuous
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Continuous (fun T : Tensor0SModel s ℝ E =>
      tensorInnerPointwise_0s (I := I) (M := M) s g b T T) := by
  have hModelCLM := (innerModelCLM (I := I) (M := M) g s b).continuous
  have : Continuous (fun T : Tensor0SModel s ℝ E =>
      innerModelCLM (I := I) (M := M) g s b T T) :=
    hModelCLM.clm_apply continuous_id
  simpa [innerModelCLM_apply] using this

/-- Diagonal continuity of the bundle-fibre inner product. -/
theorem tensor0SRiemannianInner_diagonal_continuous
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Continuous (fun v : Tensor0SSpace s I b =>
      tensor0SRiemannianInnerCLM (I := I) (M := M) g s b v v) := by
  -- Express the bundle diagonal in terms of the model diagonal via `toModel`.
  have heq : (fun v : Tensor0SSpace s I b =>
      tensor0SRiemannianInnerCLM (I := I) (M := M) g s b v v) =
      (fun v : Tensor0SSpace s I b =>
        tensorInnerPointwise_0s (I := I) (M := M) s g b
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) v)
          (Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) v)) := by
    funext v
    rw [tensor0SRiemannianInnerCLM_apply, innerBundleCLM_apply]
  rw [heq]
  have htoM : Continuous
      (fun v : Tensor0SSpace s I b =>
        Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) v) :=
    Tensor0SBundle.Tensor0SSpace.toModel_continuous
      (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
  exact (innerModel_diagonal_continuous (I := I) (M := M) g s b).comp htoM

/-- `ContinuousAt` form of the diagonal continuity at `0`. -/
theorem tensor0SRiemannianInner_diagonal_continuousAt_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    ContinuousAt (fun v : Tensor0SSpace s I b =>
      tensor0SRiemannianInnerCLM (I := I) (M := M) g s b v v) 0 :=
  (tensor0SRiemannianInner_diagonal_continuous (I := I) (M := M) g s b).continuousAt

/-! ## Von Neumann boundedness of the inner-product unit ball

To assemble a `Bundle.RiemannianMetric` we need that the inner-product sublevel
set `{v | inner b v v < 1}` is von-Neumann bounded. The bundle fibre is a
finite-dimensional normed space (using the project's
`Bundle.continuousMultilinearMap.instNormedAddCommGroup`), so it suffices to
show that the sublevel set is metrically bounded; `isVonNBounded_of_isBounded`
then gives the conclusion.

The bounded property is proved by transferring through the CLE
`tensor0SSpace_continuousLinearEquiv` to the model fibre, where the inner
product is a positive-definite continuous bilinear form and the unit ball is
bounded by the standard finite-dimensional sphere-minimisation argument. -/

/-- The diagonal `T ↦ tensor0SRiemannianInnerCLM g s b T T` viewed as a
continuous map. -/
private lemma tensor0SRiemannianInner_diagonal_clm_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M)
    (T : Tensor0SSpace s I b) :
    tensor0SRiemannianInnerCLM (I := I) (M := M) g s b T T =
      tensorInnerPointwise_0s (I := I) (M := M) s g b
        (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T)
        (Tensor0SBundle.Tensor0SSpace.toModel
          (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b) T) := by
  rw [tensor0SRiemannianInnerCLM_apply, innerBundleCLM_apply]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Boundedness on the model fibre: the diagonal sublevel set is metrically
bounded as a subset of `Tensor0SModel s ℝ E`. We invoke
`Tensor0SRiemannian.posDef_bilin_unit_ball_isBounded`, the abstract
positive-definite finite-dim boundedness lemma, applied to the model-fibre
inner CLM. -/
private lemma innerModel_diagonal_sublevel_isBounded
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    Bornology.IsBounded
      {T : Tensor0SModel s ℝ E |
        innerModelCLM (I := I) (M := M) g s b T T < 1} := by
  -- We work in the project's namespace where the model fibre has its
  -- canonical `NormedAddCommGroup` / `NormedSpace` / `FiniteDimensional`
  -- instances visible.
  by_cases hNT : Nontrivial (Tensor0SModel s ℝ E)
  · haveI := hNT
    have hPD : ∀ v : Tensor0SModel s ℝ E,
        v ≠ 0 → 0 < innerModelCLM (I := I) (M := M) g s b v v := by
      intro v hv
      change 0 < tensorInnerPointwise_0s (I := I) (M := M) s g b v v
      have hQpos := (tensorInnerPointwise_0s_eq_zero_iff
        (I := I) (M := M) g b s v).not.mpr hv
      have hnn := tensorInnerPointwise_0s_nonneg (I := I) (M := M) g b s v
      exact lt_of_le_of_ne hnn (Ne.symm hQpos)
    have hNN : ∀ v : Tensor0SModel s ℝ E,
        0 ≤ innerModelCLM (I := I) (M := M) g s b v v := fun v =>
      tensorInnerPointwise_0s_nonneg (I := I) (M := M) g b s v
    have hSmulL : ∀ (c : ℝ) (v w : Tensor0SModel s ℝ E),
        innerModelCLM (I := I) (M := M) g s b (c • v) w =
          c * innerModelCLM (I := I) (M := M) g s b v w := by
      intro c v w
      change tensorInnerPointwise_0s (I := I) (M := M) s g b (c • v) w =
        c * tensorInnerPointwise_0s (I := I) (M := M) s g b v w
      rw [tensorInnerPointwise_0s_smul_left]
    have hSmulR : ∀ (c : ℝ) (v w : Tensor0SModel s ℝ E),
        innerModelCLM (I := I) (M := M) g s b v (c • w) =
          c * innerModelCLM (I := I) (M := M) g s b v w := by
      intro c v w
      change tensorInnerPointwise_0s (I := I) (M := M) s g b v (c • w) =
        c * tensorInnerPointwise_0s (I := I) (M := M) s g b v w
      rw [tensorInnerPointwise_0s_smul_right]
    exact Tensor0SRiemannian.posDef_bilin_unit_ball_isBounded
      (innerModelCLM (I := I) (M := M) g s b) hPD hNN hSmulL hSmulR
  · -- Trivial case: subsingleton model fibre.
    have hSubsingleton : Subsingleton (Tensor0SModel s ℝ E) :=
      not_nontrivial_iff_subsingleton.mp hNT
    haveI := hSubsingleton
    refine (Metric.isBounded_iff_subset_ball 0).mpr ⟨1, ?_⟩
    intro v _
    rw [Metric.mem_ball, dist_zero_right]
    have hv0 : v = 0 := Subsingleton.elim v 0
    rw [hv0, norm_zero]; exact one_pos

/-- The model-side von-Neumann boundedness of the inner-product unit ball. -/
private lemma innerModel_diagonal_sublevel_isVonNBounded
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    IsVonNBounded ℝ
      {T : Tensor0SModel s ℝ E |
        innerModelCLM (I := I) (M := M) g s b T T < 1} :=
  NormedSpace.isVonNBounded_of_isBounded ℝ
    (innerModel_diagonal_sublevel_isBounded (I := I) (M := M) g s b)

/-- Von-Neumann boundedness of the inner-product unit ball on the bundle
fibre, transferred from the model side via the CLE
`tensor0SSpace_continuousLinearEquiv`. The image of a von-Neumann-bounded set
under a continuous linear map is von-Neumann bounded. -/
theorem tensor0SRiemannianInner_isVonNBounded
    (g : SmoothRiemannianMetric I M) (s : ℕ) (b : M) :
    IsVonNBounded ℝ
      {v : Tensor0SSpace s I b |
        tensor0SRiemannianInnerCLM (I := I) (M := M) g s b v v < 1} := by
  -- Pass through the CLE `tensor0SSpace_continuousLinearEquiv` to the
  -- model fibre, where the boundedness has already been proved.
  set e : Tensor0SSpace s I b ≃L[ℝ] Tensor0SModel s ℝ E :=
    Tensor0SBundle.tensor0SSpace_continuousLinearEquiv
      (𝕜 := ℝ) (E := E) (I := I) (M := M) s b with he_def
  have hModel := innerModel_diagonal_sublevel_isVonNBounded
    (I := I) (M := M) g s b
  -- Take the image under `e.symm.toContinuousLinearMap`.
  have hImg :=
    hModel.image (e.symm.toContinuousLinearMap)
  -- Identify the bundle-side set with the image of the model-side set.
  have hSetEq :
      e.symm.toContinuousLinearMap ''
        {T : Tensor0SModel s ℝ E |
          innerModelCLM (I := I) (M := M) g s b T T < 1} =
      {v : Tensor0SSpace s I b |
          tensor0SRiemannianInnerCLM (I := I) (M := M) g s b v v < 1} := by
    ext v
    refine ⟨?_, ?_⟩
    · rintro ⟨T, hT, rfl⟩
      rw [Set.mem_setOf_eq] at hT
      rw [Set.mem_setOf_eq, tensor0SRiemannianInner_diagonal_clm_apply]
      have hRound : (e (e.symm T) : _) = T := e.apply_symm_apply T
      have hToModel :
          Tensor0SBundle.Tensor0SSpace.toModel
            (𝕜 := ℝ) (E := E) (I := I) (M := M) (s := s) (x := b)
            ((e.symm.toContinuousLinearMap :
              Tensor0SModel s ℝ E →L[ℝ] Tensor0SSpace s I b) T) = T := hRound
      rw [hToModel]
      change tensorInnerPointwise_0s (I := I) (M := M) s g b T T < 1
      exact hT
    · intro hv
      refine ⟨e v, ?_, ?_⟩
      · rw [Set.mem_setOf_eq]
        rw [Set.mem_setOf_eq, tensor0SRiemannianInner_diagonal_clm_apply] at hv
        change tensorInnerPointwise_0s (I := I) (M := M) s g b _ _ < 1
        exact hv
      · exact e.symm_apply_apply v
  rw [← hSetEq]
  exact hImg

/-! ## Bundle `RiemannianMetric` packaging

We package the algebraic / continuity / boundedness data into Mathlib's
`Bundle.RiemannianMetric` structure, and install the resulting
`Bundle.RiemannianBundle` instance. The diamond between Mathlib's scoped
priority-80 `NormedAddCommGroup` instance coming from the
`RiemannianBundle` mechanism and the project's
`Bundle.continuousMultilinearMap.instNormedAddCommGroup` /
`Bundle.continuousMultilinearMap.instNormedSpace` global instances is
resolved locally via `attribute [-instance]` on the project instances,
following the template of `TangentRiemannian.lean`. -/

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace in
/-- The bundle Riemannian metric on the `(0, s)`-tensor bundle, built from
the underlying tangent-bundle Riemannian metric `g`. -/
noncomputable def tensor0SRiemannianMetric
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    Bundle.RiemannianMetric (E := fun b : M => Tensor0SSpace s I b) where
  inner := fun b => tensor0SRiemannianInnerCLM (I := I) (M := M) g s b
  symm := fun b T S =>
    tensor0SRiemannianInner_symm (I := I) (M := M) g s b T S
  pos := fun b T hT =>
    tensor0SRiemannianInner_pos (I := I) (M := M) g s b T hT
  continuousAt := fun b =>
    tensor0SRiemannianInner_diagonal_continuousAt_zero
      (I := I) (M := M) g s b
  isVonNBounded := fun b =>
    tensor0SRiemannianInner_isVonNBounded (I := I) (M := M) g s b

end Tensor0SRiemannianBundle
end Tensor
end DifferentialGeometry

/-! ## Public `RiemannianBundle` instance

We install the `RiemannianBundle` instance on the `(0, s)`-tensor bundle
using `tensor0SRiemannianMetric`. The instance is parameterised by a
`SmoothRiemannianMetric I M` argument supplied as a section-level variable;
downstream files may either provide it via `letI` or via a `variable
[g : SmoothRiemannianMetric I M]` declaration in their preamble. -/

namespace Tensor0SBundle

open DifferentialGeometry.Tensor.Tensor0SRiemannianBundle
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The `RiemannianBundle` class instance for the `(0, s)`-tensor bundle,
built from a smooth tangent-bundle Riemannian metric `g`. This is supplied as
a definition parameterised by the metric so that downstream files can
register it locally via `letI` to register the inner-product structure on
each fibre. -/
@[reducible]
noncomputable def tensor0S_riemannianBundle
    (g : SmoothRiemannianMetric I M) (s : ℕ) :
    Bundle.RiemannianBundle (fun b : M => Tensor0SSpace s I b) :=
  ⟨tensor0SRiemannianMetric (I := I) (M := M) g s⟩

end Tensor0SBundle
