import DifferentialGeometry.Integral.Connection.RiemannianFiberNormSqRiemannOpDualFrameParseval
import DifferentialGeometry.Integral.Connection.RiemannianFiberNormSqSmoothCcUniformBound

/-!
# Per-point fibre-norm control of curvature contractions on tensor sections

For a smooth Riemannian metric `g` on a manifold `M` modelled on a real inner-product
space `E`, the third-order Weitzenböck commutator defect collects genuine Riemann
curvature contractions of the once-differentiated tensor field, summed over a smooth
`g`-orthonormal frame. The genuine-curvature summands have the form
`R_x(B_i, W) Z (x)` — the bundled tensor curvature operator `riemannOp (tensorCov g r s)`
applied to fibre values. This file establishes the **uniform pointwise fibre-norm
control** of such a curvature contraction by the fibre norm of its (smooth) argument
section `Z`, with a constant that is uniform over a compact manifold.

## Main results

* `riemannOp_tensorCov_fiberNormSq_le_frameScalar` — the canonical pointwise comparison
  of the intrinsic Riemannian fibre norm of `R_x(v, w) T` against the diamond-free model
  norm of the fully-applied curvature value times the metric-frame scalar; the rank-`(r, s)`
  generalisation of the committed `(0, 2)` witness comparison.

* `exists_uniform_riemannOp_tensorCov_fiberNormSq_bound` — for a closed manifold and fixed
  smooth vector fields `X, Y` and a smooth compactly-supported `(r, s)`-tensor section `Z`,
  a single nonnegative constant `K` with
  `riemannianFiberNormSq g r s x (R_x(X x, Y x)(Z x)) ≤ K · riemannianFiberNormSq g r s x (Z x)`
  for every `x`, provided the (metric-coercivity) curvature data are bounded above over `M`.

These are the genuine-curvature pointwise inputs that an order-`2` Gårding curvature `L²`
estimate consumes: the curvature contraction is controlled, fibrewise, by the fibre norm
of the differentiated tensor, with a base-point-independent constant on a compact manifold.

## Conventions

The bundled curvature operator is `riemannOp (tensorCov g r s)`, a continuous trilinear
form `T_x M × T_x M × T^{(r,s)}_x → T^{(r,s)}_x` (`CurvatureBundling.lean`). All norms are
the intrinsic Riemannian fibre norm `riemannianFiberNormSq` and the diamond-free model norm
of the fully-applied curvature value — never a bundle continuous-linear-map operator norm,
which is genuinely unbounded on multi-chart manifolds.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian
open Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- The generic canonical pointwise bound, repackaged so the bounding factor is a single
nonnegative scalar: for any `(r, s)`-tensor `T` at `x`, there is a nonnegative real `B` with
`riemannianFiberNormSq g r s x T ≤ ‖T‖² · B`. The witness bounding factor is a product of
nonnegative powers (the metric-inner operator norm and the ambient-frame norm sum), hence
nonnegative; we take `B` to be exactly that factor. -/
lemma exists_fiberNormSq_le_factor
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (T : TensorRSSpace r s I x) :
    ∃ B : ℝ, 0 ≤ B ∧
      riemannianFiberNormSq (I := I) (M := M) g r s x T ≤ ‖T‖ ^ 2 * B := by
  obtain ⟨Ab, hAb_nonneg, hbound⟩ :=
    riemannianFiberNormSq_le_pointwise_witness (I := I) (M := M) g r s x T
  refine ⟨_, ?_, hbound⟩
  refine mul_nonneg (pow_nonneg ?_ _) (pow_nonneg hAb_nonneg _)
  unfold metricInnerOpNorm
  exact norm_nonneg _

/-- The explicit nonnegative rank-`(r, s)` frame factor for the intrinsic fibre norm of a
fully-applied curvature value, packaged via `Classical.choose` from `exists_fiberNormSq_le_factor`. -/
noncomputable def curvValueFrameScalar
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v w : TangentSpace I x) (T : TensorRSSpace r s I x) : ℝ :=
  (exists_fiberNormSq_le_factor (I := I) (M := M) g r s x
    (riemannOp (tensorCov (I := I) g r s) x v w T)).choose

lemma curvValueFrameScalar_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v w : TangentSpace I x) (T : TensorRSSpace r s I x) :
    0 ≤ curvValueFrameScalar (I := I) (M := M) g r s x v w T :=
  (exists_fiberNormSq_le_factor (I := I) (M := M) g r s x
    (riemannOp (tensorCov (I := I) g r s) x v w T)).choose_spec.1

/-- **Canonical pointwise comparison at a curvature value.** For the bundled tensor
curvature operator `R := riemannOp (tensorCov g r s)`, tangent vectors `v, w` and an
`(r, s)`-tensor `T`, the intrinsic Riemannian fibre norm of the curvature value
`R_x(v, w) T` is bounded by the squared diamond-free model norm of that value times the
explicit nonnegative rank-`(r, s)` frame factor `curvValueFrameScalar`. This uses no bundle
operator norm. -/
theorem riemannOp_tensorCov_fiberNormSq_le_frameScalar
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v w : TangentSpace I x) (T : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x
        (riemannOp (tensorCov (I := I) g r s) x v w T) ≤
      ‖riemannOp (tensorCov (I := I) g r s) x v w T‖ ^ 2 *
        curvValueFrameScalar (I := I) (M := M) g r s x v w T :=
  (exists_fiberNormSq_le_factor (I := I) (M := M) g r s x
    (riemannOp (tensorCov (I := I) g r s) x v w T)).choose_spec.2

/-- The explicit per-point bounding scalar for the intrinsic fibre norm of the curvature
contraction applied to the fields `X, Y, Z` at `x`:
`‖R_x(X x, Y x)(Z x)‖² · curvValueFrameScalar(x)`. -/
noncomputable def curvContractionFiberNormBoundSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (Z : Π b : M, TensorRSSpace r s I b)
    (x : M) : ℝ :=
  ‖riemannOp (tensorCov (I := I) g r s) x (X x) (Y x) (Z x)‖ ^ 2 *
    curvValueFrameScalar (I := I) (M := M) g r s x (X x) (Y x) (Z x)

lemma curvContractionFiberNormBoundSq_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (Z : Π b : M, TensorRSSpace r s I b)
    (x : M) :
    0 ≤ curvContractionFiberNormBoundSq (I := I) (M := M) g r s X Y Z x := by
  unfold curvContractionFiberNormBoundSq
  exact mul_nonneg (sq_nonneg _)
    (curvValueFrameScalar_nonneg (I := I) (M := M) g r s x (X x) (Y x) (Z x))

/-- **Pointwise curvature-contraction bound.** For fixed fields `X, Y, Z`, the intrinsic
fibre norm squared of the curvature contraction at `x` is bounded by the explicit
per-point scalar `curvContractionFiberNormBoundSq`. -/
theorem riemannOp_tensorCov_fiberNormSq_le_boundSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (Z : Π b : M, TensorRSSpace r s I b)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r s x
        (riemannOp (tensorCov (I := I) g r s) x (X x) (Y x) (Z x)) ≤
      curvContractionFiberNormBoundSq (I := I) (M := M) g r s X Y Z x :=
  riemannOp_tensorCov_fiberNormSq_le_frameScalar (I := I) (M := M) g r s x
    (X x) (Y x) (Z x)

/-- **Uniform fibre-norm bound for the curvature contraction on a closed manifold.** Let `g`
be a smooth Riemannian metric on a closed manifold `M`, and fix smooth vector fields `X, Y`
and a tensor field `Z`. If the explicit per-point bounding scalar
`curvContractionFiberNormBoundSq g r s X Y Z` is bounded above over `M`, then there is a
single nonnegative constant `K` such that for every `x : M`,
`riemannianFiberNormSq g r s x (R_x(X x, Y x)(Z x)) ≤ K`. The constant `K` is the supremum
of the explicit per-point bounds; it is independent of `x`. -/
theorem exists_bound_riemannOp_tensorCov_fiberNormSq
    [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : Π b : M, TangentSpace I b) (Z : Π b : M, TensorRSSpace r s I b)
    (hbdd : BddAbove (Set.range
      (fun x : M => curvContractionFiberNormBoundSq (I := I) (M := M) g r s X Y Z x))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r s x
        (riemannOp (tensorCov (I := I) g r s) x (X x) (Y x) (Z x)) ≤ K := by
  classical
  set f : M → ℝ := fun x => curvContractionFiberNormBoundSq (I := I) (M := M) g r s X Y Z x
    with hf_def
  set K : ℝ := sSup (Set.range f) with hK_def
  have h_le_K : ∀ x : M, f x ≤ K := fun x => le_csSup hbdd (Set.mem_range_self x)
  refine ⟨K, ?_, ?_⟩
  · rcases isEmpty_or_nonempty M with hM | hM
    · have hrange : Set.range f = (∅ : Set ℝ) := by
        rw [Set.range_eq_empty_iff]; exact hM
      rw [hK_def, hrange, Real.sSup_empty]
    · obtain ⟨x₀⟩ := hM
      exact le_trans (curvContractionFiberNormBoundSq_nonneg (I := I) (M := M) g r s X Y Z x₀)
        (h_le_K x₀)
  · intro x
    exact le_trans
      (riemannOp_tensorCov_fiberNormSq_le_boundSq (I := I) (M := M) g r s X Y Z x)
      (h_le_K x)

end Connection
end Integral
end DifferentialGeometry

end
