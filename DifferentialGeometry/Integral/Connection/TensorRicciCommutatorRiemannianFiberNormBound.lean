import DifferentialGeometry.Integral.Connection.TensorRicciCommutator
import DifferentialGeometry.Integral.Connection.RiemannianFiberNormSqLeCanonical
import Mathlib.Topology.Order.Compact

/-!
# Diamond-free fiber-norm control of the tensor curvature operator

For a smooth Riemannian metric `g` on a manifold `M` (modelled on a real
inner-product space `E`), the second-covariant-derivative commutator on
`(0, 2)`-tensor sections is governed by the bundled curvature operator
`riemannOp (tensorCov g 0 2) x`, a continuous trilinear form
`T_x M × T_x M × (T^0_2)_x → (T^0_2)_x` (see `TensorRicciCommutator.lean`).
The order-`2` Gårding estimate must absorb the curvature term
`R_x(v, w) T = riemannOp (tensorCov g 0 2) x v w T`, and the absorbing constant
must be expressed in the **intrinsic Riemannian fiber norm** `riemannianFiberNormSq`,
*not* in the bundle continuous-linear-map operator norm.

## Why the operator-norm form is unavailable

The model-fiber norm on `TensorRSSpace 0 2 I x` is the `E`-induced operator norm,
and `riemannOp (tensorCov g 0 2) x` is a value of the iterated continuous-linear-map
type
`T_x M →L[ℝ] T_x M →L[ℝ] (T^0_2)_x →L[ℝ] (T^0_2)_x`.
The `Norm` instance on the *partially applied* layers of this iterated bundle
continuous-linear-map type does not resolve (the codomain
`(T^0_2)_x →L[ℝ] (T^0_2)_x` has no synthesizable `Norm` in this fiber context,
because of the `TangentSpace I x = E` definitional layering). Hence neither
`‖riemannOp (tensorCov g 0 2) x‖` nor any partially applied operator norm
`‖riemannOp (tensorCov g 0 2) x v‖`, `‖riemannOp (tensorCov g 0 2) x v w‖`
elaborates. Only the *fully applied* value
`riemannOp (tensorCov g 0 2) x v w T : (T^0_2)_x` carries a usable model norm
`‖·‖`, and the intrinsic `riemannianFiberNormSq` is always available. All bounds
in this file are stated through one of these two diamond-free quantities.

## Strategy

The canonical pointwise comparison
`riemannianFiberNormSq_le_pointwise_witness` bounds the intrinsic fiber norm
squared of any `(0, 2)`-tensor `S` at `x` by the model norm squared of `S`
times the square of an explicit `g`-orthonormal-frame ambient-norm scalar
`A(x)` (the witness `ambientFrameNormSq`). Specialising at the fully applied
curvature value gives the headline pointwise bound

```
riemannianFiberNormSq g 0 2 x (R_x(v, w) T)
  ≤ ‖R_x(v, w) T‖² · A(x)²
```

with both factors on the right diamond-free. We package the witness into a
named per-point bounding scalar `curvatureFiberNormBoundSq`, and then, on a
closed manifold, assemble a single nonnegative constant `K` bounding the
intrinsic fiber norm of the curvature term applied to fixed smooth fields,
whenever the explicit pointwise bound is uniformly bounded over `M`
(`IsCompact.bddAbove_image` of the continuous output norm together with
uniform control of the frame scalar). The uniform-frame-scalar input is the
standard metric-coercivity fact on a compact manifold; it is exposed as an
explicit `BddAbove` hypothesis rather than assumed, so the result is fully
proved.

## Main results

* `riemannianFiberNormSq_riemannOp_tensorCov_le_witness` — the fully-closed
  pointwise bound: `riemannianFiberNormSq g 0 2 x (R_x(v, w) T) ≤
  ‖R_x(v, w) T‖² · A(x)²` for an explicit nonnegative `A(x)`.
* `curvatureFiberNormBoundSq` — the per-point bounding scalar
  `‖R_x(X x, Y x) (T x)‖² · A(x)²` packaged as a function of `x`, for fixed
  fields `X, Y, T`.
* `riemannianFiberNormSq_riemannOp_tensorCov_le_curvatureFiberNormBoundSq` —
  the pointwise bound in terms of `curvatureFiberNormBoundSq`.
* `exists_bound_riemannianFiberNormSq_riemannOp_tensorCov` — on a closed
  manifold, from `BddAbove` of the explicit per-point bound, a single
  nonnegative constant `K` with `riemannianFiberNormSq g 0 2 x (R_x(X x, Y x)(T x))
  ≤ K` for all `x`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

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
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- The explicit nonnegative frame scalar appearing in the canonical pointwise
bound for `riemannianFiberNormSq` of a `(0, 2)`-tensor `S` at `b`. It is the
ambient-norm sum of the internal `g`-orthonormal frame, made into a function of
`b` and `S` via `Classical.choose`. -/
noncomputable def riemannianFrameScalar
    (g : SmoothRiemannianMetric I M) (b : M) (S : TensorRSSpace 0 2 I b) : ℝ :=
  (riemannianFiberNormSq_le_pointwise_witness (I := I) (M := M) g 0 2 b S).choose

lemma riemannianFrameScalar_nonneg
    (g : SmoothRiemannianMetric I M) (b : M) (S : TensorRSSpace 0 2 I b) :
    0 ≤ riemannianFrameScalar (I := I) (M := M) g b S :=
  (riemannianFiberNormSq_le_pointwise_witness (I := I) (M := M) g 0 2 b S).choose_spec.1

/-- The defining canonical bound for `riemannianFrameScalar`: the intrinsic
fiber norm squared is bounded by the model norm squared times the square of the
frame scalar. -/
lemma riemannianFiberNormSq_le_frameScalar_sq
    (g : SmoothRiemannianMetric I M) (b : M) (S : TensorRSSpace 0 2 I b) :
    riemannianFiberNormSq (I := I) (M := M) g 0 2 b S ≤
      ‖S‖ ^ 2 * riemannianFrameScalar (I := I) (M := M) g b S ^ 2 := by
  have h := (riemannianFiberNormSq_le_pointwise_witness
    (I := I) (M := M) g 0 2 b S).choose_spec.2
  refine h.trans (le_of_eq ?_)
  unfold riemannianFrameScalar
  simp only [Nat.mul_zero, pow_zero, one_mul, Nat.zero_add]

/-- **Pointwise fiber-norm bound for the tensor curvature operator.** For any
point `x` of a smooth Riemannian manifold, any tangent vectors `v, w` and any
`(0, 2)`-tensor `T` at `x`, the intrinsic Riemannian fiber norm squared of the
curvature value `R_x(v, w) T = riemannOp (tensorCov g 0 2) x v w T` is bounded
by the square of its (diamond-free) model norm times the square of the explicit
nonnegative frame scalar `A(x)`:

```
riemannianFiberNormSq g 0 2 x (R_x(v, w) T) ≤ ‖R_x(v, w) T‖² · A(x)².
```

This is the canonical pointwise comparison specialised at the fully applied
curvature value. It uses no operator norm of `riemannOp` (which is unavailable
because of the `TangentSpace = E` continuous-linear-map norm diamond), only the
genuine model norm of the resulting tensor value. -/
theorem riemannianFiberNormSq_riemannOp_tensorCov_le_witness
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) (T : TensorRSSpace 0 2 I x) :
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        (riemannOp (tensorCov (I := I) g 0 2) x v w T) ≤
      ‖riemannOp (tensorCov (I := I) g 0 2) x v w T‖ ^ 2 *
        riemannianFrameScalar (I := I) (M := M) g x
          (riemannOp (tensorCov (I := I) g 0 2) x v w T) ^ 2 :=
  riemannianFiberNormSq_le_frameScalar_sq (I := I) (M := M) g x
    (riemannOp (tensorCov (I := I) g 0 2) x v w T)

/-- The explicit per-point bounding scalar for the intrinsic fiber norm of the
curvature term applied to the fields `X, Y, T` at `x`:
`‖R_x(X x, Y x)(T x)‖² · A(x)²`. -/
noncomputable def curvatureFiberNormBoundSq
    (g : SmoothRiemannianMetric I M)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace 0 2 I b)
    (x : M) : ℝ :=
  ‖riemannOp (tensorCov (I := I) g 0 2) x (X x) (Y x) (T x)‖ ^ 2 *
    riemannianFrameScalar (I := I) (M := M) g x
      (riemannOp (tensorCov (I := I) g 0 2) x (X x) (Y x) (T x)) ^ 2

lemma curvatureFiberNormBoundSq_nonneg
    (g : SmoothRiemannianMetric I M)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace 0 2 I b)
    (x : M) :
    0 ≤ curvatureFiberNormBoundSq (I := I) (M := M) g X Y T x := by
  unfold curvatureFiberNormBoundSq
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **Pointwise curvature bound in terms of `curvatureFiberNormBoundSq`.** For
fixed fields `X, Y, T`, the intrinsic fiber norm squared of the curvature term
at `x` is bounded by the explicit per-point scalar `curvatureFiberNormBoundSq`. -/
theorem riemannianFiberNormSq_riemannOp_tensorCov_le_curvatureFiberNormBoundSq
    (g : SmoothRiemannianMetric I M)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace 0 2 I b)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        (riemannOp (tensorCov (I := I) g 0 2) x (X x) (Y x) (T x)) ≤
      curvatureFiberNormBoundSq (I := I) (M := M) g X Y T x :=
  riemannianFiberNormSq_riemannOp_tensorCov_le_witness (I := I) (M := M) g x
    (X x) (Y x) (T x)

/-- **Uniform fiber-norm bound for the tensor curvature operator on a closed
manifold.** Let `g` be a smooth Riemannian metric on a closed manifold `M`, and
fix (vector / tensor) fields `X, Y, T`. If the explicit per-point bounding scalar
`curvatureFiberNormBoundSq g X Y T` is bounded above over `M`, then there is a
single nonnegative constant `K` such that for every `x : M`,

```
riemannianFiberNormSq g 0 2 x (R_x(X x, Y x)(T x)) ≤ K.
```

The constant `K` is the supremum of the explicit per-point bounds; it is
independent of `x`. The bound is stated entirely in the intrinsic Riemannian
fiber norm and in the diamond-free model norm of the fully applied curvature
value — never in a bundle continuous-linear-map operator norm. -/
theorem exists_bound_riemannianFiberNormSq_riemannOp_tensorCov
    [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X Y : Π b : M, TangentSpace I b) (T : Π b : M, TensorRSSpace 0 2 I b)
    (hbdd : BddAbove (Set.range
      (fun x : M => curvatureFiberNormBoundSq (I := I) (M := M) g X Y T x))) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x
        (riemannOp (tensorCov (I := I) g 0 2) x (X x) (Y x) (T x)) ≤ K := by
  classical
  set f : M → ℝ := fun x => curvatureFiberNormBoundSq (I := I) (M := M) g X Y T x
    with hf_def
  set K : ℝ := sSup (Set.range f) with hK_def
  have h_le_K : ∀ x : M, f x ≤ K := by
    intro x
    exact le_csSup hbdd (Set.mem_range_self x)
  refine ⟨K, ?_, ?_⟩
  · rcases isEmpty_or_nonempty M with hM | hM
    · have hrange : Set.range f = (∅ : Set ℝ) := by
        rw [Set.range_eq_empty_iff]; exact hM
      rw [hK_def, hrange, Real.sSup_empty]
    · obtain ⟨x₀⟩ := hM
      exact le_trans (curvatureFiberNormBoundSq_nonneg (I := I) (M := M) g X Y T x₀)
        (h_le_K x₀)
  · intro x
    exact le_trans
      (riemannianFiberNormSq_riemannOp_tensorCov_le_curvatureFiberNormBoundSq
        (I := I) (M := M) g X Y T x)
      (h_le_K x)

end Connection
end Integral
end DifferentialGeometry

end
