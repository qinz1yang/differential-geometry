import RicciFlower.Realized.Curvature
import RicciFlower.Metric.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false

/-!
# Hamilton Weak Maximum Principle For Symmetric Two-Tensors

This file records the RicciFlower-native interface for Hamilton's weak maximum
principle for symmetric two-tensors.  The analytic proof itself is kept as one
explicit frontier: it is the barrier and first-null-vector maximum-principle
argument, not a Ricci-algebra or curvature-identity issue.
-/

namespace RicciFlower
namespace Realized

noncomputable section

open Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A time-dependent covariant two-tensor field. -/
abbrev TwoTensorFamily : Type _ :=
  Real -> TwoTensorField (I := I) (M := M)

/-- A time-dependent vector field used for drift terms. -/
abbrev TimeDependentVectorField : Type _ :=
  Real -> (x : M) -> TangentSpace I x

/-- A fiberwise algebraic reaction term for the tensor maximum principle. -/
abbrev TwoTensorReaction : Type _ :=
  Real -> SmoothRiemannianMetric I M -> TwoTensorField (I := I) (M := M) ->
    TwoTensorField (I := I) (M := M)

/-- Pointwise symmetry of a covariant two-tensor. -/
def TwoTensorSymmetricAt (A : TwoTensorField (I := I) (M := M)) (x : M) : Prop :=
  ∀ X Y : TangentSpace I x, A x X Y = A x Y X

/-- Pointwise nonnegativity of a covariant two-tensor as a quadratic form. -/
def TwoTensorNonnegativeAt (A : TwoTensorField (I := I) (M := M)) (x : M) : Prop :=
  ∀ v : TangentSpace I x, 0 ≤ A x v v

/-- Pointwise positive definiteness of a covariant two-tensor as a quadratic form. -/
def TwoTensorPositiveDefiniteAt (A : TwoTensorField (I := I) (M := M)) (x : M) : Prop :=
  ∀ v : TangentSpace I x, v ≠ 0 -> 0 < A x v v

/-- Symmetry of a tensor family on a set of times. -/
def TwoTensorFamilySymmetricOn (S : TwoTensorFamily (I := I) (M := M))
    (U : Set Real) : Prop :=
  ∀ t, t ∈ U -> ∀ x, TwoTensorSymmetricAt (I := I) (M := M) (S t) x

/-- Nonnegativity of a tensor family on a set of times. -/
def TwoTensorFamilyNonnegativeOn (S : TwoTensorFamily (I := I) (M := M))
    (U : Set Real) : Prop :=
  ∀ t, t ∈ U -> ∀ x, TwoTensorNonnegativeAt (I := I) (M := M) (S t) x

/-- Nonnegativity of a tensor family at one time. -/
def TwoTensorFamilyNonnegativeAtTime (S : TwoTensorFamily (I := I) (M := M))
    (t : Real) : Prop :=
  ∀ x, TwoTensorNonnegativeAt (I := I) (M := M) (S t) x

/--
Hamilton's positive barrier
`S_epsilon = S + epsilon * (delta + t - t0) * g`.
-/
def tensorBarrierFamily
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) : TwoTensorFamily (I := I) (M := M) :=
  fun t x v w => S t x v w + epsilon * (delta + t - t0) * (G t).inner x v w

@[simp] theorem tensorBarrierFamily_apply
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (x : M) (v w : TangentSpace I x) :
    tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t x v w =
      S t x v w + epsilon * (delta + t - t0) * (G t).inner x v w := by
  rfl

/--
Hamilton's null-eigenvector condition for the reaction term.

At each point, whenever any symmetric two-tensor input is nonnegative and has a
null vector, the reaction term is nonnegative on that null vector.  This
reaction-wide shape is needed because Hamilton's barrier argument applies the
condition to `S_epsilon`, not only to the original tensor family.
-/
def TensorNullEigenvectorCondition
    (G : Real -> SmoothRiemannianMetric I M)
    (N : TwoTensorReaction (I := I) (M := M))
    (U : Set Real) : Prop :=
  ∀ t, t ∈ U -> ∀ A : TwoTensorField (I := I) (M := M), ∀ x,
    TwoTensorNonnegativeAt (I := I) (M := M) A x ->
    ∀ v : TangentSpace I x,
      A x v v = 0 ->
      0 ≤ N t (G t) A x v v

/--
Analytic regularity predicate for the tensor WMP barrier argument.

Future producer work should replace this placeholder by concrete smoothness and
compactness hypotheses for the tensor, metric, drift, and reaction data.
-/
def TensorBarrierRegularityOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (T : Real) : Prop :=
  True

/--
Analytic predicate for the evaluated drifted parabolic supersolution
inequality.

This is the hook for a future tensor heat-operator realization of
`(partial_t - Delta) S >= X^k nabla_k S + N(S,g,t)`.
-/
def TensorParabolicInequalityWithDriftOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (T : Real) : Prop :=
  True

/--
Regularity package needed for Hamilton's tensor weak maximum principle.

The first field is a concrete algebraic side condition used by downstream
callers.  The remaining field intentionally names the analytic regularity
content still to be produced from a future tensor heat-operator API: smoothness
on compact slabs, compact first-null setup, and the local barrier estimates.
-/
structure TensorWMPRegularityOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (T : Real) : Prop where
  symmetric : TwoTensorFamilySymmetricOn (I := I) (M := M) S (Set.Icc 0 T)
  barrierRegularity :
    TensorBarrierRegularityOn (I := I) (M := M) G S X N T

/--
Parabolic supersolution package for the drifted tensor inequality

`(partial_t - Delta) S >= X^k nabla_k S + N(S,g,t)`.

The evaluated inequality is kept as an analytic predicate in this first
interface pass, because RicciFlower does not yet have the full tensor
heat-operator realization needed to state it intrinsically.
-/
structure TensorParabolicSupersolutionWithDriftOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (T : Real) : Prop where
  evaluatedInequality :
    TensorParabolicInequalityWithDriftOn (I := I) (M := M) G S X N T

/-! ## Barrier proof blocks -/

/--
The strict barrier supersolution inequality produced after adding
`epsilon * (delta + t - t0) * g`.

This is the named target for the estimate that absorbs metric variation and
the local Lipschitz error in `N`.
-/
def TensorBarrierStrictSupersolutionOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (epsilon delta t0 : Real) : Prop :=
  TensorParabolicInequalityWithDriftOn (I := I) (M := M) G
    (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0) X N (t0 + delta)

/--
Data at the first point where the positive barrier develops a null vector.
-/
structure TensorFirstNullData
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) : Type _ where
  t1 : Real
  x1 : M
  v : TangentSpace I x1
  t1_mem : t1 ∈ Set.Ioc t0 (t0 + delta)
  v_ne_zero : v ≠ 0
  nonnegative_until :
    ∀ t, t ∈ Set.Icc t0 t1 ->
      ∀ x, TwoTensorNonnegativeAt (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t) x
  null :
    tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t1 x1 v v = 0

/--
Step 1: the barrier is initially positive definite.

This is the `S_epsilon(t0) = S(t0) + epsilon * delta * g(t0)` step.
-/
theorem tensorBarrier_initial_positive
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta)
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S t0) :
    ∀ x, TwoTensorPositiveDefiniteAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t0) x := by
  intro x v hv
  have hS : 0 ≤ S t0 x v v := hinit x v
  have hmetric : 0 < (G t0).inner x v v := (G t0).pos x v hv
  have hcoeff : 0 < epsilon * (delta + t0 - t0) := by
    have htime : delta + t0 - t0 = delta := by ring
    rw [htime]
    exact mul_pos hepsilon hdelta
  have hbarrier : 0 < epsilon * (delta + t0 - t0) * (G t0).inner x v v :=
    mul_pos hcoeff hmetric
  exact add_pos_of_nonneg_of_pos hS hbarrier

/--
Step 2: the metric-variation and Lipschitz estimates make the barrier a strict
supersolution on a short slab.
-/
theorem tensorBarrier_strict_supersolution
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {epsilon delta t0 T : Real}
    (_hepsilon : 0 < epsilon)
    (_hdelta : 0 < delta)
    (_hT : t0 + delta ≤ T)
    (_hreg : TensorWMPRegularityOn (I := I) (M := M) G S X N T)
    (_hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G S X N T) :
    TensorBarrierStrictSupersolutionOn (I := I) (M := M) G S X N
      epsilon delta t0 := by
  -- Frontier block: barrier differential inequality.
  sorry

/--
Step 3: if the barrier fails to stay positive, compactness gives first-null
data.
-/
theorem tensorBarrier_first_null_of_failure
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (_hinit_pos : ∀ x, TwoTensorPositiveDefiniteAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t0) x)
    (_hfail : ¬ TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0)
      (Set.Icc t0 (t0 + delta))) :
    Nonempty (TensorFirstNullData (I := I) (M := M) G S epsilon delta t0) := by
  -- Frontier block: compact first-null-vector extraction.
  sorry

/--
Step 4: evaluating the strict inequality at the first null vector contradicts
the scalar maximum-principle signs and the null-eigenvector condition.
-/
theorem tensor_first_null_contradiction
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (_hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N epsilon delta t0)
    (_hnull : TensorNullEigenvectorCondition (I := I) (M := M) G
      N (Set.Icc t0 (t0 + delta)))
    (_d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0) :
    False := by
  -- Frontier block: first-null scalar test-function contradiction.
  sorry

/--
Step 5: the strict barrier remains nonnegative on the short slab.
-/
theorem tensorBarrier_nonnegative_on_short_slab
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {epsilon delta t0 T : Real}
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta)
    (hT : t0 + delta ≤ T)
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G S X N T)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G
      N (Set.Icc t0 (t0 + delta)))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S t0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0)
      (Set.Icc t0 (t0 + delta)) := by
  classical
  by_contra hfail
  have hinit_pos : ∀ x, TwoTensorPositiveDefiniteAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t0) x :=
    tensorBarrier_initial_positive (I := I) (M := M)
      (G := G) (S := S) hepsilon hdelta hinit
  obtain ⟨d⟩ :=
    tensorBarrier_first_null_of_failure (I := I) (M := M)
      (G := G) (S := S) (epsilon := epsilon) (delta := delta) (t0 := t0)
      hinit_pos hfail
  have hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N epsilon delta t0 :=
    tensorBarrier_strict_supersolution (I := I) (M := M)
      (G := G) (S := S) (X := X) (N := N) hepsilon hdelta hT hreg hparabolic
  exact tensor_first_null_contradiction (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N) hstrict hnull d

/--
Step 6: iterate short slabs and let `epsilon -> 0`.
-/
theorem tensor_wmp_of_barrier_limit
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (_hT : 0 ≤ T)
    (_hreg : TensorWMPRegularityOn (I := I) (M := M) G S X N T)
    (_hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G S X N T)
    (_hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (_hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) S (Set.Icc 0 T) := by
  -- Frontier block: finite subinterval iteration and epsilon-limit closure.
  sorry

/--
Hamilton's weak maximum principle for symmetric two-tensors.

The proof is routed through the named barrier blocks above.
-/
theorem hamilton_tensor_wmp
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T : Real}
    (_hT : 0 ≤ T)
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G S X N T)
    (_hparabolic : TensorParabolicSupersolutionWithDriftOn (I := I) (M := M) G S X N T)
    (_hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (_hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) S (Set.Icc 0 T) := by
  exact tensor_wmp_of_barrier_limit (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N) _hT hreg _hparabolic _hnull _hinit

end

end Realized
end RicciFlower
