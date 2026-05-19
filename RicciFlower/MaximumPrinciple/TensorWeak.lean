import RicciFlower.Realized.Curvature
import RicciFlower.Realized.TensorOperators
import RicciFlower.Tensor.RSTensor.MetricCompatibility
import RicciFlower.Metric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

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

open Bundle Tensor0SBundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- A time-dependent covariant two-tensor field. -/
abbrev TwoTensorFamily : Type _ :=
  Real -> TwoTensorField (I := I) (M := M)

/-- A time-dependent vector field used for drift terms. -/
abbrev TimeDependentVectorField : Type _ :=
  Real -> (x : M) -> TangentSpace I x

/-- A time-dependent quadratic-form evaluation on tangent vectors. -/
abbrev TensorQuadraticFormFamily : Type _ :=
  Real -> (x : M) -> TangentSpace I x -> Real

/-- Supplied first covariant derivative tensors for a time-dependent two-tensor. -/
abbrev TensorNabla1Family : Type _ :=
  Real -> (x : M) ->
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x

/-- Supplied second covariant derivative tensors for a time-dependent two-tensor. -/
abbrev TensorNabla2Family : Type _ :=
  Real -> (x : M) ->
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 4 x

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

/-- A time-dependent smooth covariant two-tensor section. -/
abbrev TwoTensorSecFamily : Type _ :=
  Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) 2

/-- A time-dependent smooth covariant three-tensor section used as `∇S`. -/
abbrev TensorNabla1SecFamily : Type _ :=
  Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) 3

/-- A time-dependent smooth covariant four-tensor section used as `∇²S`. -/
abbrev TensorNabla2SecFamily : Type _ :=
  Real -> Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) 4

/-- Convert a section-backed two-tensor family to the pointwise quadratic-form
style used by the tensor WMP statement. -/
def twoTensorSecToFamily
    (S : TwoTensorSecFamily (I := I) (M := M)) :
    TwoTensorFamily (I := I) (M := M) :=
  fun t x v w => S t x (vec2 (I := I) v w)

@[simp]
theorem twoTensorSecToFamily_apply
    (S : TwoTensorSecFamily (I := I) (M := M))
    (t : Real) (x : M) (v w : TangentSpace I x) :
    twoTensorSecToFamily (I := I) (M := M) S t x v w =
      S t x (vec2 (I := I) v w) := by
  rfl

/-- Section-backed positive barrier.  This is the smooth-section version of
`tensorBarrierFamily`; it is used only as a producer bridge for spatial
covariant derivative data. -/
noncomputable def tensorBarrierSecFamily
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 : Real) :
    TwoTensorSecFamily (I := I) (M := M) :=
  fun t =>
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
    S t + (epsilon * (delta + t - t0)) •
      Tensor0SBundle.metricTensorField (I := I) (G t)

@[simp]
theorem tensorBarrierSec_apply
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (epsilon delta t0 t : Real) (x : M) (v w : TangentSpace I x) :
    twoTensorSecToFamily (I := I) (M := M)
        (tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0)
        t x v w =
      tensorBarrierFamily (I := I) (M := M) G
        (twoTensorSecToFamily (I := I) (M := M) S)
        epsilon delta t0 t x v w := by
  simp only [twoTensorSecToFamily, tensorBarrierSecFamily, tensorBarrierFamily,
    ContMDiffSection.coe_add, Pi.add_apply, ContMDiffSection.coe_smul,
    Pi.smul_apply]
  change
    (S t x (vec2 (I := I) v w) +
        (epsilon * (delta + t - t0)) *
          (Tensor0SBundle.metricTensorField (I := I) (G t) x)
            (vec2 (I := I) v w)) =
      S t x (vec2 (I := I) v w) +
        epsilon * (delta + t - t0) * (G t).inner x v w
  rw [Tensor0SBundle.metricTensorField_apply]
  have h0 : vec2 (I := I) v w 0 = v := by
    unfold vec2 Curvature.vec2
    simp
  have h1 : vec2 (I := I) v w 1 = w := by
    unfold vec2 Curvature.vec2
    norm_num
  rw [h0, h1]

/-- Spatial first and second covariant derivative realizations for a
section-backed two-tensor family. -/
structure TensorSpatialDerivs
    (cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (S : TwoTensorSecFamily (I := I) (M := M))
    (nablaS : TensorNabla1SecFamily (I := I) (M := M))
    (nabla2S : TensorNabla2SecFamily (I := I) (M := M)) : Prop where
  first :
    ∀ t : Real,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (cov t) (S t) (nablaS t)
  second :
    ∀ t : Real,
      TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        3 (cov t) (nablaS t) (nabla2S t)

/-- The section-backed barrier has the same spatial covariant derivative data
as `S`, because the metric addend has zero covariant derivative for a
metric-compatible connection. -/
theorem barrierDerivs
    [T2Space M]
    (cov : Real -> CovariantDerivative I E (TangentSpace I : M -> Type _))
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorSecFamily (I := I) (M := M))
    (nablaS : TensorNabla1SecFamily (I := I) (M := M))
    (nabla2S : TensorNabla2SecFamily (I := I) (M := M))
    (epsilon delta t0 : Real)
    (hmc : ∀ t : Real,
      RicciFlower.Connection.IsMetricCompatible (I := I) (cov t) (G t))
    (hS : TensorSpatialDerivs (I := I) (M := M) cov S nablaS nabla2S) :
    TensorSpatialDerivs (I := I) (M := M) cov
      (tensorBarrierSecFamily (I := I) (M := M) G S epsilon delta t0)
      nablaS nabla2S := by
  constructor
  · intro t
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2
    letI := tensor0SBundle_topology (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3
    have hmetric :
        TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 (cov t) (Tensor0SBundle.metricTensorField (I := I) (G t))
          (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            (n := (∞ : WithTop ℕ∞)) 3) :=
      Tensor0SBundle.zero_realizes_metric (I := I) (cov t) (G t) (hmc t)
    have hscaled :
        TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 (cov t)
          ((epsilon * (delta + t - t0)) •
            Tensor0SBundle.metricTensorField (I := I) (G t))
          ((epsilon * (delta + t - t0)) •
            (0 : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
              (n := (∞ : WithTop ℕ∞)) 3)) :=
      TotalNabla0SRealizes.smul (I := I) (M := M)
        (epsilon * (delta + t - t0)) hmetric
    have hadd := TotalNabla0SRealizes.add (I := I) (M := M)
      (hS.first t) hscaled
    simpa [tensorBarrierSecFamily] using hadd
  · intro t
    exact hS.second t

/-- Barrier sizes used in the final tensor-WMP epsilon limit. -/
def SmallBarrierEps (epsilon : Real) : Prop :=
  0 < epsilon ∧ epsilon ≤ 1

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

This records the concrete scalar-evaluation regularity and uniform small-barrier
reaction Lipschitz control needed by the barrier estimate.  The compact
first-null extraction and tensor heat-operator realization remain separate
frontiers.
-/
structure TensorBarrierRegularityOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (T : Real) : Prop where
  tensor_eval_continuous :
    ∀ x, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : Real => S t x v w) (Set.Icc 0 T)
  metric_eval_continuous :
    ∀ x, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : Real => (G t).inner x v w) (Set.Icc 0 T)
  barrier_eval_continuous :
    ∀ epsilon delta t0 : Real,
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      ∀ x, ∀ v w : TangentSpace I x,
        ContinuousOn
          (fun t : Real =>
            tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t x v w)
          (Set.Icc t0 (t0 + delta))
  metricGainControl :
    ∀ t0 : Real,
      t0 ∈ Set.Icc 0 T ->
      t0 < T ->
      ∃ delta0 : Real,
        0 < delta0 ∧ t0 + delta0 ≤ T ∧
          ∀ delta : Real,
            0 < delta ->
            delta ≤ delta0 ->
            ∀ epsilon : Real,
              SmallBarrierEps epsilon ->
              ∃ metricDeriv : TensorQuadraticFormFamily (I := I) (M := M),
                (∀ t, t ∈ Set.Icc t0 (t0 + delta) ->
                  ∀ x, ∀ v : TangentSpace I x,
                    HasDerivWithinAt (fun s : Real => (G s).inner x v v)
                      (metricDeriv t x v) (Set.Icc t0 (t0 + delta)) t) ∧
                (∀ t, t ∈ Set.Icc t0 (t0 + delta) ->
                  ∀ x, ∀ v : TangentSpace I x,
                    (epsilon / 2) * (G t).inner x v v ≤
                      epsilon * ((G t).inner x v v +
                        (delta + t - t0) * metricDeriv t x v))
  smallBarrierLip :
    ∀ delta0 t0 : Real,
      0 < delta0 ->
      Set.Icc t0 (t0 + delta0) ⊆ Set.Icc 0 T ->
      ∃ K : Real, 0 ≤ K ∧
        ∀ epsilon delta : Real,
          SmallBarrierEps epsilon ->
          0 < delta ->
          delta ≤ delta0 ->
          ∀ t, t ∈ Set.Icc t0 (t0 + delta) ->
            ∀ x, ∀ v : TangentSpace I x,
              |N t (G t) (S t) x v v -
                N t (G t)
                  (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
                  x v v| ≤
              K * |epsilon * (delta + t - t0) * (G t).inner x v v|

/--
Analytic predicate for the evaluated drifted parabolic supersolution
inequality.

The heat-with-drift term is evaluated by the direct tensor operator
`tensorHeatWithDrift2QuadMetricAt` from supplied first and second covariant
derivative tensors.
-/
def TensorParabolicInequalityWithDriftOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (nabla2S : TensorNabla2Family (I := I) (M := M))
    (nablaS : TensorNabla1Family (I := I) (M := M))
    (T : Real) : Prop :=
  ∃ timeDeriv : TensorQuadraticFormFamily (I := I) (M := M),
    (∀ t, t ∈ Set.Icc 0 T ->
      ∀ x, ∀ v : TangentSpace I x,
        HasDerivWithinAt
          (fun s : Real => S s x v v)
          (timeDeriv t x v)
          (Set.Icc 0 T) t) ∧
    (∀ t, t ∈ Set.Icc 0 T ->
      ∀ x, ∀ v : TangentSpace I x,
        tensorHeatWithDrift2QuadMetricAt (I := I) (G t) (X t)
            (nabla2S t x) (nablaS t x) v +
          N t (G t) (S t) x v v ≤ timeDeriv t x v)

/-- Strict evaluated drifted parabolic inequality for the positive barrier on a time set. -/
def TensorParabolicStrictInequalityWithDriftOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (nabla2S : TensorNabla2Family (I := I) (M := M))
    (nablaS : TensorNabla1Family (I := I) (M := M))
    (U : Set Real) : Prop :=
  ∃ timeDeriv : TensorQuadraticFormFamily (I := I) (M := M),
    (∀ t, t ∈ U ->
      ∀ x, ∀ v : TangentSpace I x,
        HasDerivWithinAt
          (fun s : Real => S s x v v)
          (timeDeriv t x v)
          U t) ∧
    (∀ t, t ∈ U ->
      ∀ x, ∀ v : TangentSpace I x,
        v ≠ 0 ->
        tensorHeatWithDrift2QuadMetricAt (I := I) (G t) (X t)
            (nabla2S t x) (nablaS t x) v +
          N t (G t) (S t) x v v < timeDeriv t x v)

/--
Local comparison estimates that turn the base parabolic inequality for `S`
into the strict parabolic inequality for the positive barrier.

The analytic work is concentrated in producing these estimates.  The order
argument consuming them is `strictBarrier_of_est` below.
-/
def TensorBarrierLocalEst
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (nabla2S : TensorNabla2Family (I := I) (M := M))
    (nablaS : TensorNabla1Family (I := I) (M := M))
    (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
    (nablaBarrier : TensorNabla1Family (I := I) (M := M))
    (epsilon delta t0 : Real)
    (U : Set Real)
    (timeDerivS timeDerivBarrier :
      TensorQuadraticFormFamily (I := I) (M := M)) : Prop :=
  (∀ t, t ∈ U ->
    ∀ x, ∀ v : TangentSpace I x,
      HasDerivWithinAt
        (fun s : Real =>
          tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 s x v v)
        (timeDerivBarrier t x v) U t) ∧
  (∀ t, t ∈ U ->
    ∀ x, ∀ v : TangentSpace I x,
      ∃ heatErr reactionErr metricGain : Real,
        timeDerivS t x v + metricGain ≤ timeDerivBarrier t x v ∧
        tensorHeatWithDrift2QuadMetricAt (I := I) (G t) (X t)
            (nabla2Barrier t x) (nablaBarrier t x) v ≤
          tensorHeatWithDrift2QuadMetricAt (I := I) (G t) (X t)
              (nabla2S t x) (nablaS t x) v + heatErr ∧
        N t (G t)
            (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
            x v v ≤
        N t (G t) (S t) x v v + reactionErr ∧
        (v ≠ 0 -> heatErr + reactionErr < metricGain))

/-- Reduced local estimate when the barrier spatial derivative tensors are the
same supplied tensors as for `S`.  The remaining analytic inputs are the
barrier time derivative, the positive metric gain, and the reaction error. -/
def BarrierLocalCore
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (epsilon delta t0 : Real)
    (U : Set Real)
    (timeDerivS timeDerivBarrier :
      TensorQuadraticFormFamily (I := I) (M := M)) : Prop :=
  (∀ t, t ∈ U ->
    ∀ x, ∀ v : TangentSpace I x,
      HasDerivWithinAt
        (fun s : Real =>
          tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 s x v v)
        (timeDerivBarrier t x v) U t) ∧
  (∀ t, t ∈ U ->
    ∀ x, ∀ v : TangentSpace I x,
      ∃ reactionErr metricGain : Real,
        timeDerivS t x v + metricGain ≤ timeDerivBarrier t x v ∧
        N t (G t)
            (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
            x v v ≤
        N t (G t) (S t) x v v + reactionErr ∧
        (v ≠ 0 -> reactionErr < metricGain))

/-- Product rule for the pointwise time derivative of the barrier quadratic
form.  The derivative of the metric quadratic form is still supplied by the
caller; this lemma only packages the affine barrier coefficient calculation. -/
theorem hasDerivWithinAt_barrier_quad
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {epsilon delta t0 t dS dg : Real} {U : Set Real}
    {x : M} {v : TangentSpace I x}
    (hS : HasDerivWithinAt (fun s : Real => S s x v v) dS U t)
    (hG : HasDerivWithinAt (fun s : Real => (G s).inner x v v) dg U t) :
    HasDerivWithinAt
      (fun s : Real =>
        tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 s x v v)
      (dS + epsilon * ((G t).inner x v v + (delta + t - t0) * dg))
      U t := by
  have hid : HasDerivWithinAt (fun s : Real => s) 1 U t := by
    simpa using (hasDerivWithinAt_id t U)
  have hlin : HasDerivWithinAt (fun s : Real => delta + s - t0) 1 U t := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      ((hid.const_add delta).sub_const t0)
  have hprod :
      HasDerivWithinAt
        (fun s : Real => (delta + s - t0) * (G s).inner x v v)
        ((G t).inner x v v + (delta + t - t0) * dg)
        U t := by
    have h := hlin.mul hG
    simpa [one_mul, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hmetric :
      HasDerivWithinAt
        (fun s : Real => epsilon * ((delta + s - t0) * (G s).inner x v v))
        (epsilon * ((G t).inner x v v + (delta + t - t0) * dg))
        U t := by
    exact hprod.const_mul epsilon
  have htotal := hS.add hmetric
  simpa [tensorBarrierFamily, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc] using htotal

/-- Build the reduced barrier core from the time derivatives of `S(t)(v,v)`
and `g(t)(v,v)`.  The remaining hypotheses are exactly the local gain,
reaction-error, and positive-margin estimates. -/
theorem barrierCore_deriv
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {epsilon delta t0 : Real} {U : Set Real}
    {timeDerivS metricDeriv reactionErr metricGain :
      TensorQuadraticFormFamily (I := I) (M := M)}
    (hS :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => S s x v v)
            (timeDerivS t x v) U t)
    (hG :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => (G s).inner x v v)
            (metricDeriv t x v) U t)
    (hGain :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          metricGain t x v ≤
            epsilon * ((G t).inner x v v +
              (delta + t - t0) * metricDeriv t x v))
    (hReaction :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          N t (G t)
              (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
              x v v ≤
            N t (G t) (S t) x v v + reactionErr t x v)
    (hMargin :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          v ≠ 0 -> reactionErr t x v < metricGain t x v) :
    BarrierLocalCore (I := I) (M := M) G S N epsilon delta t0 U
      timeDerivS
      (fun t x v =>
        timeDerivS t x v +
          epsilon * ((G t).inner x v v +
            (delta + t - t0) * metricDeriv t x v)) := by
  constructor
  · intro t ht x v
    exact hasDerivWithinAt_barrier_quad
      (I := I) (M := M) (hS t ht x v) (hG t ht x v)
  · intro t ht x v
    refine ⟨reactionErr t x v, metricGain t x v, ?_, hReaction t ht x v,
      hMargin t ht x v⟩
    have h := hGain t ht x v
    linarith

/-- Direct constructor for the reduced local barrier estimate from pointwise
time-derivative, reaction-error, and margin inequalities. -/
theorem barrierCore_of_pt
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {epsilon delta t0 : Real} {U : Set Real}
    {timeDerivS timeDerivBarrier :
      TensorQuadraticFormFamily (I := I) (M := M)}
    (reactionErr metricGain : TensorQuadraticFormFamily (I := I) (M := M))
    (hDerivB :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt
            (fun s : Real =>
              tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 s x v v)
            (timeDerivBarrier t x v) U t)
    (hTime :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          timeDerivS t x v + metricGain t x v ≤ timeDerivBarrier t x v)
    (hReaction :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          N t (G t)
              (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
              x v v ≤
            N t (G t) (S t) x v v + reactionErr t x v)
    (hMargin :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          v ≠ 0 -> reactionErr t x v < metricGain t x v) :
    BarrierLocalCore (I := I) (M := M) G S N epsilon delta t0 U
      timeDerivS timeDerivBarrier := by
  constructor
  · exact hDerivB
  · intro t ht x v
    exact ⟨reactionErr t x v, metricGain t x v,
      hTime t ht x v, hReaction t ht x v, hMargin t ht x v⟩

/-- If the metric barrier contributes no spatial heat-with-drift error, the
reduced time/reaction estimates produce the full local estimate expected by the
strict-barrier theorem. -/
theorem localEst_of_core
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real} {U : Set Real}
    {timeDerivS timeDerivBarrier :
      TensorQuadraticFormFamily (I := I) (M := M)}
    (hcore : BarrierLocalCore (I := I) (M := M) G S N epsilon delta t0 U
      timeDerivS timeDerivBarrier) :
    TensorBarrierLocalEst (I := I) (M := M) G S X N
      nabla2S nablaS nabla2S nablaS epsilon delta t0 U
      timeDerivS timeDerivBarrier := by
  constructor
  · exact hcore.1
  · intro t ht x v
    rcases hcore.2 t ht x v with
      ⟨reactionErr, metricGain, htime, hreaction, hmargin⟩
    refine ⟨0, reactionErr, metricGain, htime, ?_, hreaction, ?_⟩
    · linarith
    · intro hv
      have h := hmargin hv
      linarith

/-- Full local barrier estimate from pointwise time derivatives of `S` and
the metric quadratic form, when the metric barrier has already been eliminated
from the spatial heat term. -/
theorem localEst_deriv
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real} {U : Set Real}
    {timeDerivS metricDeriv reactionErr metricGain :
      TensorQuadraticFormFamily (I := I) (M := M)}
    (hS :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => S s x v v)
            (timeDerivS t x v) U t)
    (hG :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => (G s).inner x v v)
            (metricDeriv t x v) U t)
    (hGain :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          metricGain t x v ≤
            epsilon * ((G t).inner x v v +
              (delta + t - t0) * metricDeriv t x v))
    (hReaction :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          N t (G t)
              (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
              x v v ≤
            N t (G t) (S t) x v v + reactionErr t x v)
    (hMargin :
      ∀ t, t ∈ U ->
        ∀ x, ∀ v : TangentSpace I x,
          v ≠ 0 -> reactionErr t x v < metricGain t x v) :
    TensorBarrierLocalEst (I := I) (M := M) G S X N
      nabla2S nablaS nabla2S nablaS epsilon delta t0 U
      timeDerivS
      (fun t x v =>
        timeDerivS t x v +
          epsilon * ((G t).inner x v v +
            (delta + t - t0) * metricDeriv t x v)) :=
  localEst_of_core (I := I) (M := M)
    (barrierCore_deriv (I := I) (M := M)
      hS hG hGain hReaction hMargin)

theorem strictBarrier_of_derivEst
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 T : Real}
    (hsub : Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T)
    (hbase : TensorParabolicInequalityWithDriftOn (I := I) (M := M)
      G S X N nabla2S nablaS T)
    (metricDeriv reactionErr metricGain :
      TensorQuadraticFormFamily (I := I) (M := M))
    (hG :
      ∀ t, t ∈ Set.Icc t0 (t0 + delta) ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => (G s).inner x v v)
            (metricDeriv t x v) (Set.Icc t0 (t0 + delta)) t)
    (hGain :
      ∀ t, t ∈ Set.Icc t0 (t0 + delta) ->
        ∀ x, ∀ v : TangentSpace I x,
          metricGain t x v ≤
            epsilon * ((G t).inner x v v +
              (delta + t - t0) * metricDeriv t x v))
    (hReaction :
      ∀ t, t ∈ Set.Icc t0 (t0 + delta) ->
        ∀ x, ∀ v : TangentSpace I x,
          N t (G t)
              (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t)
              x v v ≤
            N t (G t) (S t) x v v + reactionErr t x v)
    (hMargin :
      ∀ t, t ∈ Set.Icc t0 (t0 + delta) ->
        ∀ x, ∀ v : TangentSpace I x,
          v ≠ 0 -> reactionErr t x v < metricGain t x v) :
    TensorParabolicStrictInequalityWithDriftOn (I := I) (M := M) G
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0) X N
      nabla2S nablaS (Set.Icc t0 (t0 + delta)) := by
  rcases hbase with ⟨timeDerivS, hSbase, hbase_ineq⟩
  let timeDerivBarrier : TensorQuadraticFormFamily (I := I) (M := M) :=
    fun t x v =>
      timeDerivS t x v +
        epsilon * ((G t).inner x v v +
          (delta + t - t0) * metricDeriv t x v)
  have hSlocal :
      ∀ t, t ∈ Set.Icc t0 (t0 + delta) ->
        ∀ x, ∀ v : TangentSpace I x,
          HasDerivWithinAt (fun s : Real => S s x v v)
            (timeDerivS t x v) (Set.Icc t0 (t0 + delta)) t := by
    intro t ht x v
    exact (hSbase t (hsub ht) x v).mono hsub
  have hest :
      TensorBarrierLocalEst (I := I) (M := M) G S X N
        nabla2S nablaS nabla2S nablaS epsilon delta t0
        (Set.Icc t0 (t0 + delta)) timeDerivS timeDerivBarrier :=
    localEst_deriv (I := I) (M := M)
      (G := G) (S := S) (X := X) (N := N)
      (nabla2S := nabla2S) (nablaS := nablaS)
      (epsilon := epsilon) (delta := delta) (t0 := t0)
      (U := Set.Icc t0 (t0 + delta))
      (timeDerivS := timeDerivS) (metricDeriv := metricDeriv)
      (reactionErr := reactionErr) (metricGain := metricGain)
      hSlocal hG hGain hReaction hMargin
  refine ⟨timeDerivBarrier, hest.1, ?_⟩
  intro t ht x v hv
  rcases hest.2 t ht x v with
    ⟨heatErr, reactionErr', metricGain', htime, hheat, hreaction, hmargin⟩
  have hbase_t := hbase_ineq t (hsub ht) x v
  have hmargin_t := hmargin hv
  linarith

theorem strictParabolic_of_est
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 T : Real} {U : Set Real}
    (hsub : U ⊆ Set.Icc 0 T)
    (hbase : TensorParabolicInequalityWithDriftOn (I := I) (M := M)
      G S X N nabla2S nablaS T)
    (hest : ∀ timeDerivS : TensorQuadraticFormFamily (I := I) (M := M),
      ∃ timeDerivBarrier : TensorQuadraticFormFamily (I := I) (M := M),
        TensorBarrierLocalEst (I := I) (M := M) G S X N
          nabla2S nablaS nabla2Barrier nablaBarrier epsilon delta t0 U
          timeDerivS timeDerivBarrier) :
    TensorParabolicStrictInequalityWithDriftOn (I := I) (M := M) G
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0) X N
      nabla2Barrier nablaBarrier U := by
  rcases hbase with ⟨timeDerivS, _hbase_deriv, hbase_ineq⟩
  rcases hest timeDerivS with ⟨timeDerivBarrier, hbarrier_deriv, hcompare⟩
  refine ⟨timeDerivBarrier, hbarrier_deriv, ?_⟩
  intro t ht x v hv
  rcases hcompare t ht x v with
    ⟨heatErr, reactionErr, metricGain, htime, hheat, hreaction, hmargin⟩
  have hbase_t := hbase_ineq t (hsub ht) x v
  have hmargin_t := hmargin hv
  linarith

/--
Data at the first point where the positive barrier develops a null vector.

The vector is normalized with respect to the metric at the first null time.
This is the shape supplied by compactness of the unit tangent bundle.
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
  unit : (G t1).inner x1 v v = 1
  nonnegative_until :
    ∀ t, t ∈ Set.Icc t0 t1 ->
      ∀ x, TwoTensorNonnegativeAt (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t) x
  null :
    tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t1 x1 v v = 0

/--
Compactness and continuity package for extracting the first null vector of the
positive tensor barrier.

This is the analytic unit-tangent-bundle compactness input: it should be
produced from compactness of `M`, compactness of the unit tangent bundle for the
metric at the first time, and continuity of the barrier quadratic form.
-/
structure TensorFirstNullCompactnessOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (epsilon delta t0 : Real) : Prop where
  firstNull_of_failure :
    (∀ x, TwoTensorPositiveDefiniteAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t0) x) ->
    (¬ TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0)
      (Set.Icc t0 (t0 + delta))) ->
    Nonempty (TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)

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
    (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
    (nablaBarrier : TensorNabla1Family (I := I) (M := M))
    (epsilon delta t0 : Real) : Prop :=
  TensorParabolicStrictInequalityWithDriftOn (I := I) (M := M) G
    (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0) X N
    nabla2Barrier nablaBarrier
    (Set.Icc t0 (t0 + delta))

theorem strictBarrier_of_est
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 T : Real}
    (hsub : Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T)
    (hbase : TensorParabolicInequalityWithDriftOn (I := I) (M := M)
      G S X N nabla2S nablaS T)
    (hest : ∀ timeDerivS : TensorQuadraticFormFamily (I := I) (M := M),
      ∃ timeDerivBarrier : TensorQuadraticFormFamily (I := I) (M := M),
        TensorBarrierLocalEst (I := I) (M := M) G S X N
          nabla2S nablaS nabla2Barrier nablaBarrier epsilon delta t0
          (Set.Icc t0 (t0 + delta)) timeDerivS timeDerivBarrier) :
    TensorBarrierStrictSupersolutionOn (I := I) (M := M) G S X N
      nabla2Barrier nablaBarrier epsilon delta t0 := by
  exact strictParabolic_of_est (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2S := nabla2S) (nablaS := nablaS)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    (epsilon := epsilon) (delta := delta) (t0 := t0) (T := T)
    (U := Set.Icc t0 (t0 + delta)) hsub hbase hest

/--
Uniform strict barrier supersolution on a fixed short slab for small barriers.

The time slab is fixed before `epsilon` varies over `0 < epsilon ≤ 1`.  This is
the mathematically usable local estimate for the final `epsilon -> 0` argument.
-/
def TensorBarrierUniformStrictOnSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (delta t0 : Real) : Prop :=
  ∀ epsilon : Real, SmallBarrierEps epsilon ->
    ∃ nabla2Barrier : TensorNabla2Family (I := I) (M := M),
    ∃ nablaBarrier : TensorNabla1Family (I := I) (M := M),
      TensorBarrierStrictSupersolutionOn (I := I) (M := M) G S X N
        nabla2Barrier nablaBarrier epsilon delta t0

/--
Scalar signs obtained by testing the tensor barrier on a locally parallel
extension of the first-null vector.

This is an existential `Prop`, rather than a `Prop` structure with `Real`
fields, because Lean does not generate projections for data fields in
proof-irrelevant structures.
-/
def TensorFirstNullScalarSigns
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (epsilon delta t0 : Real)
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0) : Prop :=
  ∃ timeDeriv laplacian drift reaction : Real,
    timeDeriv ≤ 0 ∧
    0 ≤ laplacian ∧
    drift = 0 ∧
    0 ≤ reaction ∧
    drift + reaction < timeDeriv - laplacian

/--
Uniform barrier nonnegativity on a fixed short slab for small barriers.

The time slab is fixed before `epsilon` varies over `0 < epsilon ≤ 1`; this is
the form needed for the local `epsilon -> 0` argument.
-/
def TensorBarrierUniformOnSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (delta t0 : Real) : Prop :=
  ∀ epsilon : Real, SmallBarrierEps epsilon ->
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0)
      (Set.Icc t0 (t0 + delta))

/--
On a fixed short slab, uniform nonnegativity of all small positive barriers
implies nonnegativity of the unperturbed tensor.
-/
theorem tensorBarrier_limit_on_fixed_slab
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {delta t0 : Real}
    (hdelta : 0 < delta)
    (hbarrier : TensorBarrierUniformOnSlab (I := I) (M := M) G S delta t0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) S
      (Set.Icc t0 (t0 + delta)) := by
  intro t ht x v
  let q : Real := S t x v v
  let c : Real := (delta + t - t0) * (G t).inner x v v
  have htime_nonneg : 0 ≤ delta + t - t0 := by
    have ht_sub : 0 ≤ t - t0 := sub_nonneg.mpr ht.1
    have hsum : 0 ≤ delta + (t - t0) :=
      add_nonneg (le_of_lt hdelta) ht_sub
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsum
  have hmetric_nonneg : 0 ≤ (G t).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact le_of_lt ((G t).pos x v hv)
  have hc_nonneg : 0 ≤ c := by
    simpa [c] using mul_nonneg htime_nonneg hmetric_nonneg
  have hforall : ∀ e : Real, 0 < e -> 0 ≤ q + e := by
    intro e he
    let eta : Real := min 1 (e / (c + 1))
    have hden_pos : 0 < c + 1 :=
      add_pos_of_nonneg_of_pos hc_nonneg zero_lt_one
    have hdiv_pos : 0 < e / (c + 1) :=
      div_pos he hden_pos
    have heta_pos : 0 < eta := by
      dsimp [eta]
      exact lt_min zero_lt_one hdiv_pos
    have heta_le_one : eta ≤ 1 := by
      dsimp [eta]
      exact min_le_left 1 (e / (c + 1))
    have heta_le_div : eta ≤ e / (c + 1) := by
      dsimp [eta]
      exact min_le_right 1 (e / (c + 1))
    have heta_small : SmallBarrierEps eta := ⟨heta_pos, heta_le_one⟩
    have hbar_eta :
        0 ≤
          tensorBarrierFamily (I := I) (M := M) G S eta delta t0 t x v v :=
      hbarrier eta heta_small t ht x v
    have hbar_q : 0 ≤ q + eta * c := by
      simpa [tensorBarrierFamily, q, c, mul_assoc] using hbar_eta
    have heta_nonneg : 0 ≤ eta := le_of_lt heta_pos
    have hcoeff_le : c ≤ c + 1 := le_add_of_nonneg_right zero_le_one
    have hprod_le : eta * c ≤ eta * (c + 1) :=
      mul_le_mul_of_nonneg_left hcoeff_le heta_nonneg
    have hden_ne : c + 1 ≠ 0 := ne_of_gt hden_pos
    have heta_mul_den_le : eta * (c + 1) ≤ e := by
      have hmul_le : eta * (c + 1) ≤ (e / (c + 1)) * (c + 1) :=
        mul_le_mul_of_nonneg_right heta_le_div (le_of_lt hden_pos)
      have hdiv_mul : (e / (c + 1)) * (c + 1) = e := by
        field_simp [hden_ne]
      simpa [hdiv_mul] using hmul_le
    have heta_c_le : eta * c ≤ e := by
      exact le_trans hprod_le heta_mul_den_le
    exact le_trans hbar_q (by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left heta_c_le q)
  have hq_nonneg : 0 ≤ q := le_of_forall_pos_le_add hforall
  simpa [q] using hq_nonneg

/--
Global finite-subinterval continuation for the tensor barrier.

The local input is already uniform in small `epsilon`; the fixed-slab epsilon
limit is therefore separated from the global reachability/closedness argument.
-/
def TensorBarrierLimitClosureOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (T : Real) : Prop :=
  TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S 0 ->
  (∀ t0 : Real, t0 ∈ Set.Icc 0 T -> t0 < T ->
    TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S t0 ->
    ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
      TensorBarrierUniformOnSlab (I := I) (M := M) G S delta t0) ->
  TwoTensorFamilyNonnegativeOn (I := I) (M := M) S (Set.Icc 0 T)

/--
Regularity package needed for Hamilton's tensor weak maximum principle.

The first field is a concrete algebraic side condition used by downstream
callers.  The remaining field intentionally names the analytic regularity
content still to be produced around the tensor heat-operator API: smoothness
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
  firstNullCompactness :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      TensorFirstNullCompactnessOn (I := I) (M := M) G S epsilon delta t0
  firstNullScalarSigns :
    ∀ epsilon delta t0 : Real,
      0 < epsilon ->
      0 < delta ->
      Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T ->
      ∀ (nabla2Barrier : TensorNabla2Family (I := I) (M := M))
        (nablaBarrier : TensorNabla1Family (I := I) (M := M)),
      (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
        G S X N nabla2Barrier nablaBarrier epsilon delta t0) ->
      (hnull : TensorNullEigenvectorCondition (I := I) (M := M)
        G N (Set.Icc t0 (t0 + delta))) ->
      (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0) ->
      TensorFirstNullScalarSigns (I := I) (M := M) G S X N epsilon delta t0 d
  barrierLimitClosure :
    TensorBarrierLimitClosureOn (I := I) (M := M) G S T

/-- Convert an absolute-value reaction estimate into the one-sided upper bound
needed in the strict-barrier local estimate. -/
private theorem reaction_bound_of_abs {a b R : Real}
    (h : |a - b| ≤ R) : b ≤ a + R := by
  have hnegR : -R ≤ -|a - b| := neg_le_neg h
  have hnegabs : -|a - b| ≤ a - b := neg_abs_le (a - b)
  have hle : -R ≤ a - b := le_trans hnegR hnegabs
  linarith

/-- The smallness condition `4 K delta < 1` makes the Lipschitz reaction error
smaller than the half-metric gain on nonzero tangent vectors. -/
private theorem reactionErr_lt_gain
    {K epsilon delta c g : Real}
    (hK : 0 ≤ K)
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta)
    (hc_nonneg : 0 ≤ c)
    (hc_le : c ≤ 2 * delta)
    (hsmall : 4 * K * delta < 1)
    (hg : 0 < g) :
    K * |epsilon * c * g| < (epsilon / 2) * g := by
  have harg_nonneg : 0 ≤ epsilon * c * g := by
    exact mul_nonneg (mul_nonneg (le_of_lt hepsilon) hc_nonneg) (le_of_lt hg)
  rw [abs_of_nonneg harg_nonneg]
  have hkc_le : K * c ≤ K * (2 * delta) :=
    mul_le_mul_of_nonneg_left hc_le hK
  have htwo : K * (2 * delta) < 1 / 2 := by
    nlinarith
  have hkc_lt : K * c < 1 / 2 := lt_of_le_of_lt hkc_le htwo
  have hepsg_pos : 0 < epsilon * g := mul_pos hepsilon hg
  have hmul := mul_lt_mul_of_pos_right hkc_lt hepsg_pos
  nlinarith

/-- Produce the strict-barrier constants and pointwise estimates from the
metric time-gain control and the uniform small-barrier reaction Lipschitz
bound. -/
theorem strictBarrierBounds
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {T t0 : Real}
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G S X N T)
    (ht0 : t0 ∈ Set.Icc 0 T)
    (ht0T : t0 < T)
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    (_hbase : TensorParabolicInequalityWithDriftOn (I := I) (M := M)
      G S X N nabla2S nablaS T) :
    ∃ delta0 K : Real,
      0 < delta0 ∧ 0 ≤ K ∧ t0 + delta0 ≤ T ∧
        ∀ delta : Real,
          0 < delta ->
          delta ≤ delta0 ->
          4 * K * delta < 1 ->
          ∀ epsilon : Real,
            SmallBarrierEps epsilon ->
            ∃ metricDeriv : TensorQuadraticFormFamily (I := I) (M := M),
            ∃ reactionErr : TensorQuadraticFormFamily (I := I) (M := M),
            ∃ metricGain : TensorQuadraticFormFamily (I := I) (M := M),
              (∀ t, t ∈ Set.Icc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  HasDerivWithinAt (fun s : Real => (G s).inner x v v)
                    (metricDeriv t x v) (Set.Icc t0 (t0 + delta)) t) ∧
              (∀ t, t ∈ Set.Icc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  metricGain t x v ≤
                    epsilon * ((G t).inner x v v +
                      (delta + t - t0) * metricDeriv t x v)) ∧
              (∀ t, t ∈ Set.Icc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  N t (G t)
                      (tensorBarrierFamily (I := I) (M := M)
                        G S epsilon delta t0 t) x v v ≤
                    N t (G t) (S t) x v v + reactionErr t x v) ∧
              (∀ t, t ∈ Set.Icc t0 (t0 + delta) ->
                ∀ x, ∀ v : TangentSpace I x,
                  v ≠ 0 -> reactionErr t x v < metricGain t x v) := by
  obtain ⟨delta0, hdelta0, hdelta0T, hmetric⟩ :=
    hreg.barrierRegularity.metricGainControl t0 ht0 ht0T
  have hsub0 : Set.Icc t0 (t0 + delta0) ⊆ Set.Icc 0 T := by
    intro t ht
    exact ⟨le_trans ht0.1 ht.1, le_trans ht.2 hdelta0T⟩
  obtain ⟨K, hK, hLip⟩ :=
    hreg.barrierRegularity.smallBarrierLip delta0 t0 hdelta0 hsub0
  refine ⟨delta0, K, hdelta0, hK, hdelta0T, ?_⟩
  intro delta hdelta hdelta_le hsmall epsilon hepsilon
  obtain ⟨metricDeriv, hmetric_deriv, hmetric_gain⟩ :=
    hmetric delta hdelta hdelta_le epsilon hepsilon
  let reactionErr : TensorQuadraticFormFamily (I := I) (M := M) :=
    fun t x v =>
      K * |epsilon * (delta + t - t0) * (G t).inner x v v|
  let metricGain : TensorQuadraticFormFamily (I := I) (M := M) :=
    fun t x v => (epsilon / 2) * (G t).inner x v v
  refine ⟨metricDeriv, reactionErr, metricGain, hmetric_deriv, ?_, ?_, ?_⟩
  · intro t ht x v
    exact hmetric_gain t ht x v
  · intro t ht x v
    have hLip_t := hLip epsilon delta hepsilon hdelta hdelta_le t ht x v
    dsimp [reactionErr]
    exact reaction_bound_of_abs (a := N t (G t) (S t) x v v)
      (b := N t (G t)
        (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t) x v v)
      hLip_t
  · intro t ht x v hv
    dsimp [reactionErr, metricGain]
    have htime_nonneg : 0 ≤ delta + t - t0 := by
      have ht_sub : 0 ≤ t - t0 := sub_nonneg.mpr ht.1
      have hsum : 0 ≤ delta + (t - t0) :=
        add_nonneg (le_of_lt hdelta) ht_sub
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsum
    have htime_le : delta + t - t0 ≤ 2 * delta := by
      have ht_le : t - t0 ≤ delta := by linarith [ht.2]
      linarith
    exact reactionErr_lt_gain (K := K) (epsilon := epsilon) (delta := delta)
      (c := delta + t - t0) (g := (G t).inner x v v)
      hK hepsilon.1 hdelta htime_nonneg htime_le hsmall ((G t).pos x v hv)

/--
Parabolic supersolution package for the drifted tensor inequality

`(partial_t - Delta) S >= X^k nabla_k S + N(S,g,t)`.

The evaluated inequality is kept as an analytic predicate in this first
interface pass, but its spatial part is the direct tensor heat-with-drift
operator evaluated on supplied first and second covariant derivative tensors.
-/
structure TensorParabolicSupersolutionWithDriftOn
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (X : TimeDependentVectorField (I := I) (M := M))
    (N : TwoTensorReaction (I := I) (M := M))
    (nabla2S : TensorNabla2Family (I := I) (M := M))
    (nablaS : TensorNabla1Family (I := I) (M := M))
    (T : Real) : Prop where
  evaluatedInequality :
    TensorParabolicInequalityWithDriftOn (I := I) (M := M) G S X N
      nabla2S nablaS T

/-! ## Barrier proof blocks -/

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

/-- Choose a short time step satisfying both slab containment and `4 K delta < 1`. -/
private theorem exists_small_delta
    {t0 T delta0 K : Real}
    (hroom : t0 < T)
    (hdelta0 : 0 < delta0)
    (hK : 0 ≤ K) :
    ∃ delta : Real,
      0 < delta ∧ delta ≤ delta0 ∧ t0 + delta ≤ T ∧ 4 * K * delta < 1 := by
  let delta : Real :=
    min (min (delta0 / 2) ((T - t0) / 2)) (1 / (4 * K + 1))
  have hdelta0_half_pos : 0 < delta0 / 2 := by positivity
  have hroom_half_pos : 0 < (T - t0) / 2 := by linarith
  have hden_pos : 0 < 4 * K + 1 := by nlinarith
  have hrecip_pos : 0 < 1 / (4 * K + 1) := by positivity
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact lt_min (lt_min hdelta0_half_pos hroom_half_pos) hrecip_pos
  have hdelta_le_half0 : delta ≤ delta0 / 2 := by
    dsimp [delta]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hdelta_le_room_half : delta ≤ (T - t0) / 2 := by
    dsimp [delta]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hdelta_le_recip : delta ≤ 1 / (4 * K + 1) := by
    dsimp [delta]
    exact min_le_right _ _
  have hdelta_le_delta0 : delta ≤ delta0 := by linarith
  have hdelta_le_room : delta ≤ T - t0 := by linarith
  have htime : t0 + delta ≤ T := by linarith
  have hcoef_nonneg : 0 ≤ 4 * K := by nlinarith
  have hmul_le :
      4 * K * delta ≤ 4 * K * (1 / (4 * K + 1)) := by
    exact mul_le_mul_of_nonneg_left hdelta_le_recip hcoef_nonneg
  have hfrac_lt : 4 * K * (1 / (4 * K + 1)) < 1 := by
    field_simp [hden_pos.ne']
    nlinarith
  have hstrict : 4 * K * delta < 1 := lt_of_le_of_lt hmul_le hfrac_lt
  exact Exists.intro delta
    (And.intro hdelta_pos
      (And.intro hdelta_le_delta0 (And.intro htime hstrict)))

/--
Step 2: the metric-variation and Lipschitz estimates make the barrier a strict
supersolution on a sufficiently short slab.
-/
theorem tensorBarrier_strict_supersolution
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {t0 T : Real}
    (ht0 : t0 ∈ Set.Icc 0 T)
    (ht0T : t0 < T)
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G S X N nabla2S nablaS T) :
    ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
      TensorBarrierUniformStrictOnSlab (I := I) (M := M) G S X N
        delta t0 := by
  obtain ⟨delta0, K, hdelta0, hK, _hdelta0T, hstrict_bounds⟩ :=
    strictBarrierBounds (I := I) (M := M)
      hreg ht0 ht0T hparabolic.evaluatedInequality
  obtain ⟨delta, hdelta, hdelta_le_delta0, hdeltaT, hsmall⟩ :=
    exists_small_delta (t0 := t0) (T := T) (delta0 := delta0) (K := K)
      ht0T hdelta0 hK
  refine ⟨delta, hdelta, hdeltaT, ?_⟩
  intro epsilon hepsilon
  obtain ⟨metricDeriv, reactionErr, metricGain,
      hmetric_deriv, hgain, hreaction, hmargin⟩ :=
    hstrict_bounds delta hdelta hdelta_le_delta0 hsmall epsilon hepsilon
  refine ⟨nabla2S, nablaS, ?_⟩
  have hsub : Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T := by
    intro t ht
    exact ⟨le_trans ht0.1 ht.1, le_trans ht.2 hdeltaT⟩
  exact strictBarrier_of_derivEst (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2S := nabla2S) (nablaS := nablaS)
    (epsilon := epsilon) (delta := delta) (t0 := t0) (T := T)
    hsub hparabolic.evaluatedInequality
    metricDeriv reactionErr metricGain hmetric_deriv hgain hreaction hmargin

/--
Step 3: if the barrier fails to stay positive, compactness gives first-null
data.
-/
theorem tensorBarrier_first_null_of_failure
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hcompact : TensorFirstNullCompactnessOn (I := I) (M := M)
      G S epsilon delta t0)
    (hinit_pos : ∀ x, TwoTensorPositiveDefiniteAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t0) x)
    (hfail : ¬ TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0)
      (Set.Icc t0 (t0 + delta))) :
    Nonempty (TensorFirstNullData (I := I) (M := M) G S epsilon delta t0) := by
  exact hcompact.firstNull_of_failure hinit_pos hfail

/--
Pure scalar order contradiction used at a first null vector.

Here `timeDeriv` is `partial_t phi`, `laplacian` is `Delta phi`, `drift`
is `X · nabla phi`, and `reaction` is the evaluated reaction term.
-/
private theorem firstNullOrder
    {timeDeriv laplacian drift reaction : Real}
    (htime : timeDeriv ≤ 0)
    (hlap : 0 ≤ laplacian)
    (hdrift : drift = 0)
    (hreaction : 0 ≤ reaction)
    (hstrict : drift + reaction < timeDeriv - laplacian) :
    False := by
  have hsource_nonneg : 0 ≤ drift + reaction := by
    simpa [hdrift] using hreaction
  have htarget_pos : 0 < timeDeriv - laplacian :=
    lt_of_le_of_lt hsource_nonneg hstrict
  have htarget_nonpos : timeDeriv - laplacian ≤ 0 := by
    simpa [sub_eq_add_neg] using add_nonpos htime (neg_nonpos.mpr hlap)
  exact (not_lt_of_ge htarget_nonpos) htarget_pos

/--
Step 4: evaluating the strict inequality at the first null vector contradicts
the scalar maximum-principle signs and the null-eigenvector condition.
-/
theorem tensor_first_null_contradiction
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2Barrier : TensorNabla2Family (I := I) (M := M)}
    {nablaBarrier : TensorNabla1Family (I := I) (M := M)}
    {epsilon delta t0 : Real}
    (hstrict : TensorBarrierStrictSupersolutionOn (I := I) (M := M)
      G S X N nabla2Barrier nablaBarrier epsilon delta t0)
    (_hnull : TensorNullEigenvectorCondition (I := I) (M := M) G
      N (Set.Icc t0 (t0 + delta)))
    (d : TensorFirstNullData (I := I) (M := M) G S epsilon delta t0)
    (hsigns : TensorFirstNullScalarSigns (I := I) (M := M)
      G S X N epsilon delta t0 d) :
    False := by
  rcases hstrict with ⟨timeDeriv, _hderiv, hstrict_eval⟩
  have ht1_mem_slab : d.t1 ∈ Set.Icc t0 (t0 + delta) :=
    ⟨le_of_lt d.t1_mem.1, d.t1_mem.2⟩
  have _hstrict_at_first_null :
      tensorHeatWithDrift2QuadMetricAt (I := I) (G d.t1) (X d.t1)
          (nabla2Barrier d.t1 d.x1) (nablaBarrier d.t1 d.x1) d.v +
        N d.t1 (G d.t1)
            (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
            d.x1 d.v d.v <
        timeDeriv d.t1 d.x1 d.v := by
    exact hstrict_eval d.t1 ht1_mem_slab d.x1 d.v d.v_ne_zero
  have ht1_mem_until : d.t1 ∈ Set.Icc t0 d.t1 :=
    ⟨le_of_lt d.t1_mem.1, le_rfl⟩
  have hbarrier_nonnegative :
      TwoTensorNonnegativeAt (I := I) (M := M)
        (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
        d.x1 :=
    d.nonnegative_until d.t1 ht1_mem_until d.x1
  have _hreaction_nonnegative :
      0 ≤
        N d.t1 (G d.t1)
          (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
          d.x1 d.v d.v := by
    exact _hnull d.t1 ht1_mem_slab
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 d.t1)
      d.x1 hbarrier_nonnegative d.v d.null
  rcases hsigns with
    ⟨timeDeriv, laplacian, drift, reaction,
      htime_nonpos, hlaplacian_nonneg, hdrift_zero, hreaction_nonneg, hstrict_ineq⟩
  exact firstNullOrder htime_nonpos hlaplacian_nonneg hdrift_zero
    hreaction_nonneg hstrict_ineq

/--
Step 5: the strict barrier remains nonnegative on the short slab.
-/
theorem tensorBarrier_nonnegative_on_short_slab
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {t0 T : Real}
    (ht0 : t0 ∈ Set.Icc 0 T)
    (ht0T : t0 < T)
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G S X N nabla2S nablaS T)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G
      N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S t0) :
    ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
      TensorBarrierUniformOnSlab (I := I) (M := M) G S delta t0 := by
  classical
  obtain ⟨delta, hdelta, hdeltaT, hstrict_uniform⟩ :=
    tensorBarrier_strict_supersolution (I := I) (M := M)
      (G := G) (S := S) (X := X) (N := N) ht0 ht0T hreg hparabolic
  refine ⟨delta, hdelta, hdeltaT, ?_⟩
  intro epsilon hepsilon
  obtain ⟨nabla2Barrier, nablaBarrier, hstrict⟩ :=
    hstrict_uniform epsilon hepsilon
  by_contra hfail
  have hinit_pos : ∀ x, TwoTensorPositiveDefiniteAt (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0 t0) x :=
    tensorBarrier_initial_positive (I := I) (M := M)
      (G := G) (S := S) hepsilon.1 hdelta hinit
  have hsub : Set.Icc t0 (t0 + delta) ⊆ Set.Icc 0 T := by
    intro t ht
    exact ⟨le_trans ht0.1 ht.1, le_trans ht.2 hdeltaT⟩
  have hcompact : TensorFirstNullCompactnessOn (I := I) (M := M)
      G S epsilon delta t0 :=
    hreg.firstNullCompactness epsilon delta t0 hepsilon.1 hdelta hsub
  obtain ⟨d⟩ :=
    tensorBarrier_first_null_of_failure (I := I) (M := M)
      (G := G) (S := S) (epsilon := epsilon) (delta := delta) (t0 := t0)
      hcompact hinit_pos hfail
  have hnull_slab : TensorNullEigenvectorCondition (I := I) (M := M) G
      N (Set.Icc t0 (t0 + delta)) := by
    intro t ht A x hA v hv
    exact hnull t (hsub ht) A x hA v hv
  exact tensor_first_null_contradiction (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N)
    (nabla2Barrier := nabla2Barrier) (nablaBarrier := nablaBarrier)
    hstrict hnull_slab d
    (hreg.firstNullScalarSigns epsilon delta t0 hepsilon.1 hdelta hsub
      nabla2Barrier nablaBarrier hstrict hnull_slab d)

/--
Step 6: iterate short slabs and let `epsilon -> 0`.
-/
theorem tensor_wmp_of_barrier_limit
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {T : Real}
    (_hT : 0 ≤ T)
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G S X N T)
    (hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G S X N nabla2S nablaS T)
    (hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) S (Set.Icc 0 T) := by
  exact hreg.barrierLimitClosure hinit
    (fun t0 ht0 ht0T hinit_t0 =>
      tensorBarrier_nonnegative_on_short_slab (I := I) (M := M)
        (G := G) (S := S) (X := X) (N := N)
        ht0 ht0T hreg hparabolic hnull hinit_t0)

/--
Hamilton's weak maximum principle for symmetric two-tensors.

The proof is routed through the named barrier blocks above.
-/
theorem hamilton_tensor_wmp
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {X : TimeDependentVectorField (I := I) (M := M)}
    {N : TwoTensorReaction (I := I) (M := M)}
    {nabla2S : TensorNabla2Family (I := I) (M := M)}
    {nablaS : TensorNabla1Family (I := I) (M := M)}
    {T : Real}
    (_hT : 0 ≤ T)
    (hreg : TensorWMPRegularityOn (I := I) (M := M) G S X N T)
    (_hparabolic : TensorParabolicSupersolutionWithDriftOn
      (I := I) (M := M) G S X N nabla2S nablaS T)
    (_hnull : TensorNullEigenvectorCondition (I := I) (M := M) G N (Set.Icc 0 T))
    (_hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S 0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) S (Set.Icc 0 T) := by
  exact tensor_wmp_of_barrier_limit (I := I) (M := M)
    (G := G) (S := S) (X := X) (N := N) _hT hreg _hparabolic _hnull _hinit

end

end Realized
end RicciFlower
