import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedConvergence
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.TotalNabla0SLinear

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# The background covariant metric derivative as a linear iterated operator

`metricCovDeriv h gRef a` is the `a`-fold covariant derivative of the metric
tensor field of `h`, using the **fixed** Levi-Civita connection of the reference
metric `gRef`.  Because that connection does not depend on `h`, the operation
`A ↦ (∇^a A)` is a fixed `ℝ`-linear differential operator on covariant
`(0,2)`-tensor fields, and `metricCovDeriv h gRef a` is just this operator
applied to `metricTensorField h`.

This file makes that structure explicit:

* `covDerivOfField gRef A0 a` — the same iterated background covariant derivative
  applied to an *arbitrary* `(0,2)`-tensor field `A0` (not necessarily a metric).
  This is the object used to realize the `∇^p Rc` family in the MSM135 equation
  (3.4) evolution `∂_t (∇^p g) = -2 ∇^p Rc`.
* `metricCovDeriv_eq_covDerivOfField` — `metricCovDeriv h gRef a` is
  `covDerivOfField gRef (metricTensorField h) a`.
* `covDerivOfField_smul` — the iterated operator is scalar-homogeneous.  This is
  the algebraic backbone behind the constant `-2` factoring through every
  covariant-derivative step of the Ricci-flow metric evolution.
-/

noncomputable section

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology
open DifferentialGeometry.Integral.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]

/-- The `a`-fold background covariant derivative (Levi-Civita connection of
`gRef`) of an arbitrary covariant `(0,2)`-tensor field `A0`.  This reuses the
exact recursion of `metricCovDeriv`, but with an arbitrary base field instead of
a metric tensor field. -/
noncomputable def covDerivOfField
    (gRef : SmoothRiemannianMetric I M)
    (A0 :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2) :
    (a : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2) :=
  Nat.rec
    (motive := fun a : Nat =>
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2))
    A0
    (fun a A =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          metricCovDerivStep (I := I) gRef a A)

/-- Successor step of `covDerivOfField`. -/
theorem covDerivOfField_succ
    (gRef : SmoothRiemannianMetric I M)
    (A0 :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (a : Nat) :
    covDerivOfField (I := I) gRef A0 (a + 1)
      = metricCovDerivStep (I := I) gRef a (covDerivOfField (I := I) gRef A0 a) :=
  rfl

/-- Successor step of `metricCovDeriv`. -/
theorem metricCovDeriv_succ
    (h gRef : SmoothRiemannianMetric I M) (a : Nat) :
    metricCovDeriv (I := I) h gRef (a + 1)
      = metricCovDerivStep (I := I) gRef a (metricCovDeriv (I := I) h gRef a) :=
  rfl

/-- `metricCovDeriv` is the iterated background covariant derivative applied to
the metric tensor field. -/
theorem metricCovDeriv_eq_covDerivOfField
    (h gRef : SmoothRiemannianMetric I M) (a : Nat) :
    metricCovDeriv (I := I) h gRef a
      = covDerivOfField (I := I) gRef
          (Tensor0SBundle.metricTensorField (I := I) h) a :=
  rfl

/-- Evaluation of one covariant-derivative step as the total covariant
derivative `totalNabla0SFun`. -/
theorem metricCovDerivStep_apply
    (gRef : SmoothRiemannianMetric I M) (a : Nat)
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2))
    (x : M) :
    metricCovDerivStep (I := I) gRef a A x
      = Tensor0SBundle.totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (a + 2)
          (leviCivitaConnectionOfMetric (I := I) gRef) A x :=
  rfl

/-- Boundaryless-free smooth-slot recursion for one `metricCovDeriv` step.

This is the invariant evaluation formula for the successor tower: the leading
slot gives the scalar directional derivative of the previous tower level, and
the remaining terms are the usual connection corrections in the non-leading
slots. -/
theorem metricCovDeriv_succ_eval_smooth_slots_gen
    (h gRef : SmoothRiemannianMetric I M) (a : Nat)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (V : Fin (a + 2) -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    metricCovDeriv (I := I) h gRef (a + 1) x
        (Fin.cons (X x) (fun q : Fin (a + 2) => V q x)) =
      extDerivFun (I := I)
          (fun y : M => metricCovDeriv (I := I) h gRef a y
            (fun q : Fin (a + 2) => V q y)) x (X x) -
        ∑ p : Fin (a + 2),
          metricCovDeriv (I := I) h gRef a x
            (Function.update (fun q : Fin (a + 2) => V q x) p
              (((leviCivitaConnectionOfMetric (I := I) gRef)
                  (fun y : M => V p y) x) (X x))) := by
  rw [metricCovDeriv_succ, metricCovDerivStep_apply,
    Tensor0SBundle.totalNabla0SFun_apply_section]
  exact Tensor0SBundle.nabla0SFun_eval_smooth_slots
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (leviCivitaConnectionOfMetric (I := I) gRef) X V
    (metricCovDeriv (I := I) h gRef a) x

/-- One covariant-derivative step is scalar-homogeneous in the tensor field. -/
theorem metricCovDerivStep_smul
    (gRef : SmoothRiemannianMetric I M) (c : Real) (a : Nat)
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2)) :
    metricCovDerivStep (I := I) gRef a (c • A)
      = c • metricCovDerivStep (I := I) gRef a A := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [metricCovDerivStep_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
    metricCovDerivStep_apply, Tensor0SBundle.totalNabla0SFun_smul]

/-- The iterated background covariant derivative is scalar-homogeneous. -/
theorem covDerivOfField_smul
    (gRef : SmoothRiemannianMetric I M) (c : Real)
    (A0 :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (a : Nat) :
    covDerivOfField (I := I) gRef (c • A0) a
      = c • covDerivOfField (I := I) gRef A0 a := by
  induction a with
  | zero => rfl
  | succ n ih =>
      rw [covDerivOfField_succ, covDerivOfField_succ, ih, metricCovDerivStep_smul]

/-- One covariant-derivative step is additive in the tensor field. -/
theorem metricCovDerivStep_add
    (gRef : SmoothRiemannianMetric I M) (a : Nat)
    (A B :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 2)) :
    metricCovDerivStep (I := I) gRef a (A + B)
      = metricCovDerivStep (I := I) gRef a A + metricCovDerivStep (I := I) gRef a B := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [metricCovDerivStep_apply, ContMDiffSection.coe_add, Pi.add_apply,
    metricCovDerivStep_apply, metricCovDerivStep_apply,
    Tensor0SBundle.totalNabla0SFun_add]

/-- The iterated background covariant derivative is additive in the tensor field. -/
theorem covDerivOfField_add
    (gRef : SmoothRiemannianMetric I M)
    (A0 B0 :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (a : Nat) :
    covDerivOfField (I := I) gRef (A0 + B0) a
      = covDerivOfField (I := I) gRef A0 a + covDerivOfField (I := I) gRef B0 a := by
  induction a with
  | zero => rfl
  | succ n ih =>
      rw [covDerivOfField_succ, covDerivOfField_succ, covDerivOfField_succ, ih,
        metricCovDerivStep_add]

/-- The iterated background covariant derivative preserves differences in the
tensor field (additivity plus `(-1)`-homogeneity). -/
theorem covDerivOfField_sub
    (gRef : SmoothRiemannianMetric I M)
    (A0 B0 :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (a : Nat) :
    covDerivOfField (I := I) gRef (A0 - B0) a
      = covDerivOfField (I := I) gRef A0 a - covDerivOfField (I := I) gRef B0 a := by
  rw [sub_eq_add_neg, covDerivOfField_add, ← neg_one_smul Real B0,
    covDerivOfField_smul, neg_one_smul, ← sub_eq_add_neg]

/-- One background covariant-derivative step (Levi-Civita of `gRef`) on an
arbitrary-rank covariant tensor field.  Generalises `metricCovDerivStep`, which
fixes the input rank to `a + 2`, to any rank `s`.  This is the book's `∇` acting
on a tensor of any valence (needed for the telescoping `∇ᴺT = ∇_kᴺT + Σᵢ
∇^{N−i}(∇−∇_k)∇_k^{i−1}T`, whose intermediate terms have growing rank). -/
noncomputable def covStep
    (gRef : SmoothRiemannianMetric I M) (s : Nat)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1) := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  let cov :=
    DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef
  let hcov :
      CovariantDerivative.ContMDiffCovariantDerivativeLocally
        (I := I) (E := E) (M := M) cov (∞ : WithTop ℕ∞) := by
    simpa [cov] using
      DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) gRef
  let hreg :=
    Tensor0SBundle.totalNabla0S_reg (E := E) (H := H)
      (I := I) (M := M) s cov hcov A
  exact
    Tensor0SBundle.totalNabla0S (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) s cov A hreg

/-- Evaluation of `covStep` as the total covariant derivative. -/
@[simp] theorem covStep_apply
    (gRef : SmoothRiemannianMetric I M) (s : Nat)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    covStep (I := I) gRef s A x
      = Tensor0SBundle.totalNabla0SFun (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) s
          (DifferentialGeometry.Integral.Connection.leviCivitaConnectionOfMetric (I := I) gRef)
          A x :=
  rfl

/-- `covStep` is additive in the tensor field. -/
theorem covStep_add
    (gRef : SmoothRiemannianMetric I M) (s : Nat)
    (A B : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    covStep (I := I) gRef s (A + B)
      = covStep (I := I) gRef s A + covStep (I := I) gRef s B := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [covStep_apply, ContMDiffSection.coe_add, Pi.add_apply,
    covStep_apply, covStep_apply, Tensor0SBundle.totalNabla0SFun_add]

/-- The `a`-fold background covariant derivative (Levi-Civita of `gRef`) of an
arbitrary-rank covariant tensor field `A0`.  This is the book's `∇^a` on tensors
of any valence; `covDerivOfField gRef A0 a = iterCov gRef 2 A0 a` for `(0,2)`
fields. -/
noncomputable def iterCov
    (gRef : SmoothRiemannianMetric I M) (r : Nat)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) :
    (a : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (r + a) :=
  Nat.rec A0 (fun a A => covStep (I := I) gRef (r + a) A)

/-- Successor step of `iterCov`. -/
theorem iterCov_succ
    (gRef : SmoothRiemannianMetric I M) (r : Nat)
    (A0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r)
    (a : Nat) :
    iterCov (I := I) gRef r A0 (a + 1)
      = covStep (I := I) gRef (r + a) (iterCov (I := I) gRef r A0 a) :=
  rfl

/-- `iterCov` is additive in the base tensor field. -/
theorem iterCov_add
    (gRef : SmoothRiemannianMetric I M) (r : Nat)
    (A0 B0 : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r)
    (a : Nat) :
    iterCov (I := I) gRef r (A0 + B0) a
      = iterCov (I := I) gRef r A0 a + iterCov (I := I) gRef r B0 a := by
  induction a with
  | zero => rfl
  | succ n ih =>
      rw [iterCov_succ, iterCov_succ, iterCov_succ, ih, covStep_add]

/-- The single-step connection difference `(∇₁ − ∇₂)` acting on a covariant
tensor field, where `∇ⱼ` is the Levi-Civita connection of `gⱼ`.  This is the
book's `∇ − ∇_k`, a tensorial (algebraic) operator: the derivative parts cancel
and only the Christoffel difference `Γ₁ − Γ₂` remains. -/
noncomputable def diffStep
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (s + 1) :=
  covStep (I := I) g₁ s S - covStep (I := I) g₂ s S

/-- The telescoping accumulator `Σ_{i=1}^{N} ∇₁^{N−i}(∇₁−∇₂)∇₂^{i−1}T`, built
recursively so the rank is `r + N` at every stage with no index casts.  The
recursion `accum (N+1) = ∇₁(accum N) + (∇₁−∇₂)∇₂ᴺT` increments the outer
`∇₁`-power on every existing term and appends the new innermost term. -/
noncomputable def telescAccum
    (g₁ g₂ : SmoothRiemannianMetric I M) (r : Nat)
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) :
    (N : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (r + N)
  | 0 => 0
  | (N + 1) =>
      covStep (I := I) g₁ (r + N) (telescAccum g₁ g₂ r T N)
        + diffStep (I := I) g₁ g₂ (r + N) (iterCov (I := I) g₂ r T N)

/-- **The telescoping identity** (MSM135 chapter 3, the `∇ᴺT = ∇₂ᴺT + Σᵢ
∇₁^{N−i}(∇₁−∇₂)∇₂^{i−1}T` step): the `∇₁`-iterated derivative differs from the
`∇₂`-iterated derivative by the telescoping accumulator. -/
theorem iterCov_telescoping
    (g₁ g₂ : SmoothRiemannianMetric I M) (r : Nat)
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r)
    (N : Nat) :
    iterCov (I := I) g₁ r T N
      = iterCov (I := I) g₂ r T N + telescAccum (I := I) g₁ g₂ r T N := by
  induction N with
  | zero => exact (add_zero T).symm
  | succ n ih =>
      rw [iterCov_succ, ih, covStep_add, iterCov_succ (gRef := g₂)]
      simp only [telescAccum, diffStep]
      abel

end HCGCompactness

end DifferentialGeometry
