import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.PointedConvergence
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.TotalNabla0SLinear
import DifferentialGeometry.Geometry.Metric.SmoothVectorFieldExtGlobal
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini

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
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M] [BoundarylessManifold I M]

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

/-- `covStep` is scalar-homogeneous in the tensor field. -/
theorem covStep_smul
    (gRef : SmoothRiemannianMetric I M) (c : Real) (s : Nat)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    covStep (I := I) gRef s (c • A)
      = c • covStep (I := I) gRef s A := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [covStep_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
    covStep_apply, Tensor0SBundle.totalNabla0SFun_smul]

/-- `covStep` preserves differences in the tensor field (additivity plus
`(-1)`-homogeneity).  This is the linearity fact behind the connection-difference
splitting `covStep g₂ (∇^{g₁}S − ∇^{g₂}S)`. -/
theorem covStep_sub
    (gRef : SmoothRiemannianMetric I M) (s : Nat)
    (A B : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    covStep (I := I) gRef s (A - B)
      = covStep (I := I) gRef s A - covStep (I := I) gRef s B := by
  rw [sub_eq_add_neg, covStep_add, ← neg_one_smul Real B,
    covStep_smul, neg_one_smul, ← sub_eq_add_neg]

/-- **Boundaryless-free smooth-slot recursion for one `covStep`** (generic rank).
The `covStep` analogue of `metricCovDeriv_succ_eval_smooth_slots_gen`: evaluating
`covStep g₂ r A` on `Fin.cons (X x) (V · x)` gives the leading scalar directional
derivative of `y ↦ A y (V · y)` minus the Levi-Civita connection corrections in the
non-leading slots.  This is the outer expansion gate for the base-Leibniz identity. -/
theorem covStep_eval_smooth_slots
    (g₂ : SmoothRiemannianMetric I M) (r : Nat)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin r -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    covStep (I := I) g₂ r A x (Fin.cons (X x) (fun q : Fin r => V q x))
      = extDerivFun (I := I)
          (fun y : M => A y (fun q : Fin r => V q y)) x (X x) -
        ∑ q : Fin r,
          A x (Function.update (fun b : Fin r => V b x) q
            (((leviCivitaConnectionOfMetric (I := I) g₂)
                (fun y : M => V q y) x) (X x))) := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  rw [covStep_apply, Tensor0SBundle.totalNabla0SFun_apply_section]
  exact Tensor0SBundle.nabla0SFun_eval_smooth_slots
    (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (leviCivitaConnectionOfMetric (I := I) g₂) X V A x

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

/-- **Generic-rank evaluation of the connection-difference step** (`diffStep_apply`).

Contracting the single-step connection difference `diffStep g₁ g₂ s S = ∇^{g₁}S − ∇^{g₂}S`
against a smooth vector field `X` in the leading (derivative) slot and smooth vector fields
`V` in the remaining `s` slots gives the tensorial Christoffel-difference slot sum: the
derivative parts cancel and only `Γ₁ − Γ₂ = CovariantDerivative.difference (LC g₁) (LC g₂)`
survives, inserted into each lower slot.  This is the generic-`(0,s)` lift of
`Tensor0SBundle.nabla0SFun_sub_cov` to the bundled tensor field, evaluated where the
tensor-bundle model instances at rank `s+1` are in scope (this file carries
`backward.isDefEq.respectTransparency false`, which lets `totalNabla0SFun_apply_section`
elaborate at the variable rank `s+1`).  It is the evaluation gate of brick T's norm layer:
the norm atom bounding `normSq0S (diffStep g₁ g₂ s S x)` expands the fibre norm through this
identity. -/
theorem diffStep_apply
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (V : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    diffStep (I := I) g₁ g₂ s S x
        (Fin.cons (X x) (fun q : Fin s => V q x)) =
      -∑ a : Fin s,
        (S x)
          (Function.update (fun b : Fin s => V b x) a
            (((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x) (V a x)) (X x))) := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  have hsec : diffStep (I := I) g₁ g₂ s S x =
      covStep (I := I) g₁ s S x - covStep (I := I) g₂ s S x := by
    change (covStep (I := I) g₁ s S - covStep (I := I) g₂ s S) x = _
    rw [ContMDiffSection.coe_sub, Pi.sub_apply]
  rw [hsec]
  change (covStep (I := I) g₁ s S x) (Fin.cons (X x) (fun q : Fin s => V q x))
      - (covStep (I := I) g₂ s S x) (Fin.cons (X x) (fun q : Fin s => V q x)) = _
  rw [covStep_apply, covStep_apply,
    Tensor0SBundle.totalNabla0SFun_apply_section,
    Tensor0SBundle.totalNabla0SFun_apply_section]
  exact Tensor0SBundle.nabla0SFun_sub_cov (I := I)
    (leviCivitaConnectionOfMetric (I := I) g₁)
    (leviCivitaConnectionOfMetric (I := I) g₂) X V S x

/-- **Pointwise evaluation of the connection-difference step on arbitrary tangent vectors.**

The pointwise companion of `diffStep_apply`: it drops the smooth-section hypotheses, evaluating
`diffStep g₁ g₂ s S x` on any leading (derivative-slot) vector `v` and any lower-slot tuple
`slots`.  Every tangent vector at `x` is the value of a global smooth vector field
(`Geometry.Riemannian.exists_contMDiff_vectorField_eq`, needing `[T2Space M]`), and the
Christoffel-difference slot sum on the right depends only on those values, so the
section-level identity `diffStep_apply` transfers verbatim.  This is the form consumed by the
component / fibre-norm expansion of `normSq0S (diffStep g₁ g₂ s S x)`: each `component0S` is an
evaluation of `diffStep g₁ g₂ s S x` on a tuple of basis vectors. -/
theorem diffStep_eval
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (x : M) (v : TangentSpace I x) (slots : Fin s -> TangentSpace I x) :
    diffStep (I := I) g₁ g₂ s S x (Fin.cons v slots) =
      -∑ a : Fin s,
        (S x)
          (Function.update slots a
            (((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x) (slots a)) v)) := by
  classical
  obtain ⟨Xf, hXsm, hXv⟩ :=
    Geometry.Riemannian.exists_contMDiff_vectorField_eq (I := I) x v
  choose Vf hVsm hVv using fun a : Fin s =>
    Geometry.Riemannian.exists_contMDiff_vectorField_eq (I := I) x (slots a)
  have key := diffStep_apply (I := I) g₁ g₂ s S
    (ContMDiffSection.mk Xf hXsm)
    (fun a : Fin s => ContMDiffSection.mk (Vf a) (hVsm a)) x
  simp only [ContMDiffSection.coeFn_mk, hXv, hVv] at key
  exact key

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

/-- **The base-connection Leibniz split of the connection-difference step**
(brick T-B, committed-currency form).  Differentiating the single-step connection
difference `diffStep g₁ g₂ s S = ∇^{g₁}S − ∇^{g₂}S` once more with the *base*
connection `∇^{g₂}` splits, by the tensor-derivation (product) rule
`∇^{g₂}(A ⋆ S) = (∇^{g₂}A) ⋆ S + A ⋆ (∇^{g₂}S)` where
`A = Γ₁ − Γ₂ = connectionDifferenceTensorAt (LC g₁)(LC g₂)`, into

* the **`A ⋆ (∇^{g₂}S)` term**, realized in committed currency as the connection
  difference of the base derivative `diffStep g₁ g₂ (s+1) (covStep g₂ s S)`, and
* the **`(∇^{g₂}A) ⋆ S` term**, realized as the *mixed second-derivative
  commutator* `∇^{g₂}∇^{g₁}S − ∇^{g₁}∇^{g₂}S = covStep g₂ (covStep g₁ S)
  − covStep g₁ (covStep g₂ S)` (whose second-order-in-`S` symbols cancel, leaving
  a first-order-in-`S`, one-more-jet-of-`A` object).

The identity itself is pure operator algebra (`covStep` additivity and the
`diffStep` definition); it does not require materialising `∇^{g₂}A` as a mixed
`(1,3)` tensor.  It is the algebraic backbone of the all-`∇^{g₂}` telescoping
schematic: the first term feeds directly into the base-derivative norm recursion
(bounded by `diffStep_jet_one_le` applied to `covStep g₂ s S`), and the mixed
commutator isolates the single remaining jet-of-`A` frontier. -/
theorem diffStep_leibniz
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s) :
    covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S)
      = diffStep (I := I) g₁ g₂ (s + 1) (covStep (I := I) g₂ s S)
        + (covStep (I := I) g₂ (s + 1) (covStep (I := I) g₁ s S)
            - covStep (I := I) g₁ (s + 1) (covStep (I := I) g₂ s S)) := by
  simp only [diffStep]
  rw [covStep_sub]
  abel

/-- **Base-connection splitting of one `iterCov` step.**  One further `∇^{g₁}`
derivative of the `g₁`-iterated tower is the *base* `∇^{g₂}` derivative plus the
single-step connection difference, both applied to `iterCov g₁ r T N`:
`∇^{g₁} W = ∇^{g₂} W + (∇^{g₁} − ∇^{g₂}) W`.  This is the recursion driver for the
all-`∇^{g₂}` telescoping norm bound: it rewrites the outer `g₁`-derivative of
`iterCov_succ` into a base derivative (to be pushed inward by `diffStep_leibniz`)
plus a connection-difference term (bounded pointwise by `diffStep_jet_one_le`). -/
theorem iterCov_succ_diffStep
    (g₁ g₂ : SmoothRiemannianMetric I M) (r : Nat)
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r)
    (N : Nat) :
    iterCov (I := I) g₁ r T (N + 1)
      = covStep (I := I) g₂ (r + N) (iterCov (I := I) g₁ r T N)
        + diffStep (I := I) g₁ g₂ (r + N) (iterCov (I := I) g₁ r T N) := by
  rw [iterCov_succ]
  simp only [diffStep]
  abel

/-- **The eval-form base-connection Leibniz for the connection-difference step**
(brick T-B, the mixed-commutator/`∇₂A` insertion identity).  Evaluating one further
*base* covariant derivative `∇^{g₂}` of the single-step connection difference
`diffStep g₁ g₂ s S = ∇^{g₁}S − ∇^{g₂}S` on `Fin.cons w (Fin.cons v slots)` realises
the standard tensor derivation `∇₂(A ⋆ S) = (∇₂A) ⋆ S + A ⋆ (∇₂S)`, where
`A = Γ₁ − Γ₂ = CovariantDerivative.difference (LC g₁)(LC g₂)`:

* the **`(∇₂A) ⋆ S` term** is the `covDerivConnDiff`-insertion sum (the directional
  covariant derivative of the connection-difference tensor, `= covDerivDiff (LC g₂)(LC g₁)`),
  materialising `∇₂A` at the eval level without a bundled `(1,2)` field, and
* the **`A ⋆ (∇₂S)` term** is the `A`-insertion (direction `v`) applied to the base
  derivative `∇₂_w S = covStep g₂ s S x (Fin.cons w ·)`.

This is the eval identity feeding `mixedComm_norm_le`. -/
theorem diffStep_leibniz_eval
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : Nat)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (W V : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Vslots : Fin s -> ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (x : M) :
    covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S) x
        (Fin.cons (W x) (Fin.cons (V x) (fun a : Fin s => Vslots a x)))
      = (-∑ a : Fin s,
          (S x) (Function.update (fun b : Fin s => Vslots b x) a
            (covDerivConnDiff (I := I) g₂ g₁
              (fun y : M => W y) (fun y : M => V y) (fun y : M => Vslots a y) x)))
        - ∑ a : Fin s,
            covStep (I := I) g₂ s S x
              (Fin.cons (W x) (Function.update (fun b : Fin s => Vslots b x) a
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x
                    (Vslots a x)) (V x)))) := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  haveI hcov₁ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₁) (∞ : WithTop ℕ∞) := leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₁
  haveI hcov₂ : CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivitaConnectionOfMetric (I := I) g₂) (∞ : WithTop ℕ∞) := leviCivitaConnectionOfMetric_contMDiffCovariantDerivative (I := I) g₂
  set VV : Fin (s + 1) → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) := Fin.cons V Vslots with hVVdef
  have hVVpt : ∀ y : M, (fun q : Fin (s + 1) => VV q y)
      = Fin.cons (V y) (fun a : Fin s => Vslots a y) := by
    intro y
    funext q
    refine Fin.cases ?_ (fun i => ?_) q <;> simp [hVVdef]
  rw [show Fin.cons (V x) (fun a : Fin s => Vslots a x)
        = (fun q : Fin (s + 1) => VV q x) from (hVVpt x).symm,
    covStep_eval_smooth_slots (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S) W VV x]
  have hInt : (fun y : M => (diffStep (I := I) g₁ g₂ s S) y (fun q : Fin (s + 1) => VV q y))
      = (fun y : M => -∑ a : Fin s, (S y) (Function.update (fun b : Fin s => Vslots b y) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) y
              (Vslots a y)) (V y)))) := by
    funext y
    rw [hVVpt y]
    exact diffStep_apply (I := I) g₁ g₂ s S V Vslots y
  rw [hInt]
  set cov₁ := leviCivitaConnectionOfMetric (I := I) g₁ with hcdef₁
  set cov₂ := leviCivitaConnectionOfMetric (I := I) g₂ with hcdef₂
  set Dsec : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    fun a => ContMDiffSection.mk (diffSec cov₂ cov₁ (fun y : M => V y) (fun y : M => Vslots a y))
      (diffSec_contMDiff cov₂ cov₁ V.contMDiff (by simpa using (Vslots a).contMDiff)) with hDdef
  set τ : Fin s → Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
    fun a => Function.update Vslots a (Dsec a) with hτdef
  have hDval : ∀ (a : Fin s) (y : M),
      (Dsec a) y = (CovariantDerivative.difference cov₁ cov₂ y (Vslots a y)) (V y) := by
    intro a y
    rw [hDdef]
    rfl
  have hτeval : ∀ (a : Fin s) (y : M),
      (fun b : Fin s => (τ a b) y)
        = Function.update (fun b : Fin s => Vslots b y) a
            ((CovariantDerivative.difference cov₁ cov₂ y (Vslots a y)) (V y)) := by
    intro a y
    funext b
    simp only [hτdef]
    rcases eq_or_ne b a with hb | hb
    · subst hb
      rw [Function.update_self, Function.update_self]
      exact hDval b y
    · rw [Function.update_of_ne hb, Function.update_of_ne hb]
  have hdiff : ∀ a : Fin s,
      MDifferentiableAt I 𝓘(Real, Real) (fun y : M => (S y) (fun b : Fin s => (τ a b) y)) x := by
    intro a
    have hSAt : ContMDiffAt I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
        (fun y : M => (S y) (fun b : Fin s => (τ a b) y)) x := by
      have hS := (S.contMDiff x).of_le (le_refl (∞ : WithTop ℕ∞))
      have hEval := TensorMultilinear.contMDiffAt_section_apply_gen (I := I) (M := M) (n := s) (x₀ := x)
        (T := fun y : M => S y) hS (v := fun b : Fin s => fun y : M => (τ a b) y)
        (hv := fun b => ((τ a b).contMDiff.contMDiffAt))
      simpa [Tensor0SBundle.Tensor0SSpace.toModel,
        Tensor0SBundle.tensor0SSpace_continuousLinearEquiv_apply] using hEval
    exact hSAt.mdifferentiableAt (by simp)
  simp only [← hτeval]
  have hDF : extDerivFun (I := I)
        (fun y : M => -∑ a : Fin s, (S y) (fun b : Fin s => (τ a b) y)) x (W x)
      = -∑ a : Fin s,
          extDerivFun (I := I) (fun y : M => (S y) (fun b : Fin s => (τ a b) y)) x (W x) := by
    have h1 : (fun y : M => -∑ a : Fin s, (S y) (fun b : Fin s => (τ a b) y))
        = (fun y : M => -(Finset.univ.sum
            (fun a : Fin s => fun y' : M => (S y') (fun b : Fin s => (τ a b) y'))) y) := by
      funext y; simp only [Finset.sum_apply]
    rw [h1, extDerivFun_neg_at (I := I) (W x)
          (mdiffAt_finset_sum (I := I) Finset.univ _ (fun a _ => hdiff a)),
        extDerivFun_finset_sum_at (I := I) Finset.univ
          (fun a : Fin s => fun y : M => (S y) (fun b : Fin s => (τ a b) y)) (W x)
          (fun a _ => hdiff a)]
  rw [hDF]
  have hEDF : ∀ a : Fin s,
      extDerivFun (I := I) (fun y : M => (S y) (fun b : Fin s => (τ a b) y)) x (W x)
      = (covStep (I := I) g₂ s S) x (Fin.cons (W x) (fun b : Fin s => (τ a b) x))
        + ∑ b : Fin s, (S x) (Function.update (fun b' : Fin s => (τ a b') x) b
            ((cov₂ (fun y : M => (τ a b) y) x) (W x))) := by
    intro a
    have hcs : (covStep (I := I) g₂ s S) x (Fin.cons (W x) (fun b : Fin s => (τ a b) x))
        = Tensor0SBundle.nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
            s cov₂ W S x (fun b : Fin s => (τ a b) x) := by
      rw [covStep_apply, Tensor0SBundle.totalNabla0SFun_apply_section]
    rw [hcs, Tensor0SBundle.nabla0SFun_eval_smooth_slots (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) cov₂ W (τ a) S x]
    ring
  simp only [hEDF]
  rw [Finset.sum_add_distrib]
  have hFib :
      (∑ a : Fin s, ∑ b : Fin s, (S x) (Function.update (fun b' : Fin s => (τ a b') x) b
          ((cov₂ (fun y : M => (τ a b) y) x) (W x))))
        + (∑ q : Fin (s + 1), ((diffStep (I := I) g₁ g₂ s S) x)
            (Function.update (fun b : Fin (s + 1) => (VV b) x) q
              ((cov₂ (fun y : M => (VV q) y) x) (W x))))
        = ∑ a : Fin s, (S x) (Function.update (fun b : Fin s => (Vslots b) x) a
            (covDerivConnDiff (I := I) g₂ g₁ (fun y : M => W y) (fun y : M => V y)
              (fun y : M => (Vslots a) y) x)) := by
    have hFact1 : ∀ a : Fin s,
        (cov₂ (fun y : M => (τ a a) y) x) (W x)
        = covDerivConnDiff (I := I) g₂ g₁ (fun y => W y) (fun y => V y) (fun y => (Vslots a) y) x
          + (CovariantDerivative.difference cov₁ cov₂ x (Vslots a x)) ((cov₂ (fun y : M => V y) x) (W x))
          + (CovariantDerivative.difference cov₁ cov₂ x
              ((cov₂ (fun y : M => (Vslots a) y) x) (W x))) (V x) := by
      intro a
      have hτaa : (fun y : M => (τ a a) y) = (fun y : M => (Dsec a) y) := by
        simp only [hτdef, Function.update_self]
      rw [hτaa, covDerivConnDiff_eq,
        show LeviCivita (I := I) g₂ = cov₂ from
          (LeviCivita_eq_leviCivitaConnectionOfMetric g₂).trans hcdef₂.symm,
        show LeviCivita (I := I) g₁ = cov₁ from
          (LeviCivita_eq_leviCivitaConnectionOfMetric g₁).trans hcdef₁.symm]
      simp only [covDerivDiff, covApply, hDdef, ContMDiffSection.coeFn_mk]
      abel
    have hD :
        (∑ a : Fin s, ∑ b : Fin s, (S x) (Function.update (fun b' : Fin s => (τ a b') x) b
            ((cov₂ (fun y : M => (τ a b) y) x) (W x))))
        = (∑ a : Fin s, (S x) (Function.update (fun b : Fin s => (Vslots b) x) a
              (covDerivConnDiff (I := I) g₂ g₁ (fun y => W y) (fun y => V y) (fun y => (Vslots a) y) x)))
          + (∑ a : Fin s, (S x) (Function.update (fun b : Fin s => (Vslots b) x) a
              ((CovariantDerivative.difference cov₁ cov₂ x ((Vslots a) x)) ((cov₂ (fun y => V y) x) (W x)))))
          + (∑ a : Fin s, (S x) (Function.update (fun b : Fin s => (Vslots b) x) a
              ((CovariantDerivative.difference cov₁ cov₂ x ((cov₂ (fun y => (Vslots a) y) x) (W x))) (V x))))
          + (∑ a : Fin s, ∑ b ∈ Finset.univ.erase a, (S x)
              (Function.update (Function.update (fun c : Fin s => (Vslots c) x) a
                  ((CovariantDerivative.difference cov₁ cov₂ x ((Vslots a) x)) (V x))) b
                ((cov₂ (fun y => (Vslots b) y) x) (W x)))) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), hτeval a x, Function.update_idem,
        hFact1 a, ContinuousMultilinearMap.map_update_add,
        ContinuousMultilinearMap.map_update_add]
      have herase : ∀ b ∈ Finset.univ.erase a,
          (S x) (Function.update (Function.update (fun c : Fin s => (Vslots c) x) a
              ((CovariantDerivative.difference cov₁ cov₂ x ((Vslots a) x)) (V x))) b
            ((cov₂ (fun y : M => (τ a b) y) x) (W x)))
          = (S x) (Function.update (Function.update (fun c : Fin s => (Vslots c) x) a
              ((CovariantDerivative.difference cov₁ cov₂ x ((Vslots a) x)) (V x))) b
            ((cov₂ (fun y : M => (Vslots b) y) x) (W x))) := by
        intro b hb
        have hba : b ≠ a := Finset.ne_of_mem_erase hb
        have : (fun y : M => (τ a b) y) = (fun y : M => (Vslots b) y) := by
          simp only [hτdef, Function.update_of_ne hba]
        rw [this]
      rw [Finset.sum_congr rfl herase]
    have hβ :
        (∑ q : Fin (s + 1), ((diffStep (I := I) g₁ g₂ s S) x)
            (Function.update (fun b : Fin (s + 1) => (VV b) x) q ((cov₂ (fun y : M => (VV q) y) x) (W x))))
        = -(∑ a : Fin s, (S x) (Function.update (fun b : Fin s => (Vslots b) x) a
              ((CovariantDerivative.difference cov₁ cov₂ x ((Vslots a) x)) ((cov₂ (fun y => V y) x) (W x)))))
          - (∑ a : Fin s, (S x) (Function.update (fun b : Fin s => (Vslots b) x) a
              ((CovariantDerivative.difference cov₁ cov₂ x ((cov₂ (fun y => (Vslots a) y) x) (W x))) (V x))))
          - (∑ j : Fin s, ∑ a ∈ Finset.univ.erase j, (S x)
              (Function.update (Function.update (fun c : Fin s => (Vslots c) x) j
                  ((cov₂ (fun y => (Vslots j) y) x) (W x))) a
                ((CovariantDerivative.difference cov₁ cov₂ x ((Vslots a) x)) (V x)))) := by
      rw [Fin.sum_univ_succ]
      simp only [hVVpt x, Fin.update_cons_zero, ← Fin.cons_update]
      simp only [hVVdef, Fin.cons_zero, Fin.cons_succ]
      simp only [diffStep_eval, ← hcdef₁, ← hcdef₂]
      have hj : ∀ j : Fin s,
          (∑ a : Fin s, (S x) (Function.update (Function.update (fun c : Fin s => (Vslots c) x) j
                ((cov₂ (fun y : M => (Vslots j) y) x) (W x))) a
              ((CovariantDerivative.difference cov₁ cov₂ x
                  ((Function.update (fun c : Fin s => (Vslots c) x) j
                    ((cov₂ (fun y : M => (Vslots j) y) x) (W x))) a)) (V x))))
          = (S x) (Function.update (fun b : Fin s => (Vslots b) x) j
                ((CovariantDerivative.difference cov₁ cov₂ x ((cov₂ (fun y => (Vslots j) y) x) (W x))) (V x)))
            + ∑ a ∈ Finset.univ.erase j, (S x)
                (Function.update (Function.update (fun c : Fin s => (Vslots c) x) j
                    ((cov₂ (fun y => (Vslots j) y) x) (W x))) a
                  ((CovariantDerivative.difference cov₁ cov₂ x ((Vslots a) x)) (V x))) := by
        intro j
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), Function.update_self,
          Function.update_idem]
        refine congrArg _ (Finset.sum_congr rfl (fun a ha => ?_))
        rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)]
      simp only [hj, neg_add, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      abel
    rw [hD, hβ]
    have hYY' :
        (∑ a : Fin s, ∑ b ∈ Finset.univ.erase a, (S x)
            (Function.update (Function.update (fun c : Fin s => (Vslots c) x) a
                ((CovariantDerivative.difference cov₁ cov₂ x ((Vslots a) x)) (V x))) b
              ((cov₂ (fun y => (Vslots b) y) x) (W x))))
        = (∑ j : Fin s, ∑ a ∈ Finset.univ.erase j, (S x)
            (Function.update (Function.update (fun c : Fin s => (Vslots c) x) j
                ((cov₂ (fun y => (Vslots j) y) x) (W x))) a
              ((CovariantDerivative.difference cov₁ cov₂ x ((Vslots a) x)) (V x)))) := by
      rw [Finset.sum_comm' (s := Finset.univ) (t := fun a : Fin s => Finset.univ.erase a)
        (t' := Finset.univ) (s' := fun b : Fin s => Finset.univ.erase b)
        (h := fun a b => by
          simp only [Finset.mem_univ, Finset.mem_erase, true_and, and_true]
          exact ⟨Ne.symm, Ne.symm⟩)]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun a ha => ?_))
      rw [Function.update_comm (Finset.ne_of_mem_erase ha)]
    rw [hYY']
    abel
  linarith [hFib]

end HCGCompactness

end DifferentialGeometry
