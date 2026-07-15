import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.HigherOrder
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Parametric (time) derivative of the covariant derivative

This file proves the single-step **parametric Clairaut** identity: differentiating
a time-dependent covariant tensor field `α r` in the parameter `r` commutes with
applying a fixed background covariant derivative.

The directional formula `nabla0SFun_eval_smooth_slots` writes
`(∇_X α)(V) = D_X (α(V)) - ∑_a α(…∇_X V_a…)`, a scalar exterior-derivative term
plus finitely many pointwise correction terms.  The exterior-derivative term's
parameter derivative is supplied by `FixedBaseExtDerivTimeDerivativeOn` (the
`∂_r ⇄ extDerivFun` swap, whose model-space analytic core is
`fixedBaseFDerivTimeDerivativeAt_of_contDiff`); the correction terms are
evaluated at the fixed base point with fixed (parameter-independent) slot
vectors, so their parameter derivatives are pointwise.

This is the analytic heart of the MSM135 equation (3.4) evolution
`∂_t (∇^p g) = -2 ∇^p Rc`: with the **fixed** reference Levi-Civita connection,
the time derivative passes straight through every covariant-derivative step (no
`∂_t Γ` correction, because the background connection does not move).
-/

noncomputable section

namespace Tensor0SBundle

open Bundle Set IsManifold ContinuousLinearMap TensorLieDeriv DifferentialGeometry
open scoped Manifold Topology Bundle ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [T2Space M]

/-- **Single-step parametric Clairaut for the directional covariant derivative**
(pointwise-swap form).

If, at the base point `x₀` and working time `t`, the parameter derivative of the
scalar field `r ↦ α r (·)(V ·)` commutes with the directional derivative in `X`
(hypothesis `hswap`, the single instance of the mixed-derivative swap actually
consumed), and each correction term `r ↦ α r x₀ (…)` has parameter derivative
the corresponding `β t` term (hypothesis `hpt`), then `r ↦ (∇_X (α r))(V)` is
differentiable in `r` with derivative `(∇_X (β t))(V)`.

This is the form suited to flow intervals, where the swap is only available at
regular times (`FixedBaseExtDerivTimeDerivativeOnRegular`). -/
theorem nabla0SFun_hasDerivWithinAt_pt {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (α β : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (timeSet : Set Real) (x₀ : M) (t : Real)
    (hswap :
      HasDerivWithinAt
        (fun r : Real => extDerivFun (I := I)
          (fun p : M => (α r) p (fun a : Fin s => V a p)) x₀ (X x₀))
        (extDerivFun (I := I)
          (fun p : M => (β t) p (fun a : Fin s => V a p)) x₀ (X x₀))
        timeSet t)
    (hpt : ∀ a : Fin s,
      HasDerivWithinAt
        (fun r : Real => (α r) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        ((β t) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        timeSet t) :
    HasDerivWithinAt
      (fun r : Real =>
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X (α r) x₀) (fun a : Fin s => V a x₀))
      ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X (β t) x₀) (fun a : Fin s => V a x₀))
      timeSet t := by
  simp only [nabla0SFun_eval_smooth_slots]
  refine HasDerivWithinAt.sub ?_ ?_
  · exact hswap
  · have key :
        (fun r : Real => ∑ a : Fin s, (α r) x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (fun p : M => V a p) x₀) (X x₀))))
          = ∑ a : Fin s, (fun r : Real => (α r) x₀
            (Function.update (fun b : Fin s => V b x₀) a
              ((cov (fun p : M => V a p) x₀) (X x₀)))) := by
      funext r
      simp only [Finset.sum_apply]
    rw [key]
    exact HasDerivWithinAt.sum (fun (a : Fin s) (_ : a ∈ Finset.univ) => hpt a)

/-- Predicate form of `nabla0SFun_hasDerivWithinAt_pt`: the swap supplied as a
`FixedBaseExtDerivTimeDerivativeOn` instance on the singleton `{x₀}`. -/
theorem nabla0SFun_hasDerivWithinAt {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (α β : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (timeSet : Set Real) (x₀ : M) (t : Real)
    (hswap :
      FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet ({x₀} : Set M)
        (fun r p => (α r) p (fun a : Fin s => V a p))
        (fun r p => (β r) p (fun a : Fin s => V a p)))
    (hpt : ∀ a : Fin s,
      HasDerivWithinAt
        (fun r : Real => (α r) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        ((β t) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        timeSet t) :
    HasDerivWithinAt
      (fun r : Real =>
        (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov X (α r) x₀) (fun a : Fin s => V a x₀))
      ((nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov X (β t) x₀) (fun a : Fin s => V a x₀))
      timeSet t :=
  nabla0SFun_hasDerivWithinAt_pt cov X V α β timeSet x₀ t
    (hswap t x₀ (Set.mem_singleton x₀) (X x₀)) hpt

/-- **Single-step parametric Clairaut for the total covariant derivative**
(pointwise-swap form).

The `totalNabla0SFun` version of `nabla0SFun_hasDerivWithinAt_pt`, obtained by
contracting the leading derivative slot against the section `X` via
`totalNabla0SFun_apply_section`.  The slot tuple is `Fin.cons (X x₀) (V · x₀)`. -/
theorem totalNabla0SFun_hasDerivWithinAt_pt {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (α β : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (timeSet : Set Real) (x₀ : M) (t : Real)
    (hswap :
      HasDerivWithinAt
        (fun r : Real => extDerivFun (I := I)
          (fun p : M => (α r) p (fun a : Fin s => V a p)) x₀ (X x₀))
        (extDerivFun (I := I)
          (fun p : M => (β t) p (fun a : Fin s => V a p)) x₀ (X x₀))
        timeSet t)
    (hpt : ∀ a : Fin s,
      HasDerivWithinAt
        (fun r : Real => (α r) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        ((β t) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        timeSet t) :
    HasDerivWithinAt
      (fun r : Real =>
        (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov (α r) x₀) (Fin.cons (X x₀) (fun a : Fin s => V a x₀)))
      ((totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov (β t) x₀) (Fin.cons (X x₀) (fun a : Fin s => V a x₀)))
      timeSet t := by
  simpa only [totalNabla0SFun_apply_section] using
    nabla0SFun_hasDerivWithinAt_pt cov X V α β timeSet x₀ t hswap hpt

/-- Predicate form of `totalNabla0SFun_hasDerivWithinAt_pt`: the swap supplied
as a `FixedBaseExtDerivTimeDerivativeOn` instance on the singleton `{x₀}`. -/
theorem totalNabla0SFun_hasDerivWithinAt {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (α β : Real → Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (timeSet : Set Real) (x₀ : M) (t : Real)
    (hswap :
      FixedBaseExtDerivTimeDerivativeOn (I := I) timeSet ({x₀} : Set M)
        (fun r p => (α r) p (fun a : Fin s => V a p))
        (fun r p => (β r) p (fun a : Fin s => V a p)))
    (hpt : ∀ a : Fin s,
      HasDerivWithinAt
        (fun r : Real => (α r) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        ((β t) x₀
          (Function.update (fun b : Fin s => V b x₀) a
            ((cov (fun p : M => V a p) x₀) (X x₀))))
        timeSet t) :
    HasDerivWithinAt
      (fun r : Real =>
        (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          s cov (α r) x₀) (Fin.cons (X x₀) (fun a : Fin s => V a x₀)))
      ((totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov (β t) x₀) (Fin.cons (X x₀) (fun a : Fin s => V a x₀)))
      timeSet t :=
  totalNabla0SFun_hasDerivWithinAt_pt cov X V α β timeSet x₀ t
    (hswap t x₀ (Set.mem_singleton x₀) (X x₀)) hpt

end Tensor0SBundle
