import DifferentialGeometry.Geometry.Connection.Realization.Embedding
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# Concrete connection from a CovariantDerivative

Given a Mathlib `CovariantDerivative I E (TangentSpace I)` on the tangent bundle of `M`,
this file constructs the concrete connection `conn : V → V → V` and proves its four
linearity properties.

## Main definitions

* `concreteConn` : the connection `∇_X Y` as a smooth section, defined pointwise by
  `concreteConn cov X Y x := cov Y x (X x)`.

## Main results

* `concreteConn_add_right` : `∇_X (Y + Z) = ∇_X Y + ∇_X Z`
* `concreteConn_add_left` : `∇_{X+Y} Z = ∇_X Z + ∇_Y Z`
* `concreteConn_smul_left` : `∇_{fX} Z = f • ∇_X Z`
* `concreteConn_leibniz` : `∇_X (f • Y) = (embedDeriv X f) • Y + f • ∇_X Y`

## Convention

Mathlib's `CovariantDerivative` has the signature `cov σ x v` corresponding to `(∇_v σ)(x)`.
The `conn X Y` notation corresponds to `∇_X Y`. So `conn X Y x = cov Y x (X x)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Bundle CovariantDerivative

section Connection

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Definition of concreteConn -/

/-- The connection `∇_X Y` as a smooth section of the tangent bundle.

Given a `CovariantDerivative` with `ContMDiffCovariantDerivative` regularity,
and smooth sections `X, Y`, the result `cov Y x (X x)` is smooth. This follows
because `cov Y` is a smooth section of `Hom(TM, TM)` (by the smoothness condition
of the covariant derivative), and `X` is a smooth section of `TM`, so their
pointwise pairing is smooth by `ContMDiff.clm_bundle_apply`. -/
noncomputable def concreteConn
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ where
  toFun x := cov Y x (X x)
  contMDiff_toFun := by

    have hY_plus : ContMDiff I (I.prod 𝓘(ℝ, E)) (∞ + 1) (T% fun x => Y x) := by
      rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from by simp]
      exact Y.contMDiff
    have hcov_smooth := (‹ContMDiffCovariantDerivative cov ∞›).contMDiff.contMDiff
      (hY_plus.contMDiffOn)

    have hcov_global : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
        (fun x => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun (x : M) => TangentSpace I x →L[ℝ] TangentSpace I x) x (cov Y x)) := by
      rwa [← contMDiffOn_univ]

    have hX_smooth : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun x => TotalSpace.mk' E (E := TangentSpace I) x (X x)) :=
      X.contMDiff

    exact ContMDiff.clm_bundle_apply (b := id) hcov_global hX_smooth

/-- The pointwise value of `concreteConn`: `concreteConn cov X Y x = cov Y x (X x)`. -/
theorem concreteConn_apply
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    concreteConn I M cov X Y x = cov Y x (X x) := by
  rfl

/-! ### Linearity properties -/

/-- Right-additivity of the connection: `∇_X (Y + Z) = ∇_X Y + ∇_X Z`.

Follows from `IsCovariantDerivativeOn.add`: `cov (Y + Z) x = cov Y x + cov Z x`
for differentiable sections Y, Z. -/
theorem concreteConn_add_right
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteConn I M cov X (Y + Z) = concreteConn I M cov X Y + concreteConn I M cov X Z := by
  apply ContMDiffSection.ext; intro x
  change cov (fun x => Y x + Z x) x (X x) =
    cov Y x (X x) + cov Z x (X x)
  have hY : MDiffAt (T% fun x => Y x) x := Y.mdifferentiableAt
  have hZ : MDiffAt (T% fun x => Z x) x := Z.mdifferentiableAt
  rw [show (fun x => Y x + Z x) = ((fun x => Y x) + fun x => Z x) from rfl,
    cov.isCovariantDerivativeOn.add hY hZ]
  simp [ContinuousLinearMap.add_apply]

/-- Left-additivity of the connection: `∇_{X+Y} Z = ∇_X Z + ∇_Y Z`.

Follows from the CLM linearity of `cov Z x` in the tangent vector argument:
`cov Z x (X x + Y x) = cov Z x (X x) + cov Z x (Y x)`. -/
theorem concreteConn_add_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteConn I M cov (X + Y) Z = concreteConn I M cov X Z + concreteConn I M cov Y Z := by
  apply ContMDiffSection.ext; intro x
  change cov Z x (X x + Y x) = cov Z x (X x) + cov Z x (Y x)
  exact ContinuousLinearMap.map_add (cov Z x) (X x) (Y x)

/-- Left scalar multiplication: `∇_{f•X} Z = f • ∇_X Z` for `f : C^∞⟮I, M; ℝ⟯`.

Follows from the CLM linearity of `cov Z x` in the tangent vector argument:
`cov Z x (f x • X x) = f x • cov Z x (X x)`. -/
theorem concreteConn_smul_left
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (f : C^∞⟮I, M; ℝ⟯)
    (X Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteConn I M cov (f • X) Z = f • concreteConn I M cov X Z := by
  apply ContMDiffSection.ext; intro x
  change cov Z x (f x • X x) = f x • cov Z x (X x)
  exact ContinuousLinearMap.map_smul (cov Z x) (f x) (X x)

/-- Leibniz rule: `∇_X (f • Y) = (embedDeriv I M X f) • Y + f • ∇_X Y`.

Follows from `IsCovariantDerivativeOn.leibniz`:
`cov (f • Y) x = f x • cov Y x + (extDerivFun f x).smulRight (Y x)`.

The key identification is that `(extDerivFun f x).smulRight (Y x)` applied to `X x`
gives `extDerivFun f x (X x) • Y x`, which is `vectorFieldAction I M X f x • Y x`
= `(embedDeriv I M X f) x • Y x`. -/
theorem concreteConn_leibniz
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : C^∞⟮I, M; ℝ⟯)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    concreteConn I M cov X (f • Y) =
      vectorFieldActionSmooth I M X f • Y + f • concreteConn I M cov X Y := by
  apply ContMDiffSection.ext; intro x

  change cov (fun x => (f : M → ℝ) x • Y x) x (X x) =
    (vectorFieldActionSmooth I M X f) x • Y x + f x • cov Y x (X x)

  have hY : MDiffAt (T% fun x => Y x) x := Y.mdifferentiableAt
  have hf : MDiffAt (f : M → ℝ) x :=
    f.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hfY_eq : (fun x => (f : M → ℝ) x • Y x) = ((f : M → ℝ) • fun x => Y x) := rfl
  rw [hfY_eq, cov.isCovariantDerivativeOn.leibniz hY hf]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]

  simp only [vectorFieldActionSmooth, ContMDiffMap.coeFn_mk, vectorFieldAction]
  abel
end Connection

end
