import DifferentialGeometry.Integral.Connection.LeviCivita

set_option linter.unusedSectionVars false

/-!
# Killing vector fields

Let `g : SmoothRiemannianMetric I M` be a smooth Riemannian metric on a smooth
boundaryless manifold `M` modelled on a finite-dimensional inner product space.
A smooth vector field `X` on `M` is a **Killing field** for `g` iff its
Levi-Civita covariant derivative `∇ X`, viewed as a `(1,1)`-tensor (i.e. an
endomorphism of each tangent space sending `V ↦ ∇_V X`), is antisymmetric with
respect to `g`:

```
g(∇_V X, W) + g(V, ∇_W X) = 0  for all V, W ∈ T_x M, x ∈ M.
```

Equivalently the local flow of `X` is by isometries, or the Lie derivative of
`g` along `X` vanishes; we ship only the antisymmetry formulation, which is
the most directly computable.

## Main contents

* `IsKillingField g X hX` — the antisymmetry predicate above.
* `IsKillingField_zero g` — the zero vector field is a Killing field.
* `IsKillingField.add` — the sum of two Killing fields is a Killing field.
* `IsKillingField.smul` — a scalar multiple of a Killing field is a Killing field.
* `IsKillingField.neg` — the negation of a Killing field is a Killing field.
* `IsKillingField.sub` — the difference of two Killing fields is a Killing field.

Both statements rest only on the bundled Levi-Civita covariant derivative
`LeviCivita g` and on `ContMDiffRiemannianMetric.inner`; in particular no
chart-based unfolding is needed. The closure under linear combinations follows
from the linearity of `LeviCivita g` (as a `CovariantDerivative`, via the
`add` and `smul_const` axioms of `IsCovariantDerivativeOn`) together with the
bilinearity of `g.inner x` (a `ContinuousLinearMap` in each slot).
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection

namespace Geometry
namespace Riemannian
namespace Symmetry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The Killing predicate -/

/-- A smooth vector field `X` on a smooth Riemannian manifold `(M, g)` is a
**Killing field** iff its Levi-Civita covariant derivative is antisymmetric
with respect to `g`:

```
g(∇_V X, W) + g(V, ∇_W X) = 0  for all x ∈ M and V, W ∈ T_x M.
```

The smoothness hypothesis `hX` is recorded as an unused argument so that the
predicate is restricted to genuine smooth fields; this matches the public API
elsewhere in the project, where the smoothness of a tangent-bundle section is
a separate certificate carried alongside the section. -/
def IsKillingField
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (X : ∀ x : M, TangentSpace I x)
    (_hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)) : Prop :=
  ∀ x : M, ∀ V W : TangentSpace I x,
    g.inner x ((LeviCivita (I := I) g) X x V) W +
      g.inner x V ((LeviCivita (I := I) g) X x W) = 0

/-! ## The zero vector field

The zero section `fun _ : M => 0` of the tangent bundle is smooth (this is the
canonical zero section of any vector bundle), and its Levi-Civita covariant
derivative vanishes identically by `CovariantDerivative.zero`. The Killing
identity then reduces to `0 + 0 = 0`. -/

/-- The zero tangent-bundle section is smooth. -/
lemma contMDiff_zero_tangent :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (fun x : M => (0 : TangentSpace I x))) := by
  -- `T% (fun _ : M => 0)` unfolds (via the `T%` elaborator) to
  -- `fun x => ⟨x, 0⟩ = Bundle.zeroSection E (TangentSpace I)`.
  -- Smoothness of the zero section is `Bundle.contMDiff_zeroSection`.
  exact Bundle.contMDiff_zeroSection ℝ (TangentSpace I : M → Type _)

/-- **The zero vector field is a Killing field.** Its Levi-Civita covariant
derivative is identically zero, so both inner products in the Killing identity
vanish individually. -/
theorem IsKillingField_zero
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) :
    IsKillingField (I := I) (M := M) g
      (fun x : M => (0 : TangentSpace I x))
      contMDiff_zero_tangent := by
  intro x V W
  -- Reduce `(LeviCivita g) (fun _ => 0) x V` to `0` using
  -- `CovariantDerivative.zero : cov 0 = 0` (note that `0 : Π x : M, V x` is
  -- definitionally `fun _ => 0`).
  have h0eq : (fun x : M => (0 : TangentSpace I x)) =
      (0 : ∀ x : M, TangentSpace I x) := rfl
  -- `(LeviCivita g) (fun _ => 0) = (LeviCivita g) 0 = 0`.
  have hcov_zero :
      (LeviCivita (I := I) g).toFun (fun x : M => (0 : TangentSpace I x)) = 0 := by
    rw [h0eq]
    exact (LeviCivita (I := I) g).zero
  -- At the point `x`, the CLM `(LeviCivita g) (fun _ => 0) x` is the zero CLM.
  have hcov_at :
      (LeviCivita (I := I) g).toFun (fun x : M => (0 : TangentSpace I x)) x =
        (0 : TangentSpace I x →L[ℝ] TangentSpace I x) := by
    have := congrArg (fun f => f x) hcov_zero
    simpa using this
  -- Apply at `V` and at `W` separately.
  have hV0 :
      (LeviCivita (I := I) g).toFun (fun x : M => (0 : TangentSpace I x)) x V = 0 := by
    rw [hcov_at]; rfl
  have hW0 :
      (LeviCivita (I := I) g).toFun (fun x : M => (0 : TangentSpace I x)) x W = 0 := by
    rw [hcov_at]; rfl
  -- `(LeviCivita g) X x V` is `(LeviCivita g).toFun X x V` by `CoeFun`; rewrite
  -- the goal in `toFun` form, then substitute `hV0` and `hW0`.
  change g.inner x
      ((LeviCivita (I := I) g).toFun (fun x : M => (0 : TangentSpace I x)) x V) W +
    g.inner x V
      ((LeviCivita (I := I) g).toFun (fun x : M => (0 : TangentSpace I x)) x W) = 0
  rw [hV0, hW0]
  -- `g.inner x 0 W = 0` and `g.inner x V 0 = 0` by linearity in each slot.
  simp

/-! ## Closure under linear combinations

The Killing condition is linear: a finite linear combination of Killing fields
is again a Killing field. We package this as the two basic operations, sum and
scalar multiple. The proofs use only

* the additivity / scalar-linearity axioms of the Levi-Civita covariant
  derivative as a `CovariantDerivative` (these reduce
  `(LeviCivita g) (X + Y) x` and `(LeviCivita g) (c • X) x` to the obvious
  formulas, given pointwise differentiability of `X` and `Y`), and
* the bilinearity of `g.inner x` (a `ContinuousLinearMap` in each slot).
-/

/-- **Sum of two Killing fields is a Killing field.** The proof distributes the
sum out of the Levi-Civita derivative via the `add`-axiom of the bundled
covariant derivative, and then uses bilinearity of `g.inner x` to split each
inner product into a sum of two terms; the four terms regroup into the two
Killing identities `hKX` and `hKY`, both zero. -/
theorem IsKillingField.add
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M}
    {X Y : ∀ x : M, TangentSpace I x}
    {hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)}
    {hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)}
    (hKX : IsKillingField g X hX) (hKY : IsKillingField g Y hY) :
    IsKillingField g (fun x : M => X x + Y x) (hX.add_section hY) := by
  intro x V W
  -- Pointwise differentiability of `X` and `Y` at `x` (from `ContMDiff ∞`).
  have hX_at : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hY_at : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  -- Distribute the Levi-Civita derivative across the sum. The function
  -- `fun x => X x + Y x` is `X + Y` (`Pi.add_apply` is `rfl`); the `add` axiom
  -- of the bundled covariant derivative gives the CLM-equality below.
  have hadd_cov :
      (LeviCivita (I := I) g).toFun (X + Y) x =
        (LeviCivita (I := I) g).toFun X x +
          (LeviCivita (I := I) g).toFun Y x :=
    (LeviCivita (I := I) g).isCovariantDerivativeOn.add hX_at hY_at
      (Set.mem_univ x)
  have hadd_funext :
      (fun x : M => X x + Y x) = X + Y := rfl
  -- Apply the CLM-equality at `V` and at `W`.
  have hadd_V :
      (LeviCivita (I := I) g).toFun (fun x : M => X x + Y x) x V =
        (LeviCivita (I := I) g).toFun X x V +
          (LeviCivita (I := I) g).toFun Y x V := by
    rw [hadd_funext, hadd_cov]
    rfl
  have hadd_W :
      (LeviCivita (I := I) g).toFun (fun x : M => X x + Y x) x W =
        (LeviCivita (I := I) g).toFun X x W +
          (LeviCivita (I := I) g).toFun Y x W := by
    rw [hadd_funext, hadd_cov]
    rfl
  -- Rewrite the goal in `toFun` form (this is what `CoeFun` produces).
  change g.inner x
      ((LeviCivita (I := I) g).toFun (fun x : M => X x + Y x) x V) W +
    g.inner x V
      ((LeviCivita (I := I) g).toFun (fun x : M => X x + Y x) x W) = 0
  rw [hadd_V, hadd_W]
  -- `g.inner x` is a `ContinuousLinearMap → ContinuousLinearMap → ℝ`, so it is
  -- linear in each slot. Distribute the sums:
  --   inner(∇_V X + ∇_V Y, W) = inner(∇_V X, W) + inner(∇_V Y, W),
  --   inner(V, ∇_W X + ∇_W Y) = inner(V, ∇_W X) + inner(V, ∇_W Y).
  rw [ContinuousLinearMap.map_add (g.inner x)
        ((LeviCivita (I := I) g).toFun X x V)
        ((LeviCivita (I := I) g).toFun Y x V),
      ContinuousLinearMap.add_apply,
      ContinuousLinearMap.map_add (g.inner x V)
        ((LeviCivita (I := I) g).toFun X x W)
        ((LeviCivita (I := I) g).toFun Y x W)]
  -- The four terms regroup into `(hKX x V W) + (hKY x V W)`.
  have hX_id := hKX x V W
  have hY_id := hKY x V W
  -- Both identities use the `(LeviCivita g)` coercion; rewrite the `CoeFun`
  -- form in `hX_id, hY_id` to the explicit `toFun` form used in the goal.
  change g.inner x ((LeviCivita (I := I) g).toFun X x V) W +
      g.inner x V ((LeviCivita (I := I) g).toFun X x W) = 0 at hX_id
  change g.inner x ((LeviCivita (I := I) g).toFun Y x V) W +
      g.inner x V ((LeviCivita (I := I) g).toFun Y x W) = 0 at hY_id
  linarith

/-- **Scalar multiple of a Killing field is a Killing field.** The proof pulls
the scalar out of the Levi-Civita derivative via the `smul_const`-axiom of the
bundled covariant derivative, then uses bilinearity of `g.inner x` to pull it
out of each inner product; the result reduces to `c * (hKX V W) = c * 0 = 0`. -/
theorem IsKillingField.smul
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M} (c : ℝ)
    {X : ∀ x : M, TangentSpace I x}
    {hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)}
    (hKX : IsKillingField g X hX) :
    IsKillingField g (fun x : M => c • X x) (hX.const_smul_section) := by
  intro x V W
  -- Pointwise differentiability of `X` at `x`.
  have hX_at : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp)
  -- Pull the constant scalar out of the Levi-Civita derivative. The function
  -- `fun x => c • X x` is `c • X` (`Pi.smul_apply` is `rfl`); the `smul_const`
  -- axiom of `IsCovariantDerivativeOn` then gives the CLM-equality below.
  have hsmul_cov :
      (LeviCivita (I := I) g).toFun (c • X) x =
        c • (LeviCivita (I := I) g).toFun X x :=
    (LeviCivita (I := I) g).isCovariantDerivativeOn.smul_const (a := c) hX_at
      (Set.mem_univ x)
  have hsmul_funext :
      (fun x : M => c • X x) = c • X := rfl
  have hsmul_V :
      (LeviCivita (I := I) g).toFun (fun x : M => c • X x) x V =
        c • ((LeviCivita (I := I) g).toFun X x V) := by
    rw [hsmul_funext, hsmul_cov]
    rfl
  have hsmul_W :
      (LeviCivita (I := I) g).toFun (fun x : M => c • X x) x W =
        c • ((LeviCivita (I := I) g).toFun X x W) := by
    rw [hsmul_funext, hsmul_cov]
    rfl
  -- Rewrite the goal in `toFun` form, then substitute.
  change g.inner x
      ((LeviCivita (I := I) g).toFun (fun x : M => c • X x) x V) W +
    g.inner x V
      ((LeviCivita (I := I) g).toFun (fun x : M => c • X x) x W) = 0
  rw [hsmul_V, hsmul_W]
  -- `g.inner x` is a `ContinuousLinearMap`, so it pulls scalars out of each
  -- slot. After pulling them out, the goal becomes `c * (hKX V W)`.
  rw [ContinuousLinearMap.map_smul (g.inner x) c
        ((LeviCivita (I := I) g).toFun X x V),
      ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.map_smul (g.inner x V) c
        ((LeviCivita (I := I) g).toFun X x W)]
  -- Read the Killing identity for `X` at `V, W`, in `toFun` form.
  have hX_id := hKX x V W
  change g.inner x ((LeviCivita (I := I) g).toFun X x V) W +
      g.inner x V ((LeviCivita (I := I) g).toFun X x W) = 0 at hX_id
  -- Factor `c` out and rewrite.
  change c • g.inner x ((LeviCivita (I := I) g).toFun X x V) W +
      c • g.inner x V ((LeviCivita (I := I) g).toFun X x W) = 0
  rw [show (c • g.inner x ((LeviCivita (I := I) g).toFun X x V) W : ℝ) =
        c * g.inner x ((LeviCivita (I := I) g).toFun X x V) W from rfl,
      show (c • g.inner x V ((LeviCivita (I := I) g).toFun X x W) : ℝ) =
        c * g.inner x V ((LeviCivita (I := I) g).toFun X x W) from rfl,
      ← mul_add, hX_id, mul_zero]

/-- **Negation of a Killing field is a Killing field.** Reduces to `IsKillingField.smul`
with scalar `-1`, after observing that `-X x = (-1 : ℝ) • X x` pointwise. -/
theorem IsKillingField.neg
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M}
    {X : ∀ x : M, TangentSpace I x}
    {hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)}
    (hKX : IsKillingField g X hX) :
    IsKillingField g (fun x : M => -X x) hX.neg_section := by
  -- `IsKillingField` ignores its smoothness witness, so it suffices to show
  -- the antisymmetry identity for `fun x => -X x`. Replace `-X x` by
  -- `(-1 : ℝ) • X x` and invoke the existing `IsKillingField.smul` closure.
  have hfun : (fun x : M => -X x) = (fun x : M => ((-1 : ℝ) • X x)) := by
    funext x; rw [neg_one_smul]
  have hKsmul : IsKillingField g (fun x : M => ((-1 : ℝ) • X x))
      (hX.const_smul_section) :=
    IsKillingField.smul (-1) hKX
  intro x V W
  have hsmul_id := hKsmul x V W
  -- Transport along `hfun` (the predicate body depends only on the function).
  rw [hfun]
  exact hsmul_id

/-- **Difference of two Killing fields is a Killing field.** Combines
`IsKillingField.add` with `IsKillingField.neg`, after rewriting `X x - Y x`
as `X x + (-Y x)`. -/
theorem IsKillingField.sub
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M}
    {X Y : ∀ x : M, TangentSpace I x}
    {hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)}
    {hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)}
    (hKX : IsKillingField g X hX) (hKY : IsKillingField g Y hY) :
    IsKillingField g (fun x : M => X x - Y x) (hX.sub_section hY) := by
  have hfun : (fun x : M => X x - Y x) = (fun x : M => X x + (-Y x)) := by
    funext x; rw [sub_eq_add_neg]
  -- `-Y` is Killing by `IsKillingField.neg`; sum with `X` by `IsKillingField.add`.
  have hKadd := hKX.add hKY.neg
  intro x V W
  have hadd_id := hKadd x V W
  rw [hfun]
  exact hadd_id

/-- **Killing identity at coincident slots.** For a Killing field `X` and any
tangent vector `V`, the inner product `g(∇_V X, V)` vanishes. This is the
antisymmetry identity specialised to `W = V`: `2 · g(∇_V X, V) = 0`, which over
a real-coefficient ring forces each term to be zero. -/
theorem IsKillingField.inner_covderiv_self_eq_zero
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
    {g : SmoothRiemannianMetric I M}
    {X : ∀ x : M, TangentSpace I x}
    {hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X)}
    (hKX : IsKillingField g X hX) (x : M) (V : TangentSpace I x) :
    g.inner x ((LeviCivita (I := I) g) X x V) V = 0 := by
  have h := hKX x V V
  -- `h : g(∇_V X, V) + g(V, ∇_V X) = 0`; the two summands are equal because
  -- `g.inner x` is symmetric (as a smooth Riemannian metric).
  have hsym : g.inner x V ((LeviCivita (I := I) g) X x V) =
      g.inner x ((LeviCivita (I := I) g) X x V) V :=
    g.symm x V ((LeviCivita (I := I) g) X x V)
  rw [hsym] at h
  -- Now `h : g(∇_V X, V) + g(∇_V X, V) = 0`, i.e. `2 * g(∇_V X, V) = 0`.
  have h2 : (2 : ℝ) * g.inner x ((LeviCivita (I := I) g) X x V) V = 0 := by
    have h' :
        g.inner x ((LeviCivita (I := I) g) X x V) V +
          g.inner x ((LeviCivita (I := I) g) X x V) V = 0 := h
    linarith
  have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h2).resolve_left h2_ne

end Symmetry
end Riemannian
end Geometry
