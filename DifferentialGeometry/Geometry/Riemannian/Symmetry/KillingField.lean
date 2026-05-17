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

Both statements rest only on the bundled Levi-Civita covariant derivative
`LeviCivita g` and on `ContMDiffRiemannianMetric.inner`; in particular no
chart-based unfolding is needed.
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

end Symmetry
end Riemannian
end Geometry
