import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul
import DifferentialGeometry.Geometry.Flow.ConnectionDifference

/-!
# The Christoffel-difference Koszul identity

Given two smooth Riemannian metrics `g₁` and `g₀` on a closed manifold `M`, their
Levi-Civita covariant derivatives `∇¹` and `∇⁰` differ by the connection-difference
tensor `A = connDiff g₁ g₀` (a genuine `(1,2)`-tensor, with the Mathlib evaluation
convention `connDiff g₁ g₀ x (Y x) (X x) = ∇¹_X Y − ∇⁰_X Y`).

This file proves the classical Koszul / Christoffel-difference identity in its
`g₁`-lowered form: pairing `A(X, Y)` against `g₁` produces the symmetric combination of
the `∇⁰`-covariant derivatives of `g₁`,
$$
  2\,g_1\bigl(A(X, Y), Z\bigr)
    = (\nabla^0_X g_1)(Y, Z) + (\nabla^0_Y g_1)(X, Z) - (\nabla^0_Z g_1)(X, Y),
$$
where the covariant derivative of the `(0, 2)`-tensor `g₁` along `∇⁰` is the standard
Leibniz defect
$$
  (\nabla^0_W g_1)(P, Q) = W\bigl(g_1(P, Q)\bigr) - g_1(\nabla^0_W P, Q) - g_1(P, \nabla^0_W Q).
$$
The proof is the subtraction of two Koszul identities: the `g₁`-Koszul identity for `∇¹`
supplies the directional-derivative and Lie-bracket terms; rewriting the brackets via the
torsion-freeness of `∇⁰` and the symmetry of `g₁` collapses the bracket and remainder
terms onto `−2 g₁(∇⁰_X Y, Z)`, which is exactly the contribution of `∇⁰` to the
difference. The metric-only symmetric terms that make a connection non-tensorial cancel,
which is why `A` is a tensor.

Because `∇⁰` is metric-compatible with `g₀`, its covariant derivative of `g₀` vanishes,
so the covariant derivative of the metric **difference** `h := g₁ − g₀` along `∇⁰`
coincides with that of `g₁`.  The companion result `connDiff_koszul_metricDiff` records
the identity in this `h`-form, expressing `A` through the `∇⁰`-covariant gradient of the
metric difference — the structural input for the Ricci–DeTurck linearization symbols.

## Main definitions

* `metricCovDeriv g cov X Y Z x` — the Leibniz-defect covariant derivative
  `(∇^{cov}_X g)(Y, Z)` of the `(0, 2)`-tensor `g` along a covariant derivative `cov`.

## Main results

* `connDiff_koszul` — the `g₁`-lowered Christoffel-difference Koszul identity in
  `metricCovDeriv g₁ ∇⁰` form.
* `metricCovDeriv_self_eq_zero` — metric compatibility makes the covariant derivative of a
  metric along its own Levi-Civita connection vanish.
* `connDiff_koszul_metricDiff` — the identity restated through the `∇⁰`-covariant
  derivative of the metric difference `g₁ − g₀`.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- The **Leibniz-defect covariant derivative** of the `(0, 2)`-tensor `g` along a
covariant derivative `cov`, evaluated at `x` in the direction `X x` on the sections
`Y, Z`:
$$
  (\nabla^{\mathrm{cov}}_X g)(Y, Z)
    = X\bigl(g(Y, Z)\bigr) - g(\nabla_X Y, Z) - g(Y, \nabla_X Z).
$$
For a metric-compatible `cov` (the Levi-Civita connection of `g`) this defect vanishes;
in general it measures the failure of `cov` to be compatible with `g`. -/
def metricCovDeriv (g : Measure.SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  directionalDerivAt (I := I) (fun b => g.inner b (Y b) (Z b)) x (X x)
    - g.inner x (cov.toFun Y x (X x)) (Z x)
    - g.inner x (Y x) (cov.toFun Z x (X x))

/-- The covariant derivative of a metric `g` along its **own** Levi-Civita connection
vanishes: this is exactly the metric-compatibility identity. -/
theorem metricCovDeriv_self_eq_zero (g : Measure.SmoothRiemannianMetric I M)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    metricCovDeriv (I := I) g (LeviCivita (I := I) g) X Y Z x = 0 := by
  have hmc := (LeviCivita_isMetricCompatible (I := I) g).apply hY hZ (X x)
  unfold metricCovDeriv
  rw [directionalDerivAt_eq, hmc]
  ring

/-- **The Christoffel-difference Koszul identity (`g₁`-lowered form).**

Pairing the connection-difference tensor `A = connDiff g₁ g₀` against `g₁` produces the
symmetric combination of the `∇⁰ = LeviCivita g₀`-covariant derivatives of `g₁`:
$$
  2\,g_1\bigl(A(X, Y), Z\bigr)
    = (\nabla^0_X g_1)(Y, Z) + (\nabla^0_Y g_1)(X, Z) - (\nabla^0_Z g_1)(X, Y).
$$
Here `connDiff g₁ g₀ x (Y x) (X x) = ∇¹_X Y − ∇⁰_X Y` (Mathlib convention).  The proof
subtracts the metric-only symmetric terms of the two Koszul identities, which cancel; the
surviving terms are the `∇⁰`-covariant derivatives of `g₁`. -/
theorem connDiff_koszul (g₁ g₀ : SmoothRiemannianMetric I M)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x)) (Z x) =
      metricCovDeriv (I := I) g₁ (LeviCivita (I := I) g₀) X Y Z x
      + metricCovDeriv (I := I) g₁ (LeviCivita (I := I) g₀) Y X Z x
      - metricCovDeriv (I := I) g₁ (LeviCivita (I := I) g₀) Z X Y x := by

  have hK1 := koszul_identity (I := I) (g := g₁) (LeviCivita (I := I) g₁)
    (LeviCivita_torsion_eq_zero (I := I) g₁) (LeviCivita_isMetricCompatible (I := I) g₁)
    hX hY hZ

  have hTF : ∀ ⦃A B : Π y : M, TangentSpace I y⦄ ⦃y : M⦄,
      MDiffAt (T% A) y → MDiffAt (T% B) y →
      (LeviCivita (I := I) g₀).toFun B y (A y) - (LeviCivita (I := I) g₀).toFun A y (B y)
        = VectorField.mlieBracket I A B y := fun A B y hA hB =>
    (CovariantDerivative.torsion_eq_zero_iff (LeviCivita (I := I) g₀)).mp
      (LeviCivita_torsion_eq_zero (I := I) g₀) hA hB
  have tf_XY := hTF hX hY
  have tf_XZ := hTF hX hZ
  have tf_YZ := hTF hY hZ

  set nXY := (LeviCivita (I := I) g₀).toFun Y x (X x) with hnXY
  set nYX := (LeviCivita (I := I) g₀).toFun X x (Y x) with hnYX
  set nXZ := (LeviCivita (I := I) g₀).toFun Z x (X x) with hnXZ
  set nZX := (LeviCivita (I := I) g₀).toFun X x (Z x) with hnZX
  set nYZ := (LeviCivita (I := I) g₀).toFun Z x (Y x) with hnYZ
  set nZY := (LeviCivita (I := I) g₀).toFun Y x (Z x) with hnZY

  rw [PDE.DeTurck.connDiff_apply (I := I) g₁ g₀ hY (X x)]

  unfold metricCovDeriv
  simp only [directionalDerivAt_eq, ← hnXY, ← hnYX, ← hnXZ, ← hnZX, ← hnYZ, ← hnZY]

  rw [← tf_XY, ← tf_XZ, ← tf_YZ] at hK1

  have hlin : ∀ a b c : TangentSpace I x,
      g₁.inner x (a - b) c = g₁.inner x a c - g₁.inner x b c := fun a b c => by
    simp [map_sub, ContinuousLinearMap.sub_apply]
  rw [hlin, hlin, hlin] at hK1

  rw [map_sub, ContinuousLinearMap.sub_apply, mul_sub]
  rw [hK1]

  rw [g₁.symm x (Y x) nXZ, g₁.symm x (X x) nYZ, g₁.symm x (X x) nZY]
  ring

/-- The **`∇⁰`-covariant derivative of the metric difference** `h := g₁ − g₀`, where
`∇⁰ := LeviCivita g₀`:
$$
  (\nabla^0_X h)(Y, Z) = (\nabla^0_X g_1)(Y, Z) - (\nabla^0_X g_0)(Y, Z).
$$
This is the Leibniz-defect covariant derivative of the `(0, 2)`-tensor `h` along `∇⁰`. -/
def metricDiffCovDeriv (g₁ g₀ : SmoothRiemannianMetric I M)
    (X Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  metricCovDeriv (I := I) g₁ (LeviCivita (I := I) g₀) X Y Z x
    - metricCovDeriv (I := I) g₀ (LeviCivita (I := I) g₀) X Y Z x

/-- Since `∇⁰ = LeviCivita g₀` is metric-compatible with `g₀`, the `∇⁰`-covariant
derivative of the metric difference `h := g₁ − g₀` coincides with that of `g₁`. -/
theorem metricDiffCovDeriv_eq_metricCovDeriv (g₁ g₀ : SmoothRiemannianMetric I M)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    metricDiffCovDeriv (I := I) g₁ g₀ X Y Z x =
      metricCovDeriv (I := I) g₁ (LeviCivita (I := I) g₀) X Y Z x := by
  unfold metricDiffCovDeriv
  rw [metricCovDeriv_self_eq_zero (I := I) g₀ hY hZ, sub_zero]

/-- **The Christoffel-difference Koszul identity through the metric difference.**

Restatement of `connDiff_koszul` expressing the `g₁`-pairing of the connection-difference
tensor `A = connDiff g₁ g₀` through the `∇⁰`-covariant derivatives of the metric
difference `h := g₁ − g₀`:
$$
  2\,g_1\bigl(A(X, Y), Z\bigr)
    = (\nabla^0_X h)(Y, Z) + (\nabla^0_Y h)(X, Z) - (\nabla^0_Z h)(X, Y).
$$
This is the classical $\delta\Gamma = \tfrac12 g_1^{-1}(\nabla^0 h + \nabla^0 h - \nabla^0 h)$
Koszul formula in lowered (`g₁`-paired) form; raising by `g₁⁻¹` is the un-pairing through
the non-degeneracy of `g₁`.  It is the structural input expressing the Ricci–DeTurck
linearization symbols through the covariant gradient of the metric difference. -/
theorem connDiff_koszul_metricDiff (g₁ g₀ : SmoothRiemannianMetric I M)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (X x)) (Z x) =
      metricDiffCovDeriv (I := I) g₁ g₀ X Y Z x
      + metricDiffCovDeriv (I := I) g₁ g₀ Y X Z x
      - metricDiffCovDeriv (I := I) g₁ g₀ Z X Y x := by
  rw [metricDiffCovDeriv_eq_metricCovDeriv (I := I) g₁ g₀ hY hZ,
      metricDiffCovDeriv_eq_metricCovDeriv (I := I) g₁ g₀ hX hZ,
      metricDiffCovDeriv_eq_metricCovDeriv (I := I) g₁ g₀ hX hY]
  exact connDiff_koszul (I := I) g₁ g₀ hX hY hZ

end Connection
end Integral
end DifferentialGeometry
