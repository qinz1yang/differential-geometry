import RicciFlower.Operators.LaplacianMinimum
import RicciFlower.Operators.GradientRegularity
import RicciFlower.Realized.MetricFamily

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Realized Family Scalar Operators

The metric musical maps, gradient, divergence, and Laplacian live in
RicciFlower.Operators.  This compatibility layer keeps only the realized
metric-family wrappers and maximum-principle input predicates.
-/

namespace RicciFlower
namespace Realized

noncomputable section

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Time : Type*}

private instance tangentSpace_finiteDimensional (x : M) :
    FiniteDimensional Real (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional Real E)
/-! ## Family-facing wrappers -/

/-- Gradient at a time in a realized metric family. -/
def gradientAt
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) : TangentSpace I x :=
  gradientFun (I := I) (G.metric t) f x

/-- Divergence at a time in a realized metric family. -/
def divergenceAt
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x) (x : M) : Real :=
  divergence (I := I) (G.connection t) X x

/-- Laplacian at a time in a realized metric family. -/
def laplacianAt
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) : Real :=
  laplacian (I := I) (G.connection t) (G.metric t) f x

/-- Drift term `<X, grad f>_g` at a time in a realized metric family. -/
def driftTerm
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    (f : M -> Real) (x : M) : Real :=
  (G.metric t).inner x (X x) (gradientAt (I := I) G t f x)

/-- The scalar spatial operator `Delta_g f + <X, grad f>_g`. -/
def heatOperatorWithDrift
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    (f : M -> Real) (x : M) : Real :=
  laplacianAt (I := I) G t f x + driftTerm (I := I) G t X f x

/-- The driftless scalar heat operator `Delta_g f`. -/
def heatOperator
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) : Real :=
  laplacianAt (I := I) G t f x

@[simp] theorem driftTerm_zero_drift
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    driftTerm (I := I) G t (fun y : M => (0 : TangentSpace I y)) f x = 0 := by
  simp [driftTerm]

@[simp] theorem heatOperator_eq_laplacianAt
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    heatOperator (I := I) G t f x = laplacianAt (I := I) G t f x := by
  rfl

theorem heatOperatorWithDrift_zero_drift
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    heatOperatorWithDrift (I := I) G t
        (fun y : M => (0 : TangentSpace I y)) f x =
      heatOperator (I := I) G t f x := by
  simp [heatOperatorWithDrift, heatOperator]

section FamilyAlgebraicRules

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

/-- The drift term is unchanged by subtracting a spatial constant. -/
theorem driftTerm_sub_const
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} (c : Real) {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    driftTerm (I := I) G t X (fun y : M => f y - c) x =
      driftTerm (I := I) G t X f x := by
  unfold driftTerm gradientAt
  rw [gradientFun_sub (I := I) (G.metric t) hf mdifferentiableAt_const]
  rw [gradientFun_const]
  simp

/-- The drift term scales by a spatially constant scalar. -/
theorem driftTerm_const_smul
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    (a : Real) {f : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    driftTerm (I := I) G t X (a • f) x =
      a * driftTerm (I := I) G t X f x := by
  unfold driftTerm gradientAt
  rw [gradientFun_const_smul (I := I) (G.metric t) a hf]
  simp

/-- The heat operator with drift is unchanged by subtracting a spatial constant. -/
theorem heatOperatorWithDrift_sub_const
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} (c : Real)
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (x : M) :
    heatOperatorWithDrift (I := I) G t X (fun y : M => f y - c) x =
      heatOperatorWithDrift (I := I) G t X f x := by
  unfold heatOperatorWithDrift laplacianAt
  rw [laplacian_sub_const (I := I) (G.connection t) (G.metric t) c hf x]
  rw [driftTerm_sub_const (I := I) G t X c (hf x)]

/-- The heat operator with drift scales by a spatially constant scalar. -/
theorem heatOperatorWithDrift_const_smul
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    (a : Real) {f : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x) :
    heatOperatorWithDrift (I := I) G t X (a • f) x =
      a * heatOperatorWithDrift (I := I) G t X f x := by
  unfold heatOperatorWithDrift laplacianAt
  rw [laplacian_const_smul (I := I) (G.connection t) (G.metric t) a hf hgrad]
  rw [driftTerm_const_smul (I := I) G t X a (hf x)]
  ring

/-- Family-facing subtraction rule for the scalar Laplacian. -/
theorem laplacianAt_sub
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x)
    (hgradh : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) h y) x) :
    laplacianAt (I := I) G t (fun y : M => f y - h y) x =
      laplacianAt (I := I) G t f x -
        laplacianAt (I := I) G t h x := by
  unfold laplacianAt
  exact laplacian_sub (I := I) (G.connection t) (G.metric t)
    hf hh hgradf hgradh

/-- Family-facing constant-scalar rule for the scalar Laplacian. -/
theorem laplacianAt_smul
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (a : Real) {f : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x) :
    laplacianAt (I := I) G t (a • f) x =
      a * laplacianAt (I := I) G t f x := by
  unfold laplacianAt
  exact laplacian_const_smul (I := I) (G.connection t) (G.metric t)
    a hf hgrad

/-- Family-facing scalar-square Laplacian product rule. -/
theorem laplacianAt_sq
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) {f : M -> Real} {x : M}
    (hf_all : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hf_x : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) f y) x)
    (hfg : MDiffAt (T% (f • fun y : M =>
      gradientFun (I := I) (G.metric t) f y)) x) :
    laplacianAt (I := I) G t (fun y : M => f y ^ 2) x =
      2 * f x * laplacianAt (I := I) G t f x +
        2 * (G.metric t).inner x
          (gradientAt (I := I) G t f x)
          (gradientAt (I := I) G t f x) := by
  have hhalf :=
    half_laplacian_mul_self
      (I := I) (G.connection t) (G.metric t) (f := f) (x := x)
      hf_all hf_x hgrad hfg
  unfold laplacianAt gradientAt
  have hpow :
      (fun y : M => f y ^ 2) = fun y : M => f y * f y := by
    funext y
    ring
  rw [hpow]
  have hmain :
      laplacian (I := I) (G.connection t) (G.metric t)
          (fun y : M => f y * f y) x =
        2 * (f x * laplacian (I := I) (G.connection t) (G.metric t) f x +
          (G.metric t).inner x
            (gradientFun (I := I) (G.metric t) f x)
            (gradientFun (I := I) (G.metric t) f x)) := by
    linarith
  rw [hmain]
  ring

/-- Family-facing scalar-square Laplacian product rule with the `f ∇f`
regularity input produced from scalar and gradient regularity. -/
theorem laplacianAt_sq_of_scalarRegular
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) {f : M -> Real} {x : M}
    (hf : ∀ y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : ∀ y : M, MDiffAt (T% fun z : M =>
      gradientFun (I := I) (G.metric t) f z) y) :
    laplacianAt (I := I) G t (fun y : M => f y ^ 2) x =
      2 * f x * laplacianAt (I := I) G t f x +
        2 * (G.metric t).inner x
          (gradientAt (I := I) G t f x)
          (gradientAt (I := I) G t f x) := by
  exact laplacianAt_sq (I := I) G t
    hf (hf x) (hgrad x)
    (scalar_mul_grad_mdiffAt (I := I) (G.metric t) hf hgrad)

end FamilyAlgebraicRules

@[simp] theorem gradientAt_eq
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    gradientAt (I := I) G t f x = gradientFun (I := I) (G.metric t) f x := by
  rfl

@[simp] theorem divergenceAt_eq
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x) (x : M) :
    divergenceAt (I := I) G t X x =
      divergence (I := I) (G.connection t) X x := by
  rfl

@[simp] theorem laplacianAt_eq
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (f : M -> Real) (x : M) :
    laplacianAt (I := I) G t f x =
      laplacian (I := I) (G.connection t) (G.metric t) f x := by
  rfl

/-! ## Minimum-point targets for Theorem 7.1 -/

/-- At a spatial local minimum, the drift term vanishes. -/
theorem driftTerm_eq_zero_at_spatial_min
    [I.Boundaryless]
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    driftTerm (I := I) G t X f x = 0 := by
  unfold driftTerm gradientAt
  rw [gradientFun_eq_zero_at_spatial_min (I := I) (G.metric t) hmin hf]
  simp

/-- Family version of the second-order Laplacian positivity input. -/
def LaplacianNonnegativeAtSpatialMinFamily
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Time) : Prop :=
  forall t : Time,
    LaplacianNonnegativeAtSpatialMin (I := I) (G.connection t) (G.metric t)

/-- A realized metric family supplies the Laplacian nonnegativity input at
each time. -/
theorem laplacianNonnegativeAtSpatialMinFamily_of_realizedMetricFamily
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (G : RealizedMetricFamily (I := I) (M := M) Time) :
    LaplacianNonnegativeAtSpatialMinFamily (I := I) G := by
  intro t
  exact laplacianNonnegativeAtSpatialMin_of_metricCompatible (I := I)
    (G.connection t) (G.metric t) (G.metricCompatible t)

/-- At a spatial local minimum, `Delta f + <X, grad f>` is nonnegative. -/
theorem heatOperatorWithDrift_at_spatial_min_nonneg
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hf_near : ∀ᶠ y in nhds x, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) f y) x) :
    0 <= heatOperatorWithDrift (I := I) G t X f x := by
  unfold heatOperatorWithDrift
  rw [driftTerm_eq_zero_at_spatial_min (I := I) G t X hmin hf, add_zero]
  exact laplacian_nonneg_at_spatial_min_of_metricCompatible (I := I)
    (G.connection t) (G.metric t) (G.metricCompatible t) hmin hf hf_near hgrad

end

end Realized
end RicciFlower
