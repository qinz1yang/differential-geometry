import DifferentialGeometry.Realized.Connection
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# DifferentialGeometry Realized Scalar Operators

This file defines the pointwise realized gradient, divergence, and Laplacian
directly from mathlib manifold primitives. It deliberately does not import the
experimental integral hierarchy.
-/

namespace DifferentialGeometry
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

/-- The pointwise musical-flat linear map induced by a realized metric. -/
def metricFlatLinear (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →ₗ[Real] Module.Dual Real (TangentSpace I x) where
  toFun v := (g.inner x v).toLinearMap
  map_add' v w := by
    ext u
    change g.inner x (v + w) u = g.inner x v u + g.inner x w u
    simp
  map_smul' c v := by
    ext u
    change g.inner x (c • v) u = c • g.inner x v u
    simp

@[simp] theorem metricFlatLinear_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    metricFlatLinear (I := I) g x v w = g.inner x v w := by
  rfl

/-- The flat map is injective by positive-definiteness of the metric. -/
theorem metricFlatLinear_injective
    (g : SmoothRiemannianMetric I M) (x : M) :
    Function.Injective (metricFlatLinear (I := I) g x) := by
  intro v w hvw
  have hzero : forall z : TangentSpace I x, g.inner x (v - w) z = 0 := by
    intro z
    have h := congrArg (fun L : Module.Dual Real (TangentSpace I x) => L z) hvw
    simp only [metricFlatLinear_apply] at h
    have hsub : g.inner x (v - w) z = g.inner x v z - g.inner x w z := by
      rw [map_sub]
      rfl
    rw [hsub, sub_eq_zero]
    exact h
  by_contra hne
  have hvw_ne : v - w ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < g.inner x (v - w) (v - w) := g.pos x (v - w) hvw_ne
  exact (lt_irrefl (0 : Real)) ((hzero (v - w)) ▸ hpos)

private theorem metricFlatLinear_finrank_eq (x : M) :
    Module.finrank Real (TangentSpace I x) =
      Module.finrank Real (Module.Dual Real (TangentSpace I x)) :=
  Subspace.dual_finrank_eq.symm

/-- The pointwise musical-flat equivalence induced by a realized metric. -/
def metricFlatEquiv (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x ≃ₗ[Real] Module.Dual Real (TangentSpace I x) :=
  LinearMap.linearEquivOfInjective
    (metricFlatLinear (I := I) g x)
    (metricFlatLinear_injective (I := I) g x)
    (metricFlatLinear_finrank_eq (I := I) (M := M) x)

@[simp] theorem metricFlatEquiv_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    metricFlatEquiv (I := I) g x v w = g.inner x v w := by
  rfl

/-- The pointwise musical-sharp map induced by a realized metric. -/
def metricSharp (g : SmoothRiemannianMetric I M) (x : M)
    (alpha : Module.Dual Real (TangentSpace I x)) : TangentSpace I x :=
  (metricFlatEquiv (I := I) g x).symm alpha

@[simp] theorem metricSharp_eq
    (g : SmoothRiemannianMetric I M) (x : M)
    (alpha : Module.Dual Real (TangentSpace I x)) :
    metricSharp (I := I) g x alpha =
      (metricFlatEquiv (I := I) g x).symm alpha := by
  rfl

/-- Defining identity for the sharp map. -/
theorem inner_metricSharp
    (g : SmoothRiemannianMetric I M) (x : M)
    (alpha : Module.Dual Real (TangentSpace I x)) (w : TangentSpace I x) :
    g.inner x (metricSharp (I := I) g x alpha) w = alpha w := by
  change metricFlatEquiv (I := I) g x
      ((metricFlatEquiv (I := I) g x).symm alpha) w = alpha w
  have h :
      metricFlatEquiv (I := I) g x
          ((metricFlatEquiv (I := I) g x).symm alpha) = alpha :=
    LinearEquiv.apply_symm_apply (metricFlatEquiv (I := I) g x) alpha
  exact congrArg (fun L : Module.Dual Real (TangentSpace I x) => L w) h

/-- Pointwise gradient of a scalar function with respect to a realized metric. -/
def gradientFun (g : SmoothRiemannianMetric I M) (f : M -> Real) (x : M) :
    TangentSpace I x :=
  metricSharp (I := I) g x (mfderiv I 𝓘(Real, Real) f x).toLinearMap

@[simp] theorem gradientFun_eq
    (g : SmoothRiemannianMetric I M) (f : M -> Real) (x : M) :
    gradientFun (I := I) g f x =
      metricSharp (I := I) g x (mfderiv I 𝓘(Real, Real) f x).toLinearMap := by
  rfl

/-- Gradient duality against the metric. -/
theorem inner_gradientFun
    (g : SmoothRiemannianMetric I M) (f : M -> Real) (x : M)
    (v : TangentSpace I x) :
    g.inner x (gradientFun (I := I) g f x) v =
      mfderiv I 𝓘(Real, Real) f x v := by
  simpa [gradientFun] using
    inner_metricSharp (I := I) g x
      (mfderiv I 𝓘(Real, Real) f x).toLinearMap v

/-- The gradient vanishes if the manifold derivative vanishes. -/
theorem gradientFun_eq_zero_of_mfderiv_eq_zero
    (g : SmoothRiemannianMetric I M) (f : M -> Real) {x : M}
    (hf : mfderiv I 𝓘(Real, Real) f x = 0) :
    gradientFun (I := I) g f x = 0 := by
  unfold gradientFun metricSharp
  have hto :
      (mfderiv I 𝓘(Real, Real) f x).toLinearMap =
        (0 : Module.Dual Real (TangentSpace I x)) := by
    rw [hf]
    rfl
  rw [hto]
  exact LinearEquiv.map_zero (metricFlatEquiv (I := I) g x).symm

/-- The gradient of a spatial constant vanishes. -/
@[simp] theorem gradientFun_const
    (g : SmoothRiemannianMetric I M) (c : Real) (x : M) :
    gradientFun (I := I) g (fun _ : M => c) x = 0 := by
  apply gradientFun_eq_zero_of_mfderiv_eq_zero
  exact mfderiv_const

/-- The gradient is linear under multiplication by a spatially constant scalar. -/
theorem gradientFun_const_smul
    (g : SmoothRiemannianMetric I M) (a : Real)
    {f : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g (a • f) x =
      a • gradientFun (I := I) g f x := by
  unfold gradientFun metricSharp
  rw [const_smul_mfderiv hf a]
  rw [ContinuousLinearMap.coe_smul]
  let e := (metricFlatEquiv (I := I) g x).symm
  exact e.map_smul a (mfderiv I 𝓘(Real, Real) f x).toLinearMap

/-- The gradient is additive. -/
theorem gradientFun_add
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    gradientFun (I := I) g (fun y : M => f y + h y) x =
      gradientFun (I := I) g f x + gradientFun (I := I) g h x := by
  change gradientFun (I := I) g (f + h) x =
      gradientFun (I := I) g f x + gradientFun (I := I) g h x
  unfold gradientFun metricSharp
  rw [mfderiv_add hf hh]
  rw [ContinuousLinearMap.coe_add]
  let e := (metricFlatEquiv (I := I) g x).symm
  exact e.map_add (mfderiv I 𝓘(Real, Real) f x).toLinearMap
    (mfderiv I 𝓘(Real, Real) h x).toLinearMap

/-- The gradient is linear under subtraction. -/
theorem gradientFun_sub
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    gradientFun (I := I) g (fun y : M => f y - h y) x =
      gradientFun (I := I) g f x - gradientFun (I := I) g h x := by
  change gradientFun (I := I) g (f - h) x =
      gradientFun (I := I) g f x - gradientFun (I := I) g h x
  unfold gradientFun metricSharp
  rw [mfderiv_sub hf hh]
  rw [ContinuousLinearMap.coe_sub]
  let e := (metricFlatEquiv (I := I) g x).symm
  exact e.map_sub (mfderiv I 𝓘(Real, Real) f x).toLinearMap
    (mfderiv I 𝓘(Real, Real) h x).toLinearMap

/-- First derivative of `f^2`, stated as a linear-map scalar-multiplication
identity. The proof deliberately stays in module scalar multiplication while
the target is the scalar model tangent space. -/
theorem mfderiv_mul_self_toLinearMap
    {f : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    (mfderiv I 𝓘(Real, Real) (fun y : M => f y * f y) x).toLinearMap =
      (2 * f x) • (mfderiv I 𝓘(Real, Real) f x).toLinearMap := by
  have hmul :
      mfderiv I 𝓘(Real, Real) (fun y : M => f y * f y) x =
        f x • mfderiv I 𝓘(Real, Real) f x +
          f x • mfderiv I 𝓘(Real, Real) f x := by
    simpa only [Pi.mul_apply] using
      (hf.hasMFDerivAt.mul hf.hasMFDerivAt).mfderiv
  rw [hmul]
  ext v
  rw [ContinuousLinearMap.coe_add]
  change
    f x • ((mfderiv I 𝓘(Real, Real) f x).toLinearMap v) +
      f x • ((mfderiv I 𝓘(Real, Real) f x).toLinearMap v) =
        (2 * f x) • ((mfderiv I 𝓘(Real, Real) f x).toLinearMap v)
  rw [← add_smul]
  congr 1
  ring

/-- Gradient of a scalar square. -/
theorem gradientFun_mul_self
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g (fun y : M => f y * f y) x =
      (2 * f x) • gradientFun (I := I) g f x := by
  unfold gradientFun metricSharp
  change
    (metricFlatEquiv (I := I) g x).symm
      ((mfderiv I 𝓘(Real, Real) (fun y : M => f y * f y) x).toLinearMap) =
      (2 * f x) •
        (metricFlatEquiv (I := I) g x).symm
          ((mfderiv I 𝓘(Real, Real) f x).toLinearMap)
  rw [mfderiv_mul_self_toLinearMap (I := I) (f := f) hf]
  exact LinearEquiv.map_smul
    (metricFlatEquiv (I := I) g x).symm
    (2 * f x)
    ((mfderiv I 𝓘(Real, Real) f x).toLinearMap)

/-- Divergence of a vector field, defined as the trace of its covariant derivative. -/
def divergence
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : (x : M) -> TangentSpace I x) (x : M) : Real :=
  LinearMap.trace Real (TangentSpace I x) (cov X x).toLinearMap

@[simp] theorem divergence_eq
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (X : (x : M) -> TangentSpace I x) (x : M) :
    divergence (I := I) cov X x =
      LinearMap.trace Real (TangentSpace I x) (cov X x).toLinearMap := by
  rfl

/-- Laplacian of a scalar function, defined as `div grad`. -/
def laplacian
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (f : M -> Real) (x : M) : Real :=
  divergence (I := I) cov (gradientFun (I := I) g f) x

@[simp] theorem laplacian_eq
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (f : M -> Real) (x : M) :
    laplacian (I := I) cov g f x =
      divergence (I := I) cov (gradientFun (I := I) g f) x := by
  rfl

section AlgebraicRules

variable [VectorBundle Real E (TangentSpace I : M -> Type _)]

/-- The divergence of the zero vector field is zero. -/
@[simp] theorem divergence_zero
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (x : M) :
    divergence (I := I) cov (0 : (x : M) -> TangentSpace I x) x = 0 := by
  simp [divergence]

/-- Divergence is additive on differentiable vector fields. -/
theorem divergence_add
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {X Y : (x : M) -> TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    divergence (I := I) cov (X + Y) x =
      divergence (I := I) cov X x + divergence (I := I) cov Y x := by
  unfold divergence
  rw [cov.isCovariantDerivativeOnUniv.add hX hY]
  simp

/-- Divergence is linear under multiplication by a spatially constant scalar. -/
theorem divergence_const_smul
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (a : Real) {X : (x : M) -> TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) :
    divergence (I := I) cov (a • X) x =
      a * divergence (I := I) cov X x := by
  unfold divergence
  rw [cov.isCovariantDerivativeOnUniv.smul_const a hX]
  simp

/-- Product rule for divergence of a scalar multiple of a vector field. -/
theorem divergence_smul
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {f : M -> Real} {X : (x : M) -> TangentSpace I x} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hX : MDiffAt (T% X) x) :
    divergence (I := I) cov (f • X) x =
      f x * divergence (I := I) cov X x +
        extDerivFun (I := I) f x (X x) := by
  unfold divergence
  rw [cov.isCovariantDerivativeOnUniv.leibniz hX hf]
  rw [ContinuousLinearMap.coe_add]
  rw [map_add]
  change
      LinearMap.trace Real (TangentSpace I x) (f x • (cov X x).toLinearMap) +
          LinearMap.trace Real (TangentSpace I x)
            ((extDerivFun (I := I) f x).toLinearMap.smulRight (X x)) =
        f x * LinearMap.trace Real (TangentSpace I x) (cov X x).toLinearMap +
          extDerivFun (I := I) f x (X x)
  rw [map_smul, LinearMap.trace_smulRight]
  simp [smul_eq_mul]

/-- Divergence is linear under subtraction on differentiable vector fields. -/
theorem divergence_sub
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {X Y : (x : M) -> TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    divergence (I := I) cov (X - Y) x =
      divergence (I := I) cov X x - divergence (I := I) cov Y x := by
  unfold divergence
  rw [sub_eq_add_neg,
    cov.isCovariantDerivativeOnUniv.add hX (mdifferentiableAt_neg_section hY)]
  have hneg : cov (-Y) x = (-1 : Real) • cov Y x := by
    simpa using cov.isCovariantDerivativeOnUniv.smul_const (-1 : Real) hY
  rw [hneg]
  rw [ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_smul]
  rw [map_add, map_smul]
  simp [sub_eq_add_neg]

/-- The Laplacian of a spatial constant is zero. -/
@[simp] theorem laplacian_const
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) (c : Real) (x : M) :
    laplacian (I := I) cov g (fun _ : M => c) x = 0 := by
  have hgrad :
      gradientFun (I := I) g (fun _ : M => c) =
        (0 : (x : M) -> TangentSpace I x) := by
    funext y
    exact gradientFun_const (I := I) g c y
  simp [laplacian, hgrad]

/-- The Laplacian is unchanged by subtracting a spatial constant. -/
theorem laplacian_sub_const
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} (c : Real)
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (x : M) :
    laplacian (I := I) cov g (fun y : M => f y - c) x =
      laplacian (I := I) cov g f x := by
  have hgrad :
      gradientFun (I := I) g (fun y : M => f y - c) =
        gradientFun (I := I) g f := by
    funext y
    calc
      gradientFun (I := I) g (fun y : M => f y - c) y =
          gradientFun (I := I) g f y -
            gradientFun (I := I) g (fun _ : M => c) y := by
        exact gradientFun_sub (I := I) g (hf y) mdifferentiableAt_const
      _ = gradientFun (I := I) g f y - 0 := by
        rw [gradientFun_const]
      _ = gradientFun (I := I) g f y := by simp
  simp [laplacian, hgrad]

/-- The Laplacian scales by a spatially constant scalar. -/
theorem laplacian_const_smul
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (a : Real) {f : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (a • f) x =
      a * laplacian (I := I) cov g f x := by
  have hgrad_eq :
      gradientFun (I := I) g (a • f) =
        a • gradientFun (I := I) g f := by
    funext y
    exact gradientFun_const_smul (I := I) g a (hf y)
  calc
    laplacian (I := I) cov g (a • f) x =
        divergence (I := I) cov (a • gradientFun (I := I) g f) x := by
      simp [laplacian, hgrad_eq]
    _ = a * laplacian (I := I) cov g f x := by
      rw [divergence_const_smul (I := I) cov a hgrad]
      rfl

/-- Divergence of `u ∇u`: the middle identity in the scalar square
Laplacian formula. -/
theorem divergence_smul_gradientFun
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    divergence (I := I) cov (f • fun y : M => gradientFun (I := I) g f y) x =
      f x * laplacian (I := I) cov g f x +
        g.inner x (gradientFun (I := I) g f x) (gradientFun (I := I) g f x) := by
  rw [divergence_smul (I := I) cov hf hgrad]
  have hinner := inner_gradientFun (I := I) g f x (gradientFun (I := I) g f x)
  simpa [extDerivFun] using congrArg id hinner.symm

/-- Left identity in the scalar square Laplacian formula:
`(1 / 2) Δ(f^2) = div(f ∇f)`. -/
theorem half_laplacian_mul_self_eq_divergence_smul_gradientFun
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hfg : MDiffAt
      (T% (f • fun y : M => gradientFun (I := I) g f y)) x) :
    (1 / 2 : Real) * laplacian (I := I) cov g (fun y : M => f y * f y) x =
      divergence (I := I) cov
        (f • fun y : M => gradientFun (I := I) g f y) x := by
  have hgrad :
      gradientFun (I := I) g (fun y : M => f y * f y) =
        (2 : Real) •
          (f • fun y : M => gradientFun (I := I) g f y) := by
    funext y
    rw [gradientFun_mul_self (I := I) g (hf y)]
    simp [Pi.smul_apply, smul_smul, mul_comm]
  calc
    (1 / 2 : Real) * laplacian (I := I) cov g (fun y : M => f y * f y) x =
        (1 / 2 : Real) *
          divergence (I := I) cov
            ((2 : Real) •
              (f • fun y : M => gradientFun (I := I) g f y)) x := by
      simp [laplacian, hgrad]
    _ = (1 / 2 : Real) *
        (2 * divergence (I := I) cov
          (f • fun y : M => gradientFun (I := I) g f y) x) := by
      rw [divergence_const_smul (I := I) cov (2 : Real) hfg]
    _ = divergence (I := I) cov
        (f • fun y : M => gradientFun (I := I) g f y) x := by
      ring

/-- Scalar square Laplacian formula:
`(1 / 2) Δ(f^2) = f Δf + |∇f|^2`. -/
theorem half_laplacian_mul_self
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hf_all : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hf_x : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (hfg : MDiffAt
      (T% (f • fun y : M => gradientFun (I := I) g f y)) x) :
    (1 / 2 : Real) * laplacian (I := I) cov g (fun y : M => f y * f y) x =
      f x * laplacian (I := I) cov g f x +
        g.inner x (gradientFun (I := I) g f x)
          (gradientFun (I := I) g f x) := by
  rw [half_laplacian_mul_self_eq_divergence_smul_gradientFun
    (I := I) cov g hf_all hfg]
  exact divergence_smul_gradientFun (I := I) cov g hf_x hgrad

end AlgebraicRules

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

/-- First-order Fermat rule for a scalar function on a boundaryless realized
manifold.

This is the chart-level bridge from mathlib's Euclidean
`IsLocalMin.fderiv_eq_zero` to the manifold derivative used by `gradientFun`.
The boundaryless assumption makes the model-with-corners range locally equal
to the whole model space, so `fderivWithin` becomes `fderiv`. -/
theorem mfderiv_eq_zero_at_spatial_min
    [I.Boundaryless]
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    mfderiv I 𝓘(Real, Real) f x = 0 := by
  have hmin_chart :
      IsLocalMin (fun y : E => f ((extChartAt I x).symm y))
        ((extChartAt I x) x) := by
    have hmin' :
        IsLocalMin f ((extChartAt I x).symm ((extChartAt I x) x)) := by
      simpa only [mfld_simps] using hmin
    simpa only [Function.comp_apply] using
      hmin'.comp_continuous (continuousAt_extChartAt_symm (I := I) x)
  have hderiv_chart :
      fderiv Real (fun y : E => f ((extChartAt I x).symm y))
        ((extChartAt I x) x) = 0 :=
    hmin_chart.fderiv_eq_zero
  have hrange : Set.range I ∈ nhds ((extChartAt I x) x) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ (I := I)]
    exact Filter.univ_mem
  calc
    mfderiv I 𝓘(Real, Real) f x =
        fderivWithin Real (writtenInExtChartAt I 𝓘(Real, Real) x f)
          (Set.range I) ((extChartAt I x) x) := by
      exact hf.mfderiv
    _ = fderiv Real (writtenInExtChartAt I 𝓘(Real, Real) x f)
          ((extChartAt I x) x) := by
      exact fderivWithin_of_mem_nhds hrange
    _ = 0 := by
      simpa [writtenInExtChartAt] using hderiv_chart

/-- At a spatial local minimum, the realized gradient vanishes.

Expected proof: pass to a chart at `x`, use the ordinary first-derivative test
for the chart representative, then translate `fderiv = 0` back to `mfderiv = 0`
and apply `gradientFun_eq_zero_of_mfderiv_eq_zero`. -/
theorem gradientFun_eq_zero_at_spatial_min
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g f x = 0 := by
  exact gradientFun_eq_zero_of_mfderiv_eq_zero (I := I) g f
    (mfderiv_eq_zero_at_spatial_min (I := I) hmin hf)

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

/-- The precise second-order local input needed for maximum principles.

This is not bundled into `RealizedMetricFamily`: it is the future theorem to
prove from a Levi-Civita normal-frame construction. Mathematically, the proof
should use a local orthonormal normal frame at `x`; in that frame the
connection coefficients vanish at `x`, so `Delta f` is the trace of the
ordinary Hessian of the chart representative. The Hessian is positive
semidefinite at a local minimum, hence its metric trace is nonnegative. -/
def LaplacianNonnegativeAtSpatialMin
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M) : Prop :=
  forall {f : M -> Real} {x : M},
    IsLocalMin f x ->
      MDifferentiableAt I 𝓘(Real, Real) f x ->
        MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x ->
          0 <= laplacian (I := I) cov g f x

/-- Family version of the second-order Laplacian positivity input. -/
def LaplacianNonnegativeAtSpatialMinFamily
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Time) : Prop :=
  forall t : Time,
    LaplacianNonnegativeAtSpatialMin (I := I) (G.connection t) (G.metric t)

/-- At a spatial local minimum, the Levi-Civita Laplacian is nonnegative,
assuming the local normal-frame/Hessian trace positivity input. -/
theorem laplacian_nonneg_at_spatial_min
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    (_hmc : IsMetricCompatibleMathlib (I := I) (M := M) cov g)
    (_htf : cov.torsion = 0)
    (hlap : LaplacianNonnegativeAtSpatialMin (I := I) cov g)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    0 <= laplacian (I := I) cov g f x := by
  exact hlap hmin hf hgrad

/-- At a spatial local minimum, `Delta f + <X, grad f>` is nonnegative. -/
theorem heatOperatorWithDrift_at_spatial_min_nonneg
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Time)
    (_hmc : IsMetricCompatibleFamily G)
    (_htf : IsTorsionFreeFamily G)
    (hlap : LaplacianNonnegativeAtSpatialMinFamily (I := I) G)
    (t : Time) (X : (x : M) -> TangentSpace I x)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) f y) x) :
    0 <= heatOperatorWithDrift (I := I) G t X f x := by
  unfold heatOperatorWithDrift
  rw [driftTerm_eq_zero_at_spatial_min (I := I) G t X hmin hf, add_zero]
  exact laplacian_nonneg_at_spatial_min (I := I)
    (G.connection t) (G.metric t) (_hmc t) (_htf t) (hlap t) hmin hf hgrad

end

end Realized
end DifferentialGeometry
