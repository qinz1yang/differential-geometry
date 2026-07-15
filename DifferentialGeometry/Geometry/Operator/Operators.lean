import DifferentialGeometry.Geometry.Metric.MetricBallMonotone
import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Bundle.PartialMfderiv.ModelMixed
import DifferentialGeometry.Bundle.PartialMfderiv.FixedBase
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Realized Scalar Operators

This file defines the pointwise realized gradient, divergence, and Laplacian
directly from mathlib manifold primitives. It deliberately does not import the
experimental integral hierarchy.
-/

namespace DifferentialGeometry.Integral.Connection

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

/-! ## Metric musical maps -/

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

/-- Symmetric form of the sharp identity: `g_x(w, sharp α) = α w`. -/
theorem inner_metricSharp_right
    (g : SmoothRiemannianMetric I M) (x : M)
    (alpha : Module.Dual Real (TangentSpace I x)) (w : TangentSpace I x) :
    g.inner x w (metricSharp (I := I) g x alpha) = alpha w := by
  rw [g.symm x w (metricSharp (I := I) g x alpha)]
  exact inner_metricSharp (I := I) g x alpha w

/-! ## Gradient, divergence, and Laplacian -/

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

/-- If the manifold derivative is the metric-flat covector of `v`, then the
realized gradient is `v`. -/
theorem gradientFun_eq_of_flat
    (g : SmoothRiemannianMetric I M) {f : M -> Real} {x : M}
    {v : TangentSpace I x}
    (hf : (mfderiv I 𝓘(Real, Real) f x).toLinearMap =
      metricFlatEquiv (I := I) g x v) :
    gradientFun (I := I) g f x = v := by
  unfold gradientFun metricSharp
  rw [hf]
  exact LinearEquiv.symm_apply_apply (metricFlatEquiv (I := I) g x) v

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

/-- At a local minimum of a differentiable scalar on a boundaryless manifold,
the realized gradient vanishes. -/
theorem gradientFun_eq_zero_of_isLocalMin
    [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M}
    (hmin : IsLocalMin f x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    gradientFun (I := I) g f x = 0 := by
  apply gradientFun_eq_zero_of_mfderiv_eq_zero
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

/-- The gradient of a finite sum is the finite sum of the gradients. -/
theorem gradientFun_sum {κ : Type}
    (g : SmoothRiemannianMetric I M) (s : Finset κ)
    {f : κ -> M -> Real} {x : M}
    (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    gradientFun (I := I) g (∑ i ∈ s, f i) x =
      ∑ i ∈ s, gradientFun (I := I) g (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change gradientFun (I := I) g (fun _ : M => (0 : Real)) x = 0
      exact gradientFun_const (I := I) g 0 x
  | insert a s ha ih =>
      have hfa : MDifferentiableAt I 𝓘(Real, Real) (f a) x :=
        hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, MDifferentiableAt I 𝓘(Real, Real) (f i) x := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have htail : MDifferentiableAt I 𝓘(Real, Real) (∑ i ∈ s, f i) x :=
        MDifferentiableAt.sum (𝕜 := Real) (I := I) (E' := Real)
          (t := s) (f := f) (z := x) hfs
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc
        gradientFun (I := I) g (f a + ∑ i ∈ s, f i) x
            = gradientFun (I := I) g (f a) x +
                gradientFun (I := I) g (∑ i ∈ s, f i) x := by
              change gradientFun (I := I) g
                (fun y : M => f a y + (∑ i ∈ s, f i) y) x = _
              rw [gradientFun_add (I := I) g hfa htail]
        _ = gradientFun (I := I) g (f a) x +
              ∑ i ∈ s, gradientFun (I := I) g (f i) x := by
              rw [ih hfs]

/-- The gradient of a finite weighted sum is the weighted sum of the gradients. -/
theorem gradientFun_sum_smul {κ : Type}
    (g : SmoothRiemannianMetric I M) (s : Finset κ) (c : κ -> Real)
    {f : κ -> M -> Real} {x : M}
    (hf : ∀ i ∈ s, MDifferentiableAt I 𝓘(Real, Real) (f i) x) :
    gradientFun (I := I) g (∑ i ∈ s, c i • f i) x =
      ∑ i ∈ s, c i • gradientFun (I := I) g (f i) x := by
  classical
  have hsum := gradientFun_sum (I := I) g s
    (f := fun i => c i • f i) (x := x) (by
      intro i hi
      exact (hf i hi).const_smul (c i))
  calc
    gradientFun (I := I) g (∑ i ∈ s, c i • f i) x
        = ∑ i ∈ s, gradientFun (I := I) g (c i • f i) x := hsum
    _ = ∑ i ∈ s, c i • gradientFun (I := I) g (f i) x := by
          apply Finset.sum_congr rfl
          intro i hi
          exact gradientFun_const_smul (I := I) g (c i) (hf i hi)

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

/-- Directional derivative product rule for scalar functions. -/
theorem extDerivFun_mul
    {f h : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    extDerivFun (I := I) (fun y : M => f y * h y) x v =
      f x * extDerivFun (I := I) h x v +
        extDerivFun (I := I) f x v * h x := by
  change extDerivFun (I := I) (f • h) x v =
      f x * extDerivFun (I := I) h x v +
        extDerivFun (I := I) f x v * h x
  have hprod := fromTangentSpace_mfderiv_smul_apply
    (I := I) (f := f) (g := h) hf hh v
  simpa [extDerivFun, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm,
    mul_assoc] using hprod

/-- Directional derivative of a spatially constant scalar multiple, applied to
a tangent vector. -/
theorem extDerivFun_const_mul_apply
    (a : Real) {f : M -> Real} {x : M} (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x) :
    extDerivFun (I := I) (fun y : M => a * f y) x v =
      a * extDerivFun (I := I) f x v := by
  have h := DifferentialGeometry.extDerivFun_const_mul (I := I) a hf
  have hv := DFunLike.congr_fun h v
  simpa [Pi.smul_apply, smul_eq_mul] using hv

/-- Gradient product rule for scalar functions. -/
theorem gradientFun_mul
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hh : MDifferentiableAt I 𝓘(Real, Real) h x) :
    gradientFun (I := I) g (fun y : M => f y * h y) x =
      f x • gradientFun (I := I) g h x +
        h x • gradientFun (I := I) g f x := by
  apply metricFlatLinear_injective (I := I) g x
  ext v
  have hprod := extDerivFun_mul (I := I) (f := f) (h := h) v hf hh
  have hmul :
      g.inner x (gradientFun (I := I) g (fun y : M => f y * h y) x) v =
        f x * g.inner x (gradientFun (I := I) g h x) v +
          g.inner x (gradientFun (I := I) g f x) v * h x := by
    rw [inner_gradientFun (I := I) g (fun y : M => f y * h y) x v]
    have hprod_mf :
        mfderiv I 𝓘(Real, Real) (fun y : M => f y * h y) x v =
          extDerivFun (I := I) (fun y : M => f y * h y) x v := by
      simp [extDerivFun, NormedSpace.fromTangentSpace]
    have hhinner :
        extDerivFun (I := I) h x v =
          g.inner x (gradientFun (I := I) g h x) v := by
      rw [inner_gradientFun (I := I) g h x v]
      simp [extDerivFun, NormedSpace.fromTangentSpace]
    have hfinner :
        extDerivFun (I := I) f x v =
          g.inner x (gradientFun (I := I) g f x) v := by
      rw [inner_gradientFun (I := I) g f x v]
      simp [extDerivFun, NormedSpace.fromTangentSpace]
    rw [hprod_mf, hprod, hhinner, hfinner]
  calc
    metricFlatLinear (I := I) g x
        (gradientFun (I := I) g (fun y : M => f y * h y) x) v =
        f x * g.inner x (gradientFun (I := I) g h x) v +
          g.inner x (gradientFun (I := I) g f x) v * h x := by
          simpa [metricFlatLinear_apply] using hmul
    _ = metricFlatLinear (I := I) g x
        (f x • gradientFun (I := I) g h x +
          h x • gradientFun (I := I) g f x) v := by
          simp [metricFlatLinear_apply, mul_comm]

/-- Directional derivative chain rule for real powers, valid away from zero. -/
theorem extDerivFun_rpow
    {f : M -> Real} {x : M} (p : Real) (v : TangentSpace I x)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hpos : 0 < f x) :
    extDerivFun (I := I) (fun y : M => f y ^ p) x v =
      (p * f x ^ (p - 1)) * extDerivFun (I := I) f x v := by
  let coeff : Real := p * f x ^ (p - 1)
  have hp :
      HasMFDerivAt 𝓘(Real, Real) 𝓘(Real, Real)
        (fun z : Real => z ^ p) (f x)
        (ContinuousLinearMap.toSpanSingleton Real coeff) := by
    simpa [coeff] using
      ((Real.hasDerivAt_rpow_const (p := p) (Or.inl hpos.ne')).hasFDerivAt).hasMFDerivAt
  have hcomp :
      mfderiv I 𝓘(Real, Real) (fun y : M => (fun z : Real => z ^ p) (f y)) x =
        (ContinuousLinearMap.toSpanSingleton Real coeff).comp
          (mfderiv I 𝓘(Real, Real) f x) :=
    (hp.comp x hf.hasMFDerivAt).mfderiv
  unfold extDerivFun
  rw [hcomp]
  change
    NormedSpace.fromTangentSpace (𝕜 := Real) (f x ^ p)
        (((ContinuousLinearMap.toSpanSingleton Real coeff).comp
          (mfderiv I 𝓘(Real, Real) f x)) v) =
      coeff *
        NormedSpace.fromTangentSpace (𝕜 := Real) (f x)
          ((mfderiv I 𝓘(Real, Real) f x) v)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk,
    LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
  rw [mul_comm]
  rfl

/-- Differentiability of a real-power composite at a positive point. -/
theorem mdifferentiableAt_rpow
    {f : M -> Real} {x : M} (p : Real)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hpos : 0 < f x) :
    MDifferentiableAt I 𝓘(Real, Real) (fun y : M => f y ^ p) x := by
  have hp :
      MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Real)
        (fun z : Real => z ^ p) (f x) := by
    exact (Real.differentiableAt_rpow_const_of_ne p hpos.ne').mdifferentiableAt
  exact hp.comp x hf

/-- Gradient chain rule for real powers, valid at positive points. -/
theorem gradientFun_rpow
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M} (p : Real)
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hpos : 0 < f x) :
    gradientFun (I := I) g (fun y : M => f y ^ p) x =
      (p * f x ^ (p - 1)) • gradientFun (I := I) g f x := by
  apply metricFlatLinear_injective (I := I) g x
  ext v
  have hrpow := extDerivFun_rpow (I := I) (f := f) p v hf hpos
  have hrpow_mf :
      mfderiv I 𝓘(Real, Real) (fun y : M => f y ^ p) x v =
        extDerivFun (I := I) (fun y : M => f y ^ p) x v := by
    simp [extDerivFun, NormedSpace.fromTangentSpace]
  have hfinner :
      extDerivFun (I := I) f x v =
        g.inner x (gradientFun (I := I) g f x) v := by
    rw [inner_gradientFun (I := I) g f x v]
    simp [extDerivFun, NormedSpace.fromTangentSpace]
  calc
    metricFlatLinear (I := I) g x
        (gradientFun (I := I) g (fun y : M => f y ^ p) x) v =
        (p * f x ^ (p - 1)) *
          g.inner x (gradientFun (I := I) g f x) v := by
          rw [metricFlatLinear_apply, inner_gradientFun]
          rw [hrpow_mf, hrpow, hfinner]
    _ = metricFlatLinear (I := I) g x
        ((p * f x ^ (p - 1)) • gradientFun (I := I) g f x) v := by
          simp [metricFlatLinear_apply]

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
  ring_nf

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

/-- The Laplacian is linear under subtraction on functions whose gradient
fields are differentiable at the evaluation point. -/
theorem laplacian_sub
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (hgradh : MDiffAt (T% fun y : M => gradientFun (I := I) g h y) x) :
    laplacian (I := I) cov g (fun y : M => f y - h y) x =
      laplacian (I := I) cov g f x -
        laplacian (I := I) cov g h x := by
  have hgrad :
      gradientFun (I := I) g (fun y : M => f y - h y) =
        fun y : M => gradientFun (I := I) g f y -
          gradientFun (I := I) g h y := by
    funext y
    exact gradientFun_sub (I := I) g (hf y) (hh y)
  calc
    laplacian (I := I) cov g (fun y : M => f y - h y) x =
        divergence (I := I) cov
          (fun y : M => gradientFun (I := I) g f y -
            gradientFun (I := I) g h y) x := by
          simp [laplacian, hgrad]
    _ = laplacian (I := I) cov g f x -
        laplacian (I := I) cov g h x := by
          simpa [laplacian, Pi.sub_apply] using
            (divergence_sub (I := I) cov
              (X := fun y : M => gradientFun (I := I) g f y)
              (Y := fun y : M => gradientFun (I := I) g h y)
              hgradf hgradh)

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

/-- Divergence product rule for a scalar multiple of the gradient of another
scalar function. -/
theorem divergence_smul_gradientFun_pair
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : MDifferentiableAt I 𝓘(Real, Real) f x)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g h y) x) :
    divergence (I := I) cov (f • fun y : M => gradientFun (I := I) g h y) x =
      f x * laplacian (I := I) cov g h x +
        g.inner x (gradientFun (I := I) g f x)
          (gradientFun (I := I) g h x) := by
  rw [divergence_smul (I := I) cov hf hgrad]
  have hinner := inner_gradientFun (I := I) g f x (gradientFun (I := I) g h x)
  simpa [extDerivFun] using congrArg id hinner.symm

/-- Scalar product rule for the Laplacian:
`Δ(f h) = f Δh + h Δf + 2 <∇f, ∇h>`. -/
theorem laplacian_mul
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f h : M -> Real} {x : M}
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hh : forall y : M, MDifferentiableAt I 𝓘(Real, Real) h y)
    (hgradf : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x)
    (hgradh : MDiffAt (T% fun y : M => gradientFun (I := I) g h y) x)
    (hfgradh : MDiffAt
      (T% (f • fun y : M => gradientFun (I := I) g h y)) x)
    (hhgradf : MDiffAt
      (T% (h • fun y : M => gradientFun (I := I) g f y)) x) :
    laplacian (I := I) cov g (fun y : M => f y * h y) x =
      f x * laplacian (I := I) cov g h x +
        h x * laplacian (I := I) cov g f x +
          2 * g.inner x
            (gradientFun (I := I) g f x)
            (gradientFun (I := I) g h x) := by
  have hgrad_eq :
      gradientFun (I := I) g (fun y : M => f y * h y) =
        fun y : M =>
          f y • gradientFun (I := I) g h y +
            h y • gradientFun (I := I) g f y := by
    funext y
    exact gradientFun_mul (I := I) g (hf y) (hh y)
  calc
    laplacian (I := I) cov g (fun y : M => f y * h y) x =
        divergence (I := I) cov
          (fun y : M =>
            f y • gradientFun (I := I) g h y +
              h y • gradientFun (I := I) g f y) x := by
          simp [laplacian, hgrad_eq]
    _ =
        divergence (I := I) cov
            (f • fun y : M => gradientFun (I := I) g h y) x +
          divergence (I := I) cov
            (h • fun y : M => gradientFun (I := I) g f y) x := by
          simpa [Pi.add_apply] using
            divergence_add (I := I) cov
              (X := f • fun y : M => gradientFun (I := I) g h y)
              (Y := h • fun y : M => gradientFun (I := I) g f y)
              hfgradh hhgradf
    _ =
        (f x * laplacian (I := I) cov g h x +
            g.inner x (gradientFun (I := I) g f x)
              (gradientFun (I := I) g h x)) +
          (h x * laplacian (I := I) cov g f x +
            g.inner x (gradientFun (I := I) g h x)
              (gradientFun (I := I) g f x)) := by
          rw [divergence_smul_gradientFun_pair (I := I) cov g (hf x) hgradh]
          rw [divergence_smul_gradientFun_pair (I := I) cov g (hh x) hgradf]
    _ =
        f x * laplacian (I := I) cov g h x +
          h x * laplacian (I := I) cov g f x +
            2 * g.inner x
              (gradientFun (I := I) g f x)
              (gradientFun (I := I) g h x) := by
          rw [g.symm x (gradientFun (I := I) g h x)
            (gradientFun (I := I) g f x)]
          ring_nf

/-- Scalar real-power rule for the Laplacian:
`Δ(f^p) = p f^(p-1) Δf + p(p-1) f^(p-2) |∇f|²`,
valid where `f` is positive. -/
theorem laplacian_rpow
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (g : SmoothRiemannianMetric I M)
    {f : M -> Real} {x : M} (p : Real)
    (hf : forall y : M, MDifferentiableAt I 𝓘(Real, Real) f y)
    (hpos : forall y : M, 0 < f y)
    (hgrad : MDiffAt (T% fun y : M => gradientFun (I := I) g f y) x) :
    laplacian (I := I) cov g (fun y : M => f y ^ p) x =
      (p * f x ^ (p - 1)) * laplacian (I := I) cov g f x +
        (p * (p - 1) * f x ^ (p - 2)) *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) := by
  let coeffFun : M -> Real := fun y => p * f y ^ (p - 1)
  have hcoeff :
      MDifferentiableAt I 𝓘(Real, Real) coeffFun x := by
    have hrpow :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => f y ^ (p - 1)) x :=
      mdifferentiableAt_rpow (I := I) (p - 1) (hf x) (hpos x)
    simpa [coeffFun] using mdifferentiableAt_const.mul hrpow
  have hcoeffgrad :
      MDiffAt
        (T% (coeffFun • fun y : M => gradientFun (I := I) g f y)) x := by
    exact hcoeff.smul_section hgrad
  have hgrad_eq :
      gradientFun (I := I) g (fun y : M => f y ^ p) =
        coeffFun • fun y : M => gradientFun (I := I) g f y := by
    funext y
    simpa [coeffFun] using gradientFun_rpow (I := I) g p (hf y) (hpos y)
  have hcoeff_ext :
      extDerivFun (I := I) coeffFun x (gradientFun (I := I) g f x) =
        (p * (p - 1) * f x ^ (p - 2)) *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) := by
    have hrpow :=
      extDerivFun_rpow (I := I) (f := f) (p - 1)
        (gradientFun (I := I) g f x) (hf x) (hpos x)
    have hrpow_diff :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => f y ^ (p - 1)) x :=
      mdifferentiableAt_rpow (I := I) (p - 1) (hf x) (hpos x)
    have hconst :=
      extDerivFun_const_mul_apply (I := I) p
        (f := fun y : M => f y ^ (p - 1))
        (gradientFun (I := I) g f x) hrpow_diff
    have hfinner :
        extDerivFun (I := I) f x (gradientFun (I := I) g f x) =
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) := by
      rw [inner_gradientFun (I := I) g f x (gradientFun (I := I) g f x)]
      simp [extDerivFun, NormedSpace.fromTangentSpace]
    calc
      extDerivFun (I := I) coeffFun x (gradientFun (I := I) g f x) =
          p * extDerivFun (I := I) (fun y : M => f y ^ (p - 1)) x
            (gradientFun (I := I) g f x) := by
            simpa [coeffFun] using hconst
      _ = p * (((p - 1) * f x ^ ((p - 1) - 1)) *
            extDerivFun (I := I) f x
              (gradientFun (I := I) g f x)) := by
            rw [hrpow]
      _ = (p * (p - 1) * f x ^ (p - 2)) *
          g.inner x (gradientFun (I := I) g f x)
            (gradientFun (I := I) g f x) := by
            rw [hfinner]
            ring_nf
  calc
    laplacian (I := I) cov g (fun y : M => f y ^ p) x =
        divergence (I := I) cov
          (coeffFun • fun y : M => gradientFun (I := I) g f y) x := by
          simp [laplacian, hgrad_eq]
    _ =
        coeffFun x * laplacian (I := I) cov g f x +
          extDerivFun (I := I) coeffFun x
            (gradientFun (I := I) g f x) := by
          simpa [laplacian] using
            divergence_smul (I := I) cov hcoeff hgrad
    _ =
        (p * f x ^ (p - 1)) * laplacian (I := I) cov g f x +
          (p * (p - 1) * f x ^ (p - 2)) *
            g.inner x (gradientFun (I := I) g f x)
              (gradientFun (I := I) g f x) := by
          rw [hcoeff_ext]

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
      ring_nf

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


end

end DifferentialGeometry.Integral.Connection
