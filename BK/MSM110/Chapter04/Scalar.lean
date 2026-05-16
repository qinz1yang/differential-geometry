/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RicciFlower contributors
-/

import RicciFlower.MaximumPrinciple.ScalarWeak

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# MSM110 Chapter 4 Scalar Maximum Principles

This companion module preserves the Chapter 4 scalar labels as thin wrappers
around the canonical proof interfaces in
`RicciFlower.MaximumPrinciple.ScalarWeak`.
-/

namespace BK
namespace MSM110
namespace Chapter04
namespace Scalar

noncomputable section

open Bundle Set RicciFlower.Realized
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- MSM110 Chapter 4, label `thm:scalar_maximum_principle_supersolutions`. -/
theorem thm_scalar_maximum_principle_supersolutions
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (alpha : Real)
    (hw_cont : ContinuousOn (fun p : Real × M => u p.1 p.2 - alpha)
      (spacetimeSlab (M := M) T))
    (hw_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => u s x - alpha) (Set.Icc 0 T) t)
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => u t y - alpha) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - alpha) y) x)
    (hinit : forall x : M, alpha <= u 0 x)
    (hnegative : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      u t x < alpha ->
        0 <= parabolicOperatorWithDrift (I := I) G T X
          (fun s y => u s y - alpha) t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, alpha <= u t x := by
  exact RicciFlower.Realized.msm110_ch4_scalar_supersolutions
    (I := I) G T hT X u alpha
    hw_cont hw_time hw_mdiff hw_grad hinit hnegative

/-- MSM110 Chapter 4, label `prop:scalar_maximum_principle_pointwise`. -/
theorem prop_scalar_maximum_principle_pointwise
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (C1 C2 : Real) (hC : C1 <= C2)
    (hlower_cont : ContinuousOn (fun p : Real × M => u p.1 p.2 - C1)
      (spacetimeSlab (M := M) T))
    (hlower_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => u s x - C1) (Set.Icc 0 T) t)
    (hlower_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => u t y - C1) x)
    (hlower_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - C1) y) x)
    (hupper_cont : ContinuousOn (fun p : Real × M => C2 - u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hupper_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => C2 - u s x) (Set.Icc 0 T) t)
    (hupper_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => C2 - u t y) x)
    (hupper_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => C2 - u t z) y) x)
    (hinit_lower : forall x : M, C1 <= u 0 x)
    (hinit_upper : forall x : M, u 0 x <= C2)
    (hlower_negative : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      u t x < C1 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X
          (fun s y => u s y - C1) t x)
    (hupper_negative : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      C2 < u t x ->
        0 <= parabolicOperatorWithDrift (I := I) G T X
          (fun s y => C2 - u s y) t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      C1 <= u t x ∧ u t x <= C2 := by
  exact RicciFlower.Realized.msm110_ch4_scalar_pointwise_bounds
    (I := I) G T hT X u C1 C2 hC
    hlower_cont hlower_time hlower_mdiff hlower_grad
    hupper_cont hupper_time hupper_mdiff hupper_grad
    hinit_lower hinit_upper hlower_negative hupper_negative

/-- MSM110 Chapter 4, label `prop:scalar_maximum_principle_linear_reaction`. -/
theorem prop_scalar_maximum_principle_linear_reaction
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (beta : Real -> M -> Real) (C : Real)
    (hbeta_bound : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      beta t x <= C)
    (hJ_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-C * p.1) * u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hJ_time : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, DifferentiableWithinAt Real
        (fun s : Real => Real.exp (-C * s) * u s x) (Set.Icc 0 T) t)
    (hJ_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-C * t) * u t y) x)
    (hJ_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-C * t) * u t z) y) x)
    (hinit : forall x : M, 0 <= u 0 x)
    (hJ_negative : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      Real.exp (-C * t) * u t x < 0 ->
        0 <= parabolicOperatorWithDrift (I := I) G T X
          (fun s y => Real.exp (-C * s) * u s y) t x) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, 0 <= u t x := by
  exact RicciFlower.Realized.msm110_ch4_scalar_linear_reaction
    (I := I) G T hT X u beta C hbeta_bound
    hJ_cont hJ_time hJ_mdiff hJ_grad hinit hJ_negative

/-- MSM110 Chapter 4, label `thm:scalar_maximum_principle_ode`. -/
theorem thm_scalar_maximum_principle_ode
    [I.Boundaryless]
    [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : RealizedMetricFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 <= T)
    (X : Real -> (x : M) -> TangentSpace I x)
    (u : Real -> M -> Real) (c : Real -> Real)
    (F : Real -> Real) (K : NNReal) (hF_mono : Monotone F)
    (hw_cont : ContinuousOn
      (fun p : Real × M => Real.exp (-(K : Real) * p.1) * (u p.1 p.2 - c p.1))
      (spacetimeSlab (M := M) T))
    (hw_mdiff : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun y : M => Real.exp (-(K : Real) * t) * (u t y - c t)) x)
    (hw_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t)
          (fun z : M => Real.exp (-(K : Real) * t) * (u t z - c t)) y) x)
    (hu_time : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      DifferentiableWithinAt Real (fun s : Real => u s x) (Set.Icc 0 T) t)
    (hc_time : forall t : Real, t ∈ Set.Icc 0 T ->
      DifferentiableWithinAt Real c (Set.Icc 0 T) t)
    (hu_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real) (u t) y)
    (hv_space : forall t : Real, t ∈ Set.Icc 0 T ->
      forall y : M, MDifferentiableAt I 𝓘(Real, Real)
        (fun z : M => u t z - c t) y)
    (hv_grad : forall t : Real, t ∈ Set.Icc 0 T ->
      forall x : M, MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (fun z : M => u t z - c t) y) x)
    (hsuper : forall t : Real, t ∈ Set.Icc 0 T -> forall x : M,
      F (u t x) <= parabolicOperatorWithDrift (I := I) G T X u t x)
    (hode : forall t : Real, t ∈ Set.Icc 0 T ->
      derivWithin c (Set.Icc 0 T) t = F (c t))
    (hinit : forall x : M, c 0 <= u 0 x)
    (hF_lip : forall t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K (fun a : Real => F a)
        (scalarWMPValueSet (M := M) T u c)) :
    forall t : Real, t ∈ Set.Icc 0 T -> forall x : M, c t <= u t x := by
  exact RicciFlower.Realized.msm110_ch4_scalar_ode_lower
    (I := I) G T hT X u c F K hF_mono
    hw_cont hw_mdiff hw_grad hu_time hc_time hu_space hv_space hv_grad
    hsuper hode hinit hF_lip

end

end Scalar
end Chapter04
end MSM110
end BK
