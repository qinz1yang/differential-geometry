import DifferentialGeometry.Analysis.InnerProductSpace.RankOneKernelProjection.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private def operatorTraceCLM : (E →L[ℝ] E) →L[ℝ] ℝ :=
  ((LinearMap.trace ℝ E).comp (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap

private theorem operatorTraceCLM_apply (A : E →L[ℝ] E) :
    operatorTraceCLM A = LinearMap.trace ℝ E A.toLinearMap := rfl


theorem continuousWithinAt_rankOneKernelProjection
    {T : Type*} [TopologicalSpace T] {J : Set T} {b : T}
    {A : T → (E →L[ℝ] E)} (hA : ContinuousWithinAt A J b)
    (hτ : LinearMap.trace ℝ E (A b).toLinearMap ≠ 0) :
    ContinuousWithinAt (fun t => ContinuousLinearMap.id ℝ E -
      (LinearMap.trace ℝ E (A t).toLinearMap)⁻¹ • A t) J b := by
  have htrace : ContinuousWithinAt
      (fun t => LinearMap.trace ℝ E (A t).toLinearMap) J b :=
    operatorTraceCLM.continuous.continuousAt.comp_continuousWithinAt hA
  exact continuousWithinAt_const.sub ((htrace.inv₀ hτ).smul hA)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]


theorem fderiv_rankOneKernelProjection_apply
    {A : F → (E →L[ℝ] E)} {x : F} (hA : DifferentiableAt ℝ A x)
    (hτ : LinearMap.trace ℝ E (A x).toLinearMap ≠ 0) (v : F) :
    fderiv ℝ (fun y => ContinuousLinearMap.id ℝ E -
        (LinearMap.trace ℝ E (A y).toLinearMap)⁻¹ • A y) x v =
      -(LinearMap.trace ℝ E (A x).toLinearMap)⁻¹ • fderiv ℝ A x v +
        (((LinearMap.trace ℝ E (A x).toLinearMap) ^ 2)⁻¹ *
          LinearMap.trace ℝ E (fderiv ℝ A x v).toLinearMap) • A x := by
  have htrace := (operatorTraceCLM (E := E)).hasFDerivAt.comp x hA.hasFDerivAt
  have hinv := (hasFDerivAt_inv hτ).comp x htrace
  have hfull := (hinv.smul hA.hasFDerivAt).const_sub (ContinuousLinearMap.id ℝ E)
  simp only [Function.comp_def, operatorTraceCLM_apply] at hfull
  simp only [Pi.smul_apply'] at hfull
  rw [hfull.fderiv]
  simp only [neg_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    operatorTraceCLM_apply, smul_eq_mul]
  module


theorem continuousWithinAt_fderiv_rankOneKernelProjection
    [FiniteDimensional ℝ F]
    {T : Type*} [TopologicalSpace T] {J : Set T} {b : T} (hb : b ∈ J)
    {A : T → F → (E →L[ℝ] E)} {x : F}
    (hspace : ∀ t ∈ J, DifferentiableAt ℝ (A t) x)
    (hvalue : ContinuousWithinAt (fun t => A t x) J b)
    (hjet : ContinuousWithinAt (fun t => fderiv ℝ (A t) x) J b)
    (hτ : LinearMap.trace ℝ E (A b x).toLinearMap ≠ 0) :
    ContinuousWithinAt (fun t => fderiv ℝ (fun y => ContinuousLinearMap.id ℝ E -
      (LinearMap.trace ℝ E (A t y).toLinearMap)⁻¹ • A t y) x) J b := by
  have htrace : ContinuousWithinAt
      (fun t => LinearMap.trace ℝ E (A t x).toLinearMap) J b :=
    operatorTraceCLM.continuous.continuousAt.comp_continuousWithinAt hvalue
  have hne := htrace.eventually (eventually_ne_nhds hτ)
  apply continuousWithinAt_clm_apply.mpr
  intro v
  have hjetv := hjet.clm_apply
    (continuousWithinAt_const : ContinuousWithinAt (fun _ : T => v) J b)
  have htracedJet : ContinuousWithinAt
      (fun t => LinearMap.trace ℝ E (fderiv ℝ (A t) x v).toLinearMap) J b :=
    operatorTraceCLM.continuous.continuousAt.comp_continuousWithinAt hjetv
  have hc := ((htrace.inv₀ hτ).neg.smul hjetv).add
    ((((htrace.pow 2).inv₀ (pow_ne_zero 2 hτ)).mul htracedJet).smul hvalue)
  have heq : (fun t => fderiv ℝ (fun y => ContinuousLinearMap.id ℝ E -
        (LinearMap.trace ℝ E (A t y).toLinearMap)⁻¹ • A t y) x v) =ᶠ[𝓝[J] b]
      (fun t => -(LinearMap.trace ℝ E (A t x).toLinearMap)⁻¹ • fderiv ℝ (A t) x v +
        (((LinearMap.trace ℝ E (A t x).toLinearMap) ^ 2)⁻¹ *
          LinearMap.trace ℝ E (fderiv ℝ (A t) x v).toLinearMap) • A t x) := by
    filter_upwards [hne, self_mem_nhdsWithin] with t ht htJ
    exact fderiv_rankOneKernelProjection_apply (hspace t htJ) ht v
  change Tendsto _ (𝓝[J] b) (𝓝 _)
  dsimp only
  rw [fderiv_rankOneKernelProjection_apply (hspace b hb) hτ v]
  exact hc.congr' heq.symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
