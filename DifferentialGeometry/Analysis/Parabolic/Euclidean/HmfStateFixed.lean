import DifferentialGeometry.Analysis.Parabolic.Euclidean.HmfStateRough
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HmfRoughFixedPoint

/-!
# Fixed point with a state-dependent principal coefficient

This file extends the abstract rough fixed point to a genuinely
state-dependent principal flux.  Its critical rate is

`4 * (eps + 2 * L * R) + K * R`.

For the expected strong HMF cancellation the specialization is `L = 0`; the
state-dependent quadratic source still needs the separate three-arm estimate
from `HmfStateQuad.lean`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {X E V G F : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Rough model with value differences controlled by the ambient Banach
distance.  This is the missing value-side companion to `grad_diff`. -/
structure HmfStateModel (T R : ℝ) (C : ℝ≥0∞)
    (path : X → ℝ × V → F) (grad : X → ℝ × V → G) : Prop
    extends HmfRoughModel T R C path grad where
  path_zero : path 0 = 0
  path_diff : ∀ u v,
    PathSup T ‖u - v‖ (fun z ↦ path u z - path v z)

/-- Measurability of the two state-principal arms and the two quadratic
arms in a fixed-point difference. -/
structure HmfStateMeas
    (A : ℝ × V → F → G →L[ℝ] F)
    (Q : ℝ × V → G →L[ℝ] G →L[ℝ] F)
    (path : X → ℝ × V → F) (grad : X → ℝ × V → G) : Prop where
  state_grad : ∀ u v, AEStronglyMeasurable
    (fun z ↦ A z (path u z) (grad u z - grad v z))
      (stVolume : Measure (ℝ × V))
  state_value : ∀ u v, AEStronglyMeasurable
    (fun z ↦ (A z (path u z) - A z (path v z)) (grad v z))
      (stVolume : Measure (ℝ × V))
  quad_left : ∀ u v, AEStronglyMeasurable
    (fun z ↦ Q z (grad u z - grad v z) (grad u z))
      (stVolume : Measure (ℝ × V))
  quad_right : ∀ u v, AEStronglyMeasurable
    (fun z ↦ Q z (grad v z) (grad u z - grad v z))
      (stVolume : Measure (ℝ × V))

namespace HeatRoughBound

variable {T : ℝ} {tr : X →L[ℝ] E}
  {fluxPot sourcePot : (ℝ × V → F) → X}

private theorem flux_neg
    (H : HeatRoughBound T tr fluxPot sourcePot) (p : ℝ × V → F) :
    fluxPot (fun z ↦ -p z) = -fluxPot p := by
  have h := H.flux_sub (0 : ℝ × V → F) p
  simpa only [Pi.zero_apply, zero_sub, H.flux_zero] using h

/-- The subtraction law in `HeatRoughBound` implies addition of flux
potentials. -/
theorem flux_add
    (H : HeatRoughBound T tr fluxPot sourcePot) (p q : ℝ × V → F) :
    fluxPot (fun z ↦ p z + q z) = fluxPot p + fluxPot q := by
  calc
    fluxPot (fun z ↦ p z + q z) =
        fluxPot (fun z ↦ p z - (-q z)) := by
      congr 1
      funext z
      simp
    _ = fluxPot p - fluxPot (fun z ↦ -q z) := H.flux_sub p (fun z ↦ -q z)
    _ = fluxPot p + fluxPot q := by rw [H.flux_neg]; abel

end HeatRoughBound

/-- Critical contraction rate for a state-dependent principal coefficient. -/
def hmfStateRate (eps L K R : ℝ) : ℝ :=
  hmfRate (eps + 2 * L * R) K R

/-- Build the repaired fixed-point data from the two state-principal arms
and the quadratic target arm. -/
def stateFpOfSplit
    {T eps L K R eta : ℝ} {C : ℝ≥0∞}
    {tr : X →L[ℝ] E}
    {fluxPot sourcePot : (ℝ × V → F) → X}
    {path : X → ℝ × V → F} {grad : X → ℝ × V → G}
    {A : ℝ × V → F → G →L[ℝ] F}
    {Q : ℝ × V → G →L[ℝ] G →L[ℝ] F}
    (H : HeatRoughBound T tr fluxPot sourcePot)
    (M : HmfStateModel T R C path grad)
    (hA : HmfStateCoeff eps L A)
    (hK0 : 0 ≤ K) (hQ : ∀ z, ‖Q z‖ ≤ K / 2)
    (hmeas : HmfStateMeas A Q path grad)
    (seed : X) (heta0 : 0 ≤ eta) (hseed : ‖seed‖ ≤ eta)
    (htrace : tr seed = 0)
    (hrate : hmfStateRate eps L K R < 1)
    (hsmall : eta ≤ (1 - hmfStateRate eps L K R) * R) :
    HmfFPData tr (eps + 2 * L * R) K R eta where
  seed := seed
  principal := fun u ↦ fluxPot (hmfStateFlux A (path u) (grad u))
  quadratic := fun u ↦ sourcePot (hmfQuad Q grad u)
  eps0 := by nlinarith [hA.eps0, hA.L0, M.R0]
  K0 := hK0
  R0 := M.R0
  eta0 := heta0
  principal_zero := by
    have hz : hmfStateFlux A (path 0) (grad 0) = 0 := by
      funext z
      simp only [hmfStateFlux, M.grad_zero, Pi.zero_apply, map_zero]
    rw [hz, H.flux_zero]
  quadratic_zero := by
    have hz : hmfQuad Q grad (0 : X) = 0 := by
      funext z
      simp only [hmfQuad, M.grad_zero, Pi.zero_apply, map_zero]
    rw [hz, H.source_zero]
  seed_bound := hseed
  principal_lip := by
    intro u v hu hv
    let D : ℝ := ‖u - v‖
    let p₁ : ℝ × V → F := fun z ↦
      A z (path u z) (grad u z - grad v z)
    let p₂ : ℝ × V → F := fun z ↦
      (A z (path u z) - A z (path v z)) (grad v z)
    have hw := hmfStateFluxWt2 hA M.R0 (norm_nonneg (u - v))
      (M.path_ball u hu) (M.path_diff u v)
      (M.grad_ball v hv) (M.grad_diff u v)
    have hc := hmfStateFluxCarl hA M.R0 (norm_nonneg (u - v))
      (M.path_ball u hu) (M.path_diff u v)
      (hmeas.state_grad u v) (hmeas.state_value u v)
      (M.carl_ball v hv) (M.carl_diff u v)
    have hsplit :
        (fun z ↦ hmfStateFlux A (path u) (grad u) z -
          hmfStateFlux A (path v) (grad v) z) =
        (fun z ↦ p₁ z + p₂ z) := by
      funext z
      exact hmfStateFlux_sub A (path u) (path v) (grad u) (grad v) z
    rw [← H.flux_sub, hsplit, H.flux_add]
    calc
      ‖fluxPot p₁ + fluxPot p₂‖ ≤ ‖fluxPot p₁‖ + ‖fluxPot p₂‖ :=
        norm_add_le _ _
      _ ≤ 4 * ((eps + L * R) * D) + 4 * ((L * D) * R) :=
        add_le_add (H.flux_norm hw.1 hc.1) (H.flux_norm hw.2 hc.2)
      _ = 4 * (eps + 2 * L * R) * ‖u - v‖ := by
        simp only [D]
        ring
  quadratic_lip := by
    intro u v hu hv
    have hQ0 : 0 ≤ K / 2 := by linarith
    have hw := quadDiffWt Q hQ hQ0 M.R0 (norm_nonneg (u - v))
      (M.grad_ball u hu) (M.grad_ball v hv) (M.grad_diff u v)
    have hc := quadDiffCarl Q hQ hQ0
      (hmeas.quad_left u v) (hmeas.quad_right u v)
      (M.carl_ball u hu) (M.carl_ball v hv) (M.carl_diff u v)
    rw [← H.source_sub]
    change ‖sourcePot
      (fun z ↦ Q z (grad u z) (grad u z) -
        Q z (grad v z) (grad v z))‖ ≤ _
    exact (H.source_norm hw hc).trans_eq (by ring)
  trace_seed := htrace
  trace_principal := fun u _ ↦ H.trace_flux _
  trace_quadratic := fun u _ ↦ H.trace_source _
  rate_lt_one := by simpa only [hmfStateRate] using hrate
  seed_small := by simpa only [hmfStateRate] using hsmall

/-- State-dependent-principal rough fixed point, with its realized Duhamel
equation and rough-path bounds exposed. -/
theorem stateSplit_fixed
    {T eps L K R eta : ℝ} {C : ℝ≥0∞}
    {tr : X →L[ℝ] E}
    {fluxPot sourcePot : (ℝ × V → F) → X}
    {path : X → ℝ × V → F} {grad : X → ℝ × V → G}
    {A : ℝ × V → F → G →L[ℝ] F}
    {Q : ℝ × V → G →L[ℝ] G →L[ℝ] F}
    (H : HeatRoughBound T tr fluxPot sourcePot)
    (M : HmfStateModel T R C path grad)
    (hA : HmfStateCoeff eps L A)
    (hK0 : 0 ≤ K) (hQ : ∀ z, ‖Q z‖ ≤ K / 2)
    (hmeas : HmfStateMeas A Q path grad)
    (seed : X) (heta0 : 0 ≤ eta) (hseed : ‖seed‖ ≤ eta)
    (htrace : tr seed = 0)
    (hrate : hmfStateRate eps L K R < 1)
    (hsmall : eta ≤ (1 - hmfStateRate eps L K R) * R) :
    ∃! u : X,
      u ∈ Metric.closedBall (0 : X) R ∧
      tr u = 0 ∧
      seed + fluxPot (hmfStateFlux A (path u) (grad u)) +
        sourcePot (hmfQuad Q grad u) = u ∧
      PathSup T R (path u) ∧ GradWt T R (grad u) ∧
        GradCarl T C (grad u) := by
  let D := stateFpOfSplit H M hA hK0 hQ hmeas seed heta0 hseed
    htrace hrate hsmall
  obtain ⟨u, hu, huniq⟩ := D.rough_fixed
  have heq : seed + fluxPot (hmfStateFlux A (path u) (grad u)) +
      sourcePot (hmfQuad Q grad u) = u := by
    simpa [D, stateFpOfSplit, hmfDuh] using hu.2.2
  refine ⟨u, ⟨hu.1, hu.2.1, heq, M.path_ball u hu.1,
    M.grad_ball u hu.1, M.carl_ball u hu.1⟩, ?_⟩
  intro v hv
  apply huniq v
  refine ⟨hv.1, hv.2.1, ?_⟩
  simpa [D, stateFpOfSplit, hmfDuh] using hv.2.2.1

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
