import DifferentialGeometry.Analysis.Parabolic.Euclidean.HmfFixedCore
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HmfStateQuad

/-!
# A clean fixed point for the state-dependent HMF quadratic source

The local-addition quadratic coefficient depends on the path value.  Its
difference has three genuine arms, including

`(Q(u) - Q(v)) (Dv) (Dv)`.

This file feeds the exact weighted and Carleson estimates for all three arms
into `HmfCoreData`.  It does not import the older prescribed-quadratic HMF map
or its fixed-point wrapper.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {X E V Y G F : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Linear heat-potential bounds used by the rough HMF realization.  The
divergence potential costs the critical factor four, while the ordinary
source potential costs one. -/
structure HmfQuadHeat (T : ℝ) (tr : X →L[ℝ] E)
    (fluxPot sourcePot : (ℝ × V → F) → X) : Prop where
  flux_zero : fluxPot 0 = 0
  source_zero : sourcePot 0 = 0
  flux_sub : ∀ p q, fluxPot (fun z ↦ p z - q z) = fluxPot p - fluxPot q
  source_sub : ∀ p q, sourcePot (fun z ↦ p z - q z) = sourcePot p - sourcePot q
  flux_norm : ∀ {A : ℝ} {C : ℝ≥0∞} {p : ℝ × V → F},
    GradWt T A p → GradCarl T C p → ‖fluxPot p‖ ≤ 4 * A
  source_norm : ∀ {A : ℝ} {C : ℝ≥0∞} {s : ℝ × V → F},
    SrcWt T A s → SrcCarl T C s → ‖sourcePot s‖ ≤ A
  trace_flux : ∀ p, tr (fluxPot p) = 0
  trace_source : ∀ s, tr (sourcePot s) = 0

/-- A rough path realization whose value and gradient differences are both
controlled by the ambient Banach distance. -/
structure HmfQuadModel (T R : ℝ) (C : ℝ≥0∞)
    (path : X → ℝ × V → Y) (grad : X → ℝ × V → G) : Prop where
  R0 : 0 ≤ R
  grad_zero : grad 0 = 0
  path_ball : ∀ u, u ∈ Metric.closedBall (0 : X) R → PathSup T R (path u)
  path_diff : ∀ u v,
    PathSup T ‖u - v‖ (fun z ↦ path u z - path v z)
  grad_ball : ∀ u, u ∈ Metric.closedBall (0 : X) R → GradWt T R (grad u)
  carl_ball : ∀ u, u ∈ Metric.closedBall (0 : X) R → GradCarl T C (grad u)
  grad_diff : ∀ u v,
    GradWt T ‖u - v‖ (fun z ↦ grad u z - grad v z)
  carl_diff : ∀ u v,
    GradCarl T (ENNReal.ofReal (‖u - v‖ ^ 2))
      (fun z ↦ grad u z - grad v z)

/-- Measurability of the prescribed principal flux and all three realized
state-quadratic difference arms. -/
structure HmfQuadMeas
    (A : ℝ × V → G →L[ℝ] F)
    (Q : ℝ × V → Y → G →L[ℝ] G →L[ℝ] F)
    (path : X → ℝ × V → Y) (grad : X → ℝ × V → G) : Prop where
  principal : ∀ u v, AEStronglyMeasurable
    (fun z ↦ A z (grad u z - grad v z)) (stVolume : Measure (ℝ × V))
  quad_left : ∀ u v, AEStronglyMeasurable
    (fun z ↦ Q z (path u z) (grad u z - grad v z) (grad u z))
      (stVolume : Measure (ℝ × V))
  quad_right : ∀ u v, AEStronglyMeasurable
    (fun z ↦ Q z (path u z) (grad v z) (grad u z - grad v z))
      (stVolume : Measure (ℝ × V))
  quad_state : ∀ u v, AEStronglyMeasurable
    (fun z ↦ (Q z (path u z) - Q z (path v z))
      (grad v z) (grad v z)) (stVolume : Measure (ℝ × V))

/-- Realized prescribed principal flux. -/
def hmfQuadFlux (A : ℝ × V → G →L[ℝ] F)
    (grad : X → ℝ × V → G) (u : X) (z : ℝ × V) : F :=
  A z (grad u z)

/-- Exact contraction rate: prescribed critical flux, the two base quadratic
arms, and the three state-Lipschitz radius factors. -/
def hmfQuadRate (eps K L R : ℝ) : ℝ :=
  4 * eps + K * R + 3 * L * R ^ 2

/-- Assemble the faithful state-quadratic realization into the clean Banach
core.  The base quadratic coefficient is normalized by `K / 2`, so its two
gradient arms have combined rate `K * R`. -/
def quadCoreData
    {T eps K L R eta : ℝ} {C : ℝ≥0∞}
    {tr : X →L[ℝ] E}
    {fluxPot sourcePot : (ℝ × V → F) → X}
    {path : X → ℝ × V → Y} {grad : X → ℝ × V → G}
    {A : ℝ × V → G →L[ℝ] F}
    {Q : ℝ × V → Y → G →L[ℝ] G →L[ℝ] F}
    (H : HmfQuadHeat T tr fluxPot sourcePot)
    (M : HmfQuadModel T R C path grad)
    (heps0 : 0 ≤ eps) (hA : ∀ z, ‖A z‖ ≤ eps)
    (hQ : HmfStateQuad (K / 2) L Q)
    (hmeas : HmfQuadMeas A Q path grad)
    (seed : X) (heta0 : 0 ≤ eta) (hseed : ‖seed‖ ≤ eta)
    (htrace : tr seed = 0)
    (hrate : hmfQuadRate eps K L R < 1)
    (hsmall : eta ≤ (1 - hmfQuadRate eps K L R) * R) :
    HmfCoreData tr R eta (hmfQuadRate eps K L R) where
  seed := seed
  nonlin := fun u ↦
    fluxPot (hmfQuadFlux A grad u) +
      sourcePot (fun z ↦ hmfStateQuadSrc Q (path u) (grad u) z)
  R0 := M.R0
  eta0 := heta0
  rate0 := by
    have hK0 : 0 ≤ K := by nlinarith [hQ.K0]
    unfold hmfQuadRate
    exact add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) heps0) (mul_nonneg hK0 M.R0))
      (mul_nonneg (mul_nonneg (by norm_num) hQ.L0) (sq_nonneg R))
  nonlin_zero := by
    have hflux : hmfQuadFlux A grad (0 : X) = 0 := by
      funext z
      simp only [hmfQuadFlux, M.grad_zero, Pi.zero_apply, map_zero]
    have hsource :
        (fun z ↦ hmfStateQuadSrc Q (path (0 : X)) (grad 0) z) = 0 := by
      funext z
      simp only [hmfStateQuadSrc, M.grad_zero, Pi.zero_apply, map_zero]
    rw [hflux, hsource, H.flux_zero, H.source_zero, add_zero]
  seed_bound := hseed
  nonlin_lip := by
    intro u v hu hv
    let D : ℝ := ‖u - v‖
    have hpWt := linWt_of_bound A hA heps0 (M.grad_diff u v)
    have hpCarl := linCarl_of_bound A hA heps0
      (hmeas.principal u v) (M.carl_diff u v)
    have hpEq :
        (fun z ↦ hmfQuadFlux A grad u z - hmfQuadFlux A grad v z) =
          (fun z ↦ A z (grad u z - grad v z)) := by
      funext z
      exact (map_sub (A z) (grad u z) (grad v z)).symm
    have hflux :
        ‖fluxPot (hmfQuadFlux A grad u) - fluxPot (hmfQuadFlux A grad v)‖ ≤
          4 * eps * D := by
      rw [← H.flux_sub, hpEq]
      exact (H.flux_norm hpWt hpCarl).trans_eq (by
        simp only [D]
        ring)
    have hsWt := stateQuadSrcWt hQ M.R0 (norm_nonneg (u - v))
      M.R0 (norm_nonneg (u - v))
      (M.path_ball u hu) (M.path_diff u v)
      (M.grad_ball u hu) (M.grad_ball v hv) (M.grad_diff u v)
    have hsCarl := stateQuadSrcCarl hQ M.R0 (norm_nonneg (u - v))
      (M.path_ball u hu) (M.path_diff u v)
      (hmeas.quad_left u v) (hmeas.quad_right u v) (hmeas.quad_state u v)
      (M.carl_ball u hu) (M.carl_ball v hv) (M.carl_diff u v)
    have hsource :
        ‖sourcePot (fun z ↦ hmfStateQuadSrc Q (path u) (grad u) z) -
          sourcePot (fun z ↦ hmfStateQuadSrc Q (path v) (grad v) z)‖ ≤
            (K * R + 3 * L * R ^ 2) * D := by
      rw [← H.source_sub]
      exact (H.source_norm hsWt hsCarl).trans_eq (by
        simp only [D]
        ring)
    have hsplit :
        (fluxPot (hmfQuadFlux A grad u) +
              sourcePot (fun z ↦ hmfStateQuadSrc Q (path u) (grad u) z)) -
            (fluxPot (hmfQuadFlux A grad v) +
              sourcePot (fun z ↦ hmfStateQuadSrc Q (path v) (grad v) z)) =
          (fluxPot (hmfQuadFlux A grad u) - fluxPot (hmfQuadFlux A grad v)) +
            (sourcePot (fun z ↦ hmfStateQuadSrc Q (path u) (grad u) z) -
              sourcePot (fun z ↦ hmfStateQuadSrc Q (path v) (grad v) z)) := by
      abel
    rw [hsplit]
    calc
      ‖(fluxPot (hmfQuadFlux A grad u) - fluxPot (hmfQuadFlux A grad v)) +
          (sourcePot (fun z ↦ hmfStateQuadSrc Q (path u) (grad u) z) -
            sourcePot (fun z ↦ hmfStateQuadSrc Q (path v) (grad v) z))‖
          ≤ ‖fluxPot (hmfQuadFlux A grad u) - fluxPot (hmfQuadFlux A grad v)‖ +
              ‖sourcePot (fun z ↦ hmfStateQuadSrc Q (path u) (grad u) z) -
                sourcePot (fun z ↦ hmfStateQuadSrc Q (path v) (grad v) z)‖ :=
        norm_add_le _ _
      _ ≤ 4 * eps * D + (K * R + 3 * L * R ^ 2) * D :=
        add_le_add hflux hsource
      _ = hmfQuadRate eps K L R * ‖u - v‖ := by
        simp only [hmfQuadRate, D]
        ring
  trace_seed := htrace
  trace_nonlin := by
    intro u _
    simp only [map_add, H.trace_flux, H.trace_source, add_zero]
  rate_lt_one := hrate
  seed_small := hsmall

omit [NormedSpace ℝ Y] in
/-- The clean state-quadratic HMF fixed point.  Its equation retains the
actual coefficient `Q z (path u z)` and the conclusion exposes all rough path
bounds used to realize the geometric gauge. -/
theorem quad_fixed
    {T eps K L R eta : ℝ} {C : ℝ≥0∞}
    {tr : X →L[ℝ] E}
    {fluxPot sourcePot : (ℝ × V → F) → X}
    {path : X → ℝ × V → Y} {grad : X → ℝ × V → G}
    {A : ℝ × V → G →L[ℝ] F}
    {Q : ℝ × V → Y → G →L[ℝ] G →L[ℝ] F}
    (H : HmfQuadHeat T tr fluxPot sourcePot)
    (M : HmfQuadModel T R C path grad)
    (heps0 : 0 ≤ eps) (hA : ∀ z, ‖A z‖ ≤ eps)
    (hQ : HmfStateQuad (K / 2) L Q)
    (hmeas : HmfQuadMeas A Q path grad)
    (seed : X) (heta0 : 0 ≤ eta) (hseed : ‖seed‖ ≤ eta)
    (htrace : tr seed = 0)
    (hrate : hmfQuadRate eps K L R < 1)
    (hsmall : eta ≤ (1 - hmfQuadRate eps K L R) * R) :
    ∃! u : X,
      u ∈ Metric.closedBall (0 : X) R ∧
      tr u = 0 ∧
      seed + fluxPot (hmfQuadFlux A grad u) +
        sourcePot (fun z ↦ hmfStateQuadSrc Q (path u) (grad u) z) = u ∧
      PathSup T R (path u) ∧ GradWt T R (grad u) ∧
        GradCarl T C (grad u) := by
  let D := quadCoreData H M heps0 hA hQ hmeas seed heta0 hseed htrace hrate hsmall
  obtain ⟨u, hu, huniq⟩ := D.core_fixed
  have heq : seed + fluxPot (hmfQuadFlux A grad u) +
      sourcePot (fun z ↦ hmfStateQuadSrc Q (path u) (grad u) z) = u := by
    simpa [D, quadCoreData, hmfCoreMap, add_assoc] using hu.2.2
  refine ⟨u, ⟨hu.1, hu.2.1, heq, M.path_ball u hu.1,
    M.grad_ball u hu.1, M.carl_ball u hu.1⟩, ?_⟩
  intro v hv
  apply huniq v
  refine ⟨hv.1, hv.2.1, ?_⟩
  simpa [D, quadCoreData, hmfCoreMap, add_assoc] using hv.2.2.1

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
