import DifferentialGeometry.Analysis.Parabolic.Euclidean.HarmonicMapFlow.State.Rough
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HarmonicMapFlow.FixedPoint.Rough

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

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

structure HarmonicMapFlowStateModel (T R : ℝ) (C : ℝ≥0∞)
    (path : X → ℝ × V → F) (grad : X → ℝ × V → G) : Prop
    extends HarmonicMapFlowRoughModel T R C path grad where
  path_zero : path 0 = 0
  path_diff : ∀ u v,
    PathUniformBound T ‖u - v‖ (fun z ↦ path u z - path v z)

structure HarmonicMapFlowStateMeasurability
    (A : ℝ × V → F → G →L[ℝ] F)
    (Q : ℝ × V → G →L[ℝ] G →L[ℝ] F)
    (path : X → ℝ × V → F) (grad : X → ℝ × V → G) : Prop where
  state_grad : ∀ u v, AEStronglyMeasurable
    (fun z ↦ A z (path u z) (grad u z - grad v z))
      (spaceTimeVolume : Measure (ℝ × V))
  state_value : ∀ u v, AEStronglyMeasurable
    (fun z ↦ (A z (path u z) - A z (path v z)) (grad v z))
      (spaceTimeVolume : Measure (ℝ × V))
  quad_left : ∀ u v, AEStronglyMeasurable
    (fun z ↦ Q z (grad u z - grad v z) (grad u z))
      (spaceTimeVolume : Measure (ℝ × V))
  quad_right : ∀ u v, AEStronglyMeasurable
    (fun z ↦ Q z (grad v z) (grad u z - grad v z))
      (spaceTimeVolume : Measure (ℝ × V))

namespace HeatRoughBound

variable {T : ℝ} {tr : X →L[ℝ] E}
  {fluxPot sourcePot : (ℝ × V → F) → X}

omit [CompleteSpace X]
  [NormedSpace ℝ F] in
private theorem flux_neg
    (H : HeatRoughBound T tr fluxPot sourcePot) (p : ℝ × V → F) :
    fluxPot (fun z ↦ -p z) = -fluxPot p := by
  have h := H.flux_sub (0 : ℝ × V → F) p
  simpa only [Pi.zero_apply, zero_sub, H.flux_zero] using h

omit [CompleteSpace X]
  [NormedSpace ℝ F] in
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

def harmonicMapFlowStateRate (eps L K R : ℝ) : ℝ :=
  harmonicMapFlowContractionRate (eps + 2 * L * R) K R

theorem state_split_fixed
    {T eps L K R eta : ℝ} {C : ℝ≥0∞}
    {tr : X →L[ℝ] E}
    {fluxPot sourcePot : (ℝ × V → F) → X}
    {path : X → ℝ × V → F} {grad : X → ℝ × V → G}
    {A : ℝ × V → F → G →L[ℝ] F}
    {Q : ℝ × V → G →L[ℝ] G →L[ℝ] F}
    (H : HeatRoughBound T tr fluxPot sourcePot)
    (M : HarmonicMapFlowStateModel T R C path grad)
    (hA : HarmonicMapFlowStateCoefficients eps L A)
    (hK0 : 0 ≤ K) (hQ : ∀ z, ‖Q z‖ ≤ K / 2)
    (hmeas : HarmonicMapFlowStateMeasurability A Q path grad)
    (seed : X) (hseed : ‖seed‖ ≤ eta)
    (htrace : tr seed = 0)
    (hrate : harmonicMapFlowStateRate eps L K R < 1)
    (hsmall : eta ≤ (1 - harmonicMapFlowStateRate eps L K R) * R) :
    ∃! u : X,
      u ∈ Metric.closedBall (0 : X) R ∧
      tr u = 0 ∧
      seed + fluxPot (harmonicMapFlowStateFlux A (path u) (grad u)) +
        sourcePot (harmonicMapFlowQuadraticSource Q grad u) = u ∧
      PathUniformBound T R (path u) ∧ GradientWeightedBound T R (grad u) ∧
        GradientCarlesonBound T C (grad u) := by
  have heps0 : 0 ≤ eps + 2 * L * R := by nlinarith [hA.eps0, hA.L0, M.R0]
  have hrate0 : 0 ≤ harmonicMapFlowStateRate eps L K R := by
    rw [harmonicMapFlowStateRate]
    exact add_nonneg (mul_nonneg (by norm_num) heps0) (mul_nonneg hK0 M.R0)
  let κ : ℝ≥0 := ⟨harmonicMapFlowStateRate eps L K R, hrate0⟩
  have hκ : κ < 1 := by
    rw [← NNReal.coe_lt_coe]
    exact hrate
  let Φ : X → X := fun u ↦
    seed + fluxPot (harmonicMapFlowStateFlux A (path u) (grad u)) +
      sourcePot (harmonicMapFlowQuadraticSource Q grad u)
  have hΦzero : Φ 0 = seed := by
    have hflux : harmonicMapFlowStateFlux A (path 0) (grad 0) = 0 := by
      funext z
      simp only [harmonicMapFlowStateFlux, M.grad_zero, Pi.zero_apply, map_zero]
    have hquad : harmonicMapFlowQuadraticSource Q grad (0 : X) = 0 := by
      funext z
      simp only [harmonicMapFlowQuadraticSource, M.grad_zero, Pi.zero_apply, map_zero]
    simp only [Φ, hflux, hquad, H.flux_zero, H.source_zero, add_zero]
  have hΦ0 : ‖Φ 0‖ ≤ (1 - (κ : ℝ)) * R := by
    rw [hΦzero]
    exact hseed.trans hsmall
  have hΦ : LipschitzOnWith κ Φ (Metric.closedBall (0 : X) R) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    rw [dist_eq_norm]
    let D : ℝ := ‖u - v‖
    let p₁ : ℝ × V → F := fun z ↦
      A z (path u z) (grad u z - grad v z)
    let p₂ : ℝ × V → F := fun z ↦
      (A z (path u z) - A z (path v z)) (grad v z)
    have hw := harmonicMapFlowStateFluxTermsWeightedBounds hA M.R0 (norm_nonneg (u - v))
      (M.path_ball u hu) (M.path_diff u v)
      (M.grad_ball v hv) (M.grad_diff u v)
    have hc := harmonicMapFlowStateFluxTermsCarlesonBounds hA M.R0 (norm_nonneg (u - v))
      (M.path_ball u hu) (M.path_diff u v)
      (hmeas.state_grad u v) (hmeas.state_value u v)
      (M.carleson_ball v hv) (M.carleson_diff u v)
    have hsplitPrincipal :
        (fun z ↦ harmonicMapFlowStateFlux A (path u) (grad u) z -
          harmonicMapFlowStateFlux A (path v) (grad v) z) =
        (fun z ↦ p₁ z + p₂ z) := by
      funext z
      exact harmonicMapFlowStateFlux_sub A (path u) (path v) (grad u) (grad v) z
    have hprincipal :
        ‖fluxPot (harmonicMapFlowStateFlux A (path u) (grad u)) -
          fluxPot (harmonicMapFlowStateFlux A (path v) (grad v))‖ ≤
          4 * (eps + 2 * L * R) * ‖u - v‖ := by
      rw [← H.flux_sub, hsplitPrincipal, H.flux_add]
      calc
        ‖fluxPot p₁ + fluxPot p₂‖ ≤ ‖fluxPot p₁‖ + ‖fluxPot p₂‖ :=
          norm_add_le _ _
        _ ≤ 4 * ((eps + L * R) * D) + 4 * ((L * D) * R) :=
          add_le_add (H.flux_norm hw.1 hc.1) (H.flux_norm hw.2 hc.2)
        _ = 4 * (eps + 2 * L * R) * ‖u - v‖ := by
          simp only [D]
          ring
    have hQ0 : 0 ≤ K / 2 := by linarith
    have hwq := quadratic_difference_weighted_bound Q hQ hQ0 M.R0 (norm_nonneg (u - v))
      (M.grad_ball u hu) (M.grad_ball v hv) (M.grad_diff u v)
    have hcq := quadratic_difference_carleson_bound Q hQ hQ0
      (hmeas.quad_left u v) (hmeas.quad_right u v)
      (M.carleson_ball u hu) (M.carleson_ball v hv) (M.carleson_diff u v)
    have hquadratic :
        ‖sourcePot (harmonicMapFlowQuadraticSource Q grad u) - sourcePot (harmonicMapFlowQuadraticSource Q grad v)‖ ≤
          K * R * ‖u - v‖ := by
      rw [← H.source_sub]
      change ‖sourcePot
        (fun z ↦ Q z (grad u z) (grad u z) -
          Q z (grad v z) (grad v z))‖ ≤ _
      exact (H.source_norm hwq hcq).trans_eq (by ring)
    have hsplit : Φ u - Φ v =
        (fluxPot (harmonicMapFlowStateFlux A (path u) (grad u)) -
          fluxPot (harmonicMapFlowStateFlux A (path v) (grad v))) +
        (sourcePot (harmonicMapFlowQuadraticSource Q grad u) - sourcePot (harmonicMapFlowQuadraticSource Q grad v)) := by
      simp only [Φ]
      abel
    rw [hsplit]
    calc
      ‖(fluxPot (harmonicMapFlowStateFlux A (path u) (grad u)) -
          fluxPot (harmonicMapFlowStateFlux A (path v) (grad v))) +
          (sourcePot (harmonicMapFlowQuadraticSource Q grad u) - sourcePot (harmonicMapFlowQuadraticSource Q grad v))‖
          ≤ ‖fluxPot (harmonicMapFlowStateFlux A (path u) (grad u)) -
              fluxPot (harmonicMapFlowStateFlux A (path v) (grad v))‖ +
            ‖sourcePot (harmonicMapFlowQuadraticSource Q grad u) - sourcePot (harmonicMapFlowQuadraticSource Q grad v)‖ :=
        norm_add_le _ _
      _ ≤ 4 * (eps + 2 * L * R) * ‖u - v‖ + K * R * ‖u - v‖ :=
        add_le_add hprincipal hquadratic
      _ = (κ : ℝ) * dist u v := by
        rw [show (κ : ℝ) = harmonicMapFlowStateRate eps L K R from rfl, dist_eq_norm]
        simp only [harmonicMapFlowStateRate, harmonicMapFlowContractionRate]
        ring
  obtain ⟨u, hu, huniq⟩ :=
    DifferentialGeometry.Analysis.exists_unique_fixedPoint_mem_closedBall
      M.R0 hκ hΦ0 hΦ
  have huTrace : tr u = 0 := by
    rw [← hu.2]
    simp only [Φ, map_add, htrace, H.trace_flux, H.trace_source, add_zero]
  have huFixed : Φ u = u := hu.2
  have heq : seed + fluxPot (harmonicMapFlowStateFlux A (path u) (grad u)) +
      sourcePot (harmonicMapFlowQuadraticSource Q grad u) = u := by
    simpa only [Φ] using huFixed
  refine ⟨u, ⟨hu.1, huTrace, heq, M.path_ball u hu.1,
    M.grad_ball u hu.1, M.carleson_ball u hu.1⟩, ?_⟩
  intro v hv
  apply huniq v
  refine ⟨hv.1, ?_⟩
  change Φ v = v
  simpa only [Φ] using hv.2.2.1

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
