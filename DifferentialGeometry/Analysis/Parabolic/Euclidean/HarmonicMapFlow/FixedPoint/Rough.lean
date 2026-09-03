import DifferentialGeometry.Analysis.FunctionalAnalysis.Contraction.ClosedBall
import DifferentialGeometry.Analysis.Parabolic.Euclidean.HarmonicMapFlow.RoughMap

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def hmfRate (eps K R : ℝ) : ℝ := 4 * eps + K * R

section SplitRealization

variable {V G F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

structure HeatRoughBound (T : ℝ) (tr : X →L[ℝ] E)
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

structure HmfRoughModel (T R : ℝ) (C : ℝ≥0∞)
    (path : X → ℝ × V → F) (grad : X → ℝ × V → G) : Prop where
  R0 : 0 ≤ R
  grad_zero : grad 0 = 0
  path_ball : ∀ u, u ∈ Metric.closedBall (0 : X) R → PathSup T R (path u)
  grad_ball : ∀ u, u ∈ Metric.closedBall (0 : X) R → GradWt T R (grad u)
  carl_ball : ∀ u, u ∈ Metric.closedBall (0 : X) R → GradCarl T C (grad u)
  grad_diff : ∀ u v, GradWt T ‖u - v‖ (fun z ↦ grad u z - grad v z)
  carl_diff : ∀ u v, GradCarl T (ENNReal.ofReal (‖u - v‖ ^ 2))
    (fun z ↦ grad u z - grad v z)

structure HmfMeas
    (A : ℝ × V → G →L[ℝ] F)
    (Q : ℝ × V → G →L[ℝ] G →L[ℝ] F)
    (grad : X → ℝ × V → G) : Prop where
  principal : ∀ u v, AEStronglyMeasurable
    (fun z ↦ A z (grad u z - grad v z)) (stVolume : Measure (ℝ × V))
  quad_left : ∀ u v, AEStronglyMeasurable
    (fun z ↦ Q z (grad u z - grad v z) (grad u z))
      (stVolume : Measure (ℝ × V))
  quad_right : ∀ u v, AEStronglyMeasurable
    (fun z ↦ Q z (grad v z) (grad u z - grad v z))
      (stVolume : Measure (ℝ × V))

def hmfFlux (A : ℝ × V → G →L[ℝ] F) (grad : X → ℝ × V → G)
    (u : X) (z : ℝ × V) : F :=
  A z (grad u z)

def hmfQuad (Q : ℝ × V → G →L[ℝ] G →L[ℝ] F)
    (grad : X → ℝ × V → G) (u : X) (z : ℝ × V) : F :=
  Q z (grad u z) (grad u z)

theorem split_fixed {T eps K R eta : ℝ} {C : ℝ≥0∞}
    {tr : X →L[ℝ] E}
    {fluxPot sourcePot : (ℝ × V → F) → X}
    {path : X → ℝ × V → F} {grad : X → ℝ × V → G}
    {A : ℝ × V → G →L[ℝ] F}
    {Q : ℝ × V → G →L[ℝ] G →L[ℝ] F}
    (H : HeatRoughBound T tr fluxPot sourcePot)
    (M : HmfRoughModel T R C path grad)
    (hc : HmfCoeff eps (K / 2) A Q)
    (hmeas : HmfMeas A Q grad)
    (seed : X) (hseed : ‖seed‖ ≤ eta)
    (htrace : tr seed = 0)
    (hrate : hmfRate eps K R < 1)
    (hsmall : eta ≤ (1 - hmfRate eps K R) * R) :
    ∃! u : X,
      u ∈ Metric.closedBall (0 : X) R ∧
      tr u = 0 ∧
      seed + fluxPot (hmfFlux A grad u) + sourcePot (hmfQuad Q grad u) = u ∧
      PathSup T R (path u) ∧
      GradWt T R (grad u) ∧
      GradCarl T C (grad u) := by
  have hK0 : 0 ≤ K := by nlinarith [hc.K0]
  have hrate0 : 0 ≤ hmfRate eps K R :=
    add_nonneg (mul_nonneg (by norm_num) hc.eps0) (mul_nonneg hK0 M.R0)
  let κ : ℝ≥0 := ⟨hmfRate eps K R, hrate0⟩
  have hκ : κ < 1 := by
    rw [← NNReal.coe_lt_coe]
    exact hrate
  let Φ : X → X := fun u ↦
    seed + fluxPot (hmfFlux A grad u) + sourcePot (hmfQuad Q grad u)
  have hΦzero : Φ 0 = seed := by
    have hflux : hmfFlux A grad (0 : X) = 0 := by
      funext z
      simp only [hmfFlux, M.grad_zero, Pi.zero_apply, map_zero]
    have hquad : hmfQuad Q grad (0 : X) = 0 := by
      funext z
      simp only [hmfQuad, M.grad_zero, Pi.zero_apply, map_zero]
    simp only [Φ, hflux, hquad, H.flux_zero, H.source_zero, add_zero]
  have hΦ0 : ‖Φ 0‖ ≤ (1 - (κ : ℝ)) * R := by
    rw [hΦzero]
    exact hseed.trans hsmall
  have hΦ : LipschitzOnWith κ Φ (Metric.closedBall (0 : X) R) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    rw [dist_eq_norm]
    have hs := hmfDiffSplit hc M.R0 (norm_nonneg (u - v))
      (hmeas.principal u v) (hmeas.quad_left u v) (hmeas.quad_right u v)
      (M.grad_ball u hu) (M.grad_ball v hv) (M.grad_diff u v)
      (M.carl_ball u hu) (M.carl_ball v hv) (M.carl_diff u v)
    have hpEq :
        (fun z ↦ hmfFlux A grad u z - hmfFlux A grad v z) =
          (fun z ↦ A z (grad u z - grad v z)) := by
      funext z
      exact (map_sub (A z) (grad u z) (grad v z)).symm
    have hprincipal :
        ‖fluxPot (hmfFlux A grad u) - fluxPot (hmfFlux A grad v)‖ ≤
          4 * eps * ‖u - v‖ := by
      rw [← H.flux_sub, hpEq]
      exact (H.flux_norm hs.principalWt hs.principalCarl).trans_eq (by ring)
    have hquadratic :
        ‖sourcePot (hmfQuad Q grad u) - sourcePot (hmfQuad Q grad v)‖ ≤
          K * R * ‖u - v‖ := by
      rw [← H.source_sub]
      change ‖sourcePot
        (fun z ↦ Q z (grad u z) (grad u z) - Q z (grad v z) (grad v z))‖ ≤ _
      exact (H.source_norm hs.sourceWt hs.sourceCarl).trans_eq (by ring)
    have hsplit : Φ u - Φ v =
        (fluxPot (hmfFlux A grad u) - fluxPot (hmfFlux A grad v)) +
          (sourcePot (hmfQuad Q grad u) - sourcePot (hmfQuad Q grad v)) := by
      simp only [Φ]
      abel
    rw [hsplit]
    calc
      ‖(fluxPot (hmfFlux A grad u) - fluxPot (hmfFlux A grad v)) +
          (sourcePot (hmfQuad Q grad u) - sourcePot (hmfQuad Q grad v))‖
          ≤ ‖fluxPot (hmfFlux A grad u) - fluxPot (hmfFlux A grad v)‖ +
              ‖sourcePot (hmfQuad Q grad u) - sourcePot (hmfQuad Q grad v)‖ :=
        norm_add_le _ _
      _ ≤ 4 * eps * ‖u - v‖ + K * R * ‖u - v‖ :=
        add_le_add hprincipal hquadratic
      _ = (κ : ℝ) * dist u v := by
        rw [show (κ : ℝ) = hmfRate eps K R from rfl, dist_eq_norm]
        simp only [hmfRate]
        ring
  obtain ⟨u, hu, huniq⟩ :=
    DifferentialGeometry.Analysis.exists_unique_fixedPoint_mem_closedBall
      M.R0 hκ hΦ0 hΦ
  have huTrace : tr u = 0 := by
    rw [← hu.2]
    simp only [Φ, map_add, htrace, H.trace_flux, H.trace_source, add_zero]
  have huFixed : Φ u = u := hu.2
  have heq :
      seed + fluxPot (hmfFlux A grad u) + sourcePot (hmfQuad Q grad u) = u := by
    simpa only [Φ] using huFixed
  refine ⟨u, ⟨hu.1, huTrace, heq, M.path_ball u hu.1,
    M.grad_ball u hu.1, M.carl_ball u hu.1⟩, ?_⟩
  intro v hv
  apply huniq v
  refine ⟨hv.1, ?_⟩
  change Φ v = v
  simpa only [Φ] using hv.2.2.1

end SplitRealization

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
