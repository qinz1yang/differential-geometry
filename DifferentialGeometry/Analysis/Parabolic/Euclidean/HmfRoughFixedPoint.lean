import DifferentialGeometry.Analysis.Parabolic.Euclidean.HmfRoughMap
import Mathlib.Topology.MetricSpace.Contracting

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def hmfRate (eps K R : ℝ) : ℝ := 4 * eps + K * R

structure HmfFPData (tr : X →L[ℝ] E) (eps K R eta : ℝ) where
  seed : X
  principal : X → X
  quadratic : X → X
  eps0 : 0 ≤ eps
  K0 : 0 ≤ K
  R0 : 0 ≤ R
  eta0 : 0 ≤ eta
  principal_zero : principal 0 = 0
  quadratic_zero : quadratic 0 = 0
  seed_bound : ‖seed‖ ≤ eta
  principal_lip : ∀ u v,
    u ∈ Metric.closedBall (0 : X) R →
    v ∈ Metric.closedBall (0 : X) R →
    ‖principal u - principal v‖ ≤ 4 * eps * ‖u - v‖
  quadratic_lip : ∀ u v,
    u ∈ Metric.closedBall (0 : X) R →
    v ∈ Metric.closedBall (0 : X) R →
    ‖quadratic u - quadratic v‖ ≤ K * R * ‖u - v‖
  trace_seed : tr seed = 0
  trace_principal : ∀ u, u ∈ Metric.closedBall (0 : X) R → tr (principal u) = 0
  trace_quadratic : ∀ u, u ∈ Metric.closedBall (0 : X) R → tr (quadratic u) = 0
  rate_lt_one : hmfRate eps K R < 1
  seed_small : eta ≤ (1 - hmfRate eps K R) * R

abbrev HmfBall (R : ℝ) (X : Type*) [Zero X] [PseudoMetricSpace X] :=
  Metric.closedBall (0 : X) R

def hmfDuh {tr : X →L[ℝ] E} {eps K R eta : ℝ}
    (D : HmfFPData tr eps K R eta) (u : X) : X :=
  D.seed + D.principal u + D.quadratic u

namespace HmfFPData

variable {tr : X →L[ℝ] E} {eps K R eta : ℝ}
  (D : HmfFPData tr eps K R eta)
omit [CompleteSpace X] in
include D in
theorem rate_nonneg : 0 ≤ hmfRate eps K R := by
  exact add_nonneg (mul_nonneg (by norm_num) (HmfFPData.eps0 D))
    (mul_nonneg (HmfFPData.K0 D) (HmfFPData.R0 D))
omit [CompleteSpace X] in
include D in
private theorem zero_mem : (0 : X) ∈ Metric.closedBall 0 R := by
  simpa [Metric.mem_closedBall] using HmfFPData.R0 D
omit [CompleteSpace X] in
private theorem principal_bound {u : X} (hu : u ∈ Metric.closedBall 0 R) :
    ‖D.principal u‖ ≤ 4 * eps * ‖u‖ := by
  simpa [D.principal_zero] using D.principal_lip u 0 hu (zero_mem D)
omit [CompleteSpace X] in
private theorem quadratic_bound {u : X} (hu : u ∈ Metric.closedBall 0 R) :
    ‖D.quadratic u‖ ≤ K * R * ‖u‖ := by
  simpa [D.quadratic_zero] using D.quadratic_lip u 0 hu (zero_mem D)
omit [CompleteSpace X] in
theorem duh_mem {u : X} (hu : u ∈ Metric.closedBall 0 R) :
    hmfDuh D u ∈ Metric.closedBall (0 : X) R := by
  have huR : ‖u‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hu
  have hrateR : hmfRate eps K R * ‖u‖ ≤ hmfRate eps K R * R :=
    mul_le_mul_of_nonneg_left huR (rate_nonneg D)
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖hmfDuh D u‖
        ≤ ‖D.seed‖ + ‖D.principal u‖ + ‖D.quadratic u‖ := by
          simpa only [hmfDuh] using
            (norm_add_le (D.seed + D.principal u) (D.quadratic u) |>.trans
              (add_le_add (norm_add_le D.seed (D.principal u)) (le_refl _)))
    _ ≤ eta + (4 * eps * ‖u‖) + (K * R * ‖u‖) :=
      add_le_add (add_le_add D.seed_bound (D.principal_bound hu))
        (D.quadratic_bound hu)
    _ = eta + hmfRate eps K R * ‖u‖ := by
      simp only [hmfRate]
      ring
    _ ≤ eta + hmfRate eps K R * R := add_le_add (le_refl eta) hrateR
    _ ≤ (1 - hmfRate eps K R) * R + hmfRate eps K R * R :=
      add_le_add D.seed_small (le_refl _)
    _ = R := by ring

def duhBall (u : HmfBall R X) : HmfBall R X :=
  ⟨hmfDuh D u, duh_mem D u.property⟩
omit [CompleteSpace X] in
private theorem duh_diff {u v : X}
    (hu : u ∈ Metric.closedBall 0 R) (hv : v ∈ Metric.closedBall 0 R) :
    ‖hmfDuh D u - hmfDuh D v‖ ≤ hmfRate eps K R * ‖u - v‖ := by
  have hsplit :
      hmfDuh D u - hmfDuh D v =
        (D.principal u - D.principal v) +
          (D.quadratic u - D.quadratic v) := by
    simp only [hmfDuh]
    abel
  rw [hsplit]
  calc
    ‖(D.principal u - D.principal v) +
        (D.quadratic u - D.quadratic v)‖
        ≤ ‖D.principal u - D.principal v‖ +
            ‖D.quadratic u - D.quadratic v‖ := norm_add_le _ _
    _ ≤ 4 * eps * ‖u - v‖ + K * R * ‖u - v‖ :=
      add_le_add (D.principal_lip u v hu hv) (D.quadratic_lip u v hu hv)
    _ = hmfRate eps K R * ‖u - v‖ := by
      simp only [hmfRate]
      ring

omit [CompleteSpace X] in
theorem duh_contracting :
    ContractingWith ⟨hmfRate eps K R, rate_nonneg D⟩ D.duhBall := by
  refine ⟨?_, ?_⟩
  · rw [← NNReal.coe_lt_coe]
    simpa using D.rate_lt_one
  · refine LipschitzWith.of_dist_le_mul ?_
    intro u v
    simpa only [Subtype.dist_eq, dist_eq_norm] using D.duh_diff u.property v.property
theorem rough_fixed :
    ∃! u : X,
      u ∈ Metric.closedBall (0 : X) R ∧
      tr u = 0 ∧
      hmfDuh D u = u := by
  let zeroBall : HmfBall R X := ⟨0, zero_mem D⟩
  letI : Nonempty (HmfBall R X) := ⟨zeroBall⟩
  letI : CompleteSpace (HmfBall R X) := Metric.isClosed_closedBall.completeSpace_coe
  let Φ : HmfBall R X → HmfBall R X := D.duhBall
  have hcontr : ContractingWith ⟨hmfRate eps K R, rate_nonneg D⟩ Φ :=
    D.duh_contracting
  let uStar : HmfBall R X := ContractingWith.fixedPoint Φ hcontr
  have hfixBall : Φ uStar = uStar := ContractingWith.fixedPoint_isFixedPt hcontr
  have hfix : hmfDuh D (uStar : X) = (uStar : X) :=
    congrArg Subtype.val hfixBall
  have htrace : tr (uStar : X) = 0 := by
    rw [← hfix]
    simp only [hmfDuh, map_add, D.trace_seed,
      D.trace_principal _ uStar.property, D.trace_quadratic _ uStar.property,
      add_zero]
  refine ⟨uStar, ⟨uStar.property, htrace, hfix⟩, ?_⟩
  intro v hv
  let vBall : HmfBall R X := ⟨v, hv.1⟩
  have hvfix : Φ vBall = vBall := by
    apply Subtype.ext
    exact hv.2.2
  have hEq : vBall = uStar := ContractingWith.fixedPoint_unique hcontr hvfix
  exact congrArg Subtype.val hEq

end HmfFPData

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

def fpOfSplit {T eps K R eta : ℝ} {C : ℝ≥0∞}
    {tr : X →L[ℝ] E}
    {fluxPot sourcePot : (ℝ × V → F) → X}
    {path : X → ℝ × V → F} {grad : X → ℝ × V → G}
    {A : ℝ × V → G →L[ℝ] F}
    {Q : ℝ × V → G →L[ℝ] G →L[ℝ] F}
    (H : HeatRoughBound T tr fluxPot sourcePot)
    (M : HmfRoughModel T R C path grad)
    (hc : HmfCoeff eps (K / 2) A Q)
    (hmeas : HmfMeas A Q grad)
    (seed : X) (heta0 : 0 ≤ eta) (hseed : ‖seed‖ ≤ eta)
    (htrace : tr seed = 0)
    (hrate : hmfRate eps K R < 1)
    (hsmall : eta ≤ (1 - hmfRate eps K R) * R) :
    HmfFPData tr eps K R eta where
  seed := seed
  principal := fun u ↦ fluxPot (hmfFlux A grad u)
  quadratic := fun u ↦ sourcePot (hmfQuad Q grad u)
  eps0 := hc.eps0
  K0 := by nlinarith [hc.K0]
  R0 := M.R0
  eta0 := heta0
  principal_zero := by
    have hz : hmfFlux A grad (0 : X) = 0 := by
      funext z
      simp only [hmfFlux, M.grad_zero, Pi.zero_apply, map_zero]
    rw [hz, H.flux_zero]
  quadratic_zero := by
    have hz : hmfQuad Q grad (0 : X) = 0 := by
      funext z
      simp only [hmfQuad, M.grad_zero, Pi.zero_apply, map_zero]
    rw [hz, H.source_zero]
  seed_bound := hseed
  principal_lip := by
    intro u v hu hv
    have hs := hmfDiffSplit hc M.R0 (norm_nonneg (u - v))
      (hmeas.principal u v) (hmeas.quad_left u v) (hmeas.quad_right u v)
      (M.grad_ball u hu) (M.grad_ball v hv) (M.grad_diff u v)
      (M.carl_ball u hu) (M.carl_ball v hv) (M.carl_diff u v)
    have hpEq :
        (fun z ↦ hmfFlux A grad u z - hmfFlux A grad v z) =
          (fun z ↦ A z (grad u z - grad v z)) := by
      funext z
      exact (map_sub (A z) (grad u z) (grad v z)).symm
    rw [← H.flux_sub, hpEq]
    exact (H.flux_norm hs.principalWt hs.principalCarl).trans_eq (by ring)
  quadratic_lip := by
    intro u v hu hv
    have hs := hmfDiffSplit hc M.R0 (norm_nonneg (u - v))
      (hmeas.principal u v) (hmeas.quad_left u v) (hmeas.quad_right u v)
      (M.grad_ball u hu) (M.grad_ball v hv) (M.grad_diff u v)
      (M.carl_ball u hu) (M.carl_ball v hv) (M.carl_diff u v)
    rw [← H.source_sub]
    change ‖sourcePot
      (fun z ↦ Q z (grad u z) (grad u z) - Q z (grad v z) (grad v z))‖ ≤ _
    exact (H.source_norm hs.sourceWt hs.sourceCarl).trans_eq (by ring)
  trace_seed := htrace
  trace_principal := by
    intro u _
    exact H.trace_flux _
  trace_quadratic := by
    intro u _
    exact H.trace_source _
  rate_lt_one := hrate
  seed_small := hsmall

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
    (seed : X) (heta0 : 0 ≤ eta) (hseed : ‖seed‖ ≤ eta)
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
  let D := fpOfSplit H M hc hmeas seed heta0 hseed htrace hrate hsmall
  obtain ⟨u, hu, huniq⟩ := D.rough_fixed
  have heq :
      seed + fluxPot (hmfFlux A grad u) + sourcePot (hmfQuad Q grad u) = u := by
    simpa [D, fpOfSplit, hmfDuh] using hu.2.2
  refine ⟨u, ⟨hu.1, hu.2.1, heq, M.path_ball u hu.1,
    M.grad_ball u hu.1, M.carl_ball u hu.1⟩, ?_⟩
  intro v hv
  apply huniq v
  refine ⟨hv.1, hv.2.1, ?_⟩
  simpa [D, fpOfSplit, hmfDuh] using hv.2.2.1

end SplitRealization

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
