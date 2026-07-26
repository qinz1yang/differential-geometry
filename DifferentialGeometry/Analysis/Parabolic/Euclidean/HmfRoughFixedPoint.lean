import DifferentialGeometry.Analysis.Parabolic.Euclidean.HmfRoughMap
import Mathlib.Topology.MetricSpace.Contracting

/-!
# The rough harmonic-map heat-flow fixed point

This file isolates the Banach step in the local-addition harmonic-map
heat-flow construction.  The ambient Banach space is the rough parabolic
path space and `tr` is its initial-value trace.  The fixed-point ball is
centred at the zero section.

The two critical Duhamel arms are kept separate.  The prescribed principal
coefficient contributes `4 * eps`, exactly as in `critCoeff_int_le`, while
the quadratic-gradient arm contributes `K * R` on a ball of radius `R`.
Thus the contraction rate is

`4 * eps + K * R`.

There is deliberately no power of the time horizon in the principal rate.
Shortening the horizon may only be used to make the noncritical seed `seed`
small enough to stay in the ball.
-/

noncomputable section

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exact contraction rate for the rough HMF map.  The factor `4` is the
critical time-convolution bound; `K * R` is the quadratic-gradient rate on
the radius-`R` state ball. -/
def hmfRate (eps K R : ℝ) : ℝ := 4 * eps + K * R

/-- Analytic data for the zero-initial-value rough HMF Duhamel map.

`principal` is the heat potential of the prescribed inverse-metric
difference flux and `quadratic` is the heat potential of the target/local
addition quadratic-gradient source.  Their Lipschitz estimates are required
only on the state ball.  The trace fields say that every Duhamel arm has zero
initial value; the fixed point therefore has zero initial value as a proved
conclusion. -/
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

/-- The closed rough-path state ball. -/
abbrev HmfBall (R : ℝ) (X : Type*) [Zero X] [PseudoMetricSpace X] :=
  Metric.closedBall (0 : X) R

/-- The untruncated rough HMF Duhamel map. -/
def hmfDuh {tr : X →L[ℝ] E} {eps K R eta : ℝ}
    (D : HmfFPData tr eps K R eta) (u : X) : X :=
  D.seed + D.principal u + D.quadratic u

namespace HmfFPData

variable {tr : X →L[ℝ] E} {eps K R eta : ℝ}
  (D : HmfFPData tr eps K R eta)

theorem rate_nonneg : 0 ≤ hmfRate eps K R := by
  exact add_nonneg (mul_nonneg (by norm_num) D.eps0) (mul_nonneg D.K0 D.R0)

private theorem zero_mem : (0 : X) ∈ Metric.closedBall 0 R := by
  simpa [Metric.mem_closedBall] using D.R0

private theorem principal_bound {u : X} (hu : u ∈ Metric.closedBall 0 R) :
    ‖D.principal u‖ ≤ 4 * eps * ‖u‖ := by
  simpa [D.principal_zero] using D.principal_lip u 0 hu D.zero_mem

private theorem quadratic_bound {u : X} (hu : u ∈ Metric.closedBall 0 R) :
    ‖D.quadratic u‖ ≤ K * R * ‖u‖ := by
  simpa [D.quadratic_zero] using D.quadratic_lip u 0 hu D.zero_mem

/-- The Duhamel map sends the radius-`R` rough-path ball into itself. -/
theorem duh_mem {u : X} (hu : u ∈ Metric.closedBall 0 R) :
    hmfDuh D u ∈ Metric.closedBall (0 : X) R := by
  have huR : ‖u‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hu
  have hrateR : hmfRate eps K R * ‖u‖ ≤ hmfRate eps K R * R :=
    mul_le_mul_of_nonneg_left huR D.rate_nonneg
  rw [Metric.mem_closedBall, dist_zero_left]
  calc
    ‖hmfDuh D u‖
        ≤ ‖D.seed‖ + ‖D.principal u‖ + ‖D.quadratic u‖ := by
          simpa [hmfDuh, add_assoc] using
            (norm_add_le (D.seed + D.principal u) (D.quadratic u) |>.trans
              (add_le_add_right (norm_add_le D.seed (D.principal u)) _))
    _ ≤ eta + (4 * eps * ‖u‖) + (K * R * ‖u‖) :=
      add_le_add (add_le_add D.seed_bound (D.principal_bound hu))
        (D.quadratic_bound hu)
    _ = eta + hmfRate eps K R * ‖u‖ := by
      simp only [hmfRate]
      ring
    _ ≤ eta + hmfRate eps K R * R := add_le_add_left hrateR eta
    _ ≤ (1 - hmfRate eps K R) * R + hmfRate eps K R * R :=
      add_le_add_right D.seed_small _
    _ = R := by ring

/-- The Duhamel self-map of the rough-path state ball. -/
def duhBall (u : HmfBall R X) : HmfBall R X :=
  ⟨hmfDuh D u, D.duh_mem u.property⟩

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

/-- The state-ball Duhamel map is a contraction with the exact rate
`4 * eps + K * R`. -/
theorem duh_contracting :
    ContractingWith ⟨hmfRate eps K R, D.rate_nonneg⟩ D.duhBall := by
  refine ⟨?_, ?_⟩
  · rw [← NNReal.coe_lt_coe]
    simpa using D.rate_lt_one
  · refine LipschitzWith.of_dist_le_mul ?_
    intro u v
    rw [Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    simpa using D.duh_diff u.property v.property

/-- Banach fixed point for the rough local-addition HMF equation.

The solution lies in the stated rough-path ball, has zero initial trace, and
satisfies the untruncated Duhamel equation.  It is unique among all elements
of the same ball satisfying that equation. -/
theorem rough_fixed :
    ∃! u : X,
      u ∈ Metric.closedBall (0 : X) R ∧
      tr u = 0 ∧
      hmfDuh D u = u := by
  let zeroBall : HmfBall R X := ⟨0, D.zero_mem⟩
  letI : Nonempty (HmfBall R X) := ⟨zeroBall⟩
  let Φ : HmfBall R X → HmfBall R X := D.duhBall
  have hcontr : ContractingWith ⟨hmfRate eps K R, D.rate_nonneg⟩ Φ :=
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
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A normalized linear heat-potential estimate on the rough path space.

The divergence potential consumes the weighted/Carleson gradient source
class and costs the critical constant `4`.  The ordinary potential consumes
the weighted/Carleson source class and costs `1`.  These are linear estimates,
not a disguised contraction hypothesis: the nonlinear contraction constants
are derived below from `hmfDiffSplit`. -/
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

/-- Realization of the rough Banach ball by an actual Euclidean path and its
spatial derivative.  Ball membership yields the two rough estimates, while
the ambient norm controls differences in the same scale. -/
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

/-- Measurability data for the three realized source arms in
`hmfDiffSplit`.  It is separated from coefficient bounds because the latter
are pointwise analytic estimates. -/
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

/-- The realized divergence flux of one HMF iterate. -/
def hmfFlux (A : ℝ × V → G →L[ℝ] F) (grad : X → ℝ × V → G)
    (u : X) (z : ℝ × V) : F :=
  A z (grad u z)

/-- The realized target/local-addition quadratic source of one HMF
iterate. -/
def hmfQuad (Q : ℝ × V → G →L[ℝ] G →L[ℝ] F)
    (grad : X → ℝ × V → G) (u : X) (z : ℝ × V) : F :=
  Q z (grad u z) (grad u z)

/-- Build the fixed-point data from the two rough heat-potential estimates
and `hmfDiffSplit`.

The raw quadratic coefficient is bounded by `K / 2`; its two difference arms
therefore add to the advertised combined rate `K * R`. -/
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

/-- The fixed point produced from `hmfDiffSplit`, with the actual HMF
Duhamel equation and both the weighted and Carleson gradient bounds exposed
in the conclusion. -/
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
