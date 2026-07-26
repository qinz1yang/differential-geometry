import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Contracting

/-!
# A clean Banach core for rough harmonic-map heat flow

This file isolates the part of the rough HMF construction which is only the
Banach fixed-point theorem.  The analytic realization supplies one nonlinear
map with a proved Lipschitz rate on a closed ball.  Keeping this core free of
the Euclidean source classes lets both the prescribed-coefficient and the
state-dependent quadratic realizations use the same theorem.
-/

noncomputable section

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

variable {X E : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Data for a zero-trace fixed point on the radius-`R` ball. -/
structure HmfCoreData (tr : X →L[ℝ] E) (R eta rate : ℝ) where
  seed : X
  nonlin : X → X
  R0 : 0 ≤ R
  eta0 : 0 ≤ eta
  rate0 : 0 ≤ rate
  nonlin_zero : nonlin 0 = 0
  seed_bound : ‖seed‖ ≤ eta
  nonlin_lip : ∀ u v,
    u ∈ Metric.closedBall (0 : X) R →
    v ∈ Metric.closedBall (0 : X) R →
    ‖nonlin u - nonlin v‖ ≤ rate * ‖u - v‖
  trace_seed : tr seed = 0
  trace_nonlin : ∀ u, u ∈ Metric.closedBall (0 : X) R → tr (nonlin u) = 0
  rate_lt_one : rate < 1
  seed_small : eta ≤ (1 - rate) * R

/-- The closed state ball used by the HMF contraction. -/
abbrev HmfCoreBall (R : ℝ) (X : Type*) [Zero X] [PseudoMetricSpace X] :=
  Metric.closedBall (0 : X) R

/-- The untruncated Duhamel self-map. -/
def hmfCoreMap {tr : X →L[ℝ] E} {R eta rate : ℝ}
    (D : HmfCoreData tr R eta rate) (u : X) : X :=
  D.seed + D.nonlin u

namespace HmfCoreData

variable {tr : X →L[ℝ] E} {R eta rate : ℝ}
  (D : HmfCoreData tr R eta rate)

private theorem zero_mem (D : HmfCoreData tr R eta rate) :
    (0 : X) ∈ Metric.closedBall 0 R := by
  simpa [Metric.mem_closedBall] using D.R0

private theorem nonlin_bound {u : X} (hu : u ∈ Metric.closedBall 0 R) :
    ‖D.nonlin u‖ ≤ rate * ‖u‖ := by
  simpa [D.nonlin_zero] using D.nonlin_lip u 0 hu D.zero_mem

theorem map_mem {u : X} (hu : u ∈ Metric.closedBall 0 R) :
    hmfCoreMap D u ∈ Metric.closedBall (0 : X) R := by
  have huR : ‖u‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hu
  have hrateR : rate * ‖u‖ ≤ rate * R :=
    mul_le_mul_of_nonneg_left huR D.rate0
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖hmfCoreMap D u‖ ≤ ‖D.seed‖ + ‖D.nonlin u‖ := by
      simpa only [hmfCoreMap] using norm_add_le D.seed (D.nonlin u)
    _ ≤ eta + rate * ‖u‖ := add_le_add D.seed_bound (D.nonlin_bound hu)
    _ ≤ eta + rate * R := add_le_add le_rfl hrateR
    _ ≤ (1 - rate) * R + rate * R := add_le_add D.seed_small le_rfl
    _ = R := by ring

/-- The Duhamel self-map restricted to the complete closed ball. -/
def mapBall (u : HmfCoreBall R X) : HmfCoreBall R X :=
  ⟨hmfCoreMap D u, D.map_mem u.property⟩

private theorem map_diff {u v : X}
    (hu : u ∈ Metric.closedBall 0 R) (hv : v ∈ Metric.closedBall 0 R) :
    ‖hmfCoreMap D u - hmfCoreMap D v‖ ≤ rate * ‖u - v‖ := by
  have hsplit :
      hmfCoreMap D u - hmfCoreMap D v = D.nonlin u - D.nonlin v := by
    simp only [hmfCoreMap]
    abel
  rw [hsplit]
  exact D.nonlin_lip u v hu hv

private theorem map_contracting :
    ContractingWith ⟨rate, D.rate0⟩ D.mapBall := by
  refine ⟨?_, ?_⟩
  · rw [← NNReal.coe_lt_coe]
    simpa using D.rate_lt_one
  · refine LipschitzWith.of_dist_le_mul ?_
    intro u v
    simpa only [Subtype.dist_eq, dist_eq_norm] using D.map_diff u.property v.property

/-- Banach fixed point with its zero-trace and untruncated equation. -/
theorem core_fixed [CompleteSpace X] :
    ∃! u : X,
      u ∈ Metric.closedBall (0 : X) R ∧
      tr u = 0 ∧
      hmfCoreMap D u = u := by
  let zeroBall : HmfCoreBall R X := ⟨0, D.zero_mem⟩
  letI : Nonempty (HmfCoreBall R X) := ⟨zeroBall⟩
  letI : CompleteSpace (HmfCoreBall R X) :=
    Metric.isClosed_closedBall.completeSpace_coe
  let Φ : HmfCoreBall R X → HmfCoreBall R X := D.mapBall
  have hcontr : ContractingWith ⟨rate, D.rate0⟩ Φ := D.map_contracting
  let uStar : HmfCoreBall R X := ContractingWith.fixedPoint Φ hcontr
  have hfixBall : Φ uStar = uStar := ContractingWith.fixedPoint_isFixedPt hcontr
  have hfix : hmfCoreMap D (uStar : X) = (uStar : X) :=
    congrArg Subtype.val hfixBall
  have htrace : tr (uStar : X) = 0 := by
    rw [← hfix]
    simp only [hmfCoreMap, map_add, D.trace_seed,
      D.trace_nonlin _ uStar.property, add_zero]
  refine ⟨uStar, ⟨uStar.property, htrace, hfix⟩, ?_⟩
  intro v hv
  let vBall : HmfCoreBall R X := ⟨v, hv.1⟩
  have hvfix : Φ vBall = vBall := by
    apply Subtype.ext
    exact hv.2.2
  have hEq : vBall = uStar := ContractingWith.fixedPoint_unique hcontr hvfix
  exact congrArg Subtype.val hEq

end HmfCoreData

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
