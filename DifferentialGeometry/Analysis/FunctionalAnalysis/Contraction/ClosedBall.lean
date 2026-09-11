import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Contracting

open scoped NNReal

namespace DifferentialGeometry.Analysis

variable {X : Type*} [NormedAddCommGroup X] [CompleteSpace X]

theorem exists_unique_fixedPoint_mem_closedBall
    {Φ : X → X} {R : ℝ} {κ : ℝ≥0}
    (hR : 0 ≤ R) (hκ : κ < 1)
    (hΦ0 : ‖Φ 0‖ ≤ (1 - (κ : ℝ)) * R)
    (hΦ : LipschitzOnWith κ Φ (Metric.closedBall (0 : X) R)) :
    ∃! x : X, x ∈ Metric.closedBall (0 : X) R ∧ Function.IsFixedPt Φ x := by
  have hzero : (0 : X) ∈ Metric.closedBall 0 R := by
    simpa [Metric.mem_closedBall] using hR
  have hmap : Set.MapsTo Φ (Metric.closedBall (0 : X) R)
      (Metric.closedBall (0 : X) R) := by
    intro x hx
    have hxR : ‖x‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    have hκx : (κ : ℝ) * ‖x‖ ≤ (κ : ℝ) * R :=
      mul_le_mul_of_nonneg_left hxR κ.coe_nonneg
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖Φ x‖ ≤ ‖Φ x - Φ 0‖ + ‖Φ 0‖ := by
        simpa only [sub_add_cancel] using norm_add_le (Φ x - Φ 0) (Φ 0)
      _ ≤ (κ : ℝ) * ‖x‖ + (1 - (κ : ℝ)) * R := by
        refine add_le_add ?_ hΦ0
        simpa only [dist_eq_norm, sub_zero] using hΦ.dist_le_mul x hx 0 hzero
      _ ≤ (κ : ℝ) * R + (1 - (κ : ℝ)) * R := add_le_add hκx le_rfl
      _ = R := by ring
  let Φball : Metric.closedBall (0 : X) R → Metric.closedBall (0 : X) R :=
    fun x => ⟨Φ x, hmap x.property⟩
  let zeroBall : Metric.closedBall (0 : X) R := ⟨0, hzero⟩
  let : Nonempty (Metric.closedBall (0 : X) R) := ⟨zeroBall⟩
  let : CompleteSpace (Metric.closedBall (0 : X) R) :=
    Metric.isClosed_closedBall.completeSpace_coe
  have hcontracting : ContractingWith κ Φball := by
    refine ⟨hκ, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    simpa only [Φball, Subtype.dist_eq] using
      hΦ.dist_le_mul (x : X) x.property (y : X) y.property
  let xstar : Metric.closedBall (0 : X) R :=
    ContractingWith.fixedPoint Φball hcontracting
  have hxstar : Φball xstar = xstar := hcontracting.fixedPoint_isFixedPt
  refine ⟨xstar, ⟨xstar.property, congrArg Subtype.val hxstar⟩, ?_⟩
  intro y hy
  let yball : Metric.closedBall (0 : X) R := ⟨y, hy.1⟩
  have hyball : Φball yball = yball := Subtype.ext hy.2
  exact congrArg Subtype.val (hcontracting.fixedPoint_unique hyball)

end DifferentialGeometry.Analysis
