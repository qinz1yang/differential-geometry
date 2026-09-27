import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.UniformSpace.HeineCantor



noncomputable section

open Function ContinuousMap

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F]



theorem uniformContinuous_of_continuous_unit_periodic {f : ℝ → F}
    (hc : Continuous f) (hp : Periodic f 1) : UniformContinuous f := by
  let fbar : C(UnitAddCircle, F) := ⟨hp.lift, hc.quotient_liftOn' _⟩
  have hbar := CompactSpace.uniformContinuous_of_continuous fbar.continuous
  have h := hbar.comp (AddSubgroup.zmultiples (1 : ℝ)).normedMk.uniformContinuous
  exact h


theorem exists_bound_of_continuous_unit_periodic {f : ℝ → F}
    (hc : Continuous f) (hp : Periodic f 1) : ∃ B : ℝ, 0 < B ∧ ∀ x, ‖f x‖ ≤ B := by
  let fbar : C(UnitAddCircle, F) := ⟨hp.lift, hc.quotient_liftOn' _⟩
  refine ⟨‖fbar‖ + 1, by positivity, fun x => ?_⟩
  exact (fbar.norm_coe_le_norm (x : UnitAddCircle)).trans (by linarith)


theorem affinePeriodic_sub_id {ψ : ℝ → ℝ} (hψ : ∀ t, ψ (t + 1) = ψ t + 1) :
    Periodic (fun t => ψ t - t) 1 := by
  intro t
  change ψ (t + 1) - (t + 1) = ψ t - t
  rw [hψ]
  ring



theorem uniformContinuous_affinePeriodic {ψ : ℝ → ℝ} (hc : Continuous ψ)
    (hψ : ∀ t, ψ (t + 1) = ψ t + 1) : UniformContinuous ψ := by
  have h := (uniformContinuous_of_continuous_unit_periodic (hc.sub continuous_id)
    (affinePeriodic_sub_id hψ)).add uniformContinuous_id
  simpa only [Pi.sub_apply, id_eq, sub_add_cancel] using h

end DifferentialGeometry.Analysis
