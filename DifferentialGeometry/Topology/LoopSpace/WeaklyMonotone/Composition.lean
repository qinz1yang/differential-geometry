import DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone

noncomputable section

open DifferentialGeometry.Topology

namespace CircleDeg1Lift

theorem exists_continuous_lift_comp
    {σ δ : C(loopCircle, loopCircle)} (f h : CircleDeg1Lift)
    (hf : Continuous f) (hh : Continuous h)
    (hσ : ∀ t : ℝ, (f t : loopCircle) = σ (t : loopCircle))
    (hδ : ∀ t : ℝ, (h t : loopCircle) = δ (t : loopCircle)) :
    ∃ k : CircleDeg1Lift, Continuous k ∧
      ∀ t : ℝ, (k t : loopCircle) = (σ.comp δ) (t : loopCircle) := by
  let k : CircleDeg1Lift :=
    { toFun := fun t => f (h t)
      monotone' := f.monotone.comp h.monotone
      map_add_one' := fun t => by rw [h.map_add_one, f.map_add_one] }
  refine ⟨k, hf.comp hh, ?_⟩
  intro t
  change (f (h t) : loopCircle) = σ (δ (t : loopCircle))
  rw [hσ, hδ]

end CircleDeg1Lift

end
