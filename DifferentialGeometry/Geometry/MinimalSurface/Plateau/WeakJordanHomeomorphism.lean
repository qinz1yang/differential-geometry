import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Topology.LoopSpace.HomeomorphismOrientation

section

noncomputable section

open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

theorem isWeaklyMonotoneOnce_homeomorph (e : loopCircle ≃ₜ loopCircle) :
    IsWeaklyMonotoneOnce (⟨e, e.continuous⟩ : C(loopCircle, loopCircle)) := by
  rcases circleHomeomorph_affineLift_or_neg e with ⟨F, hp, hm, he⟩ | ⟨F, hp, hm, he⟩
  · refine ⟨F, F.continuous, ?_, Or.inl ⟨hm.monotone, hp⟩⟩
    intro t
    exact (he (t : loopCircle)).symm
  · refine ⟨fun t => -F t, F.continuous.neg, ?_, Or.inr ⟨hm.monotone.neg, ?_⟩⟩
    · intro t
      change ((-F t : ℝ) : loopCircle) = e (t : loopCircle)
      rw [QuotientAddGroup.mk_neg, he, affineCircleMap_coe]
    · intro t
      change -F (t + 1) = -F t - 1
      rw [hp]
      ring

end DifferentialGeometry.Geometry

end

end
