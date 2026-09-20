import DifferentialGeometry.Topology.LoopSpace.SpanningDisk

noncomputable section

namespace DifferentialGeometry.Topology

theorem diskTrace_comp_of_map_boundary {M : Type*} [TopologicalSpace M]
    (u : C(closedDisk, M)) (φ : C(closedDisk, closedDisk)) (δ : C(loopCircle, loopCircle))
    (hboundary : ∀ θ, φ (diskBoundary θ) = diskBoundary (δ θ)) :
    diskTrace (u.comp φ) = (diskTrace u).comp δ := by
  ext θ
  exact congrArg u (hboundary θ)

end DifferentialGeometry.Topology

end
