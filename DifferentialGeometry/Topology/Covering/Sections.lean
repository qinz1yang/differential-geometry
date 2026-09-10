import Mathlib.Topology.Homotopy.Lifting

namespace DifferentialGeometry.Topology.Covering

theorem exists_unique_section {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [SimplyConnectedSpace B] [LocallyPathConnectedSpace B] {p : E → B}
    (hp : IsCoveringMap p) (b : B) (e : E) (he : p e = b) :
    ∃! s : C(B, E), s b = e ∧ Function.RightInverse s p := by
  obtain ⟨s, ⟨hs, hproj⟩, huniq⟩ :=
    hp.existsUnique_continuousMap_lifts (ContinuousMap.id B) b e he
  refine ⟨s, ⟨hs, congrFun hproj⟩, ?_⟩
  intro t ht
  exact huniq t ⟨ht.1, funext ht.2⟩

end DifferentialGeometry.Topology.Covering
