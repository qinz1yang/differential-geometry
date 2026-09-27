import DifferentialGeometry.Topology.Covering.CylindricalModel

noncomputable section
open Set Metric Manifold Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

private noncomputable def trivialCoverTrivialization (X : Type*) [TopologicalSpace X] :
    Trivialization Unit (id : X → X) :=
  { toOpenPartialHomeomorph := (Homeomorph.prodUnique X Unit).symm.toOpenPartialHomeomorph
    baseSet := Set.univ
    open_baseSet := isOpen_univ
    source_eq := by simp
    target_eq := by simp
    proj_toFun := by intro p hp; rfl }

private theorem identity_isCoveringMap (X : Type*) [TopologicalSpace X] :
    IsCoveringMap (id : X → X) := by
  refine IsCoveringMap.mk (f := (id : X → X)) (fun _ : X => Unit)
    (fun _ => trivialCoverTrivialization X) fun x => Set.mem_univ x

theorem nonempty_smoothCylinderCover_puncturedSpace :
    Nonempty (smoothCylinderCover
      (DifferentialGeometry.Topology.Manifold.puncturedSpace (EuclideanSpace ℝ (Fin 3)))) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let D := DifferentialGeometry.Topology.Manifold.sphereProdRealDiffeomorphPunctured
    (E := EuclideanSpace ℝ (Fin 3)) (n := 2) sphereTwoNorth
  have hcover : IsCoveringMap (D : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ →
      DifferentialGeometry.Topology.Manifold.puncturedSpace (EuclideanSpace ℝ (Fin 3))) := by
    simpa only [Function.comp_id, Diffeomorph.coe_toHomeomorph] using
      (identity_isCoveringMap _).homeomorph_comp D.toHomeomorph
  refine ⟨{ projection := D.toFun
            isCoveringMap := hcover
            surjective := D.surjective
            isLocalDiffeomorph := D.isLocalDiffeomorph
            deckModel := cylinderDeckModel.trivial
            fiber_iff := ?_ }⟩
  intro q r
  exact ⟨fun h => D.injective h, fun h => congrArg D h⟩

end DifferentialGeometry.Topology

end
