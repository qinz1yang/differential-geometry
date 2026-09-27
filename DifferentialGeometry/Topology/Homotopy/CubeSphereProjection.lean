import DifferentialGeometry.Topology.Homotopy.CubeCompactification



noncomputable section

open Set Function ContinuousMap
open scoped Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]


def cubeSphereProjection (n : ℕ) :
    C(Fin (n + 1) → unitInterval, Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
  ⟨fun t => cubeInteriorSphereHomeomorph n (openCollapse (cubeInterior (Fin (n + 1))) t),
    (cubeInteriorSphereHomeomorph n).continuous.comp
      (continuous_openCollapse _ (isOpen_cubeInterior _))⟩


theorem cubeSphereProjection_boundary (n : ℕ) (t : Fin (n + 1) → unitInterval)
    (ht : t ∈ Cube.boundary (Fin (n + 1))) :
    cubeSphereProjection n t = cubeSphereBasepoint n := by
  change cubeInteriorSphereHomeomorph n (openCollapse _ t) = _
  rw [openCollapse_of_notMem _ (by
    simpa only [cubeInterior_eq_compl_boundary, mem_compl_iff, not_not] using ht)]
  rfl


theorem cubeSphereProjection_surjective (n : ℕ) : Surjective (cubeSphereProjection n) :=
  (cubeInteriorSphereHomeomorph n).surjective.comp
    (openCollapse_surjective _ (cubeInterior_compl_nonempty _))


theorem genLoopSphereHomeomorph_projection (n : ℕ) (x : X)
    (p : GenLoop (Fin (n + 1)) X x) (t : Fin (n + 1) → unitInterval) :
    (genLoopSphereHomeomorph n x p).val (cubeSphereProjection n t) = p t := by
  have h := basedMappingSpaceDomainHomeomorph_apply (cubeInteriorSphereHomeomorph n).symm
    (cubeSphereBasepoint n) OnePoint.infty
    ((cubeInteriorSphereHomeomorph n).symm_apply_apply OnePoint.infty) x
    (genLoopCompactificationHomeomorph x p) (cubeSphereProjection n t)
  refine h.trans ?_
  change collapseDescendValue (cubeInterior (Fin (n + 1))) x
    (genLoopCollapseConstantHomeomorph x p)
      ((cubeInteriorSphereHomeomorph n).symm
        (cubeInteriorSphereHomeomorph n (openCollapse _ t))) = p t
  rw [Homeomorph.symm_apply_apply]
  exact collapseDescendValue_comp _ x (genLoopCollapseConstantHomeomorph x p) t


theorem genLoopSphereHomeomorph_const (n : ℕ) (x : X) :
    (genLoopSphereHomeomorph n x GenLoop.const).val = ContinuousMap.const _ x := by
  ext z
  obtain ⟨t, rfl⟩ := cubeSphereProjection_surjective n z
  exact genLoopSphereHomeomorph_projection n x GenLoop.const t

end DifferentialGeometry.Topology
