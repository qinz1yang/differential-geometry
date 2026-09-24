import DifferentialGeometry.Topology.Simplex.TriangleSphereCollapse

noncomputable section

namespace DifferentialGeometry.Simplex

variable {X : Type*} [TopologicalSpace X]

theorem exists_triangleGenLoop_eq (x : X) (a : GenLoop (Fin 2) X x) :
    ∃ g : C(stdSimplex ℝ (Fin 3), X),
      ∃ hg : ∀ p ∈ boundary (Fin 3), g p = x,
        triangleGenLoop g x hg = a := by
  let f := (Topology.genLoopSphereHomeomorph 1 x a).val
  let g := f.comp triangleCubeSphereMap
  have hg : ∀ p ∈ boundary (Fin 3), g p = x := by
    intro p hp
    change f (triangleCubeSphereMap p) = x
    rw [triangleCubeSphereMap_boundary p hp]
    exact (Topology.genLoopSphereHomeomorph 1 x a).property
  refine ⟨g, hg, ?_⟩
  apply GenLoop.ext
  intro v
  change f (triangleCubeSphereMap (triangleJoin (v 0, v 1))) = a v
  rw [triangleCubeSphereMap_triangleJoin, Topology.genLoopSphereHomeomorph_projection]
  congr 1
  ext i
  fin_cases i <;> rfl

end DifferentialGeometry.Simplex
