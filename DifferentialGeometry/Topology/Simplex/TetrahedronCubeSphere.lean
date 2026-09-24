import DifferentialGeometry.Topology.Simplex.TetrahedronJoinQuotient
import DifferentialGeometry.Topology.Simplex.TetrahedronJoinBoundary
import DifferentialGeometry.Topology.Simplex.TetrahedronGenLoop
import DifferentialGeometry.Topology.Homotopy.CubeSphereLocalHomeomorph

noncomputable section

open scoped unitInterval

namespace DifferentialGeometry.Simplex

private def cubeSphereProjectionTriple :
    C(I × I × I, Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) where
  toFun p := Topology.cubeSphereProjection 2 ![p.2.2, p.2.1, p.1]
  continuous_toFun := by
    apply Continuous.comp (Topology.cubeSphereProjection 2).continuous
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop

private theorem cubeSphereProjectionTriple_zero (t u v : I) :
    cubeSphereProjectionTriple (0, t, u) = cubeSphereProjectionTriple (0, t, v) := by
  change Topology.cubeSphereProjection 2 ![u, t, 0] =
    Topology.cubeSphereProjection 2 ![v, t, 0]
  rw [Topology.cubeSphereProjection_boundary 2 _ ⟨2, Or.inl rfl⟩,
    Topology.cubeSphereProjection_boundary 2 _ ⟨2, Or.inl rfl⟩]

private theorem cubeSphereProjectionTriple_one (t u v : I) :
    cubeSphereProjectionTriple (1, t, u) = cubeSphereProjectionTriple (1, v, u) := by
  change Topology.cubeSphereProjection 2 ![u, t, 1] =
    Topology.cubeSphereProjection 2 ![u, v, 1]
  rw [Topology.cubeSphereProjection_boundary 2 _ ⟨2, Or.inr rfl⟩,
    Topology.cubeSphereProjection_boundary 2 _ ⟨2, Or.inr rfl⟩]

def tetrahedronCubeSphereMap :
    C(stdSimplex ℝ (Fin 4), Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
  tetrahedronJoinDesc cubeSphereProjectionTriple
    cubeSphereProjectionTriple_zero cubeSphereProjectionTriple_one

@[simp] theorem tetrahedronCubeSphereMap_tetrahedronJoin (v : Fin 3 → I) :
    tetrahedronCubeSphereMap (tetrahedronJoin (v 2, v 1, v 0)) =
      Topology.cubeSphereProjection 2 v := by
  rw [tetrahedronCubeSphereMap, tetrahedronJoinDesc_apply]
  change Topology.cubeSphereProjection 2 ![v 0, v 1, v 2] = _
  congr 1
  funext i
  fin_cases i <;> rfl

theorem tetrahedronCubeSphereMap_boundary (p : stdSimplex ℝ (Fin 4))
    (hp : p ∈ boundary (Fin 4)) : tetrahedronCubeSphereMap p = Topology.cubeSphereBasepoint 2 := by
  obtain ⟨⟨s, t, u⟩, rfl⟩ := tetrahedronJoin_surjective p
  rw [show tetrahedronJoin (s, t, u) = tetrahedronJoin (![u, t, s] 2, ![u, t, s] 1, ![u, t, s] 0) from rfl,
    tetrahedronCubeSphereMap_tetrahedronJoin]
  exact Topology.cubeSphereProjection_boundary 2 _ ((tetrahedronJoin_mem_boundary_iff _).mp hp)

theorem tetrahedronCubeSphereMap_surjective : Function.Surjective tetrahedronCubeSphereMap := by
  intro z
  obtain ⟨v, rfl⟩ := Topology.cubeSphereProjection_surjective 2 z
  exact ⟨tetrahedronJoin (v 2, v 1, v 0), tetrahedronCubeSphereMap_tetrahedronJoin v⟩

theorem tetrahedronCubeSphereMap_isQuotientMap :
    _root_.Topology.IsQuotientMap tetrahedronCubeSphereMap :=
  .of_surjective_continuous tetrahedronCubeSphereMap_surjective tetrahedronCubeSphereMap.continuous

theorem tetrahedronCubeSphereMap_fiber (p q : stdSimplex ℝ (Fin 4))
    (h : tetrahedronCubeSphereMap p = tetrahedronCubeSphereMap q) :
    p = q ∨ p ∈ boundary (Fin 4) ∧ q ∈ boundary (Fin 4) := by
  obtain ⟨⟨s, t, u⟩, rfl⟩ := tetrahedronJoin_surjective p
  obtain ⟨⟨r, v, w⟩, rfl⟩ := tetrahedronJoin_surjective q
  let a : Fin 3 → I := ![u, t, s]
  let b : Fin 3 → I := ![w, v, r]
  have hab : Topology.cubeSphereProjection 2 a = Topology.cubeSphereProjection 2 b := by
    rw [← tetrahedronCubeSphereMap_tetrahedronJoin,
      ← tetrahedronCubeSphereMap_tetrahedronJoin]
    exact h
  by_cases ha : a ∈ Cube.boundary (Fin 3)
  · by_cases hb : b ∈ Cube.boundary (Fin 3)
    · right
      exact ⟨(tetrahedronJoin_mem_boundary_iff a).mpr ha,
        (tetrahedronJoin_mem_boundary_iff b).mpr hb⟩
    · have hbi : b ∈ Topology.cubeInterior (Fin 3) := by
        simpa only [Topology.cubeInterior_eq_compl_boundary, Set.mem_compl_iff] using hb
      have heq : a = b := Topology.cubeSphereProjection_eq_of_mem 2 hbi hab
      exact (hb (heq ▸ ha)).elim
  · have hai : a ∈ Topology.cubeInterior (Fin 3) := by
      simpa only [Topology.cubeInterior_eq_compl_boundary, Set.mem_compl_iff] using ha
    have heq : b = a := Topology.cubeSphereProjection_eq_of_mem 2 hai hab.symm
    left
    exact congrArg (fun c : Fin 3 → I => tetrahedronJoin (c 2, c 1, c 0)) heq.symm

variable {X : Type*} [TopologicalSpace X]

theorem genLoopSphereHomeomorph_tetrahedronGenLoop_comp (g : C(stdSimplex ℝ (Fin 4), X))
    (x : X) (hg : ∀ p ∈ boundary (Fin 4), g p = x) :
    (Topology.genLoopSphereHomeomorph 2 x (tetrahedronGenLoop g x hg)).val.comp
      tetrahedronCubeSphereMap = g := by
  ext p
  obtain ⟨⟨s, t, u⟩, rfl⟩ := tetrahedronJoin_surjective p
  rw [ContinuousMap.comp_apply,
    show tetrahedronJoin (s, t, u) = tetrahedronJoin (![u, t, s] 2, ![u, t, s] 1, ![u, t, s] 0) from rfl,
    tetrahedronCubeSphereMap_tetrahedronJoin, Topology.genLoopSphereHomeomorph_projection]
  rfl

end DifferentialGeometry.Simplex
