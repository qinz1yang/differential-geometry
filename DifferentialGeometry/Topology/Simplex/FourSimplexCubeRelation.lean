import DifferentialGeometry.Topology.Homotopy.CubeBoundaryAdjunction
import DifferentialGeometry.Topology.Simplex.FourSimplexJoinSkeleton

noncomputable section

open ContinuousMap
open scoped unitInterval

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x : X}

private def fourSimplexJoinUncurry (F : C(stdSimplex ℝ (Fin 5), X)) :
    C((I × I × I) × (Fin 1 → I), X) :=
  ⟨fun z => F (Simplex.fourSimplexJoin (z.2 0, z.1.1, z.1.2.1, z.1.2.2)), by fun_prop⟩

def fourSimplexJoinLoopCube (F : C(stdSimplex ℝ (Fin 5), X))
    (hF : ∀ p ∈ Simplex.skeleton (Fin 5) 2, F p = x) :
    C(I × I × I, GenLoop (Fin 1) X x) := by
  let P := (fourSimplexJoinUncurry F).curry
  have hP : ∀ p : I × I × I, P p ∈ GenLoop (Fin 1) X x := by
    intro p v hv
    obtain ⟨i, hi⟩ := hv
    have hi0 : i = 0 := Subsingleton.elim i 0
    subst i
    change F (Simplex.fourSimplexJoin (v 0, p.1, p.2.1, p.2.2)) = x
    rcases hi with hi | hi
    · rw [hi]
      exact hF _ (Simplex.fourSimplexJoin_first_zero_mem_skeleton _ _ _)
    · rw [hi]
      exact hF _ (Simplex.fourSimplexJoin_first_one_mem_skeleton _ _ _)
  exact ⟨fun p => ⟨P p, hP p⟩, P.continuous.subtype_mk hP⟩

theorem fourSimplexJoinLoopCube_apply (F : C(stdSimplex ℝ (Fin 5), X))
    (hF : ∀ p ∈ Simplex.skeleton (Fin 5) 2, F p = x)
    (t u v : I) (s : Fin 1 → I) :
    fourSimplexJoinLoopCube F hF (t,u,v) s =
      F (Simplex.fourSimplexJoin (s 0,t,u,v)) := rfl

theorem fourSimplexJoinLoopCube_boundary (F : C(stdSimplex ℝ (Fin 5), X))
    (hF : ∀ p ∈ Simplex.skeleton (Fin 5) 2, F p = x)
    (t u v : I)
    (h : ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) ∨
      ((t = 0 ∨ t = 1) ∧ (v = 0 ∨ v = 1)) ∨
      ((u = 0 ∨ u = 1) ∧ (v = 0 ∨ v = 1))) :
    fourSimplexJoinLoopCube F hF (t,u,v) = GenLoop.const := by
  ext s
  exact hF _ (Simplex.fourSimplexJoin_outer_edge_mem_skeleton (s 0) t u v h)

def fourSimplexCubeFace (F : C(stdSimplex ℝ (Fin 5), X))
    (hF : ∀ p ∈ Simplex.skeleton (Fin 5) 2, F p = x)
    (j : Fin 3) (e : I) (he : e = 0 ∨ e = 1) : GenLoop (Fin 3) X x :=
  cubeBoundaryLoopFace (fourSimplexJoinLoopCube F hF)
    (fourSimplexJoinLoopCube_boundary F hF) j e he

theorem fourSimplexCubeFace_apply (F : C(stdSimplex ℝ (Fin 5), X))
    (hF : ∀ p ∈ Simplex.skeleton (Fin 5) 2, F p = x)
    (j : Fin 3) (e : I) (he : e = 0 ∨ e = 1) (v : Fin 3 → I) :
    fourSimplexCubeFace F hF j e he v = F (Simplex.fourSimplexJoin
      (match j with
        | 0 => (v 2, e, v 1, v 0)
        | 1 => (v 2, v 1, e, v 0)
        | 2 => (v 2, v 1, v 0, e))) := by
  rw [fourSimplexCubeFace, cubeBoundaryLoopFace_apply]
  fin_cases j <;> rfl

theorem fourSimplexCubeFace_zero (F : C(stdSimplex ℝ (Fin 5), X))
    (hF : ∀ p ∈ Simplex.skeleton (Fin 5) 2, F p = x) :
    fourSimplexCubeFace F hF 1 0 (Or.inl rfl) = GenLoop.const := by
  ext v
  rw [fourSimplexCubeFace_apply]
  exact hF _ (Simplex.fourSimplexJoin_third_zero_mem_skeleton _ _ _)

theorem homotopyGroup_fourSimplexCubeFace_relation (F : C(stdSimplex ℝ (Fin 5), X))
    (hF : ∀ p ∈ Simplex.skeleton (Fin 5) 2, F p = x) :
    let q (i : Fin 3) (e : I) (he : e = 0 ∨ e = 1) : HomotopyGroup (Fin 3) X x :=
      ⟦fourSimplexCubeFace F hF i e he⟧
    q 0 1 (Or.inr rfl) * q 2 1 (Or.inr rfl) =
      q 0 0 (Or.inl rfl) * q 1 1 (Or.inr rfl) * q 2 0 (Or.inl rfl) := by
  let q (i : Fin 3) (e : I) (he : e = 0 ∨ e = 1) : HomotopyGroup (Fin 3) X x :=
    ⟦fourSimplexCubeFace F hF i e he⟧
  have h : q 0 1 (Or.inr rfl) * q 1 0 (Or.inl rfl) * q 2 1 (Or.inr rfl) =
      q 0 0 (Or.inl rfl) * q 1 1 (Or.inr rfl) * q 2 0 (Or.inl rfl) :=
    homotopyGroup_loop_cube_boundary_relation
      (fourSimplexJoinLoopCube F hF) (fourSimplexJoinLoopCube_boundary F hF)
  have hzero : q 1 0 (Or.inl rfl) = 1 :=
    congrArg (fun a : GenLoop (Fin 3) X x => (⟦a⟧ : HomotopyGroup (Fin 3) X x))
      (fourSimplexCubeFace_zero F hF)
  rw [hzero, mul_one] at h
  exact h

end DifferentialGeometry.Topology
