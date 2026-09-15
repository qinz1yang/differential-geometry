import DifferentialGeometry.Topology.Homotopy.CubeBoundaryRelation
import DifferentialGeometry.Topology.Homotopy.Adjunction
import DifferentialGeometry.Topology.Homotopy.Reindex
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section

open ContinuousMap
open scoped unitInterval

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X] {x : X}

private def homotopyGroupLoopTwoMulEquiv :
    HomotopyGroup (Fin 2) (GenLoop (Fin 1) X x) GenLoop.const ≃*
      HomotopyGroup (Fin 3) X x :=
  (homotopyGroupIteratedLoopMulEquiv (K := Fin 2) (N := Fin 1) x).trans
    (homotopyGroupReindexMulEquiv finSumFinEquiv x)

def cubeBoundaryLoopFace (G : C(I × I × I, GenLoop (Fin 1) X x))
    (hG : ∀ s t u, ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) ∨
      ((s = 0 ∨ s = 1) ∧ (u = 0 ∨ u = 1)) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = GenLoop.const)
    (j : Fin 3) (e : I) (he : e = 0 ∨ e = 1) : GenLoop (Fin 3) X x :=
  GenLoop.congr x finSumFinEquiv
    (GenLoop.genLoopGenLoopEquiv x (cubeBoundaryFace G hG j e he))

theorem cubeBoundaryLoopFace_apply (G : C(I × I × I, GenLoop (Fin 1) X x))
    (hG : ∀ s t u, ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) ∨
      ((s = 0 ∨ s = 1) ∧ (u = 0 ∨ u = 1)) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = GenLoop.const)
    (j : Fin 3) (e : I) (he : e = 0 ∨ e = 1) (v : Fin 3 → I) :
    cubeBoundaryLoopFace G hG j e he v =
      G (match j with
        | 0 => (e, v 1, v 0)
        | 1 => (v 1, e, v 0)
        | 2 => (v 1, v 0, e)) (fun _ => v 2) := by
  fin_cases j <;>
    change G _ (fun k => v (finSumFinEquiv (Sum.inr k))) = _ <;>
    congr 1 <;> funext k <;> fin_cases k <;> rfl

theorem homotopyGroup_loop_cube_boundary_relation
    (G : C(I × I × I, GenLoop (Fin 1) X x))
    (hG : ∀ s t u, ((s = 0 ∨ s = 1) ∧ (t = 0 ∨ t = 1)) ∨
      ((s = 0 ∨ s = 1) ∧ (u = 0 ∨ u = 1)) ∨
      ((t = 0 ∨ t = 1) ∧ (u = 0 ∨ u = 1)) → G (s, t, u) = GenLoop.const) :
    let q (i : Fin 3) (e : I) (he : e = 0 ∨ e = 1) : HomotopyGroup (Fin 3) X x :=
      ⟦cubeBoundaryLoopFace G hG i e he⟧
    q 0 1 (Or.inr rfl) * q 1 0 (Or.inl rfl) * q 2 1 (Or.inr rfl) =
      q 0 0 (Or.inl rfl) * q 1 1 (Or.inr rfl) * q 2 0 (Or.inl rfl) := by
  let E := homotopyGroupLoopTwoMulEquiv (x := x)
  let q (i : Fin 3) (e : I) (he : e = 0 ∨ e = 1) :
      HomotopyGroup (Fin 2) (GenLoop (Fin 1) X x) GenLoop.const :=
    ⟦cubeBoundaryFace G hG i e he⟧
  have h : q 0 1 (Or.inr rfl) * q 1 0 (Or.inl rfl) * q 2 1 (Or.inr rfl) =
      q 0 0 (Or.inl rfl) * q 1 1 (Or.inr rfl) * q 2 0 (Or.inl rfl) :=
    homotopyGroup_cube_boundary_relation G hG
  have h' := congrArg E h
  rw [map_mul, map_mul, map_mul, map_mul] at h'
  exact h'

end DifferentialGeometry.Topology
