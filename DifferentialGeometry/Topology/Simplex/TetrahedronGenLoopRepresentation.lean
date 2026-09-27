import DifferentialGeometry.Topology.Simplex.TetrahedronJoinQuotient
import DifferentialGeometry.Topology.Simplex.TetrahedronGenLoop
import DifferentialGeometry.Topology.Simplex.TetrahedronJoinBoundary

noncomputable section
open ContinuousMap
open scoped unitInterval
namespace DifferentialGeometry.Simplex
variable {X : Type*} [TopologicalSpace X] {x : X}

private def genLoopCubeMap (p : GenLoop (Fin 3) X x) : C(I × I × I, X) :=
  ⟨fun q => p ![q.2.2,q.2.1,q.1], by fun_prop⟩

private theorem genLoopCubeMap_zero (p : GenLoop (Fin 3) X x) (t u v : I) :
    genLoopCubeMap p (0,t,u) = genLoopCubeMap p (0,t,v) := by
  exact (p.property _ ⟨2,Or.inl rfl⟩).trans (p.property _ ⟨2,Or.inl rfl⟩).symm

private theorem genLoopCubeMap_one (p : GenLoop (Fin 3) X x) (t u v : I) :
    genLoopCubeMap p (1,t,u) = genLoopCubeMap p (1,v,u) := by
  exact (p.property _ ⟨2,Or.inr rfl⟩).trans (p.property _ ⟨2,Or.inr rfl⟩).symm

def tetrahedronGenLoopRepresentative (p : GenLoop (Fin 3) X x) : C(stdSimplex ℝ (Fin 4), X) :=
  tetrahedronJoinDesc (genLoopCubeMap p) (genLoopCubeMap_zero p) (genLoopCubeMap_one p)

theorem tetrahedronGenLoopRepresentative_join (p : GenLoop (Fin 3) X x) (q : I × I × I) :
    tetrahedronGenLoopRepresentative p (tetrahedronJoin q) = p ![q.2.2,q.2.1,q.1] :=
  tetrahedronJoinDesc_apply (genLoopCubeMap p) (genLoopCubeMap_zero p) (genLoopCubeMap_one p) q

theorem tetrahedronGenLoopRepresentative_boundary (p : GenLoop (Fin 3) X x)
    (q : stdSimplex ℝ (Fin 4)) (hq : q ∈ boundary (Fin 4)) :
    tetrahedronGenLoopRepresentative p q = x := by
  obtain ⟨r, rfl⟩ := tetrahedronJoin_surjective q
  rw [tetrahedronGenLoopRepresentative_join]
  exact p.property _ ((tetrahedronJoin_mem_boundary_iff ![r.2.2,r.2.1,r.1]).mp hq)

theorem tetrahedronGenLoop_representative (p : GenLoop (Fin 3) X x) :
    tetrahedronGenLoop (tetrahedronGenLoopRepresentative p) x
      (tetrahedronGenLoopRepresentative_boundary p) = p := by
  ext v
  rw [tetrahedronGenLoop_apply, tetrahedronGenLoopRepresentative_join]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem exists_tetrahedronGenLoop_eq (p : GenLoop (Fin 3) X x) :
    ∃ g : C(stdSimplex ℝ (Fin 4), X), ∃ hg : ∀ q ∈ boundary (Fin 4), g q = x,
      tetrahedronGenLoop g x hg = p :=
  ⟨tetrahedronGenLoopRepresentative p, tetrahedronGenLoopRepresentative_boundary p,
    tetrahedronGenLoop_representative p⟩

theorem exists_tetrahedronGenLoop_class_eq (a : HomotopyGroup (Fin 3) X x) :
    ∃ g : C(stdSimplex ℝ (Fin 4), X), ∃ hg : ∀ q ∈ boundary (Fin 4), g q = x,
      (⟦tetrahedronGenLoop g x hg⟧ : HomotopyGroup (Fin 3) X x) = a := by
  induction a using Quotient.inductionOn with
  | h p =>
    obtain ⟨g,hg,hp⟩ := exists_tetrahedronGenLoop_eq p
    exact ⟨g,hg,congrArg (fun q : GenLoop (Fin 3) X x => (⟦q⟧ : HomotopyGroup (Fin 3) X x)) hp⟩

end DifferentialGeometry.Simplex
