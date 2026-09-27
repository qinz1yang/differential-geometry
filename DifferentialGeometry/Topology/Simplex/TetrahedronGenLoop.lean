import DifferentialGeometry.Topology.Simplex.TriangleGenLoop
import DifferentialGeometry.Topology.Simplex.CubeParametrization
import DifferentialGeometry.Topology.Simplex.TetrahedronConeHomotopy
import DifferentialGeometry.Topology.Homotopy.CoordinateSwap

noncomputable section
open ContinuousMap
open scoped unitInterval
namespace DifferentialGeometry.Simplex
variable {X : Type*} [TopologicalSpace X]

def tetrahedronGenLoop (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 4), g p = x) : GenLoop (Fin 3) X x :=
  ⟨⟨fun v => g (Simplex.tetrahedronJoin (v 2, v 1, v 0)), by fun_prop⟩, by
    rintro v ⟨i, hi⟩
    apply hg
    fin_cases i
    · rcases hi with h | h
      · exact ⟨3, by simp [tetrahedronJoin, show v 0 = 0 from h]⟩
      · exact ⟨2, by simp [tetrahedronJoin, show v 0 = 1 from h]⟩
    · rcases hi with h | h
      · exact ⟨1, by simp [tetrahedronJoin, show v 1 = 0 from h]⟩
      · exact ⟨0, by simp [tetrahedronJoin, show v 1 = 1 from h]⟩
    · rcases hi with h | h
      · exact ⟨2, by simp [tetrahedronJoin, show v 2 = 0 from h]⟩
      · exact ⟨0, by simp [tetrahedronJoin, show v 2 = 1 from h]⟩⟩

@[simp] theorem tetrahedronGenLoop_apply (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 4), g p = x) (v : Fin 3 → unitInterval) :
    tetrahedronGenLoop g x hg v = g (Simplex.tetrahedronJoin (v 2, v 1, v 0)) := rfl


def tetrahedronConeGenLoop (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 4), g p = x) : GenLoop (Fin 3) X x :=
  ⟨⟨fun v => g (tetrahedronCone (v 2, v 1, v 0)), by fun_prop⟩, by
    rintro v ⟨i, hi⟩
    apply hg
    fin_cases i
    · rcases hi with h | h
      · exact ⟨3, by simp [tetrahedronCone, show v 0 = 0 from h]⟩
      · exact ⟨2, by simp [tetrahedronCone, show v 0 = 1 from h]⟩
    · rcases hi with h | h
      · exact ⟨2, by simp [tetrahedronCone, show v 1 = 0 from h]⟩
      · exact ⟨1, by simp [tetrahedronCone, show v 1 = 1 from h]⟩
    · rcases hi with h | h
      · exact ⟨1, by simp [tetrahedronCone, show v 2 = 0 from h]⟩
      · exact ⟨0, by simp [tetrahedronCone, show v 2 = 1 from h]⟩⟩

def tetrahedronConeGenLoopHomotopyRel (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 4), g p = x) :
    (tetrahedronConeGenLoop g x hg).val.HomotopyRel
      (GenLoop.congr x (Equiv.swap (1 : Fin 3) 2) (tetrahedronGenLoop g x hg)).val
      (Cube.boundary (Fin 3)) where
  toContinuousMap := (tetrahedronConeHomotopyRel g hg).toContinuousMap.comp
    ⟨fun z => (z.1,z.2 2,z.2 1,z.2 0), by fun_prop⟩
  map_zero_left v := by
    change tetrahedronConeHomotopyRel g hg (0,v 2,v 1,v 0) = _
    rw [ContinuousMap.HomotopyWith.apply_zero]
    rfl
  map_one_left v := by
    change tetrahedronConeHomotopyRel g hg (1,v 2,v 1,v 0) = _
    rw [ContinuousMap.HomotopyWith.apply_one]
    change g (tetrahedronJoin (v 1,v 2,v 0)) =
      g (tetrahedronJoin (v (Equiv.swap (1 : Fin 3) 2 2),
        v (Equiv.swap (1 : Fin 3) 2 1), v (Equiv.swap (1 : Fin 3) 2 0)))
    simp [Equiv.swap_apply_def]
  prop' t v hv := by
    have hb : (v 2,v 1,v 0) ∈ {p : unitInterval × unitInterval × unitInterval |
        p.1 = 0 ∨ p.1 = 1 ∨ p.2.1 = 0 ∨ p.2.1 = 1 ∨ p.2.2 = 0 ∨ p.2.2 = 1} := by
      obtain ⟨i,hi⟩ := hv
      fin_cases i
      · exact Or.inr (Or.inr (Or.inr (Or.inr hi)))
      · rcases hi with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · rcases hi with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    exact (tetrahedronConeHomotopyRel g hg).eq_fst t hb

theorem tetrahedronConeGenLoop_class_eq_inv (g : C(stdSimplex ℝ (Fin 4), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 4), g p = x) :
    (⟦tetrahedronConeGenLoop g x hg⟧ : HomotopyGroup (Fin 3) X x) =
      ((·⁻¹) : HomotopyGroup (Fin 3) X x → HomotopyGroup (Fin 3) X x)
        ⟦tetrahedronGenLoop g x hg⟧ := by
  have h : (⟦tetrahedronConeGenLoop g x hg⟧ : HomotopyGroup (Fin 3) X x) =
      (⟦GenLoop.congr x (Equiv.swap (1 : Fin 3) 2) (tetrahedronGenLoop g x hg)⟧ :
        HomotopyGroup (Fin 3) X x) :=
    Quotient.sound ⟨tetrahedronConeGenLoopHomotopyRel g x hg⟩
  exact h.trans
    (Topology.homotopyGroup_swap_eq_inv_of_ne 1 2 (by decide) (tetrahedronGenLoop g x hg))

end DifferentialGeometry.Simplex
