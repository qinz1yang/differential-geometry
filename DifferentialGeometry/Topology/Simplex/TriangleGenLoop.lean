import DifferentialGeometry.Topology.Simplex.BoundaryRetraction
import DifferentialGeometry.Topology.Homotopy.CubeCompactification
import DifferentialGeometry.Topology.Simplex.CubeParametrization

noncomputable section

open Set ContinuousMap
open scoped unitInterval

namespace DifferentialGeometry.Simplex

variable {X : Type*} [TopologicalSpace X]

def triangleGenLoop (g : C(stdSimplex ℝ (Fin 3), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 3), g p = x) :
    GenLoop (Fin 2) X x :=
  ⟨⟨fun v => g (triangleJoin (v 0, v 1)),
    g.continuous.comp (triangleJoin.continuous.comp
      ((continuous_apply 0).prodMk (continuous_apply 1)))⟩, by
    rintro v ⟨i, hi⟩
    change g (triangleJoin (v 0, v 1)) = x
    fin_cases i
    · rcases hi with hi | hi
      · rw [show v 0 = 0 from hi, triangleJoin_zero]
        exact hg _ ⟨1, by simp⟩
      · rw [show v 0 = 1 from hi, triangleJoin_one]
        exact hg _ ⟨0, map_succAbove_apply_pivot _ _⟩
    · rcases hi with hi | hi
      · rw [show v 1 = 0 from hi, triangleJoin_second_zero]
        exact hg _ ⟨2, map_succAbove_apply_pivot _ _⟩
      · rw [show v 1 = 1 from hi, triangleJoin_second_one]
        exact hg _ ⟨1, map_succAbove_apply_pivot _ _⟩⟩

@[simp] theorem triangleGenLoop_apply (g : C(stdSimplex ℝ (Fin 3), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 3), g p = x) (v : Fin 2 → unitInterval) :
    triangleGenLoop g x hg v = g (triangleJoin (v 0, v 1)) := rfl

end DifferentialGeometry.Simplex
