import DifferentialGeometry.Topology.Simplex.FourSimplexJoin
import DifferentialGeometry.Topology.Simplex.BoundaryRetraction

noncomputable section

open scoped unitInterval

namespace DifferentialGeometry.Simplex

private def coneJoinLine {X : Type*} [TopologicalSpace X]
    (f : C(stdSimplex ℝ (Fin 4), X)) :
    C(unitInterval × (unitInterval × unitInterval × unitInterval), X) where
  toFun p :=
    f ⟨(1 - (p.1 : ℝ)) • (tetrahedronCone p.2 : Fin 4 → ℝ) +
      (p.1 : ℝ) • (tetrahedronJoin (p.2.2.1, p.2.1, p.2.2.2) : Fin 4 → ℝ),
      (convex_stdSimplex ℝ _) (tetrahedronCone p.2).property
        (tetrahedronJoin (p.2.2.1, p.2.1, p.2.2.2)).property
        (sub_nonneg.mpr p.1.2.2) p.1.2.1 (by ring)⟩
  continuous_toFun := by fun_prop

private theorem coneJoinLine_boundary {X : Type*} [TopologicalSpace X]
    (f : C(stdSimplex ℝ (Fin 4), X)) {x : X}
    (hf : ∀ y ∈ boundary (Fin 4), f y = x)
    {p : unitInterval × unitInterval × unitInterval × unitInterval}
    (hp : p.2.1 = 0 ∨ p.2.1 = 1 ∨ p.2.2.1 = 0 ∨ p.2.2.1 = 1 ∨
      p.2.2.2 = 0 ∨ p.2.2.2 = 1) :
    coneJoinLine f p = x := by
  apply hf
  rcases hp with h | h | h | h | h | h
  · refine ⟨1, ?_⟩
    change (1 - (p.1 : ℝ)) * ((p.2.1 : ℝ) * (1 - (p.2.2.1 : ℝ))) +
      (p.1 : ℝ) * ((1 - (p.2.2.1 : ℝ)) * (p.2.1 : ℝ)) = 0
    simp [h]
  · refine ⟨0, ?_⟩
    change (1 - (p.1 : ℝ)) * (1 - (p.2.1 : ℝ)) +
      (p.1 : ℝ) * ((1 - (p.2.2.1 : ℝ)) * (1 - (p.2.1 : ℝ))) = 0
    simp [h]
  · refine ⟨2, ?_⟩
    change (1 - (p.1 : ℝ)) * ((p.2.1 : ℝ) * (p.2.2.1 : ℝ) * (1 - (p.2.2.2 : ℝ))) +
      (p.1 : ℝ) * ((p.2.2.1 : ℝ) * (1 - (p.2.2.2 : ℝ))) = 0
    simp [h]
  · refine ⟨1, ?_⟩
    change (1 - (p.1 : ℝ)) * ((p.2.1 : ℝ) * (1 - (p.2.2.1 : ℝ))) +
      (p.1 : ℝ) * ((1 - (p.2.2.1 : ℝ)) * (p.2.1 : ℝ)) = 0
    simp [h]
  · refine ⟨3, ?_⟩
    change (1 - (p.1 : ℝ)) * ((p.2.1 : ℝ) * (p.2.2.1 : ℝ) * (p.2.2.2 : ℝ)) +
      (p.1 : ℝ) * ((p.2.2.1 : ℝ) * (p.2.2.2 : ℝ)) = 0
    simp [h]
  · refine ⟨2, ?_⟩
    change (1 - (p.1 : ℝ)) * ((p.2.1 : ℝ) * (p.2.2.1 : ℝ) * (1 - (p.2.2.2 : ℝ))) +
      (p.1 : ℝ) * ((p.2.2.1 : ℝ) * (1 - (p.2.2.2 : ℝ))) = 0
    simp [h]

def tetrahedronConeHomotopyRel {X : Type*} [TopologicalSpace X]
    (f : C(stdSimplex ℝ (Fin 4), X)) {x : X}
    (hf : ∀ y ∈ boundary (Fin 4), f y = x) :
    (f.comp tetrahedronCone).HomotopyRel
      ((f.comp tetrahedronJoin).comp ⟨fun p => (p.2.1, p.1, p.2.2), by fun_prop⟩)
      {p | p.1 = 0 ∨ p.1 = 1 ∨ p.2.1 = 0 ∨ p.2.1 = 1 ∨ p.2.2 = 0 ∨ p.2.2 = 1} where
  toContinuousMap := coneJoinLine f
  map_zero_left p := by
    change f _ = f (tetrahedronCone p)
    congr 1
    apply Subtype.ext
    funext i
    simp
    rfl
  map_one_left p := by
    change f _ = f (tetrahedronJoin (p.2.1, p.1, p.2.2))
    congr 1
    apply Subtype.ext
    funext i
    simp
    rfl
  prop' t p hp := by
    change coneJoinLine f (t, p) = f (tetrahedronCone p)
    rw [coneJoinLine_boundary f hf (p := (t, p)) hp]
    symm
    have he : coneJoinLine f (0, p) = f (tetrahedronCone p) := by
      change f _ = _
      congr 1
      apply Subtype.ext
      funext i
      simp
      rfl
    rw [← he]
    exact coneJoinLine_boundary f hf (p := (0, p)) hp

end DifferentialGeometry.Simplex
