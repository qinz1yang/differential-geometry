import DifferentialGeometry.Topology.Simplex.CubeParametrization
import DifferentialGeometry.Topology.Simplex.BoundaryRetraction

noncomputable section

open scoped unitInterval

namespace DifferentialGeometry.Simplex

private def joinLine {X : Type*} [TopologicalSpace X]
    (f : C(stdSimplex ℝ (Fin 3), X)) :
    C(unitInterval × (unitInterval × unitInterval), X) where
  toFun p :=
    f ⟨(1 - (p.1 : ℝ)) • (triangleJoinReverse p.2 : Fin 3 → ℝ) +
      (p.1 : ℝ) • (triangleJoin (p.2.2, p.2.1) : Fin 3 → ℝ),
      (convex_stdSimplex ℝ _) (triangleJoinReverse p.2).property
        (triangleJoin (p.2.2, p.2.1)).property
        (sub_nonneg.mpr p.1.2.2) p.1.2.1 (by ring)⟩
  continuous_toFun := by fun_prop

private theorem joinLine_boundary {X : Type*} [TopologicalSpace X]
    (f : C(stdSimplex ℝ (Fin 3), X)) {x : X}
    (hf : ∀ y ∈ boundary (Fin 3), f y = x)
    {p : unitInterval × unitInterval × unitInterval}
    (hp : p.2.1 = 0 ∨ p.2.1 = 1 ∨ p.2.2 = 0 ∨ p.2.2 = 1) :
    joinLine f p = x := by
  apply hf
  rcases hp with h | h | h | h
  · refine ⟨2, ?_⟩
    change (1 - (p.1 : ℝ)) * (p.2.1 : ℝ) +
      (p.1 : ℝ) * ((p.2.2 : ℝ) * (p.2.1 : ℝ)) = 0
    simp [h]
  · refine ⟨1, ?_⟩
    change (1 - (p.1 : ℝ)) * ((1 - (p.2.1 : ℝ)) * (p.2.2 : ℝ)) +
      (p.1 : ℝ) * ((p.2.2 : ℝ) * (1 - (p.2.1 : ℝ))) = 0
    simp [h]
  · refine ⟨1, ?_⟩
    change (1 - (p.1 : ℝ)) * ((1 - (p.2.1 : ℝ)) * (p.2.2 : ℝ)) +
      (p.1 : ℝ) * ((p.2.2 : ℝ) * (1 - (p.2.1 : ℝ))) = 0
    simp [h]
  · refine ⟨0, ?_⟩
    change (1 - (p.1 : ℝ)) * ((1 - (p.2.1 : ℝ)) * (1 - (p.2.2 : ℝ))) +
      (p.1 : ℝ) * (1 - (p.2.2 : ℝ)) = 0
    simp [h]

def triangleJoinReverseHomotopyRel {X : Type*} [TopologicalSpace X]
    (f : C(stdSimplex ℝ (Fin 3), X)) {x : X}
    (hf : ∀ y ∈ boundary (Fin 3), f y = x) :
    (f.comp triangleJoinReverse).HomotopyRel
      ((f.comp triangleJoin).comp ⟨Prod.swap, continuous_swap⟩)
      {p | p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1} where
  toContinuousMap := joinLine f
  map_zero_left p := by
    change f _ = f (triangleJoinReverse p)
    congr 1
    apply Subtype.ext
    funext i
    simp
    rfl
  map_one_left p := by
    change f _ = f (triangleJoin (p.2, p.1))
    congr 1
    apply Subtype.ext
    funext i
    simp
    rfl
  prop' t p hp := by
    change joinLine f (t, p) = f (triangleJoinReverse p)
    rw [joinLine_boundary f hf (p := (t, p)) hp]
    symm
    have he : joinLine f (0, p) = f (triangleJoinReverse p) := by
      change f _ = _
      congr 1
      apply Subtype.ext
      funext i
      simp
      rfl
    rw [← he]
    exact joinLine_boundary f hf (p := (0, p)) hp

end DifferentialGeometry.Simplex
