/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage
import DifferentialGeometry.Topology.PiecewiseLinear.StdSimplexCone

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem isPLHomeomorphOn_triangle_coordinate_projection :
    IsPLHomeomorphOn (fun x : Fin 3 → ℝ => (x 1, x 2)) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1} := by
  let π : (Fin 3 → ℝ) →ₗ[ℝ] ℝ × ℝ :=
    { toFun := fun x => (x 1, x 2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hπ : IsPLHomeomorphOn π (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1} := by
    apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
      (isHPolytope_stdSimplex (Fin 3)).isPolyhedron
      (isPiecewiseAffineOn_of_affine_of_isHPolytope π.toAffineMap
        (isHPolytope_stdSimplex (Fin 3)))
    refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun z hz => ?_⟩
    · have hsum : x 0 + x 1 + x 2 = 1 := by
        simpa only [Fin.sum_univ_three] using hx.2
      exact ⟨hx.1 1, hx.1 2, by dsimp [π]; linarith [hx.1 0]⟩
    · have h1 : x 1 = y 1 := congrArg Prod.fst hxy
      have h2 : x 2 = y 2 := congrArg Prod.snd hxy
      have hsx : x 0 + x 1 + x 2 = 1 := by
        simpa only [Fin.sum_univ_three] using hx.2
      have hsy : y 0 + y 1 + y 2 = 1 := by
        simpa only [Fin.sum_univ_three] using hy.2
      funext i
      fin_cases i
      · change x 0 = y 0
        linarith
      · exact h1
      · exact h2
    · refine ⟨![1 - z.1 - z.2, z.1, z.2], ⟨?_, ?_⟩, rfl⟩
      · intro i
        fin_cases i
        · change 0 ≤ 1 - z.1 - z.2
          linarith [hz.2.2]
        · exact hz.1
        · exact hz.2.1
      · simp only [Fin.sum_univ_three]
        change 1 - z.1 - z.2 + z.1 + z.2 = 1
        ring
  exact hπ

theorem stdCenter_mem_interior_coordinate_triangle :
    ((stdCenter 1) 1, (stdCenter 1) 2) ∈
      interior {z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1} := by
  have hO : IsOpen {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2 ∧ z.1 + z.2 < 1} :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))
  have hsub : {z : ℝ × ℝ | 0 < z.1 ∧ 0 < z.2 ∧ z.1 + z.2 < 1} ⊆
      {z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1} :=
    fun _ hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
  exact interior_maximal hsub hO (by norm_num [stdCenter])

end DifferentialGeometry.Topology.PiecewiseLinear
