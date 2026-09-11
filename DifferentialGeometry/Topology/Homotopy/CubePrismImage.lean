import DifferentialGeometry.Topology.Homotopy.CubePrism



noncomputable section

open Set Function
open scoped Topology

namespace DifferentialGeometry.Topology


theorem cubePrismRetract_time_zero (n : ℕ)
    (z : unitInterval × (Fin (n + 1) → unitInterval))
    (h : cubeRadius n z.2 ≤ 1 - z.1.val / 2) : (cubePrismRetract n z).1 = 0 := by
  have hr := cubePrismScale_pos n z
  have hs : cubePrismScale n z = 1 - z.1.val / 2 := max_eq_right h
  have hd : (2 - z.1.val) / cubePrismScale n z = 2 :=
    (div_eq_iff hr.ne').mpr (by rw [hs]; ring)
  apply Subtype.ext
  change 2 - (2 - z.1.val) / cubePrismScale n z = 0
  rw [hd, sub_self]


theorem cubePrismRetract_position_boundary (n : ℕ)
    (z : unitInterval × (Fin (n + 1) → unitInterval))
    (h : 1 - z.1.val / 2 ≤ cubeRadius n z.2) :
    (cubePrismRetract n z).2 ∈ Cube.boundary (Fin (n + 1)) := by
  have hr := cubePrismScale_pos n z
  have hs : cubePrismScale n z = cubeRadius n z.2 := max_eq_left h
  obtain ⟨i, hi⟩ := cubeRadius_attained n z.2
  have ha : |2 * (z.2 i).val - 1| = cubePrismScale n z := hi.symm.trans hs.symm
  have hcoord : |2 * ((cubePrismRetract n z).2 i).val - 1| = 1 := by
    change |2 * (((2 * (z.2 i).val - 1) / cubePrismScale n z + 1) / 2) - 1| = 1
    have heq : 2 * (((2 * (z.2 i).val - 1) / cubePrismScale n z + 1) / 2) - 1 =
        (2 * (z.2 i).val - 1) / cubePrismScale n z := by ring
    rw [heq, abs_div, abs_of_pos hr, ha, div_self hr.ne']
  apply (cubeRadius_eq_one_iff n _).mp
  apply le_antisymm (cubeRadius_le_one n _)
  rw [← hcoord]
  exact cubeRadius_coordinate_le n _ i



theorem cubePrismRetract_image (n : ℕ)
    (z : unitInterval × (Fin (n + 1) → unitInterval)) :
    (cubePrismRetract n z).1 = 0 ∨
      (cubePrismRetract n z).2 ∈ Cube.boundary (Fin (n + 1)) := by
  rcases le_total (cubeRadius n z.2) (1 - z.1.val / 2) with h | h
  · exact Or.inl (cubePrismRetract_time_zero n z h)
  · exact Or.inr (cubePrismRetract_position_boundary n z h)


theorem cubePrismRetract_idempotent (n : ℕ)
    (z : unitInterval × (Fin (n + 1) → unitInterval)) :
    cubePrismRetract n (cubePrismRetract n z) = cubePrismRetract n z := by
  rcases cubePrismRetract_image n z with h | h
  · have heq : cubePrismRetract n z = (0, (cubePrismRetract n z).2) :=
      Prod.ext h rfl
    rw [heq]
    exact cubePrismRetract_bottom n _
  · exact cubePrismRetract_side n _ _ h

end DifferentialGeometry.Topology
