import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSchoenflies

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Schoenflies

open Classical in
theorem isPLSphere_one_of_isJordanCurve_of_isPolygonal {J : Set Plane}
    (hJ : IsJordanCurve J) (hpoly : IsPolygonal J) : IsPLSphere 1 J := by
  obtain ⟨m, P, hP⟩ := exists_closedPolygon hJ hpoly
  let Q : LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle := {
    n := m + 3
    three_le := by omega
    vertex := P.vertex
    adjacent_ne := P.vertex_ne
    consecutive_inter := by
      intro i
      have hc := P.corner (i + 1)
      simp only [add_sub_cancel_right, add_assoc, one_add_one_eq_two] at hc
      have hdet : Plane.det (P.vertex (i + 1) - P.vertex i)
          (P.vertex (i + 2) - P.vertex (i + 1)) ≠ 0 := by
        intro hzero
        apply hc
        calc
          Plane.det (P.vertex i - P.vertex (i + 1)) (P.vertex (i + 2) - P.vertex (i + 1)) =
              -Plane.det (P.vertex (i + 1) - P.vertex i) (P.vertex (i + 2) - P.vertex (i + 1)) := by
            simp only [Plane.det, Plane.sub_apply]
            ring
          _ = 0 := by rw [hzero, neg_zero]
      exact Subset.antisymm (segment_inter_shared hdet)
        (singleton_subset_iff.mpr ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩)
    nonadjacent_disjoint := by
      intro i j hij hprev hnext
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hi := P.edges_meet i j hij hx
      have hj := P.edges_meet j i hij.symm ⟨hx.2, hx.1⟩
      simp only [mem_insert_iff, mem_singleton_iff] at hi hj
      rcases hi with hi | hi <;> rcases hj with hj | hj
      · exact hij (P.vertex_inj (hi.symm.trans hj))
      · exact hprev (P.vertex_inj (hi.symm.trans hj))
      · exact hnext (P.vertex_inj (hi.symm.trans hj)).symm
      · exact hij (add_right_cancel (P.vertex_inj (hi.symm.trans hj))) }
  have hcarrier : Q.carrier = J := hP
  exact hcarrier ▸ isPLSphere_one_carrier Q

end DifferentialGeometry.Topology.PiecewiseLinear
