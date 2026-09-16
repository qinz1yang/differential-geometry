import DifferentialGeometry.Topology.PlanarJordan.ArcDiskNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalJordan

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLBall_neighborhood_of_isArc {A U : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : Schoenflies.IsArc A) (hU : U ∈ 𝓝ˢ A) :
    ∃ D : Set (EuclideanSpace ℝ (Fin 2)), IsPLBall 2 D ∧ A ⊆ interior D ∧ D ⊆ U := by
  obtain ⟨J, hJ, hpoly, hAJ, hJU⟩ :=
    PlanarJordan.exists_polygonal_jordan_neighborhood_of_isArc hA hU
  refine ⟨closure (Schoenflies.inside J),
    isPLBall_closure_inside_of_isPLSphere_one
      (isPLSphere_one_of_isJordanCurve_of_isPolygonal hJ hpoly), ?_, hJU⟩
  intro x hx
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
    ((Schoenflies.jordan_curve_theorem hJ).isOpen_inside.mem_nhds (hAJ hx)) subset_closure)

open Classical in
theorem exists_pairwise_disjoint_isPLBall_neighborhoods_of_isArc
    {ι : Type*} [Finite ι] (A U : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (hA : ∀ i, Schoenflies.IsArc (A i)) (hU : ∀ i, U i ∈ 𝓝ˢ (A i))
    (hdis : Pairwise fun i j => Disjoint (A i) (A j)) :
    ∃ D : ι → Set (EuclideanSpace ℝ (Fin 2)),
      (∀ i, IsPLBall 2 (D i) ∧ A i ⊆ interior (D i) ∧ D i ⊆ U i) ∧
      Pairwise fun i j => Disjoint (D i) (D j) := by
  have hfilters : Pairwise fun i j => Disjoint (𝓝ˢ (A i)) (𝓝ˢ (A j)) := by
    intro i j hij
    exact separatedNhds_iff_disjoint.mp (SeparatedNhds.of_isCompact_isCompact_isClosed
      (hA i).isCompact (hA j).isCompact (hA j).isClosed (hdis hij))
  obtain ⟨V, hV, hVdis⟩ := hfilters.exists_mem_filter_of_disjoint
  have hlocal (i : ι) := exists_isPLBall_neighborhood_of_isArc (hA i)
    (Filter.inter_mem (hU i) (hV i))
  choose D hD hAD hDU using hlocal
  exact ⟨D, fun i => ⟨hD i, hAD i, (hDU i).trans inter_subset_left⟩,
    fun i j hij => (hVdis hij).mono ((hDU i).trans inter_subset_right)
      ((hDU j).trans inter_subset_right)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
