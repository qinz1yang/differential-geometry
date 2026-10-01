import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.GraphTube
import DifferentialGeometry.Topology.PiecewiseLinear.Section33TubeFrame
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralGraph

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_derivedNeighborhood_isPLHomeomorphOn_dist_lt
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) (hfin : Finite L.faces)
    (hdim : ∀ s ∈ L.faces, s.card ≤ 2) (hedge : ∃ e ∈ L.faces, e.card = 2)
    (hconn : IsConnected L.space)
    (hend : ∀ v : L.vertices, ((SimplicialComplex.edgeGraph L).neighborSet v).ncard ≠ 1)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U) (hLU : L.space ⊆ U)
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hh : Topology.IsEmbedding (U.domRestrict h)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (T L' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      T.faces.Finite ∧ IsSubdivision L' L ∧ L'.faces ⊆ T.faces ∧
      IsCombinatorialManifoldWithBoundary 3 T ∧ T.space ∈ nhdsSet L.space ∧
      IsCombinatorialManifoldWithBoundary 3 (derivedNeighborhood T L') ∧
      (derivedNeighborhood T L').space ∈ nhdsSet L.space ∧
      (derivedNeighborhood T L').space ⊆ U ∧
      ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphOn f (derivedNeighborhood T L').space
          (f '' (derivedNeighborhood T L').space) ∧
        f '' (derivedNeighborhood T L').space ∈ nhdsSet (h '' L.space) ∧
        ∀ x ∈ (derivedNeighborhood T L').space, dist (f x) (h x) < ε := by
  let _ : Finite L.faces := hfin
  obtain ⟨T, L', C, D, Dbd, hTfin, hsub, hLT, hT, hDN, hNU, hend', ht, -, hCsmall⟩ :=
    exists_section33TubeFrame L hdim hedge hend hU hLU hh hε
  have hconn' : IsConnected L'.space := by
    rw [hsub.space_eq]
    exact hconn
  obtain ⟨f, hf, hfN, hfC⟩ := exists_isPLHomeomorphOn_tube_image_dualCell_subset L' _ _ C D Dbd h ht hconn' hend'
    (fun v => Metric.thickening (ε / 4) (h '' C v)) fun v _ =>
      Metric.isOpen_thickening.mem_nhdsSet.mpr (Metric.self_subset_thickening (by linarith) _)
  refine ⟨T, L', hTfin, hsub, hLT, hT, ?_, hDN, ?_, hNU, f, hf, ?_, fun x hx => ?_⟩
  · rw [← hsub.space_eq]
    exact Filter.mem_of_superset ht.isNeighborhood (derivedNeighborhood_space_subset T L')
  · rw [← hsub.space_eq]
    exact ht.isNeighborhood
  · rw [← hsub.space_eq]
    exact hfN
  · have hx' : x ∈ ⋃ v ∈ L'.vertices, C v := by
      rw [← ht.unionEq]
      exact hx
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx'
    obtain ⟨z, ⟨y, hy, rfl⟩, hdz⟩ := Metric.mem_thickening_iff.mp (hfC v hv ⟨x, hxv, rfl⟩)
    have h1 := hCsmall v hv y hy x hxv
    have h2 := dist_triangle (f x) (h y) (h x)
    linarith

open Classical in
theorem exists_derivedNeighborhood_isPLHomeomorphOn_dist_lt_tetrahedron_oneSkeleton :
    ∃ L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      L.faces.Finite ∧
      (∃ v : L.vertices,
        ((SimplicialComplex.edgeGraph L).neighborSet v).ncard = 3) ∧
      ∀ U : Set (EuclideanSpace ℝ (Fin 3)), IsOpen U → L.space ⊆ U →
      ∀ h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        Topology.IsEmbedding (U.domRestrict h) →
      ∀ ε : ℝ, 0 < ε →
        ∃ (T L' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
          T.faces.Finite ∧
          IsSubdivision L' L ∧
          L'.faces ⊆ T.faces ∧
          IsCombinatorialManifoldWithBoundary 3 T ∧
          T.space ∈ nhdsSet L.space ∧
          IsCombinatorialManifoldWithBoundary 3 (derivedNeighborhood T L') ∧
          (derivedNeighborhood T L').space ∈ nhdsSet L.space ∧
          (derivedNeighborhood T L').space ⊆ U ∧
          ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
            IsPLHomeomorphOn f (derivedNeighborhood T L').space
              (f '' (derivedNeighborhood T L').space) ∧
            f '' (derivedNeighborhood T L').space ∈ nhdsSet (h '' L.space) ∧
            ∀ x ∈ (derivedNeighborhood T L').space, dist (f x) (h x) < ε := by
  obtain ⟨L, hfin, hdim, hedge, hconn, hend, hbranch⟩ := exists_tetrahedron_oneSkeleton
  let _ : Finite L.faces := hfin.to_subtype
  exact ⟨L, hfin, hbranch, exists_derivedNeighborhood_isPLHomeomorphOn_dist_lt L inferInstance hdim hedge hconn hend⟩

end DifferentialGeometry.Topology.PiecewiseLinear
