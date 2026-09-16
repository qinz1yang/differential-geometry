import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.BallDensity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLBall.subset_closure_sdiff_finite {A F : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : IsPLBall 1 A) (hF : F.Finite) : A ⊆ closure (A \ F) :=
  (hA.closure_sdiff_of_finite hF).symm.subset

open Classical in
theorem isPLBall_union_and_finite_frontier_inter {C D : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : IsPLBall 2 C) (hD : IsPLBall 2 D) (hI : IsPLBall 1 (C ∩ D))
    (hIC : C ∩ D ⊆ frontier C) (hID : C ∩ D ⊆ frontier D) :
    IsPLBall 2 (C ∪ D) ∧ (frontier (C ∪ D) ∩ (C ∩ D)).Finite := by
  obtain ⟨K, hKfin, hKC⟩ := hC.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hLfin, hLD⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hK : IsPLBall 2 K.space := hKC.symm ▸ hC
  have hL : IsPLBall 2 L.space := hLD.symm ▸ hD
  have hAK : K.space ∩ L.space ⊆ (boundaryComplex 2 K).space := by
    rw [boundaryComplex_space_eq_of_isPLBall_of_frontier K hK hK.isPLSphere_frontier rfl, hKC, hLD]
    exact hIC
  have hAL : K.space ∩ L.space ⊆ (boundaryComplex 2 L).space := by
    rw [boundaryComplex_space_eq_of_isPLBall_of_frontier L hL hL.isPLSphere_frontier rfl, hKC, hLD]
    exact hID
  have hArc : Schoenflies.IsArc (K.space ∩ L.space) := by
    rw [hKC, hLD]
    exact hI.isArc
  simpa only [hKC, hLD] using
    isPLBall_union_and_finite_frontier_inter_of_boundary_arc K L hK hL hArc hAK hAL

end DifferentialGeometry.Topology.PiecewiseLinear
