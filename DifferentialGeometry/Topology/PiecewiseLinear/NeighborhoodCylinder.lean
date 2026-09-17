import DifferentialGeometry.Topology.PiecewiseLinear.NeighborhoodCycle
import DifferentialGeometry.Topology.PiecewiseLinear.BallIntersectionBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalDiagram
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodManifold
import DifferentialGeometry.Topology.PiecewiseLinear.Orientation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_ball_pair_with_boundary_cover_derivedNeighborhood_circle
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space) :
    ∃ (A B : Geometry.SimplicialComplex ℝ E) (D₀ D₁ : Set E),
      A.faces.Finite ∧ B.faces.Finite ∧ IsPLBall 3 A.space ∧ IsPLBall 3 B.space ∧
      IsPLBall 2 D₀ ∧ IsPLBall 2 D₁ ∧ Disjoint D₀ D₁ ∧
      A.space ∪ B.space = (derivedNeighborhood K L).space ∧ A.space ∩ B.space = D₀ ∪ D₁ ∧
      D₀ ⊆ (boundaryComplex 3 A).space ∧ D₁ ⊆ (boundaryComplex 3 A).space ∧
      D₀ ⊆ (boundaryComplex 3 B).space ∧ D₁ ⊆ (boundaryComplex 3 B).space := by
  let _ : DecidableEq E := Classical.decEq _
  obtain ⟨A, B, D₀, D₁, hA, hB, hD₀, hD₁, hdis, hcover, hinter, Q, hQfin, hQB, hD₀Q, hD₁Q⟩ :=
    exists_isPLBall_pair_cover_derivedNeighborhood_circle_with_boundary K L hK hLK hL hconn
  obtain ⟨R, hRfin, hRA⟩ := hA.isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  let _ : Finite Q.faces := hQfin.to_subtype
  have hR : IsPLBall 3 R.space := hRA.symm ▸ hA
  have hQ : IsPLBall 3 Q.space := hQB.symm ▸ hB
  have hRK : R.space ⊆ K.space := hRA.subset.trans
    (subset_union_left.trans (hcover.subset.trans (derivedNeighborhood_space_subset K L)))
  have hQK : Q.space ⊆ K.space := hQB.subset.trans
    (subset_union_right.trans (hcover.subset.trans (derivedNeighborhood_space_subset K L)))
  have hmeet : R.space ∩ Q.space = D₀ ∪ D₁ := by rwa [hRA, hQB]
  have hmeetQ : R.space ∩ Q.space ⊆ (boundaryComplex 3 Q).space :=
    hmeet.subset.trans (union_subset hD₀Q hD₁Q)
  have hD₀R := hK.subset_boundaryComplex_of_subset_inter_of_isPLBall R Q hR hQ hRK hQK hmeetQ
    hD₀ (subset_union_left.trans hmeet.symm.subset)
  have hD₁R := hK.subset_boundaryComplex_of_subset_inter_of_isPLBall R Q hR hQ hRK hQK hmeetQ
    hD₁ (subset_union_right.trans hmeet.symm.subset)
  refine ⟨R, Q, D₀, D₁, hRfin, hQfin, hR, hQ, hD₀, hD₁, hdis, ?_, hmeet,
    hD₀R, hD₁R, hD₀Q, hD₁Q⟩
  rwa [hRA, hQB]

open Classical in
theorem exists_cylindricalDiagram_derivedNeighborhood_circle
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space) :
    ∃ φ : (Fin 3 → ℝ) × ℝ → E,
      IsCylindricalDiagram φ (stdSimplex ℝ (Fin 3)) (derivedNeighborhood K L).space := by
  classical
  obtain ⟨A, B, D₀, D₁, hAfin, hBfin, hA, hB, hD₀, hD₁, hdis, hcover, hinter,
    hD₀A, hD₁A, hD₀B, hD₁B⟩ :=
    exists_ball_pair_with_boundary_cover_derivedNeighborhood_circle K L hK hLK hL hconn
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite B.faces := hBfin.to_subtype
  obtain ⟨g₀, hg₀⟩ := hD₀
  have hP : IsPLBall 2 (stdSimplex ℝ (Fin 3)) :=
    ⟨id, (isHPolytope_stdSimplex (Fin 3)).isPolyhedron.isPLHomeomorphOn_id⟩
  obtain ⟨φ, hφ, _⟩ := exists_cylindricalDiagram_of_ball_pair hP A B hA hB hD₁ hdis
    hD₀A hD₁A hD₀B hD₁B hinter hg₀
  exact ⟨φ, hcover ▸ hφ⟩

open Classical in
theorem exists_cylindricalDiagram_isOrientable_derivedNeighborhood_circle
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hL : IsCombinatorialManifold 1 L) (hconn : IsConnected L.space) (hor : IsOrientable 3 K) :
    let _ : Finite (derivedNeighborhood K L).faces := (derivedNeighborhood_faces_finite K L).to_subtype
    IsOrientable 3 (derivedNeighborhood K L) ∧
      ∃ φ : (Fin 3 → ℝ) × ℝ → E,
        IsCylindricalDiagram φ (stdSimplex ℝ (Fin 3)) (derivedNeighborhood K L).space := by
  let _ : Finite (derivedNeighborhood K L).faces := (derivedNeighborhood_faces_finite K L).to_subtype
  have hN := IsOrientable.of_le (secondDerived K) (derivedNeighborhood K L)
    (derivedNeighborhood_faces_subset K L) hK.secondDerived (hK.derivedNeighborhood L)
    (hor.barycentricSubdivision hK |>.barycentricSubdivision hK.barycentricSubdivision)
  exact ⟨hN, exists_cylindricalDiagram_derivedNeighborhood_circle K L hK hLK hL hconn⟩

end DifferentialGeometry.Topology.PiecewiseLinear
