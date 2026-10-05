import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialResidualFaces

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

def radialCuspRow : radialSlims.RowIndex := .inr (.inl 0)
def radialSlimRow : radialSlims.RowIndex := .inr (.inr (0 : Fin 1))

theorem radial_allPiece_cases (a : radialSlims.RowIndex ⊕ Bool) :
    a = .inl radialCuspRow ∨ a = .inl radialSlimRow ∨ a = .inr true ∨ a = .inr false := by
  rcases a with i | b
  · rcases i with i | b | j
    · exact Fin.elim0 i
    · have hb : b = (0 : Fin 1) := Subsingleton.elim _ _
      subst b
      exact Or.inl rfl
    · have hj : j = (0 : Fin 1) := @Subsingleton.elim (Fin 1) inferInstance j 0
      subst j
      exact Or.inr (Or.inl rfl)
  · cases b
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl rfl))

theorem radial_piece_cusp : allPieces radialSlims radialEdgeBundle radialCircleBundle
    (.inl radialCuspRow) = range cuspToCarrier := rfl

theorem radial_piece_slim : allPieces radialSlims radialEdgeBundle radialCircleBundle
    (.inl radialSlimRow) = range slimToCarrier := rfl

theorem radial_piece_edge : allPieces radialSlims radialEdgeBundle radialCircleBundle
    (.inr true) = {p | height p ≤ -(3 / 4 : ℝ)} := radial_edge_height

theorem radial_piece_circle : allPieces radialSlims radialEdgeBundle radialCircleBundle
    (.inr false) = {p | -(3 / 4 : ℝ) ≤ height p ∧ height p ≤ -(1 / 2 : ℝ)} :=
  radialCircleBundle_region

theorem radial_pieces_cover : (⋃ a, allPieces radialSlims radialEdgeBundle
    radialCircleBundle a) = univ := by
  apply eq_univ_of_forall
  intro p
  by_cases hc : -(1 / 4 : ℝ) ≤ height p
  · apply mem_iUnion.mpr
    refine ⟨.inl radialCuspRow, ?_⟩
    rw [radial_piece_cusp, cuspToCarrier_range]
    exact hc
  · by_cases hs : -(1 / 2 : ℝ) ≤ height p
    · apply mem_iUnion.mpr
      refine ⟨.inl radialSlimRow, ?_⟩
      rw [radial_piece_slim, slimToCarrier_range]
      exact ⟨hs, (not_le.mp hc).le⟩
    · by_cases hr : -(3 / 4 : ℝ) ≤ height p
      · apply mem_iUnion.mpr
        refine ⟨.inr false, ?_⟩
        rw [radial_piece_circle]
        exact ⟨hr, (not_le.mp hs).le⟩
      · apply mem_iUnion.mpr
        refine ⟨.inr true, ?_⟩
        rw [radial_piece_edge]
        exact (not_le.mp hr).le

theorem radial_pieces_interiors_disjoint : Pairwise fun a a' =>
    Disjoint (interior (allPieces radialSlims radialEdgeBundle radialCircleBundle a))
      (interior (allPieces radialSlims radialEdgeBundle radialCircleBundle a')) := by
  intro a b hne
  rcases radial_allPiece_cases a with ha | ha | ha | ha <;> subst a
  all_goals rcases radial_allPiece_cases b with hb | hb | hb | hb <;> subst b
  all_goals first | exact (hne rfl).elim | skip
  all_goals simp only [radial_piece_cusp, radial_piece_slim, radial_piece_edge,
    radial_piece_circle, radial_cusp_interior, radial_slim_interior,
    height_interior_le (-(3 / 4 : ℝ)) (by norm_num) (by norm_num),
    height_interior_band (-(3 / 4 : ℝ)) (-(1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  all_goals rw [disjoint_left]
  all_goals intro p hp hq
  all_goals simp only [mem_ofPred_eq] at hp hq
  all_goals try rcases hp with ⟨hp, hp'⟩
  all_goals try rcases hq with ⟨hq, hq'⟩
  all_goals linarith

end GC.GraphManifold.Assembly.FC39P0.X135Radial
