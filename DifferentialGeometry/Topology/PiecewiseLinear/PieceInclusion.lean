import DifferentialGeometry.Topology.PiecewiseLinear.PieceTransition
import DifferentialGeometry.Topology.PiecewiseLinear.PieceRestrict
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem IsPolyhedralBall.nonempty {m : ℕ} {P : Set X}
    (hP : IsPolyhedralBall (n := n) m P) : P.Nonempty := by
  obtain ⟨T, hT⟩ := hP
  rw [← T.piece.bijOn.image_eq]
  exact hT.nonempty.image T.piece.map

theorem IsPolyhedralBall.isPLBall_inter_preimage {m : ℕ} {P Y : Set X}
    (hP : IsPolyhedralBall (n := n) m P) (T : PLPieceIn E n X Y) (hPY : P ⊆ Y) :
    IsPLBall m (T.complex.space ∩ T.map ⁻¹' P) := by
  obtain ⟨S, hS⟩ := hP
  exact hS.of_isPLHomeomorphOn (S.piece.isPLHomeomorphOn_transition_of_subset T hPY)

theorem PLPieceIn.exists_restrict_of_isPolyhedron {Y : Set X} (T : PLPieceIn E n X Y)
    {P : Set E} (hP : IsPolyhedron P) (hPK : P ⊆ T.complex.space) :
    ∃ S : PLPieceIn E n X (T.map '' P), S.complex.space = P ∧ S.map = T.map := by
  let _ : Finite T.complex.faces := T.finite_faces.to_subtype
  obtain ⟨K, hK, hfin, hrestrict⟩ := exists_isSubdivision_restrict_space T.complex hP hPK
  let T' := T.subdivide K hK hfin
  let S := T'.restrict (PiecewiseLinear.restrict K P) (restrict_faces_subset K P)
  have h : ∃ S : PLPieceIn E n X (T.map '' (PiecewiseLinear.restrict K P).space),
      S.complex.space = P ∧ S.map = T.map := ⟨S, hrestrict, rfl⟩
  rwa [hrestrict] at h

theorem PLPieceIn.isPolyhedralBall_image {Y : Set X} (T : PLPieceIn E n X Y)
    {m : ℕ} {P : Set E} (hP : IsPLBall m P) (hPK : P ⊆ T.complex.space) :
    IsPolyhedralBall (n := n) m (T.map '' P) := by
  obtain ⟨S, hS, -⟩ := T.exists_restrict_of_isPolyhedron hP.isPolyhedron hPK
  exact isPolyhedralBall_of_pieceIn S (hS.symm ▸ hP)

theorem PLPieceIn.exists_restrict_of_isPolyhedralBall {m : ℕ} {P Y : Set X}
    (T : PLPieceIn E n X Y) (hP : IsPolyhedralBall (n := n) m P) (hPY : P ⊆ Y) :
    ∃ S : PLPieceIn E n X P,
      S.complex.space = T.complex.space ∩ T.map ⁻¹' P ∧ S.map = T.map := by
  have hB := hP.isPLBall_inter_preimage T hPY
  obtain ⟨S, hspace, hmap⟩ := T.exists_restrict_of_isPolyhedron hB.isPolyhedron inter_subset_left
  have himage : T.map '' (T.complex.space ∩ T.map ⁻¹' P) = P := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := T.bijOn.surjOn (hPY hy)
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  have h : ∃ S : PLPieceIn E n X (T.map '' (T.complex.space ∩ T.map ⁻¹' P)),
      S.complex.space = T.complex.space ∩ T.map ⁻¹' P ∧ S.map = T.map := ⟨S, hspace, hmap⟩
  rwa [himage] at h

end DifferentialGeometry.Topology.PiecewiseLinear
