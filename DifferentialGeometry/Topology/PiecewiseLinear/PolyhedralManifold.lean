import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.PieceRestrict
import DifferentialGeometry.Topology.PiecewiseLinear.PieceTransition

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

open Classical in
def IsPolyhedralManifoldWithBoundary (m : ℕ) (P : Set X) : Prop :=
  ∃ T : PLPiece n X P, IsCombinatorialManifoldWithBoundary m T.piece.complex

open Classical in
def IsPolyhedralManifold (m : ℕ) (P : Set X) : Prop :=
  ∃ T : PLPiece n X P, IsCombinatorialManifold m T.piece.complex

open Classical in
theorem IsPolyhedralManifoldWithBoundary.isCombinatorialManifoldWithBoundary_of_piece
    {m : ℕ} {P : Set X} (hP : IsPolyhedralManifoldWithBoundary (n := n) m P)
    (T : PLPiece n X P) : IsCombinatorialManifoldWithBoundary m T.piece.complex := by
  obtain ⟨T₀, hT₀⟩ := hP
  have := T₀.piece.finite_faces.to_subtype
  have := T.piece.finite_faces.to_subtype
  exact hT₀.of_isPLHomeomorphOn (T₀.piece.isPLHomeomorphOn_transition T.piece)

open Classical in
theorem IsPolyhedralManifold.isCombinatorialManifold_of_piece {m : ℕ} {P : Set X}
    (hP : IsPolyhedralManifold (n := n) m P) (T : PLPiece n X P) :
    IsCombinatorialManifold m T.piece.complex := by
  obtain ⟨T₀, hT₀⟩ := hP
  have := T₀.piece.finite_faces.to_subtype
  have := T.piece.finite_faces.to_subtype
  exact hT₀.of_isPLHomeomorphOn (T₀.piece.isPLHomeomorphOn_transition T.piece)

open Classical in
theorem isPolyhedralManifoldWithBoundary_of_pieceIn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ} {P : Set X} (T : PLPieceIn E n X P)
    (hT : IsCombinatorialManifoldWithBoundary m T.complex) :
    IsPolyhedralManifoldWithBoundary (n := n) m P := by
  obtain ⟨T'⟩ := T.exists_pLPiece
  have := T.finite_faces.to_subtype
  have := T'.piece.finite_faces.to_subtype
  exact ⟨T', hT.of_isPLHomeomorphOn (T.isPLHomeomorphOn_transition T'.piece)⟩

open Classical in
theorem isPolyhedralManifold_of_pieceIn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ} {P : Set X} (T : PLPieceIn E n X P)
    (hT : IsCombinatorialManifold m T.complex) : IsPolyhedralManifold (n := n) m P := by
  obtain ⟨T'⟩ := T.exists_pLPiece
  have := T.finite_faces.to_subtype
  have := T'.piece.finite_faces.to_subtype
  exact ⟨T', hT.of_isPLHomeomorphOn (T.isPLHomeomorphOn_transition T'.piece)⟩

theorem IsPolyhedralManifoldWithBoundary.isCompact {m : ℕ} {P : Set X}
    (hP : IsPolyhedralManifoldWithBoundary (n := n) m P) : IsCompact P := by
  obtain ⟨T, _⟩ := hP
  exact T.piece.isCompact

theorem IsPolyhedralManifold.isCompact {m : ℕ} {P : Set X}
    (hP : IsPolyhedralManifold (n := n) m P) : IsCompact P := by
  obtain ⟨T, _⟩ := hP
  exact T.piece.isCompact

theorem IsPolyhedralBall.isPolyhedralManifoldWithBoundary {m : ℕ} {P : Set X}
    (hP : IsPolyhedralBall (n := n) (m + 1) P) :
    IsPolyhedralManifoldWithBoundary (n := n) (m + 1) P := by
  obtain ⟨T, hT⟩ := hP
  have := T.piece.finite_faces.to_subtype
  exact ⟨T, hT.isCombinatorialManifoldWithBoundary⟩

theorem IsPolyhedralSphere.isPolyhedralManifold {m : ℕ} {P : Set X}
    (hP : IsPolyhedralSphere (n := n) (m + 1) P) :
    IsPolyhedralManifold (n := n) (m + 1) P := by
  obtain ⟨T, hT⟩ := hP
  have := T.piece.finite_faces.to_subtype
  exact ⟨T, hT.isCombinatorialManifold⟩

theorem IsPolyhedralManifold.isPolyhedralManifoldWithBoundary {m : ℕ} {P : Set X}
    (hP : IsPolyhedralManifold (n := n) m P) :
    IsPolyhedralManifoldWithBoundary (n := n) m P := by
  obtain ⟨T, hT⟩ := hP
  exact ⟨T, hT.isCombinatorialManifoldWithBoundary⟩

end DifferentialGeometry.Topology.PiecewiseLinear
