import DifferentialGeometry.Topology.Engulfing.Simplex.Columns.ColumnPolyhedron
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.PolyhedralMap

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

variable {E F ι : Type*} [DecidableEq E] [DecidableEq F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq E] [DecidableEq F] in
theorem exists_subdivision_column_preimage
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (w : E → F)
    (hw : ∀ s ∈ K.faces, AffineIndependent ℝ (fun x : s => w x))
    (s : SimplexSplit ι) (v : ι → F) (hv : AffineIndependent ℝ v)
    (T : SimplicialComplex ℝ F) (hT : T.faces.Finite)
    (hinside : T.space ⊆ convexHull ℝ (range v)) {d e : ℕ}
    (hd : ∀ t ∈ K.faces, t.card ≤ d + 1) (he : ∀ t ∈ T.faces, t.card ≤ e + 1) :
    ∃ (C : SimplicialComplex ℝ F) (L P : SimplicialComplex ℝ E),
      C.faces.Finite ∧ C.space = s.columnSaturation v hv T.space ∧
      (∀ t ∈ C.faces, t.card ≤ e + 2) ∧
      L.faces.Finite ∧ L.space = K.space ∧ simplicialRefines L K ∧
      (∀ t ∈ L.faces, t.card ≤ d + 1) ∧ P.faces.Finite ∧ P.faces ⊆ L.faces ∧
      P.space = Subtype.val '' (interpolateVertices K hK w ⁻¹' C.space) ∧
      (∀ t ∈ P.faces, t.card ≤ e + 2) := by
  classical
  obtain ⟨C, hC, hCspace, hCdim⟩ := s.exists_column_complex v hv T hT hinside he
  obtain ⟨L, P, hL, hLspace, hLref, hLdim, hP, hPL, hPspace, hPdim⟩ :=
    exists_subdivision_preimage_of_interpolate K hK w hw C hC hd hCdim
  exact ⟨C, L, P, hC, hCspace, hCdim, hL, hLspace, hLref, hLdim, hP, hPL,
    hPspace, hPdim⟩

end DifferentialGeometry.Topology.Engulfing
