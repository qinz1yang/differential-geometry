import DifferentialGeometry.Topology.PiecewiseLinear.PreimageBoundary
import Mathlib.Topology.MetricSpace.Thickening

open Set Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem even_ncard_boundary_preimage_of_transverse_subcomplex
    (K B : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ F)
    [Finite K.faces] [Finite L.faces] (hBK : B.faces ⊆ K.faces) (φ : E → F) {m n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (m + 1) K)
    (hL : IsCombinatorialManifold (n + 1) L) (hdim : Module.finrank ℝ F = m + n + 1)
    (hB : ∀ s ∈ B.faces, AffineIndependent ℝ (fun v : s => φ v) ∧
      ∀ t ∈ L.faces,
        (convexHull ℝ (s.image φ : Set F) ∩ convexHull ℝ (t : Set F)).Nonempty →
          vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t : Set F) = ⊤)
    (hout : ∀ s ∈ (boundaryComplex (m + 1) K).faces, s ∉ B.faces →
      MapsTo (simplicialMap K φ) (convexHull ℝ (s : Set E)) L.spaceᶜ) :
    Even ((boundaryComplex (m + 1) K).space ∩ simplicialMap K φ ⁻¹' L.space).ncard := by
  let J := (boundaryComplex (m + 1) K).faces \ B.faces
  let Q := ⋃ s ∈ J, convexHull ℝ (s : Set E)
  have hJ : J.Finite := (Set.toFinite K.faces).subset fun s hs =>
    boundaryComplex_faces_subset (m + 1) K hs.1
  have hQ : IsCompact Q := hJ.isCompact_biUnion fun s _ => s.finite_toSet.isCompact_convexHull ℝ
  have hQK : Q ⊆ K.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    exact K.convexHull_subset_space (boundaryComplex_faces_subset (m + 1) K hs.1) hxs
  have hQout : MapsTo (simplicialMap K φ) Q L.spaceᶜ := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    exact hout s hs.1 hs.2 hxs
  have himage : IsCompact (simplicialMap K φ '' Q) :=
    hQ.image_of_continuousOn ((isPiecewiseAffineOn_simplicialMap K φ).continuousOn.mono hQK)
  obtain ⟨ε, hε, hthick⟩ := himage.exists_thickening_subset_open
    (isPolyhedron_space L).isClosed.isOpen_compl hQout.image_subset
  obtain ⟨R, ψ, G, hR, hfinite, _, _, hclose, hfix, hgood, _⟩ :=
    exists_small_simplicialMap_preimage_manifold_relative K B L hBK hK hL hdim φ hB hε
  let _ : Finite R.faces := hfinite.to_subtype
  have hnewout : MapsTo (simplicialMap R ψ) Q L.spaceᶜ := by
    intro x hx
    exact hthick (mem_thickening_iff.mpr ⟨simplicialMap K φ x, ⟨x, hx, rfl⟩,
      hclose x (hQK hx)⟩)
  have hcover : ∀ x ∈ (boundaryComplex (m + 1) K).space, x ∈ B.space ∨ x ∈ Q := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := (boundaryComplex (m + 1) K).mem_space_iff.mp hx
    by_cases hsB : s ∈ B.faces
    · exact Or.inl (B.convexHull_subset_space hsB hxs)
    · exact Or.inr (mem_iUnion₂.mpr ⟨s, ⟨hs, hsB⟩, hxs⟩)
  have heq : (boundaryComplex (m + 1) K).space ∩ simplicialMap R ψ ⁻¹' L.space =
      (boundaryComplex (m + 1) K).space ∩ simplicialMap K φ ⁻¹' L.space := by
    ext x
    constructor
    · rintro ⟨hx, hxL⟩
      rcases hcover x hx with hxB | hxQ
      · exact ⟨hx, by simpa only [mem_preimage, hfix hxB] using hxL⟩
      · exact (hnewout hxQ hxL).elim
    · rintro ⟨hx, hxL⟩
      rcases hcover x hx with hxB | hxQ
      · exact ⟨hx, by simpa only [mem_preimage, hfix hxB] using hxL⟩
      · exact (hQout hxQ hxL).elim
  have heven := even_ncard_boundary_preimage_of_transverse_faces R L ψ
    (hK.of_isSubdivision hR) hL hdim (fun s hs => (hgood s hs).1)
    (fun s hs => (hgood s hs).2.2)
  rwa [boundaryComplex_space_of_isSubdivision K R hK hR, heq] at heven

end DifferentialGeometry.Topology.PiecewiseLinear
