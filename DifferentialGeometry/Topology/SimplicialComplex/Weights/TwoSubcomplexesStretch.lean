import DifferentialGeometry.Topology.SimplicialComplex.Weights.ProjectiveStretch
import DifferentialGeometry.Topology.SimplicialComplex.Weights.VertexCoordinates
import DifferentialGeometry.Topology.Homeomorph.CompactSupportExtension

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [DecidableEq E] in
theorem exists_stretch_cover_of_complementary_faces (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hconv : Convex ℝ K.space)
    (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 ≤ w v)
    (hboundary : ∀ v ∈ K.vertices, v ∈ frontier K.space → w v = 1)
    (I : Set (Finset E)) (hIK : I ⊆ K.faces)
    {R U V : Set E} (hR : IsCompact R) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : ∀ x ∈ R, ∃ s ∈ I, x ∈ convexHull ℝ (s : Set E))
    (hlow : ∀ s ∈ I, convexHull ℝ ((s.filter (fun v => w v ≠ 0) : Finset E) : Set E) ⊆ U)
    (hhigh : ∀ s ∈ I, convexHull ℝ ((s.filter (fun v => w v = 0) : Finset E) : Set E) ⊆ V) :
    ∃ H : E ≃ₜ E, (∀ x ∉ interior K.space, H x = x) ∧ R ⊆ H '' U ∪ V ∧
      (∀ s ∈ K.faces, H '' convexHull ℝ (s : Set E) = convexHull ℝ (s : Set E)) := by
  classical
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces K hK)
  let C : Set K.space := Subtype.val ⁻¹' (R \ V)
  have hC : IsCompact C :=
    ((hR.isClosed.inter hV.isClosed_compl).preimage continuous_subtype_val).isCompact
  have hpos : ∀ x ∈ C, 0 < interpolateVertices K hK w x := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := hcover x.1 hx.1
    have hn : interpolateVertices K hK w x ≠ 0 := by
      intro hz
      exact hx.2 (hhigh s hs (interpolation_zero_mem_face_filter K hK w hw x hz (hIK hs) hxs))
    exact lt_of_le_of_ne (interpolateVertices_nonneg K hK w hw x) (Ne.symm hn)
  have hlim : ∀ x ∈ C, (interpolateVertices K hK w x)⁻¹ •
      interpolateVertices K hK (fun v => w v • v) x ∈ U := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := hcover x.1 hx.1
    exact hlow s hs (normalized_interpolation_mem_face K hK w hw x (hpos x hx) (hIK hs) hxs)
  obtain ⟨H, hfix, hHC, hfaces⟩ :=
    exists_ambient_projective_stretch K hK hconv w hw hboundary hC hU hpos hlim
  refine ⟨H, hfix, ?_, hfaces⟩
  intro x hx
  by_cases hxV : x ∈ V
  · exact Or.inr hxV
  · obtain ⟨s, hs, hxs⟩ := hcover x hx
    let x' : K.space := ⟨x, K.convexHull_subset_space (hIK hs) hxs⟩
    exact Or.inl (hHC ⟨x', ⟨hx, hxV⟩, rfl⟩)

omit [DecidableEq E] in
theorem exists_stretch_cover_in_chart {M : Type*} [TopologicalSpace M] [T2Space M]
    {j : E → M} (hj : IsOpenEmbedding j)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hconv : Convex ℝ K.space)
    (w : E → ℝ) (hw : ∀ v ∈ K.vertices, 0 ≤ w v)
    (hboundary : ∀ v ∈ K.vertices, v ∈ frontier K.space → w v = 1)
    (I : Set (Finset E)) (hIK : I ⊆ K.faces)
    {R : Set E} {U V : Set M} (hR : IsCompact R) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : ∀ x ∈ R, ∃ s ∈ I, x ∈ convexHull ℝ (s : Set E))
    (hlow : ∀ s ∈ I, j '' convexHull ℝ ((s.filter (fun v => w v ≠ 0) : Finset E) : Set E) ⊆ U)
    (hhigh : ∀ s ∈ I, j '' convexHull ℝ ((s.filter (fun v => w v = 0) : Finset E) : Set E) ⊆ V) :
    ∃ H : M ≃ₜ M, (∀ x ∉ j '' interior K.space, H x = x) ∧
      j '' R ⊆ H '' U ∪ V ∧
      (∀ s ∈ K.faces, H '' (j '' convexHull ℝ (s : Set E)) = j '' convexHull ℝ (s : Set E)) := by
  classical
  obtain ⟨G, hfixG, hcoverG, hfaces⟩ := exists_stretch_cover_of_complementary_faces K hK hconv
    w hw hboundary I hIK hR (hU.preimage hj.continuous) (hV.preimage hj.continuous) hcover
    (fun s hs x hx => hlow s hs ⟨x, hx, rfl⟩)
    (fun s hs x hx => hhigh s hs ⟨x, hx, rfl⟩)
  obtain ⟨H, hH, hfixH, htransport⟩ := exists_homeomorph_extension_of_isOpenEmbedding hj G
    (isCompact_space_of_finite_faces K hK)
    (fun x hx => hfixG x (fun hi => hx (interior_subset hi)))
  refine ⟨H, ?_, ?_, fun s hs => by rw [htransport, hfaces s hs]⟩
  · intro x hx
    by_cases hxK : x ∈ j '' K.space
    · obtain ⟨y, hy, rfl⟩ := hxK
      rw [hH, hfixG y (fun hi => hx ⟨y, hi, rfl⟩)]
    · exact hfixH x hxK
  · rintro _ ⟨x, hx, rfl⟩
    rcases hcoverG hx with hleft | hright
    · obtain ⟨y, hy, heq⟩ := hleft
      exact Or.inl ⟨j y, hy, (hH y).trans (congrArg j heq)⟩
    · exact Or.inr hright

omit [DecidableEq E] [FiniteDimensional ℝ E] in
theorem subset_image_of_face_preserving {M : Type*} [TopologicalSpace M]
    (H : M ≃ₜ M) {j : E → M} (K : SimplicialComplex ℝ E) {U B : Set M}
    (hfix : ∀ x ∉ j '' K.space, H x = x)
    (hfaces : ∀ s ∈ K.faces,
      H '' (j '' convexHull ℝ (s : Set E)) = j '' convexHull ℝ (s : Set E))
    (hBU : B ⊆ U)
    (hlocal : ∀ x ∈ B, x ∈ j '' K.space →
      ∃ s ∈ K.faces, x ∈ j '' convexHull ℝ (s : Set E) ∧ j '' convexHull ℝ (s : Set E) ⊆ U) :
    B ⊆ H '' U := by
  intro x hx
  by_cases hxK : x ∈ j '' K.space
  · obtain ⟨s, hs, hxs, hsub⟩ := hlocal x hx hxK
    exact image_mono hsub ((hfaces s hs).symm ▸ hxs)
  · exact ⟨x, hBU hx, hfix x hxK⟩

end DifferentialGeometry.Topology.Engulfing
