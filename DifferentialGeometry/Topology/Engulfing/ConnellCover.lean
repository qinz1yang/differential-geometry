import DifferentialGeometry.Topology.SimplicialComplex.Weights.TwoSubcomplexesStretch
import DifferentialGeometry.Topology.SimplicialComplex.Weights.DualSkeleton
import DifferentialGeometry.Topology.Manifold.EuclideanCellCover
import Mathlib.Topology.MetricSpace.Thickening

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

def facesMeeting (K : SimplicialComplex ℝ E) (A : Set E) : Set (Finset E) :=
  {s | s ∈ K.faces ∧ (convexHull ℝ (s : Set E) ∩ A).Nonempty}

def faceNeighborhood (K : SimplicialComplex ℝ E) (A : Set E) : Set E :=
  ⋃ s ∈ facesMeeting K A, convexHull ℝ (s : Set E)

omit [DecidableEq E] in
theorem isCompact_faceNeighborhood (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (A : Set E) : IsCompact (faceNeighborhood K A) := by
  classical
  exact (hK.subset (fun _ h => h.1 : facesMeeting K A ⊆ K.faces)).isCompact_biUnion
    (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)

omit [DecidableEq E] in
theorem convexHull_subset_faceNeighborhood (K : SimplicialComplex ℝ E) (A : Set E)
    {s : Finset E} (hs : s ∈ facesMeeting K A) :
    convexHull ℝ (s : Set E) ⊆ faceNeighborhood K A := by
  classical
  exact fun _ hx => mem_iUnion₂.mpr ⟨s, hs, hx⟩

omit [DecidableEq E] in
theorem subset_faceNeighborhood (K : SimplicialComplex ℝ E) (A : Set E) :
    A ∩ K.space ⊆ faceNeighborhood K A := by
  classical
  rintro x ⟨hxA, hxK⟩
  obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hxK
  exact convexHull_subset_faceNeighborhood K A ⟨hs, x, hxs, hxA⟩ hxs

def chartProtectedCore {M : Type*} (K : SimplicialComplex ℝ E) (j : E → M) (B : Set M) : Set M :=
  B ∪ j '' faceNeighborhood K (j ⁻¹' B)

omit [DecidableEq E] in
theorem isCompact_chartProtectedCore {M : Type*} [TopologicalSpace M]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) {j : E → M} (hj : Continuous j)
    {B : Set M} (hB : IsCompact B) : IsCompact (chartProtectedCore K j B) := by
  classical
  exact hB.union ((isCompact_faceNeighborhood K hK _).image hj)

omit [DecidableEq E] in
theorem chartProtectedCore_subset {M : Type*} (K : SimplicialComplex ℝ E) (j : E → M)
    {B U : Set M} (hBU : B ⊆ U)
    (hfaces : ∀ s ∈ facesMeeting K (j ⁻¹' B), j '' convexHull ℝ (s : Set E) ⊆ U) :
    chartProtectedCore K j B ⊆ U := by
  classical
  rintro x (hx | ⟨y, hy, rfl⟩)
  · exact hBU hx
  · obtain ⟨s, hs, hys⟩ := mem_iUnion₂.mp hy
    exact hfaces s hs ⟨y, hys, rfl⟩

omit [DecidableEq E] in
theorem chartProtectedCore_contains_face {M : Type*} (K : SimplicialComplex ℝ E)
    (j : E → M) {B : Set M} {x : M} (hx : x ∈ B) (hxK : x ∈ j '' K.space) :
    ∃ s ∈ K.faces, x ∈ j '' convexHull ℝ (s : Set E) ∧
      j '' convexHull ℝ (s : Set E) ⊆ chartProtectedCore K j B := by
  classical
  obtain ⟨y, hy, rfl⟩ := hxK
  obtain ⟨s, hs, hys⟩ := SimplicialComplex.mem_space_iff.mp hy
  refine ⟨s, hs, ⟨y, hys, rfl⟩, ?_⟩
  exact (image_mono (convexHull_subset_faceNeighborhood K (j ⁻¹' B)
    ⟨hs, y, hys, hx⟩)).trans subset_union_right

omit [DecidableEq E] in
theorem convexHull_filter_subset_vertexRestriction (K : SimplicialComplex ℝ E)
    (S : Set E) [DecidablePred (fun x => x ∈ S)] {s : Finset E} (hs : s ∈ K.faces) :
    convexHull ℝ ((s.filter (fun x => x ∈ S) : Finset E) : Set E) ⊆
      (vertexRestriction K S).space := by
  classical
  by_cases hne : (s.filter (fun x => x ∈ S)).Nonempty
  · exact (vertexRestriction K S).convexHull_subset_space
      ⟨K.down_closed hs (Finset.filter_subset _ _) hne,
        fun _ hv => (Finset.mem_filter.mp hv).2⟩
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hempty]

omit [DecidableEq E] in
theorem facesMeeting_control_refines {K L : SimplicialComplex ℝ E}
    (href : simplicialRefines L K) {A U : Set E}
    (hcontrol : ∀ s ∈ facesMeeting K A, convexHull ℝ (s : Set E) ⊆ U) :
    ∀ s ∈ facesMeeting L A, convexHull ℝ (s : Set E) ⊆ U := by
  classical
  intro s hs
  obtain ⟨t, ht, hst⟩ := href s hs.1
  obtain ⟨x, hxs, hxA⟩ := hs.2
  exact hst.trans (hcontrol t ⟨ht, x, hst hxs, hxA⟩)

omit [DecidableEq E] in
theorem exists_subdivision_controlling_face_neighborhood (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {A U : Set E} (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧
      ∀ s ∈ facesMeeting L A, convexHull ℝ (s : Set E) ⊆ U := by
  classical
  obtain ⟨δ, hδ, hδU⟩ := hA.exists_thickening_subset_open hU hAU
  obtain ⟨L, hL, hspace, href, hmesh, -⟩ := exists_fine_subdivision K hK hδ
  refine ⟨L, hL, hspace, href, ?_⟩
  intro s hs x hx
  obtain ⟨a, has, haA⟩ := hs.2
  apply hδU
  apply mem_thickening_iff.mpr
  exact ⟨a, haA, (dist_le_diam_of_mem (s.finite_toSet.isCompact_convexHull ℝ).isBounded
    hx has).trans_lt (hmesh s hs.1)⟩

theorem exists_connell_chart_preparation {M : Type*} [TopologicalSpace M] [T2Space M]
    {j : E → M} (hj : IsOpenEmbedding j)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {R : Set E} {B₁ B₂ U₀ V₀ : Set M}
    (hR : IsCompact R) (hRK : R ⊆ interior K.space)
    (hB₁ : IsCompact B₁) (hB₂ : IsCompact B₂)
    (hU₀ : IsOpen U₀) (hV₀ : IsOpen V₀) (hB₁U : B₁ ⊆ U₀) (hB₂V : B₂ ⊆ V₀) :
    ∃ D : SimplicialComplex ℝ E, D.faces.Finite ∧ D.space = K.space ∧
      simplicialRefines D K ∧
      (∀ s ∈ facesMeeting (barycentricSubdivision D) R,
        convexHull ℝ (s : Set E) ⊆ interior D.space) ∧
      IsCompact (chartProtectedCore (barycentricSubdivision D) j B₁) ∧
      IsCompact (chartProtectedCore (barycentricSubdivision D) j B₂) ∧
      chartProtectedCore (barycentricSubdivision D) j B₁ ⊆ U₀ ∧
      chartProtectedCore (barycentricSubdivision D) j B₂ ⊆ V₀ := by
  let A₁ := K.space ∩ j ⁻¹' B₁
  let A₂ := K.space ∩ j ⁻¹' B₂
  have hcompact : IsCompact K.space := isCompact_space_of_finite_faces K hK
  have hA₁ : IsCompact A₁ := hcompact.inter_right (hB₁.isClosed.preimage hj.continuous)
  have hA₂ : IsCompact A₂ := hcompact.inter_right (hB₂.isClosed.preimage hj.continuous)
  obtain ⟨K₁, hK₁, hspace₁, href₁, hnearR⟩ :=
    exists_subdivision_controlling_face_neighborhood K hK hR isOpen_interior hRK
  obtain ⟨K₂, hK₂, hspace₂, href₂, hnear₁⟩ :=
    exists_subdivision_controlling_face_neighborhood K₁ hK₁ hA₁
      (hU₀.preimage hj.continuous) (fun _ hx => hB₁U hx.2)
  obtain ⟨D, hD, hspace₃, href₃, hnear₂⟩ :=
    exists_subdivision_controlling_face_neighborhood K₂ hK₂ hA₂
      (hV₀.preimage hj.continuous) (fun _ hx => hB₂V hx.2)
  have hspace : D.space = K.space := hspace₃.trans (hspace₂.trans hspace₁)
  let L := barycentricSubdivision D
  have hL : L.faces.Finite := barycentricSubdivision_finite_faces D hD
  have hLspace : L.space = K.space := (barycentricSubdivision_space D).trans hspace
  have hnearR' := facesMeeting_control_refines
    ((barycentricSubdivision_refines D).trans (href₃.trans href₂)) hnearR
  have hnear₁' := facesMeeting_control_refines
    ((barycentricSubdivision_refines D).trans href₃) hnear₁
  have hnear₂' := facesMeeting_control_refines (barycentricSubdivision_refines D) hnear₂
  refine ⟨D, hD, hspace, href₃.trans (href₂.trans href₁), ?_,
    isCompact_chartProtectedCore L hL hj.continuous hB₁,
    isCompact_chartProtectedCore L hL hj.continuous hB₂, ?_, ?_⟩
  · simpa only [hspace] using hnearR'
  · apply chartProtectedCore_subset L j hB₁U
    intro s hs
    obtain ⟨x, hxs, hxB⟩ := hs.2
    have hxK : x ∈ K.space := hLspace ▸ L.convexHull_subset_space hs.1 hxs
    exact fun y hy => by
      obtain ⟨z, hz, rfl⟩ := hy
      exact hnear₁' s ⟨hs.1, x, hxs, hxK, hxB⟩ hz
  · apply chartProtectedCore_subset L j hB₂V
    intro s hs
    obtain ⟨x, hxs, hxB⟩ := hs.2
    have hxK : x ∈ K.space := hLspace ▸ L.convexHull_subset_space hs.1 hxs
    exact fun y hy => by
      obtain ⟨z, hz, rfl⟩ := hy
      exact hnear₂' s ⟨hs.1, x, hxs, hxK, hxB⟩ hz

noncomputable def connellWeights (K : SimplicialComplex ℝ E) (C : Set E) (v : E) : ℝ := by
  classical
  exact if v ∈ frontier K.space ∨ v ∈ C then 1 else 0

omit [DecidableEq E] in
theorem connellWeights_nonneg (K : SimplicialComplex ℝ E) (C : Set E) (v : E) :
    0 ≤ connellWeights K C v := by
  classical
  simp only [connellWeights]
  split_ifs <;> norm_num

omit [DecidableEq E] in
theorem connellWeights_boundary (K : SimplicialComplex ℝ E) (C : Set E) {v : E}
    (hv : v ∈ frontier K.space) : connellWeights K C v = 1 := by
  classical
  simp [connellWeights, hv]

omit [DecidableEq E] in
theorem connellWeights_filters (K : SimplicialComplex ℝ E) (C : Set E)
    [DecidablePred (fun v => v ∈ C)]
    {s : Finset E} (hinside : convexHull ℝ (s : Set E) ⊆ interior K.space) :
    s.filter (fun v => connellWeights K C v ≠ 0) = s.filter (fun v => v ∈ C) ∧
      s.filter (fun v => connellWeights K C v = 0) = s.filter (fun v => v ∈ Cᶜ) := by
  classical
  have hn (v : E) (hv : v ∈ s) : v ∉ frontier K.space :=
    (mem_interior_iff_notMem_frontier (interior_subset (hinside (subset_convexHull ℝ _ hv)))).mp
      (hinside (subset_convexHull ℝ _ hv))
  constructor <;> apply Finset.filter_congr <;> intro v hv <;>
    simp [connellWeights, hn v hv]

omit [DecidableEq E] in
theorem exists_connell_stretch_of_vertex_colors {M : Type*} [TopologicalSpace M] [T2Space M]
    {j : E → M} (hj : IsOpenEmbedding j)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hconv : Convex ℝ K.space)
    (C : Set E) {R : Set E} {U V : Set M}
    (hR : IsCompact R) (hRK : R ⊆ K.space) (hU : IsOpen U) (hV : IsOpen V)
    (hinterior : ∀ s ∈ facesMeeting K R, convexHull ℝ (s : Set E) ⊆ interior K.space)
    (hlow : j '' (vertexRestriction K C).space ⊆ U)
    (hhigh : j '' (vertexRestriction K Cᶜ).space ⊆ V) :
    ∃ H : M ≃ₜ M, (∀ x ∉ j '' interior K.space, H x = x) ∧
      j '' R ⊆ H '' U ∪ V ∧
      ∀ s ∈ K.faces, H '' (j '' convexHull ℝ (s : Set E)) =
        j '' convexHull ℝ (s : Set E) := by
  classical
  apply exists_stretch_cover_in_chart hj K hK hconv (connellWeights K C)
    (fun v _ => connellWeights_nonneg K C v)
    (fun _ _ hv => connellWeights_boundary K C hv)
    (facesMeeting K R) (fun _ hs => hs.1) hR hU hV
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp (hRK hx)
    exact ⟨s, ⟨hs, x, hxs, hx⟩, hxs⟩
  · intro s hs
    rw [(connellWeights_filters K C (hinterior s hs)).1]
    exact (image_mono (convexHull_filter_subset_vertexRestriction K C hs.1)).trans hlow
  · intro s hs
    rw [(connellWeights_filters K C (hinterior s hs)).2]
    exact (image_mono (convexHull_filter_subset_vertexRestriction K Cᶜ hs.1)).trans hhigh

theorem exists_connell_stretch_of_skeleta {M : Type*} [TopologicalSpace M] [T2Space M]
    {j : E → M} (hj : IsOpenEmbedding j)
    (D : SimplicialComplex ℝ E) (hD : D.faces.Finite) (hconv : Convex ℝ D.space) (r : ℕ)
    {R : Set E} {U V : Set M} (hR : IsCompact R) (hRD : R ⊆ D.space)
    (hU : IsOpen U) (hV : IsOpen V)
    (hinterior : ∀ s ∈ facesMeeting (barycentricSubdivision D) R,
      convexHull ℝ (s : Set E) ⊆ interior D.space)
    (hlow : j '' (skeleton D r).space ⊆ U)
    (hhigh : j '' (vertexRestriction (barycentricSubdivision D) (lowCentroids D r)ᶜ).space ⊆ V) :
    ∃ H : M ≃ₜ M, (∀ x ∉ j '' interior D.space, H x = x) ∧
      j '' R ⊆ H '' U ∪ V ∧
      ∀ s ∈ (barycentricSubdivision D).faces,
        H '' (j '' convexHull ℝ (s : Set E)) = j '' convexHull ℝ (s : Set E) := by
  have hspace := barycentricSubdivision_space D
  have hconv' : Convex ℝ (barycentricSubdivision D).space := hspace ▸ hconv
  have hR' : R ⊆ (barycentricSubdivision D).space := hspace ▸ hRD
  obtain ⟨H, hfix, hcover, hfaces⟩ := exists_connell_stretch_of_vertex_colors hj
    (barycentricSubdivision D) (barycentricSubdivision_finite_faces D hD) hconv'
    (lowCentroids D r) hR hR' hU hV (by simpa only [hspace] using hinterior)
    (by simpa only [vertexRestriction_lowCentroids_space] using hlow) hhigh
  exact ⟨H, by simpa only [hspace] using hfix, hcover, hfaces⟩

omit [DecidableEq E] in
theorem exists_connell_cover_three_cores {M : Type*} [TopologicalSpace M] [T2Space M]
    {j : E → M} (hj : IsOpenEmbedding j)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hconv : Convex ℝ K.space)
    (C : Set E) {R : Set E} {B₁ B₂ U V : Set M}
    (hR : IsCompact R) (hRK : R ⊆ K.space) (hU : IsOpen U) (hV : IsOpen V)
    (hinterior : ∀ s ∈ facesMeeting K R, convexHull ℝ (s : Set E) ⊆ interior K.space)
    (hprotect₁ : chartProtectedCore K j B₁ ⊆ U)
    (hprotect₂ : chartProtectedCore K j B₂ ⊆ V)
    (hlow : j '' (vertexRestriction K C).space ⊆ U)
    (hhigh : j '' (vertexRestriction K Cᶜ).space ⊆ V) :
    ∃ H : M ≃ₜ M, (∀ x ∉ j '' interior K.space, H x = x) ∧
      B₁ ⊆ H '' U ∧ B₂ ⊆ V ∧ B₁ ∪ B₂ ∪ j '' R ⊆ H '' U ∪ V := by
  classical
  obtain ⟨H, hfix, hcover, hfaces⟩ := exists_connell_stretch_of_vertex_colors hj K hK hconv
    C hR hRK hU hV hinterior hlow hhigh
  have hB₁ : B₁ ⊆ H '' U := subset_image_of_face_preserving H K
    (fun x hx => hfix x (fun hi => hx (image_mono interior_subset hi))) hfaces
    (fun _ hx => hprotect₁ (Or.inl hx)) (by
      intro x hx hxK
      obtain ⟨s, hs, hxs, hsp⟩ := chartProtectedCore_contains_face K j hx hxK
      exact ⟨s, hs, hxs, hsp.trans hprotect₁⟩)
  have hB₂ : B₂ ⊆ V := fun _ hx => hprotect₂ (Or.inl hx)
  refine ⟨H, hfix, hB₁, hB₂, ?_⟩
  rintro x ((hx | hx) | hx)
  · exact Or.inl (hB₁ hx)
  · exact Or.inr (hB₂ hx)
  · exact hcover hx

omit [DecidableEq E] in
theorem exists_two_open_cells_cover_three_cores {M : Type*} [TopologicalSpace M] [T2Space M]
    {j : E → M} (hj : IsOpenEmbedding j)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hconv : Convex ℝ K.space)
    (C : Set E) {R : Set E} {B₁ B₂ : Set M}
    (hR : IsCompact R) (hRK : R ⊆ K.space)
    (hinterior : ∀ s ∈ facesMeeting K R, convexHull ℝ (s : Set E) ⊆ interior K.space)
    (hengulf : ∃ u v : E → M, IsOpenEmbedding u ∧ IsOpenEmbedding v ∧
      chartProtectedCore K j B₁ ⊆ range u ∧ chartProtectedCore K j B₂ ⊆ range v ∧
      j '' (vertexRestriction K C).space ⊆ range u ∧
      j '' (vertexRestriction K Cᶜ).space ⊆ range v) :
    ∃ u v : E → M, IsOpenEmbedding u ∧ IsOpenEmbedding v ∧
      B₁ ⊆ range u ∧ B₂ ⊆ range v ∧ B₁ ∪ B₂ ∪ j '' R ⊆ range u ∪ range v := by
  classical
  obtain ⟨u, v, hu, hv, hp₁, hp₂, hlow, hhigh⟩ := hengulf
  obtain ⟨H, -, hB₁, hB₂, hcover⟩ := exists_connell_cover_three_cores hj K hK hconv C
    hR hRK hu.isOpen_range hv.isOpen_range hinterior hp₁ hp₂ hlow hhigh
  refine ⟨H ∘ u, v, H.isOpenEmbedding.comp hu, hv, ?_, hB₂, ?_⟩
  · simpa only [range_comp] using hB₁
  · simpa only [range_comp] using hcover

theorem exists_two_open_cells_cover_three_cores_of_skeleta
    {M : Type*} [TopologicalSpace M] [T2Space M]
    {j : E → M} (hj : IsOpenEmbedding j)
    (D : SimplicialComplex ℝ E) (hD : D.faces.Finite) (hconv : Convex ℝ D.space) (r : ℕ)
    {R : Set E} {B₁ B₂ : Set M} (hR : IsCompact R) (hRD : R ⊆ D.space)
    (hinterior : ∀ s ∈ facesMeeting (barycentricSubdivision D) R,
      convexHull ℝ (s : Set E) ⊆ interior D.space)
    (hengulf : ∃ u v : E → M, IsOpenEmbedding u ∧ IsOpenEmbedding v ∧
      chartProtectedCore (barycentricSubdivision D) j B₁ ⊆ range u ∧
      chartProtectedCore (barycentricSubdivision D) j B₂ ⊆ range v ∧
      j '' (skeleton D r).space ⊆ range u ∧
      j '' (vertexRestriction (barycentricSubdivision D) (lowCentroids D r)ᶜ).space ⊆
        range v) :
    ∃ u v : E → M, IsOpenEmbedding u ∧ IsOpenEmbedding v ∧
      B₁ ⊆ range u ∧ B₂ ⊆ range v ∧ B₁ ∪ B₂ ∪ j '' R ⊆ range u ∪ range v := by
  have hspace := barycentricSubdivision_space D
  apply exists_two_open_cells_cover_three_cores hj
    (barycentricSubdivision D) (barycentricSubdivision_finite_faces D hD)
    (hspace ▸ hconv) (lowCentroids D r) hR (hspace ▸ hRD)
    (by simpa only [hspace] using hinterior)
  simpa only [vertexRestriction_lowCentroids_space] using hengulf

theorem exists_compact_pair_subsets_of_open_cover {X : Type*}
    [TopologicalSpace X] [T2Space X] [NormalSpace X]
    {T U V : Set X} (hT : IsCompact T) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : T ⊆ U ∪ V) :
    ∃ A B, IsCompact A ∧ IsCompact B ∧ A ⊆ U ∧ B ⊆ V ∧ T ⊆ A ∪ B := by
  have hC : IsCompact (T \ V) := hT.diff hV
  have hCU : T \ V ⊆ U := by
    intro x hx
    exact (hcover hx.1).resolve_right hx.2
  obtain ⟨O, hO, hCO, hOU⟩ := normal_exists_closure_subset hC.isClosed hU hCU
  refine ⟨T ∩ closure O, T ∩ Oᶜ, hT.inter_right isClosed_closure,
    hT.inter_right hO.isClosed_compl, fun _ hx => hOU hx.2, ?_, ?_⟩
  · intro x hx
    by_contra hxV
    exact hx.2 (hCO ⟨hx.1, hxV⟩)
  · intro x hx
    by_cases hxO : x ∈ O
    · exact Or.inl ⟨hx, subset_closure hxO⟩
    · exact Or.inr ⟨hx, hxO⟩

theorem exists_pair_cover_of_finite_compact_core_cover {X ι : Type*}
    [TopologicalSpace X] [T2Space X] [NormalSpace X] [Finite ι]
    (P : Set X → Prop) (hopen : ∀ U, P U → IsOpen U) (hne : ∃ U, P U)
    (hmerge : ∀ A B C U V W, IsCompact A → IsCompact B → IsCompact C →
      P U → P V → P W → A ⊆ U → B ⊆ V → C ⊆ W →
      ∃ U' V', P U' ∧ P V' ∧ A ∪ B ∪ C ⊆ U' ∪ V')
    (A U : ι → Set X) (hA : ∀ i, IsCompact (A i)) (hU : ∀ i, P (U i))
    (hAU : ∀ i, A i ⊆ U i) (hcover : (⋃ i, A i) = univ) :
    ∃ U' V', P U' ∧ P V' ∧ U' ∪ V' = univ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hfinite (s : Finset ι) :
      ∃ V W, P V ∧ P W ∧ (⋃ i ∈ s, A i) ⊆ V ∪ W := by
    induction s using Finset.induction_on with
    | empty =>
        obtain ⟨V, hV⟩ := hne
        exact ⟨V, V, hV, hV, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨V, W, hV, hW, hs⟩ := ih
        have hT : IsCompact (⋃ j ∈ s, A j) :=
          s.finite_toSet.isCompact_biUnion (fun j _ => hA j)
        obtain ⟨B, C, hB, hC, hBV, hCW, hBC⟩ :=
          exists_compact_pair_subsets_of_open_cover hT (hopen V hV) (hopen W hW) hs
        obtain ⟨V', W', hV', hW', hnew⟩ :=
          hmerge (A i) B C (U i) V W (hA i) hB hC (hU i) hV hW (hAU i) hBV hCW
        refine ⟨V', W', hV', hW', ?_⟩
        intro x hx
        obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hnew (Or.inl (Or.inl hxj))
        · rcases hBC (mem_iUnion₂.mpr ⟨j, hj, hxj⟩) with hxB | hxC
          · exact hnew (Or.inl (Or.inr hxB))
          · exact hnew (Or.inr hxC)
  obtain ⟨V, W, hV, hW, hVW⟩ := hfinite Finset.univ
  refine ⟨V, W, hV, hW, eq_univ_of_univ_subset ?_⟩
  simpa only [Finset.mem_univ, iUnion_true, hcover] using hVW

theorem exists_two_open_cells_of_compact_three_core_reduction {n : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (hmerge : ∀ (A B C : Set M) (u v w : EuclideanSpace ℝ (Fin n) → M),
      IsCompact A → IsCompact B → IsCompact C →
      IsOpenEmbedding u → IsOpenEmbedding v → IsOpenEmbedding w →
      A ⊆ range u → B ⊆ range v → C ⊆ range w →
      ∃ u' v' : EuclideanSpace ℝ (Fin n) → M,
        IsOpenEmbedding u' ∧ IsOpenEmbedding v' ∧ A ∪ B ∪ C ⊆ range u' ∪ range v') :
    ∃ u v : EuclideanSpace ℝ (Fin n) → M,
      IsOpenEmbedding u ∧ IsOpenEmbedding v ∧ range u ∪ range v = univ := by
  classical
  let P : Set M → Prop := fun U =>
    ∃ u : EuclideanSpace ℝ (Fin n) → M, IsOpenEmbedding u ∧ range u = U
  have hopen : ∀ U, P U → IsOpen U := by
    rintro U ⟨u, hu, rfl⟩
    exact hu.isOpen_range
  have hne : ∃ U, P U := by
    obtain ⟨u, hu, -⟩ := exists_openEmbedding_euclidean_at
      (n := n) (Classical.arbitrary M)
    exact ⟨range u, u, hu, rfl⟩
  obtain ⟨k, φ, hφ, hcover, hcompact⟩ :=
    exists_finite_euclidean_cell_cover (n := n) (M := M)
  have hcover' : (⋃ i, φ i '' closedBall 0 1) = univ := by
    apply eq_univ_of_univ_subset
    rw [← hcover]
    exact iUnion_mono fun i => image_mono
      ((ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans ball_subset_closedBall)
  obtain ⟨U, V, hU, hV, hUV⟩ := exists_pair_cover_of_finite_compact_core_cover P hopen hne
    (by
      rintro A B C U V W hA hB hC ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩ hAu hBv hCw
      obtain ⟨u', v', hu', hv', hcov⟩ := hmerge A B C u v w hA hB hC hu hv hw hAu hBv hCw
      exact ⟨range u', range v', ⟨u', hu', rfl⟩, ⟨v', hv', rfl⟩, hcov⟩)
    (fun i => φ i '' closedBall 0 1) (fun i => range (φ i)) hcompact
    (fun i => ⟨φ i, hφ i, rfl⟩) (fun _ => image_subset_range _ _) hcover'
  obtain ⟨u, hu, rfl⟩ := hU
  obtain ⟨v, hv, rfl⟩ := hV
  exact ⟨u, v, hu, hv, hUV⟩

end DifferentialGeometry.Topology.Engulfing
