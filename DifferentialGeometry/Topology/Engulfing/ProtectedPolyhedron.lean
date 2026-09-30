import DifferentialGeometry.Topology.SimplicialComplex.Subcomplex.SubcomplexNeighborhood
import DifferentialGeometry.Topology.Engulfing.Newman.Induction.NewmanProblem
import DifferentialGeometry.Topology.Homeomorph.CompactSupportExtension
import Mathlib.Geometry.Manifold.HasGroupoid

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

variable {E M : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M]

omit [DecidableEq E] in
theorem exists_polyhedral_target_away_from_closed_core
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) {p : ℕ}
    (hdim : ∀ s ∈ K.faces, s.card ≤ p + 1) {j : E → M} (hj : Continuous j)
    {C U : Set M} (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ (D : SimplicialComplex ℝ E) (B : Set M),
      D.faces.Finite ∧ (∀ s ∈ D.faces, s.card ≤ p + 1) ∧
      D.space ⊆ K.space ∧ simplicialRefines D K ∧
      Disjoint (j '' D.space) C ∧ IsCompact B ∧ B ⊆ U ∧
      B ⊆ j '' K.space ∧ j '' K.space ⊆ B ∪ j '' D.space := by
  classical
  let A := K.space ∩ j ⁻¹' Uᶜ
  have hA : IsCompact A :=
    (isCompact_space_of_finite_faces K hK).inter_right (hU.isClosed_compl.preimage hj)
  have hAW : A ⊆ j ⁻¹' Cᶜ := by
    intro x hx hxC
    exact hx.2 (hCU hxC)
  obtain ⟨P, J, D, hP, hPspace, hPref, hPdim, _, _, _, _, hD, hDP, hDW, _, hinterior⟩ :=
    exists_subcomplex_neighborhood_preserving K ⊥ hK (empty_subset _)
      hA inter_subset_left (hC.isOpen_compl.preimage hj) hAW hdim
  let : CompactSpace P.space :=
    isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces P hP)
  let Z : Set P.space := (interior (Subtype.val ⁻¹' D.space))ᶜ
  let B : Set M := (fun x : P.space => j x.1) '' Z
  have hDK : D.space ⊆ K.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    rw [← hPspace]
    exact P.convexHull_subset_space (hDP hs) hxs
  refine ⟨D, B, hD, fun s hs => hPdim s (hDP hs), hDK, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact hPref s (hDP hs)
  · exact disjoint_left.mpr (by rintro y ⟨x, hx, rfl⟩ hyC; exact hDW hx hyC)
  · exact isOpen_interior.isClosed_compl.isCompact.image (hj.comp continuous_subtype_val)
  · rintro y ⟨x, hx, rfl⟩
    by_contra hxU
    apply hx
    exact hinterior ⟨hPspace ▸ x.2, hxU⟩
  · rintro y ⟨x, _, rfl⟩
    exact ⟨x.1, hPspace ▸ x.2, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    have hxP : x ∈ P.space := hPspace.symm ▸ hx
    by_cases hxD : (⟨x, hxP⟩ : P.space) ∈ interior (Subtype.val ⁻¹' D.space)
    · exact Or.inr ⟨x, (show (⟨x, hxP⟩ : P.space) ∈ Subtype.val ⁻¹' D.space from
        interior_subset hxD), rfl⟩
    · exact Or.inl ⟨⟨x, hxP⟩, hxD, rfl⟩

theorem exists_protected_engulfing_of_complement [T2Space M]
    {C U Y : Set M} (hC : IsClosed C) (hCU : C ⊆ U)
    (e : (Cᶜ : Set M) ≃ₜ (Cᶜ : Set M))
    (he : IsCompact (closure {x | e x ≠ x}))
    (hcover : (Subtype.val ⁻¹' Y : Set (Cᶜ : Set M)) ⊆ e '' (Subtype.val ⁻¹' U)) :
    ∃ H : M ≃ₜ M, (∀ x ∈ C, H x = x) ∧ Y ⊆ H '' U ∧
      IsCompact (closure {x | H x ≠ x}) := by
  obtain ⟨H, hH, hfix, _⟩ := exists_homeomorph_extension_of_compact_moved_closure
    hC.isOpen_compl.isOpenEmbedding_subtypeVal e he
  have hfixC : ∀ x ∈ C, H x = x := by
    intro x hx
    apply hfix
    rintro ⟨y, _, hy⟩
    exact y.2 (hy ▸ hx)
  refine ⟨H, hfixC, ?_, ?_⟩
  · intro x hx
    by_cases hxC : x ∈ C
    · exact ⟨x, hCU hxC, hfixC x hxC⟩
    · obtain ⟨y, hy, hye⟩ := hcover (show (⟨x, hxC⟩ : (Cᶜ : Set M)) ∈
          Subtype.val ⁻¹' Y from hx)
      exact ⟨y.1, hy, (hH y).trans (congrArg Subtype.val hye)⟩
  · have hcompact := he.image (continuous_subtype_val : Continuous (Subtype.val : (Cᶜ : Set M) → M))
    apply hcompact.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hcompact.isClosed
    intro x hx
    by_contra hnot
    exact hx (hfix x hnot)

section MetricManifold

variable {M : Type*} [MetricSpace M] {n p : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem exists_protected_chart_polyhedron_engulfing
    {C U : Set M} (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hcodim : p + 3 ≤ n)
    (hconn : NewmanConnectivity (Cᶜ : Set M) (Subtype.val ⁻¹' U) p)
    (hnewman : relativeNewmanAt (Cᶜ : Set M) n p (p + 1))
    (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (hK : K.faces.Finite)
    (hdim : ∀ s ∈ K.faces, s.card ≤ p + 1)
    {j : EuclideanSpace ℝ (Fin n) → M} (hj : IsOpenEmbedding j) :
    ∃ H : M ≃ₜ M, (∀ x ∈ C, H x = x) ∧ j '' K.space ⊆ H '' U ∧
      IsCompact (closure {x | H x ≠ x}) := by
  classical
  obtain ⟨D, B, hD, hDdim, _, _, havoid, hB, hBU, hBK, hcover⟩ :=
    exists_polyhedral_target_away_from_closed_core K hK hdim hj.continuous hC hU hCU
  let O : TopologicalSpace.Opens M := ⟨Cᶜ, hC.isOpen_compl⟩
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Cᶜ : Set M) :=
    inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin n)) O)
  have hO : Nonempty O := hconn.nonempty.to_subtype.map Subtype.val
  let f : C(D.space, (Cᶜ : Set M)) :=
    ⟨fun x => ⟨j x.1, fun hxC => disjoint_left.mp havoid ⟨x.1, x.2, rfl⟩ hxC⟩,
      (hj.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let X : Set (Cᶜ : Set M) := Subtype.val ⁻¹' B
  let e₀ := (hj.toOpenPartialHomeomorph j).symm
  let e := e₀.subtypeRestr (s := O) hO
  have he₀source : e₀.source = range j := by
    change (hj.toOpenPartialHomeomorph j).target = range j
    exact IsOpenEmbedding.toOpenPartialHomeomorph_target j hj
  have he₀coords (x : EuclideanSpace ℝ (Fin n)) : e₀ (j x) = x :=
    hj.toOpenPartialHomeomorph_left_inv
  have hfsource (x : D.space) : f x ∈ e.source := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    change j x.1 ∈ e₀.source
    rw [he₀source]
    exact mem_range_self _
  have hfcoords (x : D.space) : e (f x) = x.1 := he₀coords x.1
  have hXsource : X ⊆ e.source := by
    intro x hx
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    change x.1 ∈ e₀.source
    rw [he₀source]
    exact image_subset_range j K.space (hBK hx)
  have hXpoly : e '' X ⊆ K.space := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := hBK hx
    change e₀ x.1 ∈ K.space
    rw [← hzx, he₀coords]
    exact hz
  have hXclosed : IsClosed X := hB.isClosed.preimage continuous_subtype_val
  have hlocal := hasAdaptedPiecewiseLinearCharts_of_chart D D K hD hD hK hdim f e
    hfsource hfcoords hXclosed hXsource hXpoly
  let P : NewmanProblem (EuclideanSpace ℝ (Fin n)) (Cᶜ : Set M) n p (p + 1) :=
    { source := D
      fixed := D
      target := D
      source_finite := hD
      fixed_subcomplex := subset_rfl
      target_subcomplex := subset_rfl
      source_dimension := fun s hs => (hDdim s hs).trans (by omega)
      target_dimension := hDdim
      map := f
      fixed_injective := fun x _ y _ hxy => Subtype.ext (hj.injective (congrArg Subtype.val hxy))
      obstacle := X
      openSet := Subtype.val ⁻¹' U
      obstacle_closed := hXclosed
      open_openSet := hU.preimage continuous_subtype_val
      obstacle_subset := fun x hx => hBU hx
      localData := hlocal
      codimension := hcodim
      connectivity := hconn
      decomposition := engulfingDecomposition_of_face_card_le D D f _ hDdim }
  obtain ⟨g, h, hfix, _, hengulf, hcompact⟩ :=
    hnewman (EuclideanSpace ℝ (Fin n)) P 1 zero_lt_one
  apply exists_protected_engulfing_of_complement hC hCU h hcompact
  intro x hx
  rcases hcover hx with hxB | ⟨y, hy, hyx⟩
  · exact hengulf (Or.inl hxB)
  · apply hengulf
    refine Or.inr ⟨⟨y, hy⟩, hy, ?_⟩
    rw [hfix ⟨y, hy⟩ hy]
    exact Subtype.ext hyx

end MetricManifold

end DifferentialGeometry.Topology.Engulfing
