import DifferentialGeometry.Topology.SimplicialComplex.Stellar.StellarInvariantSubdivision
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry Module

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def coordinateGridCut {ι : Type*} (b : Basis ι ℝ E) (z : ι × ℝ) :
    E →ᵃ[ℝ] ℝ := (b.coord z.1).toAffineMap - AffineMap.const ℝ E z.2

omit [DecidableEq E] in
@[simp] theorem coordinateGridCut_apply {ι : Type*} (b : Basis ι ℝ E) (z : ι × ℝ) (x : E) :
    coordinateGridCut b z x = b.coord z.1 x - z.2 := by
  classical
  exact rfl

def affineCutSeparates (f : E →ᵃ[ℝ] ℝ) (x y : E) : Prop :=
  (f x < 0 ∧ 0 < f y) ∨ (f y < 0 ∧ 0 < f x)

omit [DecidableEq E] in
theorem isOpen_affineCutSeparates (f : E →ᵃ[ℝ] ℝ) :
    IsOpen {p : E × E | affineCutSeparates f p.1 p.2} := by
  classical
  have hf := f.continuous_of_finiteDimensional
  exact ((isOpen_lt (hf.comp continuous_fst) continuous_const).inter
      (isOpen_lt continuous_const (hf.comp continuous_snd))).union
    ((isOpen_lt (hf.comp continuous_snd) continuous_const).inter
      (isOpen_lt continuous_const (hf.comp continuous_fst)))

omit [DecidableEq E] in
theorem exists_coordinateGridCut_separates {ι : Type*} (b : Basis ι ℝ E)
    {x y : E} (hxy : x ≠ y) : ∃ z : ι × ℝ, affineCutSeparates (coordinateGridCut b z) x y := by
  classical
  have hcoord : ∃ i, b.coord i x ≠ b.coord i y := by
    by_contra! hn
    apply hxy
    apply b.repr.injective
    ext i
    exact hn i
  obtain ⟨i, hi⟩ := hcoord
  refine ⟨(i, (b.coord i x + b.coord i y) / 2), ?_⟩
  simp only [affineCutSeparates, coordinateGridCut_apply]
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · exact Or.inl ⟨by linarith, by linarith⟩
  · exact Or.inr ⟨by linarith, by linarith⟩

omit [DecidableEq E] in
theorem exists_finite_separating_coordinate_grid {ι : Type*} (b : Basis ι ℝ E)
    {S : Set E} (hS : IsCompact S) {ε : ℝ} (hε : 0 < ε) :
    ∃ I : Finset (ι × ℝ), ∀ x ∈ S, ∀ y ∈ S, ε ≤ dist x y →
      ∃ z ∈ I, affineCutSeparates (coordinateGridCut b z) x y := by
  classical
  let B : Set (E × E) := (S ×ˢ S) ∩ {p | ε ≤ dist p.1 p.2}
  have hB : IsCompact B := (hS.prod hS).inter_right
    (isClosed_le continuous_const (continuous_fst.dist continuous_snd))
  let U : (ι × ℝ) → Set (E × E) := fun z =>
    {p | affineCutSeparates (coordinateGridCut b z) p.1 p.2}
  have hcover : B ⊆ ⋃ z, U z := by
    rintro ⟨x, y⟩ hxy
    have hne : x ≠ y := by
      intro heq
      have hdist : ε ≤ dist x y := hxy.2
      rw [heq, dist_self] at hdist
      exact hε.not_ge hdist
    obtain ⟨z, hz⟩ := exists_coordinateGridCut_separates b hne
    exact mem_iUnion.mpr ⟨z, hz⟩
  obtain ⟨I, hI⟩ := hB.elim_finite_subcover U
    (fun z => isOpen_affineCutSeparates (coordinateGridCut b z)) hcover
  refine ⟨I, ?_⟩
  intro x hx y hy hdist
  have hm := hI (show (x, y) ∈ B from ⟨⟨hx, hy⟩, hdist⟩)
  obtain ⟨z, hz⟩ := mem_iUnion.mp hm
  obtain ⟨hzI, hzxy⟩ := mem_iUnion.mp hz
  exact ⟨z, hzI, hzxy⟩

omit [DecidableEq E] in
theorem respectsAffineHyperplane.not_separates {K : SimplicialComplex ℝ E}
    {f : E →ᵃ[ℝ] ℝ} (h : respectsAffineHyperplane K f) {s : Finset E} (hs : s ∈ K.faces)
    {x y : E} (hx : x ∈ convexHull ℝ (s : Set E)) (hy : y ∈ convexHull ℝ (s : Set E)) :
    ¬ affineCutSeparates f x y := by
  classical
  intro hsep
  rcases h s hs with hle | hge
  · have hxle : f x ≤ 0 := hle hx
    have hyle : f y ≤ 0 := hle hy
    exact hsep.elim (fun h => h.2.not_ge hyle) (fun h => h.2.not_ge hxle)
  · have hxge : 0 ≤ f x := hge hx
    have hyge : 0 ≤ f y := hge hy
    exact hsep.elim (fun h => h.1.not_ge hxge) (fun h => h.1.not_ge hyge)

omit [DecidableEq E] in
theorem mesh_le_of_respects_separating_grid {ι : Type*} (b : Basis ι ℝ E)
    {S : Set E} {ε : ℝ} (hε : 0 ≤ ε) (I : Finset (ι × ℝ))
    (hI : ∀ x ∈ S, ∀ y ∈ S, ε ≤ dist x y →
      ∃ z ∈ I, affineCutSeparates (coordinateGridCut b z) x y)
    (K : SimplicialComplex ℝ E) (hKS : K.space ⊆ S)
    (hcut : ∀ z ∈ I, respectsAffineHyperplane K (coordinateGridCut b z)) :
    hasMeshLE K ε := by
  classical
  intro s hs
  apply diam_le_of_forall_dist_le hε
  intro x hx y hy
  apply le_of_lt
  by_contra! hdist
  obtain ⟨z, hz, hsep⟩ := hI x (hKS (K.convexHull_subset_space hs hx))
    y (hKS (K.convexHull_subset_space hs hy)) hdist
  exact (hcut z hz).not_separates hs hx hy hsep

theorem exists_fine_grid_subdivision_preserving
    (P : SimplicialComplex ℝ E → Prop)
    (hstable : ∀ K (d : EdgeSubdivisionPoint K), P K → P d.subdivision)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hP : P K)
    {n : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ n + 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ (∀ s ∈ L.faces, s.card ≤ n + 1) ∧
      (∀ s ∈ L.faces, diam (convexHull ℝ (s : Set E)) < ε) ∧ P L := by
  have hcompact : IsCompact K.space :=
    hK.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)
  let b := Module.finBasis ℝ E
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨I, hI⟩ := exists_finite_separating_coordinate_grid b hcompact hhalf
  obtain ⟨L, hL, hspace, href, hcut, hdim, hPL⟩ :=
    exists_subdivision_respects_affineHyperplanes_preserving P hstable K hK hP I
      (coordinateGridCut b) hd
  refine ⟨L, hL, hspace, href, hdim, ?_, hPL⟩
  have hmesh := mesh_le_of_respects_separating_grid b hhalf.le I hI L hspace.subset hcut
  intro s hs
  exact (hmesh s hs).trans_lt (by linarith)

inductive EdgeStellarRefinement (K : SimplicialComplex ℝ E) : SimplicialComplex ℝ E → Prop
  | refl : EdgeStellarRefinement K K
  | step {L : SimplicialComplex ℝ E} (h : EdgeStellarRefinement K L)
      (d : EdgeSubdivisionPoint L) : EdgeStellarRefinement K d.subdivision

theorem EdgeStellarRefinement.preserves {K L : SimplicialComplex ℝ E}
    (h : EdgeStellarRefinement K L) (P : SimplicialComplex ℝ E → Prop)
    (hstable : ∀ K (d : EdgeSubdivisionPoint K), P K → P d.subdivision) (hK : P K) : P L := by
  induction h with
  | refl => exact hK
  | step h d ih => exact hstable _ d ih

theorem exists_fine_edge_stellar_refinement
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ n + 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ (∀ s ∈ L.faces, s.card ≤ n + 1) ∧
      (∀ s ∈ L.faces, diam (convexHull ℝ (s : Set E)) < ε) ∧ EdgeStellarRefinement K L :=
  exists_fine_grid_subdivision_preserving (EdgeStellarRefinement K)
    (fun _ d h => h.step d) K hK .refl hd hε

section InnerProduct

variable {F : Type*} [DecidableEq F] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]

theorem exists_fine_grid_subdivision_with_expansion
    (K : SimplicialComplex ℝ F) (hK : K.faces.Finite) {A C : Set F}
    (hAC : FiniteSimplexExpansionIn K A C)
    {n : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ n + 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : SimplicialComplex ℝ F, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ (∀ s ∈ L.faces, s.card ≤ n + 1) ∧
      (∀ s ∈ L.faces, diam (convexHull ℝ (s : Set F)) < ε) ∧
      FiniteSimplexExpansionIn L A C :=
  exists_fine_grid_subdivision_preserving (fun L => FiniteSimplexExpansionIn L A C)
    (fun _ d h => d.preserves_finite_expansion h) K hK hAC hd hε

theorem exists_fine_grid_subdivision_preserving_expansions
    (K : SimplicialComplex ℝ F) (hK : K.faces.Finite)
    {n : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ n + 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : SimplicialComplex ℝ F, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ (∀ s ∈ L.faces, s.card ≤ n + 1) ∧
      (∀ s ∈ L.faces, diam (convexHull ℝ (s : Set F)) < ε) ∧
      ∀ A C, FiniteSimplexExpansionIn K A C → FiniteSimplexExpansionIn L A C :=
  exists_fine_grid_subdivision_preserving
    (fun L => ∀ A C, FiniteSimplexExpansionIn K A C → FiniteSimplexExpansionIn L A C)
    (fun _ d h A C hAC => d.preserves_finite_expansion (h A C hAC))
    K hK (fun _ _ h => h) hd hε

end InnerProduct

end DifferentialGeometry.Topology.Engulfing
