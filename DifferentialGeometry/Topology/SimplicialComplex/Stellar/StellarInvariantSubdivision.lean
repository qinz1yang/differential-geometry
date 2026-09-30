import DifferentialGeometry.Topology.SimplicialComplex.Expansion.StellarCollapse

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_subdivision_respects_affineHyperplane_preserving
    (P : SimplicialComplex ℝ E → Prop)
    (hstable : ∀ K (d : EdgeSubdivisionPoint K), P K → P d.subdivision)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hP : P K)
    (f : E →ᵃ[ℝ] ℝ) {n : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ n + 1) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ respectsAffineHyperplane L f ∧
      (∀ s ∈ L.faces, s.card ≤ n + 1) ∧ P L := by
  generalize hcount : (crossingEdges K f).ncard = N
  induction N using Nat.strong_induction_on generalizing K with
  | h N ih =>
    by_cases hempty : crossingEdges K f = ∅
    · exact ⟨K, hK, rfl, simplicialRefines.refl K,
        respectsAffineHyperplane_of_crossingEdges_empty K f hempty, hd, hP⟩
    · obtain ⟨s, hs⟩ := Set.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨d, hedge, hp⟩ := exists_edgeSubdivisionPoint_on_hyperplane f hs
      have he : {d.a, d.b} ∈ crossingEdges K f := hedge ▸ hs
      have hlt : (crossingEdges d.subdivision f).ncard < N := by
        rw [← hcount]
        exact Set.ncard_lt_ncard (d.crossingEdges_ssubset f hp he) (crossingEdges_finite K hK f)
      obtain ⟨L, hL, hspace, href, hcut, hdim, hPL⟩ :=
        ih _ hlt d.subdivision (d.subdivision_finite_faces hK) (hstable K d hP)
          (d.subdivision_face_card_le hd) rfl
      exact ⟨L, hL, hspace.trans d.subdivision_space,
        href.trans d.subdivision_refines, hcut, hdim, hPL⟩

theorem exists_subdivision_respects_affineHyperplanes_preserving {ι : Type*}
    (P : SimplicialComplex ℝ E → Prop)
    (hstable : ∀ K (d : EdgeSubdivisionPoint K), P K → P d.subdivision)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hP : P K) (I : Finset ι)
    (f : ι → E →ᵃ[ℝ] ℝ) {n : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ n + 1) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ (∀ i ∈ I, respectsAffineHyperplane L (f i)) ∧
      (∀ s ∈ L.faces, s.card ≤ n + 1) ∧ P L := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨K, hK, rfl, simplicialRefines.refl K, by simp, hd, hP⟩
  | @insert i I hi ih =>
    obtain ⟨J, hJ, hJK, hJref, hJI, hJdim, hPJ⟩ := ih
    obtain ⟨L, hL, hLJ, hLref, hLi, hLdim, hPL⟩ :=
      exists_subdivision_respects_affineHyperplane_preserving P hstable J hJ hPJ (f i) hJdim
    refine ⟨L, hL, hLJ.trans hJK, hLref.trans hJref, ?_, hLdim, hPL⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hLi
    · exact (hJI j hj).refines hLref

section InnerProduct

variable {F : Type*} [DecidableEq F] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem exists_subdivision_respects_affineHyperplanes_with_expansion {ι : Type*}
    (K : SimplicialComplex ℝ F) (hK : K.faces.Finite) {A C : Set F}
    (hAC : FiniteSimplexExpansionIn K A C) (I : Finset ι)
    (f : ι → F →ᵃ[ℝ] ℝ) {n : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ n + 1) :
    ∃ L : SimplicialComplex ℝ F, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ (∀ i ∈ I, respectsAffineHyperplane L (f i)) ∧
      (∀ s ∈ L.faces, s.card ≤ n + 1) ∧ FiniteSimplexExpansionIn L A C := by
  exact exists_subdivision_respects_affineHyperplanes_preserving
    (fun L => FiniteSimplexExpansionIn L A C)
    (fun _ d h => d.preserves_finite_expansion h) K hK hAC I f hd

theorem exists_subdivision_respects_affineHyperplanes_preserving_expansions {ι : Type*}
    (K : SimplicialComplex ℝ F) (hK : K.faces.Finite) (I : Finset ι)
    (f : ι → F →ᵃ[ℝ] ℝ) {n : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ n + 1) :
    ∃ L : SimplicialComplex ℝ F, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ (∀ i ∈ I, respectsAffineHyperplane L (f i)) ∧
      (∀ s ∈ L.faces, s.card ≤ n + 1) ∧
      ∀ A C, FiniteSimplexExpansionIn K A C → FiniteSimplexExpansionIn L A C := by
  exact exists_subdivision_respects_affineHyperplanes_preserving
    (fun L => ∀ A C, FiniteSimplexExpansionIn K A C → FiniteSimplexExpansionIn L A C)
    (fun _ d h A C hAC => d.preserves_finite_expansion (h A C hAC))
    K hK (fun _ _ h => h) I f hd

end InnerProduct

end DifferentialGeometry.Topology.Engulfing
