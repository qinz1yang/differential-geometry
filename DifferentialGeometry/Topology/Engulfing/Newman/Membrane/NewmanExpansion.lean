import DifferentialGeometry.Topology.Engulfing.Newman.Membrane.NewmanMembranePreparation
import DifferentialGeometry.Topology.Engulfing.Newman.Data.NewmanLocalData
import DifferentialGeometry.Topology.SimplicialComplex.Weights.DualSkeleton
import DifferentialGeometry.Topology.SimplicialComplex.Refinement.RefinementRestriction
import DifferentialGeometry.Topology.SimplicialComplex.Subcomplex.SubcomplexSpaces

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

noncomputable section

set_option linter.unusedSectionVars false

variable {E M : Type*} [DecidableEq E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MetricSpace M]

theorem FiniteSimplexExpansionIn.isCompact {K : SimplicialComplex ℝ E} {A C : Set E}
    (h : FiniteSimplexExpansionIn K A C) (hA : IsCompact A) : IsCompact C := by
  induction h with
  | refl => exact hA
  | @snoc C V B h hV ha ih => exact ih.union (V.finite_toSet.isCompact_convexHull ℝ)

def mapSimplexAttachmentStep (K L : SimplicialComplex ℝ E) (X U : Set M)
    (Good : C(K.space, M) → Prop) : Prop :=
  ∀ (C : Set E) (V B : Finset E), IsCompact C → C ⊆ K.space → V ∈ K.faces →
    SimplexAttachment C V B → ∀ (g : C(K.space, M)) (H : M ≃ₜ M), Good g →
      X ∪ g '' (Subtype.val ⁻¹' C) ⊆ H '' U →
      ∀ ε : ℝ, 0 < ε → ∃ (g' : C(K.space, M)) (G : M ≃ₜ M),
        Good g' ∧ (∀ x : K.space, x.1 ∈ L.space → g' x = g x) ∧
        (∀ x, dist (g' x) (g x) < ε) ∧
        X ∪ g' '' (Subtype.val ⁻¹' (C ∪ convexHull ℝ (V : Set E))) ⊆ G '' (H '' U) ∧
        IsCompact (closure {x | G x ≠ x})

theorem exists_map_engulfing_of_expansion
    (K L : SimplicialComplex ℝ E) (f : C(K.space, M))
    (X U : Set M) (Good : C(K.space, M) → Prop) (hfGood : Good f)
    (hstep : mapSimplexAttachmentStep K L X U Good)
    {A C : Set E} (hexp : FiniteSimplexExpansionIn K A C)
    (hA : IsCompact A) (hC : C ⊆ K.space)
    (hstart : X ∪ f '' (Subtype.val ⁻¹' A) ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : C(K.space, M)) (H : M ≃ₜ M),
      Good g ∧ (∀ x : K.space, x.1 ∈ L.space → g x = f x) ∧
      (∀ x, dist (g x) (f x) < ε) ∧
      X ∪ g '' (Subtype.val ⁻¹' C) ⊆ H '' U ∧ IsCompact (closure {x | H x ≠ x}) := by
  induction hexp generalizing ε with
  | refl =>
    refine ⟨f, Homeomorph.refl M, hfGood, fun _ _ => rfl, ?_, ?_, ?_⟩
    · intro x
      simpa only [dist_self] using hε
    · exact fun x hx => ⟨x, hstart hx, rfl⟩
    · simp
  | @snoc C V B h hV ha ih =>
    have hCK : C ⊆ K.space := subset_union_left.trans hC
    obtain ⟨g, H, hgGood, hgfix, hgnear, hgcover, hHcompact⟩ := ih hCK (half_pos hε)
    obtain ⟨g', G, hg'Good, hg'fix, hg'near, hg'cover, hGcompact⟩ :=
      hstep C V B (h.isCompact hA) hCK hV ha g H hgGood hgcover (ε / 2) (half_pos hε)
    refine ⟨g', H.trans G, hg'Good, fun x hx => (hg'fix x hx).trans (hgfix x hx),
      ?_, ?_, isCompact_closure_moved_trans H G hHcompact hGcompact⟩
    · intro x
      calc
        dist (g' x) (f x) ≤ dist (g' x) (g x) + dist (g x) (f x) := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add (hg'near x) (hgnear x)
        _ = ε := add_halves ε
    · intro x hx
      obtain ⟨y, ⟨z, hz, rfl⟩, hy⟩ := hg'cover hx
      exact ⟨z, hz, hy⟩

theorem simplexRoof_subset_skeleton (K : SimplicialComplex ℝ E) {V B : Finset E} {q : ℕ}
    (hV : V ∈ K.faces) (hB : B ⊆ V) (hcard : V.card ≤ q + 2) :
    simplexRoof V B ⊆ (skeleton K q).space := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
  have hne : (V.erase i).Nonempty := Finset.coe_nonempty.mp
    (convexHull_nonempty_iff.mp ⟨x, hxi⟩)
  have hiV := hB hi
  apply (skeleton K q).convexHull_subset_space
    ⟨K.down_closed hV (Finset.erase_subset _ _) hne, ?_⟩ hxi
  rw [Finset.card_erase_of_mem hiV]
  omega

omit [DecidableEq E] in
theorem skeleton_space_mono (K : SimplicialComplex ℝ E) {q p : ℕ} (hqp : q ≤ p) :
    (skeleton K q).space ⊆ (skeleton K p).space := by
  classical
  intro x hx
  obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hx
  exact (skeleton K p).convexHull_subset_space
    ⟨ht.1, ht.2.trans (Nat.add_le_add_right hqp 1)⟩ hxt

def skeletalCovered (K : SimplicialComplex ℝ E) (A C : Set E) (q : ℕ) : Set E :=
  A ∪ (C ∩ (skeleton K q).space)

omit [DecidableEq E] in
theorem skeletalCovered_self (K : SimplicialComplex ℝ E) (A : Set E) (q : ℕ) :
    skeletalCovered K A A q = A := by
  classical
  exact union_eq_left.mpr inter_subset_left

omit [DecidableEq E] in
theorem skeletalCovered_subset {K : SimplicialComplex ℝ E} {A C : Set E} {q : ℕ}
    (hAC : A ⊆ C) : skeletalCovered K A C q ⊆ C := by
  classical
  exact union_subset hAC inter_subset_left

omit [DecidableEq E] in
theorem skeletalCovered_union (K : SimplicialComplex ℝ E) (A C S : Set E) (q : ℕ) :
    skeletalCovered K A (C ∪ S) q = skeletalCovered K A C q ∪ (S ∩ (skeleton K q).space) := by
  classical
  ext x
  simp only [skeletalCovered, mem_union, mem_inter_iff]
  tauto

omit [DecidableEq E] in
theorem skeletalCovered_union_of_subset (K : SimplicialComplex ℝ E) (A C S : Set E) (q : ℕ)
    (hSA : S ⊆ A) : skeletalCovered K A (C ∪ S) q = skeletalCovered K A C q := by
  classical
  rw [skeletalCovered_union]
  exact union_eq_left.mpr (inter_subset_left.trans (hSA.trans subset_union_left))

omit [DecidableEq E] in
theorem skeletalCovered_isCompact {K : SimplicialComplex ℝ E} (hK : K.faces.Finite)
    {A C : Set E} (hA : IsCompact A) (hC : IsCompact C) (q : ℕ) :
    IsCompact (skeletalCovered K A C q) := by
  classical
  have hsk : (skeleton K q).faces.Finite := hK.subset (fun _ hs => hs.1)
  exact hA.union (hC.inter_right
    (hsk.isCompact_biUnion (fun t _ => t.finite_toSet.isCompact_convexHull ℝ)).isClosed)

theorem SimplexAttachment.skeletalCovered {K : SimplicialComplex ℝ E}
    {A C : Set E} {V B : Finset E} {q : ℕ}
    (h : SimplexAttachment C V B) (hV : V ∈ K.faces)
    (hAC : A ⊆ C) (hcard : V.card ≤ q + 2) :
    SimplexAttachment (skeletalCovered K A C q) V B := by
  refine ⟨h.independent, h.properRoof, ?_⟩
  apply Subset.antisymm
  · rintro x ⟨hx, hxV⟩
    exact h.intersection ▸ ⟨skeletalCovered_subset hAC hx, hxV⟩
  · intro x hx
    have hroof := h.intersection.symm ▸ hx
    exact ⟨Or.inr ⟨hroof.1, simplexRoof_subset_skeleton K hV h.properRoof.subset hcard hx⟩,
      hroof.2⟩

theorem FiniteSimplexExpansionIn.isSubcomplexSpace {K : SimplicialComplex ℝ E}
    {A C : Set E} (h : FiniteSimplexExpansionIn K A C) (hA : isSubcomplexSpace K A) :
    isSubcomplexSpace K C := by
  induction h with
  | refl => exact hA
  | snoc _ hV _ ih => exact ih.union (.face hV)

def mapSkeletalSimplexStep (K L : SimplicialComplex ℝ E) (X U : Set M)
    (Good : C(K.space, M) → Prop) (Base Region : Set E) (p q : ℕ) : Prop :=
  ∀ (C : Set E) (V B : Finset E), IsCompact C → isSubcomplexSpace K C → Base ⊆ C → C ⊆ K.space →
    C ⊆ (skeleton K p).space → V ∈ K.faces → V.card ≤ q + 2 →
    SimplexAttachment C V B → C ∪ convexHull ℝ (V : Set E) ⊆ Region → ∀ (g : C(K.space, M)) (H : M ≃ₜ M), Good g →
      X ∪ g '' (Subtype.val ⁻¹' C) ⊆ H '' U →
      ∀ ε : ℝ, 0 < ε → ∃ (g' : C(K.space, M)) (G : M ≃ₜ M),
        Good g' ∧ (∀ x : K.space, x.1 ∈ L.space → g' x = g x) ∧
        (∀ x, dist (g' x) (g x) < ε) ∧
        X ∪ g' '' (Subtype.val ⁻¹' (C ∪
          (convexHull ℝ (V : Set E) ∩ (skeleton K q).space))) ⊆ G '' (H '' U) ∧
        IsCompact (closure {x | G x ≠ x})

theorem exists_map_engulfing_of_skeletal_expansion
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (f : C(K.space, M))
    (X U : Set M) (Good : C(K.space, M) → Prop) (hfGood : Good f)
    {p q : ℕ} (hqp : q ≤ p) {A C Region : Set E}
    (hstep : mapSkeletalSimplexStep K L X U Good A Region p q) (hexp : FiniteSimplexExpansionIn K A C)
    (hA : IsCompact A) (hApoly : isSubcomplexSpace K A) (hC : C ⊆ K.space) (hRegion : C ⊆ Region) (hAdim : A ⊆ (skeleton K p).space)
    (hbound : ∀ V ∈ K.faces, convexHull ℝ (V : Set E) ⊆ C →
      convexHull ℝ (V : Set E) ⊆ A ∨ V.card ≤ q + 2)
    (hstart : X ∪ f '' (Subtype.val ⁻¹' A) ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : C(K.space, M)) (H : M ≃ₜ M),
      Good g ∧ (∀ x : K.space, x.1 ∈ L.space → g x = f x) ∧
      (∀ x, dist (g x) (f x) < ε) ∧
      X ∪ g '' (Subtype.val ⁻¹' skeletalCovered K A C q) ⊆ H '' U ∧
      IsCompact (closure {x | H x ≠ x}) := by
  induction hexp generalizing ε with
  | refl =>
    refine ⟨f, Homeomorph.refl M, hfGood, fun _ _ => rfl, ?_, ?_, ?_⟩
    · intro x
      simpa only [dist_self] using hε
    · rw [skeletalCovered_self]
      exact fun x hx => ⟨x, hstart hx, rfl⟩
    · simp
  | @snoc C V B h hV ha ih =>
    have hCK : C ⊆ K.space := subset_union_left.trans hC
    have hRegion₀ : C ⊆ Region := subset_union_left.trans hRegion
    have hbound₀ : ∀ W ∈ K.faces, convexHull ℝ (W : Set E) ⊆ C →
        convexHull ℝ (W : Set E) ⊆ A ∨ W.card ≤ q + 2 :=
      fun W hW hWC => hbound W hW (hWC.trans subset_union_left)
    rcases hbound V hV subset_union_right with hVA | hcard
    · obtain ⟨g, H, hgGood, hgfix, hgnear, hgcover, hcompact⟩ := ih hCK hRegion₀ hbound₀ hε
      refine ⟨g, H, hgGood, hgfix, hgnear, ?_, hcompact⟩
      rwa [skeletalCovered_union_of_subset K A C _ q hVA]
    · obtain ⟨g, H, hgGood, hgfix, hgnear, hgcover, hHcompact⟩ :=
        ih hCK hRegion₀ hbound₀ (half_pos hε)
      have hsmall : skeletalCovered K A C q ⊆ (skeleton K p).space :=
        union_subset hAdim (inter_subset_right.trans (skeleton_space_mono K hqp))
      obtain ⟨g', G, hg'Good, hg'fix, hg'near, hg'cover, hGcompact⟩ :=
        hstep (skeletalCovered K A C q) V B
          (skeletalCovered_isCompact hK hA (h.isCompact hA) q)
          (hApoly.union ((h.isSubcomplexSpace hApoly).inter (.skeleton K q))) subset_union_left
          ((skeletalCovered_subset h.subset).trans hCK) hsmall hV hcard
          (ha.skeletalCovered hV h.subset hcard)
          ((union_subset_union (skeletalCovered_subset h.subset) subset_rfl).trans hRegion) g H hgGood hgcover (ε / 2) (half_pos hε)
      refine ⟨g', H.trans G, hg'Good, fun x hx => (hg'fix x hx).trans (hgfix x hx),
        ?_, ?_, isCompact_closure_moved_trans H G hHcompact hGcompact⟩
      · intro x
        calc
          dist (g' x) (f x) ≤ dist (g' x) (g x) + dist (g x) (f x) := dist_triangle _ _ _
          _ < ε / 2 + ε / 2 := add_lt_add (hg'near x) (hgnear x)
          _ = ε := add_halves ε
      · intro x hx
        have hx' : x ∈ X ∪ g' '' (Subtype.val ⁻¹' (skeletalCovered K A C q ∪
            (convexHull ℝ (V : Set E) ∩ (skeleton K q).space))) := by
          rcases hx with hx | ⟨z, hz, rfl⟩
          · exact Or.inl hx
          · refine Or.inr ⟨z, ?_, rfl⟩
            rw [skeletalCovered_union] at hz
            exact hz
        obtain ⟨y, ⟨z, hz, rfl⟩, hy⟩ := hg'cover hx'
        exact ⟨z, hz, hy⟩

end

end DifferentialGeometry.Topology.Engulfing
