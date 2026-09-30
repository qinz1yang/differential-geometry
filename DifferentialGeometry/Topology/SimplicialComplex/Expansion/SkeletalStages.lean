import DifferentialGeometry.Topology.SimplicialComplex.Expansion.PrincipalFaces

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

def skeletalStage (K R : SimplicialComplex ℝ E) (q : ℕ) (F : Finset (Finset E)) :
    SimplicialComplex ℝ E where
  faces := {s | s ∈ K.faces ∧ (s ∈ R.faces ∨ s.card < q ∨ ∃ t ∈ F, s ⊆ t)}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
    intro u hus hu
    refine ⟨K.down_closed hs.1 hus hu, ?_⟩
    rcases hs.2 with hsR | hsmall | ⟨t, ht, hst⟩
    · exact Or.inl (R.down_closed hsR hus hu)
    · exact Or.inr (Or.inl ((Finset.card_le_card hus).trans_lt hsmall))
    · exact Or.inr (Or.inr ⟨t, ht, hus.trans hst⟩)
  indep := fun hs => K.indep hs.1
  inter_subset_convexHull := fun hs ht => K.inter_subset_convexHull hs.1 ht.1

omit [DecidableEq E] in
theorem skeletalStage_faces_subset (K R : SimplicialComplex ℝ E) (q : ℕ)
    (F : Finset (Finset E)) : (skeletalStage K R q F).faces ⊆ K.faces := by
  classical
  exact fun _ hs => hs.1

omit [DecidableEq E] in
theorem skeletalStage_finite_faces (K R : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (q : ℕ) (F : Finset (Finset E)) : (skeletalStage K R q F).faces.Finite := by
  classical
  exact hK.subset (skeletalStage_faces_subset K R q F)

omit [DecidableEq E] in
theorem skeletalStage_mono (K R : SimplicialComplex ℝ E) (q : ℕ)
    {F G : Finset (Finset E)} (hFG : F ⊆ G) :
    (skeletalStage K R q F).faces ⊆ (skeletalStage K R q G).faces := by
  classical
  intro s hs
  refine ⟨hs.1, ?_⟩
  rcases hs.2 with hsR | hsmall | ⟨t, ht, hst⟩
  · exact Or.inl hsR
  · exact Or.inr (Or.inl hsmall)
  · exact Or.inr (Or.inr ⟨t, hFG ht, hst⟩)

theorem skeletalStage_space_insert (K R : SimplicialComplex ℝ E) (q : ℕ)
    (F : Finset (Finset E)) {s : Finset E} (hs : s ∈ K.faces) :
    (skeletalStage K R q (insert s F)).space =
      (skeletalStage K R q F).space ∪ convexHull ℝ (s : Set E) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hx
    rcases ht.2 with htR | hsmall | ⟨u, hu, htu⟩
    · exact Or.inl ((skeletalStage K R q F).convexHull_subset_space ⟨ht.1, Or.inl htR⟩ hxt)
    · exact Or.inl ((skeletalStage K R q F).convexHull_subset_space
        ⟨ht.1, Or.inr (Or.inl hsmall)⟩ hxt)
    · rcases Finset.mem_insert.mp hu with rfl | hu
      · exact Or.inr (convexHull_mono htu hxt)
      · exact Or.inl ((skeletalStage K R q F).convexHull_subset_space
          ⟨ht.1, Or.inr (Or.inr ⟨u, hu, htu⟩)⟩ hxt)
  · rintro (hx | hx)
    · obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hx
      exact (skeletalStage K R q (insert s F)).convexHull_subset_space
        (skeletalStage_mono K R q (Finset.subset_insert _ _) ht) hxt
    · exact (skeletalStage K R q (insert s F)).convexHull_subset_space
        ⟨hs, Or.inr (Or.inr ⟨s, Finset.mem_insert_self _ _, subset_rfl⟩)⟩ hx

omit [DecidableEq E] in
theorem skeletalStage_eq (K R : SimplicialComplex ℝ E) (q : ℕ)
    (F : Finset (Finset E))
    (hbound : ∀ s ∈ K.faces, s ∈ R.faces ∨ s.card ≤ q)
    (hselected : ∀ s ∈ K.faces, s.card = q → s ∈ F) : skeletalStage K R q F = K := by
  classical
  apply SimplicialComplex.ext
  ext s
  constructor
  · exact fun hs => hs.1
  · intro hs
    refine ⟨hs, ?_⟩
    rcases hbound s hs with hsR | hcard
    · exact Or.inl hsR
    · by_cases hsmall : s.card < q
      · exact Or.inr (Or.inl hsmall)
      · exact Or.inr (Or.inr ⟨s, hselected s hs (by omega), subset_rfl⟩)

theorem finiteSimplexBoundary_subset_skeletalStage (K R : SimplicialComplex ℝ E)
    (q : ℕ) (F : Finset (Finset E)) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = q) : finiteSimplexBoundary s ⊆ (skeletalStage K R q F).space := by
  classical
  intro x hx
  obtain ⟨a, has, hxa⟩ := mem_iUnion₂.mp hx
  by_cases hne : (s.erase a).Nonempty
  · apply (skeletalStage K R q F).convexHull_subset_space _ hxa
    refine ⟨K.down_closed hs (Finset.erase_subset _ _) hne, Or.inr (Or.inl ?_)⟩
    rw [← hcard]
    exact Finset.card_erase_lt_of_mem has
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne] at hxa
    simp only [Finset.coe_empty, convexHull_empty, notMem_empty] at hxa

theorem skeletalStage_inter_simplex (K R : SimplicialComplex ℝ E)
    (q : ℕ) (F : Finset (Finset E)) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = q) (hnew : s ∉ (skeletalStage K R q F).faces) :
    (skeletalStage K R q F).space ∩ convexHull ℝ (s : Set E) = finiteSimplexBoundary s := by
  classical
  ext x
  constructor
  · rintro ⟨hxK, hxs⟩
    obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hxK
    have hnot : ¬ s ⊆ t := fun hst => hnew
      ((skeletalStage K R q F).down_closed ht hst (K.nonempty_of_mem_faces hs))
    obtain ⟨a, has, hat⟩ := Finset.not_subset.mp hnot
    have hxi := K.inter_subset_convexHull hs ht.1 ⟨hxs, hxt⟩
    refine mem_iUnion₂.mpr ⟨a, has, convexHull_mono ?_ hxi⟩
    intro z hz
    exact Finset.mem_erase.mpr ⟨fun hza => hat (hza ▸ hz.2), hz.1⟩
  · intro hx
    refine ⟨finiteSimplexBoundary_subset_skeletalStage K R q F hs hcard hx, ?_⟩
    obtain ⟨a, _, hxa⟩ := mem_iUnion₂.mp hx
    exact convexHull_mono (Finset.erase_subset _ _) hxa

omit [DecidableEq E] in
theorem engulfingDecomposition_skeletalStage_empty {M : Type*} [MetricSpace M]
    (G H R : SimplicialComplex ℝ E) (f : C(G.space, M)) {U : Set M}
    (hRH : R.faces ⊆ H.faces) (hR : ∀ x : G.space, x.1 ∈ R.space → f x ∈ U)
    (q : ℕ) : engulfingDecomposition G (skeletalStage H R (q + 1) ∅) f U q := by
  classical
  let Q := skeletalStage H ⊥ (q + 1) ∅
  refine ⟨R, Q, ?_, ?_, ?_, ?_, hR⟩
  · exact fun s hs => ⟨hRH hs, Or.inl hs⟩
  · intro s hs
    refine ⟨hs.1, ?_⟩
    rcases hs.2 with hsbot | hsmall | ⟨t, ht, _⟩
    · exact hsbot.elim
    · exact Or.inr (Or.inl hsmall)
    · exact (Finset.notMem_empty _ ht).elim
  · ext s
    constructor
    · intro hs
      rcases hs.2 with hsR | hsmall | ⟨t, ht, _⟩
      · exact Or.inl hsR
      · exact Or.inr ⟨hs.1, Or.inr (Or.inl hsmall)⟩
      · exact (Finset.notMem_empty _ ht).elim
    · rintro (hsR | hsQ)
      · exact ⟨hRH hsR, Or.inl hsR⟩
      · refine ⟨hsQ.1, ?_⟩
        rcases hsQ.2 with hsbot | hsmall | ⟨t, ht, _⟩
        · exact hsbot.elim
        · exact Or.inr (Or.inl hsmall)
        · exact (Finset.notMem_empty _ ht).elim
  · intro s hs
    rcases hs.2 with hsbot | hsmall | ⟨t, ht, _⟩
    · exact hsbot.elim
    · omega
    · exact (Finset.notMem_empty _ ht).elim

theorem skeletalStage_mem_insert_of_ne (K R : SimplicialComplex ℝ E) (q : ℕ)
    (F : Finset (Finset E)) {s t : Finset E} (hcard : s.card = q)
    (ht : t ∈ (skeletalStage K R q (insert s F)).faces) (hne : t ≠ s) :
    t ∈ (skeletalStage K R q F).faces := by
  classical
  refine ⟨ht.1, ?_⟩
  rcases ht.2 with htR | hsmall | ⟨u, hu, htu⟩
  · exact Or.inl htR
  · exact Or.inr (Or.inl hsmall)
  · rcases Finset.mem_insert.mp hu with rfl | hu
    · refine Or.inr (Or.inl ?_)
      have hle := Finset.card_le_card htu
      have hlt : t.card < u.card := lt_of_le_of_ne hle
        (fun heq => hne (Finset.eq_of_subset_of_card_le htu heq.ge))
      omega
    · exact Or.inr (Or.inr ⟨u, hu, htu⟩)

theorem engulfingDecomposition_skeletalStage_insert {M : Type*} [MetricSpace M]
    (G K R : SimplicialComplex ℝ E) (q : ℕ) (F : Finset (Finset E))
    {s : Finset E} (hcard : s.card = q) (g : C(G.space, M)) {U : Set M}
    (hcovered : ∀ x : G.space, x.1 ∈ (skeletalStage K R q F).space → g x ∈ U) :
    engulfingDecomposition G (skeletalStage K R q (insert s F)) g U q := by
  classical
  let A := skeletalStage K R q (insert s F)
  let B := skeletalStage K R q F
  let Q := skeletalStage A ⊥ 0 {s}
  have hBA : B.faces ⊆ A.faces := skeletalStage_mono K R q (Finset.subset_insert _ _)
  refine ⟨B, Q, hBA, skeletalStage_faces_subset _ _ _ _, ?_, ?_, hcovered⟩
  · ext t
    constructor
    · intro ht
      by_cases hts : t = s
      · exact Or.inr ⟨ht, Or.inr (Or.inr ⟨s, Finset.mem_singleton_self _, hts ▸ subset_rfl⟩)⟩
      · exact Or.inl (skeletalStage_mem_insert_of_ne K R q F hcard ht hts)
    · exact fun ht => ht.elim (fun h => hBA h) (fun h => h.1)
  · intro t ht
    rcases ht.2 with hbot | hsmall | ⟨u, hu, htu⟩
    · exact hbot.elim
    · omega
    · have hus : u = s := Finset.mem_singleton.mp hu
      subst u
      exact (Finset.card_le_card htu).trans_eq hcard

open scoped ContinuousMap

theorem exists_engulfing_of_skeletal_steps {M : Type*} [MetricSpace M]
    (G H R L : SimplicialComplex ℝ E) (hH : H.faces.Finite) (q : ℕ)
    (hbound : ∀ s ∈ H.faces, s ∈ R.faces ∨ s.card ≤ q)
    (f : C(G.space, M)) (Good : C(G.space, M) → Prop) (hf : Good f)
    {X U : Set M} (hU : IsOpen U)
    (OpenGood : Set M → Prop) (hOpenGood : OpenGood U)
    (hOpenGood_image : ∀ V : Set M, ∀ h : M ≃ₜ M, OpenGood V → OpenGood (h '' V))
    (hstart : X ∪ f '' (Subtype.val ⁻¹' (skeletalStage H R q ∅).space) ⊆ U)
    (hstep : ∀ (F : Finset (Finset E)) (s : Finset E), s ∈ H.faces → s.card = q →
      s ∉ (skeletalStage H R q F).faces →
      ∀ (g : C(G.space, M)) (V : Set M), IsOpen V → OpenGood V → Good g →
      X ∪ g '' (Subtype.val ⁻¹' (skeletalStage H R q F).space) ⊆ V →
      g '' (Subtype.val ⁻¹' finiteSimplexBoundary s) ⊆ V →
      ∀ δ : ℝ, 0 < δ → ∃ (g' : C(G.space, M)) (h : M ≃ₜ M),
        Good g' ∧ (∀ x : G.space, x.1 ∈ L.space → g' x = g x) ∧
        (∀ x, dist (g' x) (g x) < δ) ∧
        X ∪ g' '' (Subtype.val ⁻¹' (skeletalStage H R q (insert s F)).space) ⊆ h '' V ∧
        IsCompact (closure {x | h x ≠ x})) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : C(G.space, M)) (h : M ≃ₜ M),
      Good g ∧ (∀ x : G.space, x.1 ∈ L.space → g x = f x) ∧
      (∀ x, dist (g x) (f x) < ε) ∧
      X ∪ g '' (Subtype.val ⁻¹' H.space) ⊆ h '' U ∧
      IsCompact (closure {x | h x ≠ x}) := by
  classical
  have hfinite (F : Finset (Finset E)) (hF : ∀ s ∈ F, s ∈ H.faces ∧ s.card = q)
      {η : ℝ} (hη : 0 < η) :
      ∃ (g : C(G.space, M)) (h : M ≃ₜ M),
        Good g ∧ (∀ x : G.space, x.1 ∈ L.space → g x = f x) ∧
        (∀ x, dist (g x) (f x) < η) ∧
        X ∪ g '' (Subtype.val ⁻¹' (skeletalStage H R q F).space) ⊆ h '' U ∧
        IsCompact (closure {x | h x ≠ x}) := by
    induction F using Finset.induction_on generalizing η with
    | empty =>
        refine ⟨f, Homeomorph.refl M, hf, fun _ _ => rfl, ?_, ?_, ?_⟩
        · intro x; simpa only [dist_self] using hη
        · exact fun x hx => ⟨x, hstart hx, rfl⟩
        · simp
    | @insert s F hsF ih =>
        have hs := hF s (Finset.mem_insert_self _ _)
        obtain ⟨g, h, hg, hfix, hnear, hcover, hcompact⟩ :=
          ih (fun t ht => hF t (Finset.mem_insert_of_mem ht)) (half_pos hη)
        by_cases hsp : s ∈ (skeletalStage H R q F).faces
        · have heq : (skeletalStage H R q (insert s F)).space = (skeletalStage H R q F).space := by
            rw [skeletalStage_space_insert H R q F hs.1]
            exact union_eq_left.mpr ((skeletalStage H R q F).convexHull_subset_space hsp)
          refine ⟨g, h, hg, hfix, fun x => (hnear x).trans (half_lt_self hη), ?_, hcompact⟩
          simpa only [heq] using hcover
        · have hb : g '' (Subtype.val ⁻¹' finiteSimplexBoundary s) ⊆ h '' U := by
            rintro y ⟨x, hx, rfl⟩
            exact hcover (Or.inr ⟨x,
              finiteSimplexBoundary_subset_skeletalStage H R q F hs.1 hs.2 hx, rfl⟩)
          obtain ⟨g', h', hg', hfix', hnear', hcover', hcompact'⟩ :=
            hstep F s hs.1 hs.2 hsp g (h '' U) (h.isOpenMap _ hU)
              (hOpenGood_image U h hOpenGood) hg hcover hb
              (η / 2) (half_pos hη)
          refine ⟨g', h.trans h', hg', fun x hx => (hfix' x hx).trans (hfix x hx),
            ?_, ?_, isCompact_closure_moved_trans h h' hcompact hcompact'⟩
          · intro x
            calc
              dist (g' x) (f x) ≤ dist (g' x) (g x) + dist (g x) (f x) := dist_triangle _ _ _
              _ < η / 2 + η / 2 := add_lt_add (hnear' x) (hnear x)
              _ = η := add_halves η
          · intro x hx
            obtain ⟨y, ⟨z, hz, rfl⟩, hy⟩ := hcover' hx
            exact ⟨z, hz, hy⟩
  let F := hH.toFinset.filter (fun s => s.card = q)
  have hF (s : Finset E) : s ∈ F ↔ s ∈ H.faces ∧ s.card = q := by simp [F]
  obtain ⟨g, h, hg, hfix, hnear, hcover, hcompact⟩ :=
    hfinite F (fun s hs => (hF s).mp hs) hε
  have heq : skeletalStage H R q F = H :=
    skeletalStage_eq H R q F hbound (fun s hs hcard => (hF s).mpr ⟨hs, hcard⟩)
  exact ⟨g, h, hg, hfix, hnear, by simpa only [heq] using hcover, hcompact⟩

end DifferentialGeometry.Topology.Engulfing
