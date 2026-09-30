import DifferentialGeometry.Topology.SimplicialComplex.Expansion.ElementaryCollapse
import DifferentialGeometry.Topology.SimplicialComplex.Stellar.HyperplaneRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.PiecewiseLinear

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace EdgeSubdivisionPoint

variable {K : SimplicialComplex ℝ E} (d : EdgeSubdivisionPoint K)

def firstSimplex (V : Finset E) : Finset E := insert d.p (V.erase d.a)

def secondSimplex (V : Finset E) : Finset E := insert d.p (V.erase d.b)

private theorem affineMap_point (f : E →ᵃ[ℝ] ℝ) :
    f d.p = d.alpha * f d.a + d.beta * f d.b := by
  have hp : d.p = AffineMap.lineMap d.a d.b d.beta := by
    rw [d.point_eq, AffineMap.lineMap_apply_module, show 1 - d.beta = d.alpha by linarith [d.total]]
  rw [hp, f.apply_lineMap, AffineMap.lineMap_apply_module,
    show 1 - d.beta = d.alpha by linarith [d.total]]
  rfl

theorem firstSimplex_inter_facet {V : Finset E} (hV : V ∈ K.faces)
    (ha : d.a ∈ V) (hb : d.b ∈ V) (i : E) :
    convexHull ℝ (d.firstSimplex V : Set E) ∩ convexHull ℝ ((V.erase i : Finset E) : Set E) =
      convexHull ℝ ((if i = d.a ∨ i = d.b then (V.erase d.a).erase i
        else insert d.p ((V.erase d.a).erase i) : Finset E) : Set E) := by
  obtain ⟨f, hf⟩ := exists_affineMap_of_affineIndependent (K.indep hV)
    (fun x : E => if x = i then (1 : ℝ) else 0)
  have hfp : f d.p = d.alpha * (if d.a = i then 1 else 0) +
      d.beta * (if d.b = i then 1 else 0) := by
    rw [d.affineMap_point, hf d.a ha, hf d.b hb]
  have hfp0 : f d.p = 0 ↔ i ≠ d.a ∧ i ≠ d.b := by
    rw [hfp]
    by_cases hia : i = d.a
    · subst i
      simp [d.endpoints_ne, d.endpoints_ne.symm, d.alpha_pos.ne']
    · by_cases hib : i = d.b
      · subst i
        simp [d.endpoints_ne, d.endpoints_ne.symm, d.beta_pos.ne']
      · simp [hia, hib, Ne.symm hia, Ne.symm hib]
  have hfV : ∀ x ∈ V, 0 ≤ f x := by
    intro x hx
    rw [hf x hx]
    split_ifs <;> norm_num
  have hfnew : ∀ x ∈ d.firstSimplex V, 0 ≤ f x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · rw [hfp]
      exact add_nonneg (mul_nonneg d.alpha_pos.le (by split_ifs <;> norm_num))
        (mul_nonneg d.beta_pos.le (by split_ifs <;> norm_num))
    · exact hfV x (Finset.mem_erase.mp hx).2
  have hfilter : V.filter (fun x => f x = 0) = V.erase i := by
    ext x
    by_cases hx : x ∈ V
    · simp [hx, hf x hx, eq_comm]
    · simp [hx]
  have hfilternew : (d.firstSimplex V).filter (fun x => f x = 0) =
      if i = d.a ∨ i = d.b then (V.erase d.a).erase i
        else insert d.p ((V.erase d.a).erase i) := by
    ext x
    by_cases hxp : x = d.p
    · subst x
      simp [firstSimplex, d.point_not_mem_face hV, hfp0]
      split_ifs <;> simp_all [d.point_not_mem_face hV]
      tauto
    · by_cases hxV : x ∈ V
      · simp [firstSimplex, hxp, hxV, hf x hxV, eq_comm]
        split_ifs <;> simp_all [eq_comm, and_comm]
      · simp [firstSimplex, hxp, hxV]
        split_ifs <;> simp_all [eq_comm, and_comm]
  have hsub : convexHull ℝ (d.firstSimplex V : Set E) ⊆ convexHull ℝ (V : Set E) :=
    d.convexHull_subset_parent
      (Finset.insert_subset_insert _ (Finset.erase_subset _ _)) (fun _ => ⟨ha, hb⟩)
  rw [← hfilter, ← convexHull_inter_affine_zero_of_nonneg V f hfV,
    ← inter_assoc, inter_eq_left.mpr hsub,
    convexHull_inter_affine_zero_of_nonneg _ f hfnew, hfilternew]

def reverse : EdgeSubdivisionPoint K where
  a := d.b
  b := d.a
  p := d.p
  alpha := d.beta
  beta := d.alpha
  endpoints_ne := d.endpoints_ne.symm
  edge_mem := by simpa only [Finset.pair_comm] using d.edge_mem
  alpha_pos := d.beta_pos
  beta_pos := d.alpha_pos
  total := by linarith [d.total]
  point_eq := by simpa only [add_comm] using d.point_eq

def firstRoof (B : Finset E) : Finset E :=
  B.filter (fun i => i ≠ d.a ∧ i ≠ d.b) ∪ if d.a ∈ B then {d.p} else ∅

theorem mem_firstRoof (B : Finset E) (i : E) :
    i ∈ d.firstRoof B ↔ (i ∈ B ∧ i ≠ d.a ∧ i ≠ d.b) ∨ (i = d.p ∧ d.a ∈ B) := by
  by_cases ha : d.a ∈ B <;> simp [firstRoof, ha, or_comm]

@[simp] theorem firstSimplex_erase_point {V : Finset E} (hV : V ∈ K.faces) :
    (d.firstSimplex V).erase d.p = V.erase d.a := by
  simp [firstSimplex, d.point_not_mem_face hV]

theorem firstSimplex_inter_facet_a {V : Finset E} (hV : V ∈ K.faces)
    (ha : d.a ∈ V) (hb : d.b ∈ V) :
    convexHull ℝ (d.firstSimplex V : Set E) ∩ convexHull ℝ ((V.erase d.a : Finset E) : Set E) =
      convexHull ℝ (((d.firstSimplex V).erase d.p : Finset E) : Set E) := by
  rw [d.firstSimplex_erase_point hV]
  simpa only [eq_self_iff_true, true_or, ite_true, Finset.erase_idem] using
    d.firstSimplex_inter_facet hV ha hb d.a

theorem firstSimplex_inter_facet_other {V : Finset E} (hV : V ∈ K.faces)
    (ha : d.a ∈ V) (hb : d.b ∈ V) {i : E} (hia : i ≠ d.a) (hib : i ≠ d.b)
    (hip : i ≠ d.p) :
    convexHull ℝ (d.firstSimplex V : Set E) ∩ convexHull ℝ ((V.erase i : Finset E) : Set E) =
      convexHull ℝ (((d.firstSimplex V).erase i : Finset E) : Set E) := by
  have he : (d.firstSimplex V).erase i = insert d.p ((V.erase d.a).erase i) := by
    ext x
    simp [firstSimplex]
    aesop
  rw [he]
  simpa only [ite_eq_right (not_or_intro hia hib)] using d.firstSimplex_inter_facet hV ha hb i

theorem firstSimplex_inter_roof {V B : Finset E} (hV : V ∈ K.faces)
    (ha : d.a ∈ V) (hb : d.b ∈ V) (hBV : B ⊆ V) (horder : d.b ∈ B → d.a ∈ B) :
    simplexRoof V B ∩ convexHull ℝ (d.firstSimplex V : Set E) =
      simplexRoof (d.firstSimplex V) (d.firstRoof B) := by
  ext x
  constructor
  · rintro ⟨hx, hxfirst⟩
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    by_cases hia : i = d.a
    · subst i
      exact mem_iUnion₂.mpr ⟨d.p, (d.mem_firstRoof B d.p).mpr (Or.inr ⟨rfl, hi⟩),
        (d.firstSimplex_inter_facet_a hV ha hb).subset ⟨hxfirst, hxi⟩⟩
    · by_cases hib : i = d.b
      · subst i
        have hcut := (d.firstSimplex_inter_facet hV ha hb d.b).subset ⟨hxfirst, hxi⟩
        simp only [or_true, ite_true] at hcut
        refine mem_iUnion₂.mpr ⟨d.p, (d.mem_firstRoof B d.p).mpr (Or.inr ⟨rfl, horder hi⟩), ?_⟩
        rw [d.firstSimplex_erase_point hV]
        exact convexHull_mono (Finset.erase_subset _ _) hcut
      · have hip : i ≠ d.p := fun he => d.point_not_mem_face hV (he ▸ hBV hi)
        exact mem_iUnion₂.mpr ⟨i, (d.mem_firstRoof B i).mpr (Or.inl ⟨hi, hia, hib⟩),
          (d.firstSimplex_inter_facet_other hV ha hb hia hib hip).subset ⟨hxfirst, hxi⟩⟩
  · intro hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    have hxfirst := convexHull_mono (Finset.erase_subset i (d.firstSimplex V)) hxi
    refine ⟨?_, hxfirst⟩
    rcases (d.mem_firstRoof B i).mp hi with ⟨hiB, hia, hib⟩ | ⟨rfl, haB⟩
    · have hip : i ≠ d.p := fun he => d.point_not_mem_face hV (he ▸ hBV hiB)
      exact mem_iUnion₂.mpr ⟨i, hiB,
        ((d.firstSimplex_inter_facet_other hV ha hb hia hib hip).symm.subset hxi).2⟩
    · exact mem_iUnion₂.mpr ⟨d.a, haB,
        ((d.firstSimplex_inter_facet_a hV ha hb).symm.subset hxi).2⟩

theorem secondSimplex_inter_firstSimplex {V : Finset E} (hV : V ∈ K.faces)
    (ha : d.a ∈ V) (hb : d.b ∈ V) :
    convexHull ℝ (d.secondSimplex V : Set E) ∩ convexHull ℝ (d.firstSimplex V : Set E) =
      convexHull ℝ (((d.firstSimplex V).erase d.b : Finset E) : Set E) := by
  have h := d.subdivision.convexHull_inter_convexHull
    (d.right_piece_isFace hV ha hb) (d.left_piece_isFace hV ha hb)
  change convexHull ℝ (d.secondSimplex V : Set E) ∩ convexHull ℝ (d.firstSimplex V : Set E) = _ at h
  rw [h]
  congr 1
  ext x
  simp [firstSimplex]
  have hp := d.point_ne_right
  aesop

theorem firstSimplex_inter_roof_union_second {V B : Finset E} (hV : V ∈ K.faces)
    (ha : d.a ∈ V) (hb : d.b ∈ V) (hBV : B ⊆ V) :
    (simplexRoof V B ∪ convexHull ℝ (d.secondSimplex V : Set E)) ∩
        convexHull ℝ (d.firstSimplex V : Set E) =
      simplexRoof (d.firstSimplex V) (insert d.b (d.firstRoof B)) := by
  ext x
  constructor
  · rintro ⟨hx, hxfirst⟩
    rcases hx with hx | hx
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      by_cases hia : i = d.a
      · subst i
        exact mem_iUnion₂.mpr ⟨d.p, Finset.mem_insert_of_mem
          ((d.mem_firstRoof B d.p).mpr (Or.inr ⟨rfl, hi⟩)),
          (d.firstSimplex_inter_facet_a hV ha hb).subset ⟨hxfirst, hxi⟩⟩
      · by_cases hib : i = d.b
        · subst i
          have hcut := (d.firstSimplex_inter_facet hV ha hb d.b).subset ⟨hxfirst, hxi⟩
          simp only [or_true, ite_true] at hcut
          refine mem_iUnion₂.mpr ⟨d.b, Finset.mem_insert_self _ _, ?_⟩
          apply convexHull_mono _ hcut
          intro y hy
          have hys := Finset.mem_erase.mp hy
          exact Finset.mem_erase.mpr ⟨hys.1, Finset.mem_insert_of_mem hys.2⟩
        · have hip : i ≠ d.p := fun he => d.point_not_mem_face hV (he ▸ hBV hi)
          exact mem_iUnion₂.mpr ⟨i, Finset.mem_insert_of_mem
            ((d.mem_firstRoof B i).mpr (Or.inl ⟨hi, hia, hib⟩)),
            (d.firstSimplex_inter_facet_other hV ha hb hia hib hip).subset ⟨hxfirst, hxi⟩⟩
    · exact mem_iUnion₂.mpr ⟨d.b, Finset.mem_insert_self _ _,
        (d.secondSimplex_inter_firstSimplex hV ha hb).subset ⟨hx, hxfirst⟩⟩
  · intro hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    have hxfirst := convexHull_mono (Finset.erase_subset i (d.firstSimplex V)) hxi
    refine ⟨?_, hxfirst⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Or.inr (((d.secondSimplex_inter_firstSimplex hV ha hb).symm.subset hxi).1)
    · left
      rcases (d.mem_firstRoof B i).mp hi with ⟨hiB, hia, hib⟩ | ⟨rfl, haB⟩
      · have hip : i ≠ d.p := fun he => d.point_not_mem_face hV (he ▸ hBV hiB)
        exact mem_iUnion₂.mpr ⟨i, hiB,
          ((d.firstSimplex_inter_facet_other hV ha hb hia hib hip).symm.subset hxi).2⟩
      · exact mem_iUnion₂.mpr ⟨d.a, haB,
          ((d.firstSimplex_inter_facet_a hV ha hb).symm.subset hxi).2⟩

def secondRoof (B : Finset E) : Finset E := insert d.a (d.reverse.firstRoof B)

theorem secondSimplex_inter_roof_union_first {V B : Finset E} (hV : V ∈ K.faces)
    (ha : d.a ∈ V) (hb : d.b ∈ V) (hBV : B ⊆ V) :
    (simplexRoof V B ∪ convexHull ℝ (d.firstSimplex V : Set E)) ∩
        convexHull ℝ (d.secondSimplex V : Set E) =
      simplexRoof (d.secondSimplex V) (d.secondRoof B) :=
  d.reverse.firstSimplex_inter_roof_union_second hV hb ha hBV

theorem proper_firstRoof {V B : Finset E} (_hV : V ∈ K.faces)
    (_ha : d.a ∈ V) (hb : d.b ∈ V) (hB : ProperSimplexRoof V B)
    (horder : d.b ∈ B → d.a ∈ B) :
    ProperSimplexRoof (d.firstSimplex V) (d.firstRoof B) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rcases (d.mem_firstRoof B i).mp hi with ⟨hiB, hia, _⟩ | ⟨rfl, _⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hia, hB.subset hiB⟩)
    · exact Finset.mem_insert_self _ _
  · by_cases haB : d.a ∈ B
    · exact ⟨d.p, (d.mem_firstRoof B d.p).mpr (Or.inr ⟨rfl, haB⟩)⟩
    · obtain ⟨i, hi⟩ := hB.nonempty
      have hia : i ≠ d.a := fun he => haB (he ▸ hi)
      have hib : i ≠ d.b := fun he => haB (horder (he ▸ hi))
      exact ⟨i, (d.mem_firstRoof B i).mpr (Or.inl ⟨hi, hia, hib⟩)⟩
  · refine ⟨d.b, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨d.endpoints_ne.symm, hb⟩)
    · rw [d.mem_firstRoof]
      simp [d.point_ne_right.symm]

theorem proper_secondRoof {V B : Finset E} (hV : V ∈ K.faces)
    (ha : d.a ∈ V) (_hb : d.b ∈ V) (hB : ProperSimplexRoof V B)
    (horder : d.b ∈ B → d.a ∈ B) :
    ProperSimplexRoof (d.secondSimplex V) (d.secondRoof B) := by
  refine ⟨?_, Finset.insert_nonempty _ _, ?_⟩
  · intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨d.endpoints_ne, ha⟩)
    · rcases (d.reverse.mem_firstRoof B i).mp hi with ⟨hiB, hib, _⟩ | ⟨rfl, _⟩
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hib, hB.subset hiB⟩)
      · exact Finset.mem_insert_self _ _
  · by_cases hbB : d.b ∈ B
    · obtain ⟨i, hi⟩ := hB.complement_nonempty
      obtain ⟨hiV, hiB⟩ := Finset.mem_sdiff.mp hi
      have hia : i ≠ d.a := fun he => hiB (he ▸ horder hbB)
      have hib : i ≠ d.b := fun he => hiB (he ▸ hbB)
      have hip : i ≠ d.p := fun he => d.point_not_mem_face hV (he ▸ hiV)
      refine ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hib, hiV⟩), ?_⟩⟩
      simp only [secondRoof, Finset.mem_insert, d.reverse.mem_firstRoof]
      simpa only [reverse] using (show ¬(i = d.a ∨
        (i ∈ B ∧ i ≠ d.b ∧ i ≠ d.a) ∨ (i = d.p ∧ d.b ∈ B)) by tauto)
    · refine ⟨d.p, Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _, ?_⟩⟩
      have hpB : d.p ∉ B := fun h => d.point_not_mem_face hV (hB.subset h)
      simp only [secondRoof, Finset.mem_insert, d.reverse.mem_firstRoof]
      simp only [reverse]
      simp [d.point_ne_left, hpB, hbB]

theorem stellar_attachments_ordered {A : Set E} {V B : Finset E} (hV : V ∈ K.faces)
    (ha : d.a ∈ V) (hb : d.b ∈ V) (hattach : SimplexAttachment A V B)
    (horder : d.b ∈ B → d.a ∈ B) :
    SimplexAttachment A (d.firstSimplex V) (d.firstRoof B) ∧
      SimplexAttachment (A ∪ convexHull ℝ (d.firstSimplex V : Set E))
        (d.secondSimplex V) (d.secondRoof B) ∧
      (A ∪ convexHull ℝ (d.firstSimplex V : Set E)) ∪
        convexHull ℝ (d.secondSimplex V : Set E) = A ∪ convexHull ℝ (V : Set E) := by
  have hsub₁ : convexHull ℝ (d.firstSimplex V : Set E) ⊆ convexHull ℝ (V : Set E) :=
    d.convexHull_subset_parent
      (Finset.insert_subset_insert _ (Finset.erase_subset _ _)) (fun _ => ⟨ha, hb⟩)
  have hsub₂ : convexHull ℝ (d.secondSimplex V : Set E) ⊆ convexHull ℝ (V : Set E) :=
    d.convexHull_subset_parent
      (Finset.insert_subset_insert _ (Finset.erase_subset _ _)) (fun _ => ⟨ha, hb⟩)
  refine ⟨⟨(d.left_piece_isFace hV ha hb).affineIndependent d,
    d.proper_firstRoof hV ha hb hattach.properRoof horder, ?_⟩,
    ⟨(d.right_piece_isFace hV ha hb).affineIndependent d,
      d.proper_secondRoof hV ha hb hattach.properRoof horder, ?_⟩, ?_⟩
  · have h := d.firstSimplex_inter_roof hV ha hb hattach.properRoof.subset horder
    rwa [← hattach.intersection, inter_assoc, inter_eq_right.mpr hsub₁] at h
  · have hi : A ∩ convexHull ℝ (d.secondSimplex V : Set E) =
        simplexRoof V B ∩ convexHull ℝ (d.secondSimplex V : Set E) := by
      rw [← hattach.intersection, inter_assoc, inter_eq_right.mpr hsub₂]
    rw [union_inter_distrib_right, hi, ← union_inter_distrib_right]
    exact d.secondSimplex_inter_roof_union_first hV ha hb hattach.properRoof.subset
  · rw [union_assoc]
    congr 1
    exact (convexHull_eq_union_stellar_edge ha hb d.endpoints_ne
      (openSegment_subset_segment _ _ _ d.point_mem_openSegment)).symm

theorem exists_stellar_shelling {A : Set E} {V B : Finset E} (hV : V ∈ K.faces)
    (ha : d.a ∈ V) (hb : d.b ∈ V) (hattach : SimplexAttachment A V B) :
    ∃ V₁ B₁ V₂ B₂ : Finset E,
      V₁ ∈ d.subdivision.faces ∧ V₂ ∈ d.subdivision.faces ∧
      SimplexAttachment A V₁ B₁ ∧
      SimplexAttachment (A ∪ convexHull ℝ (V₁ : Set E)) V₂ B₂ ∧
      (A ∪ convexHull ℝ (V₁ : Set E)) ∪ convexHull ℝ (V₂ : Set E) =
        A ∪ convexHull ℝ (V : Set E) := by
  by_cases horder : d.b ∈ B → d.a ∈ B
  · obtain ⟨hfirst, hsecond, hcover⟩ := d.stellar_attachments_ordered hV ha hb hattach horder
    exact ⟨_, _, _, _, d.left_piece_isFace hV ha hb, d.right_piece_isFace hV ha hb,
      hfirst, hsecond, hcover⟩
  · have hreverse : d.a ∈ B → d.b ∈ B := by tauto
    obtain ⟨hfirst, hsecond, hcover⟩ :=
      d.reverse.stellar_attachments_ordered hV hb ha hattach hreverse
    exact ⟨_, _, _, _, d.right_piece_isFace hV ha hb, d.left_piece_isFace hV ha hb,
      hfirst, hsecond, hcover⟩

theorem preserves_finite_expansion {A C : Set E} (h : FiniteSimplexExpansionIn K A C) :
    FiniteSimplexExpansionIn d.subdivision A C := by
  induction h with
  | refl => exact .refl _
  | @snoc C V B h hV hattach ih =>
      by_cases ha : d.a ∈ V
      · by_cases hb : d.b ∈ V
        · obtain ⟨V₁, B₁, V₂, B₂, hV₁, hV₂, hfirst, hsecond, hcover⟩ :=
            d.exists_stellar_shelling hV ha hb hattach
          rw [← hcover]
          exact (ih.snoc hV₁ hfirst).snoc hV₂ hsecond
        · exact ih.snoc (d.old_face_isFace hV (Or.inr hb)) hattach
      · exact ih.snoc (d.old_face_isFace hV (Or.inl ha)) hattach

theorem simplex_expansion_from_roof {V B : Finset E} (hV : V ∈ K.faces)
    (hB : ProperSimplexRoof V B) :
    FiniteSimplexExpansionIn d.subdivision (simplexRoof V B) (convexHull ℝ (V : Set E)) :=
  d.preserves_finite_expansion (FiniteSimplexExpansionIn.simplex_of_properRoof hV hB)

end EdgeSubdivisionPoint

end DifferentialGeometry.Topology.Engulfing
