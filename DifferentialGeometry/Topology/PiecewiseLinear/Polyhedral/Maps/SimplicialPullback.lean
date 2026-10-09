import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.CompatibleSimplicialImage

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [DecidableEq E] [DecidableEq F]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [DecidableEq F] in
theorem convexHull_inter_subset_filter_of_vertexRestriction
    (T : SimplicialComplex ℝ F) (S : Set F) [DecidablePred (· ∈ S)]
    (hS : (vertexRestriction T S).space = S)
    {t : Finset F} (ht : t ∈ T.faces) :
    convexHull ℝ (t : Set F) ∩ S ⊆
      convexHull ℝ ((t.filter (fun y => y ∈ S) : Finset F) : Set F) := by
  classical
  intro x hx
  have hxS : x ∈ (vertexRestriction T S).space := hS.symm ▸ hx.2
  obtain ⟨u, hu, hxu⟩ := SimplicialComplex.mem_space_iff.mp hxS
  have h := T.inter_subset_convexHull ht hu.1 ⟨hx.1, hxu⟩
  exact convexHull_mono (fun y hy => Finset.mem_filter.mpr ⟨hy.1, hu.2 hy.2⟩) h

namespace FacewiseAffineInverse

variable {K : SimplicialComplex ℝ E} {f : E → F}

def localPullback (B : FacewiseAffineInverse K f) (T : SimplicialComplex ℝ F)
    (hT : ∀ s : K.faces, (vertexRestriction T (f '' convexHull ℝ (s.val : Set E))).space =
      f '' convexHull ℝ (s.val : Set E)) (s : K.faces) : SimplicialComplex ℝ E :=
  injectiveImageComplex (vertexRestriction T (f '' convexHull ℝ (s.val : Set E))) (B.inverse s)
    (fun _ _ => ⟨B.inverse s, fun _ _ => rfl⟩)
    (fun _ hx _ hy hxy => B.injOn s ((hT s).subset hx) ((hT s).subset hy) hxy)

omit [DecidableEq F] in
theorem localPullback_space (B : FacewiseAffineInverse K f) (T : SimplicialComplex ℝ F)
    (hT : ∀ s : K.faces, (vertexRestriction T (f '' convexHull ℝ (s.val : Set E))).space =
      f '' convexHull ℝ (s.val : Set E)) (s : K.faces) :
    (B.localPullback T hT s).space = convexHull ℝ (s.val : Set E) := by
  classical
  erw [localPullback, injectiveImageComplex_space, hT s]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact B.map_mem s hy
  · intro hx
    exact ⟨f x, mem_image_of_mem _ hx, B.left_inverse s x hx⟩

omit [DecidableEq F] in
theorem localPullback_image_face (B : FacewiseAffineInverse K f) (T : SimplicialComplex ℝ F)
    (hT : ∀ s : K.faces, (vertexRestriction T (f '' convexHull ℝ (s.val : Set E))).space =
      f '' convexHull ℝ (s.val : Set E)) (s : K.faces) {t : Finset F}
    (ht : t ∈ (vertexRestriction T (f '' convexHull ℝ (s.val : Set E))).faces) :
    f '' convexHull ℝ (t.image (B.inverse s) : Set E) = convexHull ℝ (t : Set F) := by
  classical
  rw [Finset.coe_image, ← (B.inverse s).image_convexHull, Set.image_image]
  have hr : EqOn (f ∘ B.inverse s) id (convexHull ℝ (t : Set F)) := by
    intro y hy
    exact B.right_inverse s ((hT s).subset
      ((vertexRestriction T _).convexHull_subset_space ht hy))
  exact (Set.image_congr hr).trans (Set.image_id _)

theorem localPullback_face_image (B : FacewiseAffineInverse K f) (T : SimplicialComplex ℝ F)
    (_hT : ∀ s : K.faces, (vertexRestriction T (f '' convexHull ℝ (s.val : Set E))).space =
      f '' convexHull ℝ (s.val : Set E)) (s : K.faces) {t : Finset F}
    (ht : t ∈ (vertexRestriction T (f '' convexHull ℝ (s.val : Set E))).faces) :
    (t.image (B.inverse s)).image f = t := by
  rw [Finset.image_image]
  ext y
  simp only [Finset.mem_image, Function.comp_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [B.right_inverse s (ht.2 hz)]
  · intro hy
    exact ⟨y, hy, B.right_inverse s (ht.2 hy)⟩

omit [DecidableEq F] in
theorem localPullback_inter_subset_convexHull
    (B : FacewiseAffineInverse K f) (T : SimplicialComplex ℝ F)
    (hT : ∀ s : K.faces, (vertexRestriction T (f '' convexHull ℝ (s.val : Set E))).space =
      f '' convexHull ℝ (s.val : Set E))
    (a b : K.faces) {s t : Finset E}
    (hs : s ∈ (B.localPullback T hT a).faces)
    (ht : t ∈ (B.localPullback T hT b).faces) :
    convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
      convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
  classical
  intro x hx
  have hxa : x ∈ convexHull ℝ (a.val : Set E) := (B.localPullback_space T hT a).subset
    ((B.localPullback T hT a).convexHull_subset_space hs hx.1)
  have hxb : x ∈ convexHull ℝ (b.val : Set E) := (B.localPullback_space T hT b).subset
    ((B.localPullback T hT b).convexHull_subset_space ht hx.2)
  let v := a.val ∩ b.val
  have hxv : x ∈ convexHull ℝ (v : Set E) := by
    simpa only [v, Finset.coe_inter] using K.inter_subset_convexHull a.property b.property ⟨hxa, hxb⟩
  have hvne : v.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hxv
    simp at hxv
  let c : K.faces := ⟨v, K.down_closed a.property Finset.inter_subset_left hvne⟩
  have hfxc : f x ∈ f '' convexHull ℝ (c.val : Set E) := mem_image_of_mem _ hxv
  obtain ⟨u, hu, rfl⟩ := hs
  obtain ⟨w, hw, rfl⟩ := ht
  have hfxu : f x ∈ convexHull ℝ (u : Set F) :=
    (B.localPullback_image_face T hT a hu).subset (mem_image_of_mem _ hx.1)
  have hfxw : f x ∈ convexHull ℝ (w : Set F) :=
    (B.localPullback_image_face T hT b hw).subset (mem_image_of_mem _ hx.2)
  let u' := u.filter (fun y => y ∈ f '' convexHull ℝ (c.val : Set E))
  have hfxu' : f x ∈ convexHull ℝ (u' : Set F) :=
    convexHull_inter_subset_filter_of_vertexRestriction T _ (hT c) hu.1 ⟨hfxu, hfxc⟩
  have hu'ne : u'.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hfxu'
    simp at hfxu'
  have hu'T : u' ∈ T.faces := T.down_closed hu.1 (Finset.filter_subset _ _) hu'ne
  have hfxr : f x ∈ convexHull ℝ ((u' ∩ w : Finset F) : Set F) := by
    simpa only [Finset.coe_inter] using T.inter_subset_convexHull hu'T hw.1 ⟨hfxu', hfxw⟩
  have hxr : x ∈ convexHull ℝ ((u' ∩ w).image (B.inverse a) : Set E) := by
    rw [Finset.coe_image, ← (B.inverse a).image_convexHull]
    exact ⟨f x, hfxr, B.left_inverse a x hxa⟩
  apply convexHull_mono (s := ((u' ∩ w).image (B.inverse a) : Set E)) ?_ hxr
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
  have hyu := Finset.mem_filter.mp (Finset.mem_inter.mp hy).1
  have hyw := (Finset.mem_inter.mp hy).2
  obtain ⟨p, hp, hpy⟩ := hyu.2
  have hpa : p ∈ convexHull ℝ (a.val : Set E) := convexHull_mono Finset.inter_subset_left hp
  have hpb : p ∈ convexHull ℝ (b.val : Set E) := convexHull_mono Finset.inter_subset_right hp
  have hsame : B.inverse a y = B.inverse b y := by
    rw [← hpy, B.left_inverse a p hpa, B.left_inverse b p hpb]
  exact ⟨Finset.mem_image.mpr ⟨y, hyu.1, rfl⟩, Finset.mem_image.mpr ⟨y, hyw, hsame.symm⟩⟩

def pullbackComplex (B : FacewiseAffineInverse K f) (T : SimplicialComplex ℝ F)
    (hT : ∀ s : K.faces, (vertexRestriction T (f '' convexHull ℝ (s.val : Set E))).space =
      f '' convexHull ℝ (s.val : Set E)) : SimplicialComplex ℝ E where
  faces := ⋃ s : K.faces, (B.localPullback T hT s).faces
  isRelLowerSet_faces := by
    intro t ht
    obtain ⟨s, hs⟩ := mem_iUnion.mp ht
    exact ⟨(B.localPullback T hT s).nonempty_of_mem_faces hs, fun u hut hu =>
      mem_iUnion.mpr ⟨s, (B.localPullback T hT s).down_closed hs hut hu⟩⟩
  indep := by
    intro t ht
    obtain ⟨s, hs⟩ := mem_iUnion.mp ht
    exact (B.localPullback T hT s).indep hs
  inter_subset_convexHull := by
    intro s t hs ht
    obtain ⟨a, ha⟩ := mem_iUnion.mp hs
    obtain ⟨b, hb⟩ := mem_iUnion.mp ht
    exact B.localPullback_inter_subset_convexHull T hT a b ha hb

omit [DecidableEq F] in
theorem pullbackComplex_space (B : FacewiseAffineInverse K f) (T : SimplicialComplex ℝ F)
    (hT : ∀ s : K.faces, (vertexRestriction T (f '' convexHull ℝ (s.val : Set E))).space =
      f '' convexHull ℝ (s.val : Set E)) :
    (B.pullbackComplex T hT).space = K.space := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨s, hs⟩ := mem_iUnion.mp ht
    exact K.convexHull_subset_space s.property ((B.localPullback_space T hT s).subset
      ((B.localPullback T hT s).convexHull_subset_space hs hxt))
  · intro hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    have hxL := (B.localPullback_space T hT ⟨s, hs⟩).symm.subset hxs
    obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hxL
    exact (B.pullbackComplex T hT).convexHull_subset_space (mem_iUnion.mpr ⟨⟨s, hs⟩, ht⟩) hxt

omit [DecidableEq F] in
theorem pullbackComplex_refines (B : FacewiseAffineInverse K f) (T : SimplicialComplex ℝ F)
    (hT : ∀ s : K.faces, (vertexRestriction T (f '' convexHull ℝ (s.val : Set E))).space =
      f '' convexHull ℝ (s.val : Set E)) :
    simplicialRefines (B.pullbackComplex T hT) K := by
  classical
  intro t ht
  obtain ⟨s, hs⟩ := mem_iUnion.mp ht
  exact ⟨s.val, s.property, fun x hx => (B.localPullback_space T hT s).subset
    ((B.localPullback T hT s).convexHull_subset_space hs hx)⟩

omit [DecidableEq F] in
theorem pullbackComplex_finite_faces (B : FacewiseAffineInverse K f) (hK : K.faces.Finite)
    (T : SimplicialComplex ℝ F) (hTf : T.faces.Finite)
    (hT : ∀ s : K.faces, (vertexRestriction T (f '' convexHull ℝ (s.val : Set E))).space =
      f '' convexHull ℝ (s.val : Set E)) :
    (B.pullbackComplex T hT).faces.Finite := by
  classical
  let := hK.fintype
  apply finite_iUnion
  intro s
  exact injectiveImageComplex_finite_faces _ (vertexRestriction_finite_faces T _ hTf) _ _ _

theorem pullbackComplex_face_image_mem (B : FacewiseAffineInverse K f) (T : SimplicialComplex ℝ F)
    (hT : ∀ s : K.faces, (vertexRestriction T (f '' convexHull ℝ (s.val : Set E))).space =
      f '' convexHull ℝ (s.val : Set E)) {t : Finset E}
    (ht : t ∈ (B.pullbackComplex T hT).faces) : t.image f ∈ T.faces := by
  obtain ⟨s, hs⟩ := mem_iUnion.mp ht
  obtain ⟨u, hu, rfl⟩ := hs
  rw [B.localPullback_face_image T hT s hu]
  exact hu.1

theorem pullbackComplex_surjective_faces (B : FacewiseAffineInverse K f) (T : SimplicialComplex ℝ F)
    (hT : ∀ s : K.faces, (vertexRestriction T (f '' convexHull ℝ (s.val : Set E))).space =
      f '' convexHull ℝ (s.val : Set E))
    (hparent : ∀ t ∈ T.faces, ∃ s ∈ K.faces,
      convexHull ℝ (t : Set F) ⊆ f '' convexHull ℝ (s : Set E)) :
    ∀ t ∈ T.faces, ∃ u ∈ (B.pullbackComplex T hT).faces, u.image f = t := by
  intro t ht
  obtain ⟨s, hs, hts⟩ := hparent t ht
  let a : K.faces := ⟨s, hs⟩
  have htJ : t ∈ (vertexRestriction T (f '' convexHull ℝ (a.val : Set E))).faces :=
    ⟨ht, fun y hy => hts (subset_convexHull ℝ _ hy)⟩
  refine ⟨t.image (B.inverse a), mem_iUnion.mpr ⟨a, ?_⟩, B.localPullback_face_image T hT a htJ⟩
  exact ⟨t, htJ, rfl⟩

omit [DecidableEq F] in
theorem pullbackComplex_face_card_le (B : FacewiseAffineInverse K f) (T : SimplicialComplex ℝ F)
    (hT : ∀ s : K.faces, (vertexRestriction T (f '' convexHull ℝ (s.val : Set E))).space =
      f '' convexHull ℝ (s.val : Set E)) {d : ℕ}
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∀ t ∈ (B.pullbackComplex T hT).faces, t.card ≤ d + 1 := by
  classical
  exact (B.pullbackComplex_refines T hT).face_card_le hd

omit [DecidableEq F] in
theorem pullbackComplex_parent_vertexRestriction_space
    (B : FacewiseAffineInverse K f) (T : SimplicialComplex ℝ F)
    (hT : ∀ s : K.faces, (vertexRestriction T (f '' convexHull ℝ (s.val : Set E))).space =
      f '' convexHull ℝ (s.val : Set E)) (a : K.faces) :
    (vertexRestriction (B.pullbackComplex T hT) (convexHull ℝ (a.val : Set E))).space =
      convexHull ℝ (a.val : Set E) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    exact convexHull_min hs.2 (convex_convexHull ℝ _) hxs
  · intro hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp
      ((B.localPullback_space T hT a).symm.subset hx)
    apply SimplicialComplex.mem_space_iff.mpr
    refine ⟨s, ⟨mem_iUnion.mpr ⟨a, hs⟩, ?_⟩, hxs⟩
    intro y hy
    exact (B.localPullback_space T hT a).subset ((B.localPullback T hT a).subset_space hs hy)

omit [DecidableEq F] in
theorem pullbackComplex_subcomplex_space
    (B : FacewiseAffineInverse K f) (T : SimplicialComplex ℝ F)
    (hT : ∀ s : K.faces, (vertexRestriction T (f '' convexHull ℝ (s.val : Set E))).space =
      f '' convexHull ℝ (s.val : Set E))
    (D : SimplicialComplex ℝ E) (hDK : D.faces ⊆ K.faces) :
    (complexRestriction (B.pullbackComplex T hT) D).space = D.space := by
  classical
  have hsub : D.space ⊆ K.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    exact K.convexHull_subset_space (hDK hs) hxs
  have hcompat : ∀ s ∈ D.faces,
      (vertexRestriction (B.pullbackComplex T hT) (convexHull ℝ (s : Set E))).space =
        (B.pullbackComplex T hT).space ∩ convexHull ℝ (s : Set E) := by
    intro s hs
    rw [B.pullbackComplex_parent_vertexRestriction_space T hT ⟨s, hDK hs⟩,
      B.pullbackComplex_space T hT, inter_eq_right.mpr (K.convexHull_subset_space (hDK hs))]
  rw [complexRestriction_space_of_compatible _ _ hcompat, B.pullbackComplex_space T hT,
    inter_eq_right.mpr hsub]

end FacewiseAffineInverse

omit [DecidableEq E] in
theorem exists_compatible_simplicial_refinement [FiniteDimensional ℝ F]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ K.faces, InjOn f (convexHull ℝ (s : Set E)))
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ L : SimplicialComplex ℝ E, ∃ T : SimplicialComplex ℝ F,
      L.faces.Finite ∧ T.faces.Finite ∧ L.space = K.space ∧ T.space = f '' K.space ∧
      simplicialRefines L K ∧ (∀ s ∈ L.faces, s.card ≤ d + 1) ∧
      (∀ t ∈ T.faces, t.card ≤ d + 1) ∧
      (∀ s ∈ L.faces, s.image f ∈ T.faces) ∧
      (∀ t ∈ T.faces, ∃ s ∈ L.faces, s.image f = t) ∧
      (∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E))) ∧
      (∀ s ∈ L.faces, InjOn f (convexHull ℝ (s : Set E))) := by
  classical
  obtain ⟨T, hTf, hTspace, hTdim, hTcompat, hTparent⟩ :=
    exists_compatible_image_triangulation K hK f hf hinj hd
  obtain ⟨B⟩ := exists_facewiseAffineInverse K f hf hinj
  let hT := fun s : K.faces => hTcompat s.val s.property
  let L := B.pullbackComplex T hT
  have href : simplicialRefines L K := B.pullbackComplex_refines T hT
  refine ⟨L, T, B.pullbackComplex_finite_faces hK T hTf hT, hTf,
    B.pullbackComplex_space T hT, hTspace, href, B.pullbackComplex_face_card_le T hT hd,
    hTdim, fun _ hs => B.pullbackComplex_face_image_mem T hT hs,
    B.pullbackComplex_surjective_faces T hT hTparent, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, hst⟩ := href s hs
    obtain ⟨A, hA⟩ := hf t ht
    exact ⟨A, hA.mono hst⟩
  · intro s hs
    obtain ⟨t, ht, hst⟩ := href s hs
    exact (hinj t ht).mono hst

end

end DifferentialGeometry.Topology.Engulfing
