import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Geometry.SimplexInequalities
import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.Perturbation.VertexPerturbation
import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.OptimalMap
import DifferentialGeometry.Topology.SimplicialComplex.Subcomplex.SubcomplexUnion
import Mathlib.Analysis.Convex.Radon

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry
open scoped _root_.Topology

variable {E F : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [DecidableEq E] in
theorem vertexRestriction_space_of_facewise_inter (K : SimplicialComplex ℝ E) (S : Set E)
    [DecidablePred (fun x => x ∈ S)]
    (hface : ∀ s ∈ K.faces, convexHull ℝ (s : Set E) ∩ S =
      convexHull ℝ ((s.filter (fun x => x ∈ S) : Finset E) : Set E)) :
    (vertexRestriction K S).space = K.space ∩ S := by
  classical
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    have hf : s.filter (fun x => x ∈ S) = s := Finset.filter_eq_self.mpr hs.2
    have h := hface s hs.1
    rw [hf] at h
    exact ⟨K.convexHull_subset_space hs.1 hxs, (h.symm ▸ hxs).2⟩
  · rintro x ⟨hx, hxS⟩
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    have hxf : x ∈ convexHull ℝ ((s.filter (fun x => x ∈ S) : Finset E) : Set E) := by
      rw [← hface s hs]
      exact ⟨hxs, hxS⟩
    have hne : (s.filter (fun x => x ∈ S)).Nonempty := by
      exact_mod_cast (convexHull_nonempty_iff.mp ⟨x, hxf⟩)
    exact (vertexRestriction K S).convexHull_subset_space
      ⟨K.down_closed hs (Finset.filter_subset _ _) hne,
        fun v hv => (Finset.mem_filter.mp hv).2⟩ hxf

omit [DecidableEq E] in
theorem vertexRestriction_piecewise_affine_nonneg (K : SimplicialComplex ℝ E)
    (q : E → ℝ)
    (haff : ∀ s ∈ K.faces, ∃ a : E →ᵃ[ℝ] ℝ, EqOn q a (convexHull ℝ (s : Set E)))
    (hcut : ∀ s ∈ K.faces, convexHull ℝ (s : Set E) ⊆ {x | q x ≤ 0} ∨
      convexHull ℝ (s : Set E) ⊆ {x | 0 ≤ q x}) :
    (vertexRestriction K {x | 0 ≤ q x}).space = K.space ∩ {x | 0 ≤ q x} := by
  classical
  apply vertexRestriction_space_of_facewise_inter
  intro s hs
  change convexHull ℝ (s : Set E) ∩ {x | 0 ≤ q x} =
    convexHull ℝ ((s.filter (fun x => 0 ≤ q x) : Finset E) : Set E)
  obtain ⟨a, ha⟩ := haff s hs
  rcases hcut s hs with hle | hge
  · have hzero : convexHull ℝ (s : Set E) ∩ {x | 0 ≤ q x} =
        convexHull ℝ (s : Set E) ∩ {x | a x = 0} := by
      ext x
      apply and_congr_right
      intro hx
      change (0 ≤ q x) ↔ a x = 0
      rw [← ha hx]
      exact ⟨fun h => le_antisymm (hle hx) h, fun h => h.ge⟩
    rw [hzero, convexHull_inter_affine_zero_of_nonpos s a
      (fun v hv => by rw [← ha (subset_convexHull ℝ _ hv)]; exact hle (subset_convexHull ℝ _ hv))]
    congr 2
    apply Finset.filter_congr
    intro v hv
    have hvh := subset_convexHull ℝ (s : Set E) hv
    rw [← ha hvh]
    exact ⟨fun h => h.ge, fun h => le_antisymm (hle hvh) h⟩
  · have hf : s.filter (fun x => 0 ≤ q x) = s := Finset.filter_eq_self.mpr
      (fun v hv => hge (subset_convexHull ℝ _ hv))
    rw [hf, inter_eq_left.mpr hge]

omit [DecidableEq E] in
theorem vertexRestriction_piecewise_affine_halfspaces {ι : Type*}
    (K : SimplicialComplex ℝ E) (I : Finset ι) (q : ι → E → ℝ)
    (haff : ∀ s ∈ K.faces, ∀ i ∈ I,
      ∃ a : E →ᵃ[ℝ] ℝ, EqOn (q i) a (convexHull ℝ (s : Set E)))
    (hcut : ∀ s ∈ K.faces, ∀ i ∈ I,
      convexHull ℝ (s : Set E) ⊆ {x | q i x ≤ 0} ∨
        convexHull ℝ (s : Set E) ⊆ {x | 0 ≤ q i x}) :
    (vertexRestriction K {x | ∀ i ∈ I, 0 ≤ q i x}).space =
      K.space ∩ {x | ∀ i ∈ I, 0 ≤ q i x} := by
  classical
  induction I using Finset.induction_on generalizing K with
  | empty => simp
  | @insert i I hi ih =>
    have hset : {x | ∀ j ∈ insert i I, 0 ≤ q j x} =
        {x | 0 ≤ q i x} ∩ {x | ∀ j ∈ I, 0 ≤ q j x} := by ext x; simp
    rw [hset, ← vertexRestriction_inter]
    rw [ih (vertexRestriction K {x | 0 ≤ q i x})
      (fun s hs j hj => haff s hs.1 j (Finset.mem_insert_of_mem hj))
      (fun s hs j hj => hcut s hs.1 j (Finset.mem_insert_of_mem hj)),
      vertexRestriction_piecewise_affine_nonneg K (q i)
        (fun s hs => haff s hs i (Finset.mem_insert_self _ _))
        (fun s hs => hcut s hs i (Finset.mem_insert_self _ _)), inter_assoc]

omit [DecidableEq E] in
theorem exists_subdivision_pullback_halfspaces {ι : Type*}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (J : Finset ι) (P : ι → Finset (F →ᵃ[ℝ] ℝ)) {d : ℕ}
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ (∀ s ∈ L.faces, s.card ≤ d + 1) ∧
      ∀ j ∈ J, (vertexRestriction L {x | ∀ a ∈ P j, 0 ≤ a (f x)}).space =
        K.space ∩ {x | ∀ a ∈ P j, 0 ≤ a (f x)} := by
  classical
  let := hK.fintype
  choose A hA using fun s : K.faces => hf s.1 s.2
  let I : Finset (K.faces × (F →ᵃ[ℝ] ℝ)) := Finset.univ.product (J.biUnion P)
  let Q : K.faces × (F →ᵃ[ℝ] ℝ) → E →ᵃ[ℝ] ℝ := fun p => p.2.comp (A p.1)
  obtain ⟨L, hL, hspace, href, hcut, hdim⟩ :=
    exists_subdivision_respects_affineHyperplanes K hK I Q hd
  refine ⟨L, hL, hspace, href, hdim, ?_⟩
  intro j hj
  rw [← hspace]
  apply vertexRestriction_piecewise_affine_halfspaces L (P j) (fun a x => a (f x))
  · intro s hs a ha
    obtain ⟨t, ht, hst⟩ := href s hs
    exact ⟨a.comp (A ⟨t, ht⟩), fun x hx => congrArg a (hA ⟨t, ht⟩ (hst hx))⟩
  · intro s hs a ha
    obtain ⟨t, ht, hst⟩ := href s hs
    have hp : ((⟨t, ht⟩ : K.faces), a) ∈ I := Finset.mem_product.mpr
      ⟨Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨j, hj, ha⟩⟩
    rcases hcut _ hp s hs with hle | hge
    · exact Or.inl (fun x hx => by
        change a (f x) ≤ 0
        rw [hA ⟨t, ht⟩ (hst hx)]
        exact hle hx)
    · exact Or.inr (fun x hx => by
        change 0 ≤ a (f x)
        rw [hA ⟨t, ht⟩ (hst hx)]
        exact hge hx)

omit [DecidableEq E] in
theorem exists_subdivision_pullback_simplices {ι : Type*} [Finite ι]
    [FiniteDimensional ℝ F]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (V : ι → Finset F) (hV : ∀ i, AffineIndependent ℝ ((↑) : V i → F)) {d : ℕ}
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ (∀ s ∈ L.faces, s.card ≤ d + 1) ∧
      ∀ i, (vertexRestriction L (f ⁻¹' convexHull ℝ (V i : Set F))).space =
        K.space ∩ f ⁻¹' convexHull ℝ (V i : Set F) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose P hP using fun i => exists_affine_inequalities_of_affineIndependent (V i) (hV i)
  obtain ⟨L, hL, hspace, href, hdim, hrestr⟩ :=
    exists_subdivision_pullback_halfspaces K hK f hf Finset.univ P hd
  refine ⟨L, hL, hspace, href, hdim, ?_⟩
  intro i
  simpa only [hP i, preimage_ofPred_eq] using hrestr i (Finset.mem_univ _)

omit [DecidableEq E] in
theorem affineIndependent_of_injOn_convexHull {s : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) (A : E →ᵃ[ℝ] F)
    (hA : InjOn A (convexHull ℝ (s : Set E))) :
    AffineIndependent ℝ (fun x : s => A x) := by
  classical
  by_contra hdep
  obtain ⟨I, z, hzI, hzIc⟩ := Convex.radon_partition hdep
  have himage (J : Set s) : (fun x : s => A x) '' J = A '' (Subtype.val '' J) := by
    rw [Set.image_image]
  rw [himage I, ← A.image_convexHull] at hzI
  rw [himage Iᶜ, ← A.image_convexHull] at hzIc
  obtain ⟨x, hx, hAx⟩ := hzI
  obtain ⟨y, hy, hAy⟩ := hzIc
  have hsub (J : Set s) : convexHull ℝ (Subtype.val '' J) ⊆ convexHull ℝ (s : Set E) :=
    convexHull_mono (by rintro _ ⟨a, _, rfl⟩; exact a.2)
  have hxy : x = y := hA (hsub I hx) (hsub Iᶜ hy) (hAx.trans hAy.symm)
  have hdis := hs.affineSpan_disjoint_of_disjoint (disjoint_compl_right : Disjoint I Iᶜ)
  exact disjoint_left.mp hdis (convexHull_subset_affineSpan _ hx)
    (hxy ▸ convexHull_subset_affineSpan _ hy)

omit [DecidableEq E] in
theorem exists_affine_inverse_on_affineSpan {s : Finset E} (hs : s.Nonempty)
    (A : E →ᵃ[ℝ] F) (hA : AffineIndependent ℝ (fun x : s => A x)) :
    ∃ B : F →ᵃ[ℝ] E,
      (∀ x ∈ affineSpan ℝ (s : Set E), B (A x) = x) ∧
      (∀ y ∈ affineSpan ℝ (A '' (s : Set E)), A (B y) = y) := by
  classical
  let : Nonempty s := hs.to_subtype
  let p : s → F := fun x => A x
  have himage : AffineIndependent ℝ ((↑) : s.image A → F) := by
    have heq : range p = (s.image A : Set F) := by
      ext y
      exact ⟨fun ⟨x, hx⟩ => Finset.mem_image.mpr ⟨x.1, x.2, hx⟩,
        fun hy => by obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy; exact ⟨⟨x, hx⟩, hxy⟩⟩
    have h := hA.range
    change AffineIndependent ℝ ((↑) : range p → F) at h
    rwa [heq] at h
  obtain ⟨B, hB⟩ := exists_affineMap_of_affineIndependent himage
    (fun y => (Function.invFun p y).1)
  have hBA (x : E) (hx : x ∈ s) : B (A x) = x := by
    rw [hB _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)]
    exact congrArg Subtype.val (Function.leftInverse_invFun hA.injective (⟨x, hx⟩ : s))
  refine ⟨B, ?_, ?_⟩
  · exact AffineMap.eqOn_affineSpan (f := B.comp A) (g := AffineMap.id ℝ E) hBA
  · apply AffineMap.eqOn_affineSpan (f := A.comp B) (g := AffineMap.id ℝ F)
    rintro _ ⟨x, hx, rfl⟩
    change A (B (A x)) = A x
    rw [hBA x hx]

omit [DecidableEq E] in
theorem homeomorph_inverse_affine_on_simplex (H : E ≃ₜ F) {s : Finset E}
    (hs : s.Nonempty) (hind : AffineIndependent ℝ ((↑) : s → E))
    (A : E →ᵃ[ℝ] F) (hH : EqOn H A (convexHull ℝ (s : Set E))) :
    ∃ B : F →ᵃ[ℝ] E, EqOn H.symm B (H '' convexHull ℝ (s : Set E)) := by
  have hAi : InjOn A (convexHull ℝ (s : Set E)) := by
    intro x hx y hy hxy
    apply H.injective
    rwa [hH hx, hH hy]
  obtain ⟨B, hBA, -⟩ := exists_affine_inverse_on_affineSpan hs A
    (affineIndependent_of_injOn_convexHull hind A hAi)
  refine ⟨B, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [H.symm_apply_apply, hH hx]
  exact (hBA x (convexHull_subset_affineSpan _ hx)).symm

omit [DecidableEq E] in
theorem image_convexHull_eq_of_eqOn_affineMap (f : E → F) (A : E →ᵃ[ℝ] F)
    {S : Set E} (hf : EqOn f A (convexHull ℝ S)) :
    f '' convexHull ℝ S = convexHull ℝ (f '' S) := by
  rw [image_congr hf, A.image_convexHull,
    image_congr (fun x hx => (hf (subset_convexHull ℝ S hx)).symm)]

section HomeomorphImage

variable [DecidableEq F]

omit [DecidableEq E] in
theorem homeomorph_image_face_independent (K : SimplicialComplex ℝ E) (H : E ≃ₜ F)
    (hH : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn H A (convexHull ℝ (s : Set E)))
    {s : Finset E} (hs : s ∈ K.faces) :
    AffineIndependent ℝ ((↑) : s.image H → F) := by
  classical
  obtain ⟨A, hA⟩ := hH s hs
  have hAi : InjOn A (convexHull ℝ (s : Set E)) := by
    intro x hx y hy hxy
    apply H.injective
    rwa [hA hx, hA hy]
  have hind := affineIndependent_of_injOn_convexHull (K.indep hs) A hAi
  have hindex : AffineIndependent ℝ (fun x : s => H x) := by
    convert hind using 1
    funext x
    exact hA (subset_convexHull ℝ _ x.2)
  have heq : range (fun x : s => H x) = (s.image H : Set F) := by
    ext y
    exact ⟨fun ⟨x, hx⟩ => Finset.mem_image.mpr ⟨x.1, x.2, hx⟩,
      fun hy => by obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy; exact ⟨⟨x, hx⟩, hxy⟩⟩
  have hr := hindex.range
  rwa [heq] at hr

def homeomorphImageComplex (K : SimplicialComplex ℝ E) (H : E ≃ₜ F)
    (hH : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn H A (convexHull ℝ (s : Set E))) :
    SimplicialComplex ℝ F where
  faces := {t | ∃ s ∈ K.faces, s.image H = t}
  isRelLowerSet_faces := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨(K.nonempty_of_mem_faces hs).image H, ?_⟩
    intro t hts ht
    refine ⟨t.image H.symm, K.down_closed hs ?_ (ht.image H.symm), ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (hts hy)
      simpa only [H.symm_apply_apply] using hz
    · simp only [Finset.image_image, Function.comp_def, H.apply_symm_apply]
      exact Finset.image_id'
  indep := by
    rintro _ ⟨s, hs, rfl⟩
    exact homeomorph_image_face_independent K H hH hs
  inter_subset_convexHull := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    obtain ⟨A, hA⟩ := hH s hs
    obtain ⟨B, hB⟩ := hH t ht
    have hsImage := image_convexHull_eq_of_eqOn_affineMap H A hA
    have htImage := image_convexHull_eq_of_eqOn_affineMap H B hB
    have hiImage := image_convexHull_eq_of_eqOn_affineMap H A
      (hA.mono (convexHull_mono (inter_subset_left :
        (s : Set E) ∩ (t : Set E) ⊆ (s : Set E))))
    simp only [Finset.coe_image]
    rw [← hsImage, ← htImage, ← Set.image_inter H.injective,
      ← Set.image_inter H.injective, ← hiImage]
    exact image_mono (K.inter_subset_convexHull hs ht)

theorem homeomorphImageComplex_finite_faces (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (H : E ≃ₜ F)
    (hH : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn H A (convexHull ℝ (s : Set E))) :
    (homeomorphImageComplex K H hH).faces.Finite := by
  change ((fun s : Finset E => s.image H) '' K.faces).Finite
  exact hK.image (fun s : Finset E => s.image H)

theorem homeomorphImageComplex_space (K : SimplicialComplex ℝ E) (H : E ≃ₜ F)
    (hH : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn H A (convexHull ℝ (s : Set E))) :
    (homeomorphImageComplex K H hH).space = H '' K.space := by
  apply Subset.antisymm
  · intro y hy
    obtain ⟨t, ⟨s, hs, rfl⟩, hyt⟩ := SimplicialComplex.mem_space_iff.mp hy
    obtain ⟨A, hA⟩ := hH s hs
    rw [Finset.coe_image, ← image_convexHull_eq_of_eqOn_affineMap H A hA] at hyt
    exact image_mono (K.convexHull_subset_space hs) hyt
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨A, hA⟩ := hH s hs
    apply (homeomorphImageComplex K H hH).convexHull_subset_space ⟨s, hs, rfl⟩
    rw [Finset.coe_image, ← image_convexHull_eq_of_eqOn_affineMap H A hA]
    exact mem_image_of_mem H hxs

theorem homeomorphImageComplex_inverse_affine (K : SimplicialComplex ℝ E) (H : E ≃ₜ F)
    (hH : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn H A (convexHull ℝ (s : Set E))) :
    ∀ t ∈ (homeomorphImageComplex K H hH).faces,
      ∃ B : F →ᵃ[ℝ] E, EqOn H.symm B (convexHull ℝ (t : Set F)) := by
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨A, hA⟩ := hH s hs
  obtain ⟨B, hB⟩ := homeomorph_inverse_affine_on_simplex H (K.nonempty_of_mem_faces hs)
    (K.indep hs) A hA
  refine ⟨B, ?_⟩
  rw [Finset.coe_image, ← image_convexHull_eq_of_eqOn_affineMap H A hA]
  exact hB

theorem homeomorphImageComplex_face_card_le (K : SimplicialComplex ℝ E) (H : E ≃ₜ F)
    (hH : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn H A (convexHull ℝ (s : Set E)))
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∀ t ∈ (homeomorphImageComplex K H hH).faces, t.card ≤ d + 1 := by
  rintro _ ⟨s, hs, rfl⟩
  rw [Finset.card_image_of_injective _ H.injective]
  exact hd s hs

end HomeomorphImage

section InjectiveImage

variable [DecidableEq F]

def injectiveImageComplex (K : SimplicialComplex ℝ E) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : InjOn f K.space) : SimplicialComplex ℝ F where
  faces := {t | ∃ s ∈ K.faces, s.image f = t}
  isRelLowerSet_faces := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨(K.nonempty_of_mem_faces hs).image f, ?_⟩
    intro t hts ht
    classical
    let r := s.filter (fun x => f x ∈ t)
    have hr : r.image f = t := by
      ext y
      constructor
      · rintro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact (Finset.mem_filter.mp hx).2
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hts hy)
        exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hy⟩, rfl⟩
    have hrne : r.Nonempty := by
      have h : (r.image f).Nonempty := hr.symm ▸ ht
      exact Finset.image_nonempty.mp h
    exact ⟨r, K.down_closed hs (Finset.filter_subset _ _) hrne, hr⟩
  indep := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨A, hA⟩ := hf s hs
    have hAi : InjOn A (convexHull ℝ (s : Set E)) := by
      intro x hx y hy hxy
      exact hinj (K.convexHull_subset_space hs hx) (K.convexHull_subset_space hs hy)
        ((hA hx).trans (hxy.trans (hA hy).symm))
    have hind := affineIndependent_of_injOn_convexHull (K.indep hs) A hAi
    have hindex : AffineIndependent ℝ (fun x : s => f x) := by
      convert hind using 1
      funext x
      exact hA (subset_convexHull ℝ _ x.2)
    have hr : range (fun x : s => f x) = (s.image f : Set F) := by
      ext y
      exact ⟨fun ⟨x, hx⟩ => Finset.mem_image.mpr ⟨x.1, x.2, hx⟩,
        fun hy => by obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy; exact ⟨⟨x, hx⟩, hxy⟩⟩
    have h := hindex.range
    rwa [hr] at h
  inter_subset_convexHull := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    obtain ⟨A, hA⟩ := hf s hs
    obtain ⟨B, hB⟩ := hf t ht
    have hsImage := image_convexHull_eq_of_eqOn_affineMap f A hA
    have htImage := image_convexHull_eq_of_eqOn_affineMap f B hB
    have hiImage := image_convexHull_eq_of_eqOn_affineMap f A
      (hA.mono (convexHull_mono (inter_subset_left :
        (s : Set E) ∩ (t : Set E) ⊆ (s : Set E))))
    simp only [Finset.coe_image]
    rw [← hsImage, ← htImage,
      ← hinj.image_inter (K.convexHull_subset_space hs) (K.convexHull_subset_space ht),
      ← hinj.image_inter (K.subset_space hs) (K.subset_space ht), ← hiImage]
    exact image_mono (K.inter_subset_convexHull hs ht)

omit [DecidableEq E] in
theorem injectiveImageComplex_finite_faces (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : InjOn f K.space) : (injectiveImageComplex K f hf hinj).faces.Finite :=
  hK.image (fun s : Finset E => s.image f)

omit [DecidableEq E] in
theorem injectiveImageComplex_space (K : SimplicialComplex ℝ E) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : InjOn f K.space) : (injectiveImageComplex K f hf hinj).space = f '' K.space := by
  apply Subset.antisymm
  · intro y hy
    obtain ⟨t, ⟨s, hs, rfl⟩, hyt⟩ := SimplicialComplex.mem_space_iff.mp hy
    obtain ⟨A, hA⟩ := hf s hs
    rw [Finset.coe_image, ← image_convexHull_eq_of_eqOn_affineMap f A hA] at hyt
    exact image_mono (K.convexHull_subset_space hs) hyt
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨A, hA⟩ := hf s hs
    apply (injectiveImageComplex K f hf hinj).convexHull_subset_space ⟨s, hs, rfl⟩
    rw [Finset.coe_image, ← image_convexHull_eq_of_eqOn_affineMap f A hA]
    exact mem_image_of_mem f hxs

omit [DecidableEq E] in
theorem inverse_affine_on_injectiveImageComplex (K : SimplicialComplex ℝ E) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : InjOn f K.space) (r : F → E) (hr : ∀ x ∈ K.space, r (f x) = x) :
    ∀ t ∈ (injectiveImageComplex K f hf hinj).faces,
      ∃ B : F →ᵃ[ℝ] E, EqOn r B (convexHull ℝ (t : Set F)) := by
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨A, hA⟩ := hf s hs
  have hAi : InjOn A (convexHull ℝ (s : Set E)) := by
    intro x hx y hy hxy
    exact hinj (K.convexHull_subset_space hs hx) (K.convexHull_subset_space hs hy)
      ((hA hx).trans (hxy.trans (hA hy).symm))
  obtain ⟨B, hBA, -⟩ := exists_affine_inverse_on_affineSpan (K.nonempty_of_mem_faces hs) A
    (affineIndependent_of_injOn_convexHull (K.indep hs) A hAi)
  refine ⟨B, ?_⟩
  rw [Finset.coe_image, ← image_convexHull_eq_of_eqOn_affineMap f A hA]
  rintro _ ⟨x, hx, rfl⟩
  rw [hr x (K.convexHull_subset_space hs hx), hA hx,
    hBA x (convexHull_subset_affineSpan _ hx)]

end InjectiveImage

section DimensionBounds

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [DecidableEq E] [FiniteDimensional ℝ E] in
theorem exists_affineSubspace_cover_preimage_on_simplex {s : Finset E}
    (hs : s.Nonempty) (hind : AffineIndependent ℝ ((↑) : s → E))
    (A : E →ᵃ[ℝ] F) (hA : InjOn A (convexHull ℝ (s : Set E)))
    (P : AffineSubspace ℝ F) :
    ∃ Q : AffineSubspace ℝ E,
      convexHull ℝ (s : Set E) ∩ A ⁻¹' (P : Set F) ⊆ Q ∧
        Module.finrank ℝ Q.direction ≤ Module.finrank ℝ P.direction := by
  obtain ⟨B, hBA, -⟩ := exists_affine_inverse_on_affineSpan hs A
    (affineIndependent_of_injOn_convexHull hind A hA)
  refine ⟨P.map B, ?_, ?_⟩
  · intro x hx
    exact AffineSubspace.mem_map.mpr ⟨A x, hx.2,
      hBA x (convexHull_subset_affineSpan _ hx.1)⟩
  · rw [AffineSubspace.map_direction]
    exact Submodule.finrank_map_le _ _

omit [DecidableEq E] in
theorem face_card_le_of_image_mem_affineSubspace {s t : Finset E}
    (hs : s.Nonempty) (hind : AffineIndependent ℝ ((↑) : s → E))
    (ht : AffineIndependent ℝ ((↑) : t → E))
    (hst : (t : Set E) ⊆ convexHull ℝ (s : Set E))
    (A : E →ᵃ[ℝ] F) (hA : InjOn A (convexHull ℝ (s : Set E)))
    (P : AffineSubspace ℝ F) (hP : ∀ x ∈ t, A x ∈ P) :
    t.card ≤ Module.finrank ℝ P.direction + 1 := by
  obtain ⟨Q, hQ, hdim⟩ := exists_affineSubspace_cover_preimage_on_simplex hs hind A hA P
  have hspan : affineSpan ℝ (t : Set E) ≤ Q :=
    affineSpan_le.mpr (fun x hx => hQ ⟨hst hx, hP x hx⟩)
  have hcard : t.card ≤ Module.finrank ℝ (affineSpan ℝ (t : Set E)).direction + 1 := by
    have h := ht.card_le_finrank_succ
    simp only [Fintype.card_coe] at h
    have hr : Set.range ((↑) : t → E) = (t : Set E) := by ext x; simp
    change t.card ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E))) + 1 at h
    rw [hr] at h
    rw [direction_affineSpan]
    exact h
  exact hcard.trans (Nat.add_le_add_right
    ((Submodule.finrank_mono (AffineSubspace.direction_le hspan)).trans hdim) 1)

omit [FiniteDimensional ℝ F] in
omit [DecidableEq E] in
theorem exists_image_complex_inverse_affine_of_interpolate
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (w : E → F) (H : E ≃ₜ F)
    (hH : ∀ x : K.space, H x = interpolateVertices K hK w x) :
    ∃ J : SimplicialComplex ℝ F, J.faces.Finite ∧ J.space = H '' K.space ∧
      (∀ t ∈ J.faces, ∃ B : F →ᵃ[ℝ] E, EqOn H.symm B (convexHull ℝ (t : Set F))) ∧
      (∀ d : ℕ, (∀ s ∈ K.faces, s.card ≤ d + 1) → ∀ t ∈ J.faces, t.card ≤ d + 1) := by
  classical
  have hAff : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn H A (convexHull ℝ (s : Set E)) := by
    intro s hs
    obtain ⟨A, -, hA⟩ := interpolateVertices_affineOn K hK w ⟨s, hs⟩
    refine ⟨A, ?_⟩
    intro x hx
    exact (hH ⟨x, K.convexHull_subset_space hs hx⟩).trans (hA _ hx)
  exact ⟨homeomorphImageComplex K H hAff, homeomorphImageComplex_finite_faces K hK H hAff,
    homeomorphImageComplex_space K H hAff, homeomorphImageComplex_inverse_affine K H hAff,
    fun _ hd => homeomorphImageComplex_face_card_le K H hAff hd⟩

end DimensionBounds

omit [DecidableEq E] in
theorem face_card_le_of_image_mem_convexHull {s t : Finset E} (V : Finset F)
    (hs : s.Nonempty) (hind : AffineIndependent ℝ ((↑) : s → E))
    (ht : AffineIndependent ℝ ((↑) : t → E))
    (hst : (t : Set E) ⊆ convexHull ℝ (s : Set E))
    (A : E →ᵃ[ℝ] F) (hA : InjOn A (convexHull ℝ (s : Set E)))
    (hV : ∀ x ∈ t, A x ∈ convexHull ℝ (V : Set F)) : t.card ≤ V.card := by
  classical
  obtain ⟨B, hBA, -⟩ := exists_affine_inverse_on_affineSpan hs A
    (affineIndependent_of_injOn_convexHull hind A hA)
  have hspan : (t : Set E) ⊆ affineSpan ℝ (V.image B : Set E) := by
    intro x hx
    apply convexHull_subset_affineSpan
    rw [Finset.coe_image, ← B.image_convexHull]
    exact ⟨A x, hV x hx, hBA x (convexHull_subset_affineSpan _ (hst hx))⟩
  exact (ht.card_le_card_of_subset_affineSpan hspan).trans (Finset.card_image_le)

omit [DecidableEq E] in
theorem exists_subdivision_pullback_simplices_with_card_bound {ι : Type*} [Finite ι]
    [FiniteDimensional ℝ F]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ K.faces, InjOn f (convexHull ℝ (s : Set E)))
    (V : ι → Finset F) (hV : ∀ i, AffineIndependent ℝ ((↑) : V i → F)) {d : ℕ}
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ (∀ s ∈ L.faces, s.card ≤ d + 1) ∧
      ∀ i, (vertexRestriction L (f ⁻¹' convexHull ℝ (V i : Set F))).space =
        K.space ∩ f ⁻¹' convexHull ℝ (V i : Set F) ∧
        ∀ t ∈ (vertexRestriction L (f ⁻¹' convexHull ℝ (V i : Set F))).faces,
          t.card ≤ (V i).card := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨L, hL, hspace, href, hdim, hrestr⟩ :=
    exists_subdivision_pullback_simplices K hK f hf V hV hd
  refine ⟨L, hL, hspace, href, hdim, fun i => ⟨hrestr i, ?_⟩⟩
  intro t ht
  obtain ⟨s, hs, hts⟩ := href t ht.1
  obtain ⟨A, hA⟩ := hf s hs
  apply face_card_le_of_image_mem_convexHull (V i) (K.nonempty_of_mem_faces hs)
    (K.indep hs) (L.indep ht.1) ((subset_convexHull ℝ _).trans hts) A
  · intro x hx y hy hxy
    exact hinj s hs hx hy ((hA hx).trans (hxy.trans (hA hy).symm))
  · intro x hx
    rw [← hA (hts (subset_convexHull ℝ _ hx))]
    exact ht.2 hx

omit [DecidableEq E] in
theorem exists_subdivision_preimage_complex [FiniteDimensional ℝ F]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ K.faces, InjOn f (convexHull ℝ (s : Set E)))
    (T : SimplicialComplex ℝ F) (hT : T.faces.Finite) {d e : ℕ}
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) (he : ∀ t ∈ T.faces, t.card ≤ e + 1) :
    ∃ L P : SimplicialComplex ℝ E,
      L.faces.Finite ∧ L.space = K.space ∧ simplicialRefines L K ∧
      (∀ s ∈ L.faces, s.card ≤ d + 1) ∧ P.faces.Finite ∧ P.faces ⊆ L.faces ∧
      P.space = K.space ∩ f ⁻¹' T.space ∧ (∀ s ∈ P.faces, s.card ≤ e + 1) := by
  classical
  let := hT.fintype
  obtain ⟨L, hL, hspace, href, hdim, hrestr⟩ :=
    exists_subdivision_pullback_simplices_with_card_bound K hK f hf hinj
      (fun t : T.faces => t.1) (fun t => T.indep t.2) hd
  let J : T.faces → SimplicialComplex ℝ E :=
    fun t => vertexRestriction L (f ⁻¹' convexHull ℝ (t.1 : Set F))
  have hJ (i : T.faces) : (J i).faces ⊆ L.faces := fun _ h => h.1
  refine ⟨L, subcomplexUnion L J hJ, hL, hspace, href, hdim,
    hL.subset (subcomplexUnion_faces_subset L J hJ),
    subcomplexUnion_faces_subset L J hJ, ?_, ?_⟩
  · rw [subcomplexUnion_space]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      change x ∈ (vertexRestriction L (f ⁻¹' convexHull ℝ (i.1 : Set F))).space at hi
      rw [(hrestr i).1] at hi
      exact ⟨hi.1, T.convexHull_subset_space i.2 hi.2⟩
    · rintro ⟨hx, hfx⟩
      obtain ⟨t, ht, hft⟩ := SimplicialComplex.mem_space_iff.mp hfx
      apply mem_iUnion.mpr
      refine ⟨⟨t, ht⟩, ?_⟩
      change x ∈ (vertexRestriction L (f ⁻¹' convexHull ℝ (t : Set F))).space
      rw [(hrestr ⟨t, ht⟩).1]
      exact ⟨hx, hft⟩
  · apply subcomplexUnion_face_card_le
    intro i s hs
    exact ((hrestr i).2 s hs).trans (he i.1 i.2)

omit [DecidableEq E] in
theorem exists_subdivision_preimage_of_interpolate [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (w : E → F)
    (hw : ∀ s ∈ K.faces, AffineIndependent ℝ (fun x : s => w x))
    (T : SimplicialComplex ℝ F) (hT : T.faces.Finite) {d e : ℕ}
    (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) (he : ∀ t ∈ T.faces, t.card ≤ e + 1) :
    ∃ L P : SimplicialComplex ℝ E,
      L.faces.Finite ∧ L.space = K.space ∧ simplicialRefines L K ∧
      (∀ s ∈ L.faces, s.card ≤ d + 1) ∧ P.faces.Finite ∧ P.faces ⊆ L.faces ∧
      P.space = Subtype.val '' (interpolateVertices K hK w ⁻¹' T.space) ∧
      (∀ s ∈ P.faces, s.card ≤ e + 1) := by
  classical
  let f : E → F := fun x => if hx : x ∈ K.space then interpolateVertices K hK w ⟨x, hx⟩ else 0
  have hfeq (x : E) (hx : x ∈ K.space) : f x = interpolateVertices K hK w ⟨x, hx⟩ :=
    dite_eq_left hx
  have hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)) := by
    intro s hs
    obtain ⟨A, -, hA⟩ := interpolateVertices_affineOn K hK w ⟨s, hs⟩
    exact ⟨A, fun x hx => (hfeq x (K.convexHull_subset_space hs hx)).trans (hA _ hx)⟩
  have hinj : ∀ s ∈ K.faces, InjOn f (convexHull ℝ (s : Set E)) := by
    intro s hs x hx y hy hxy
    have hxK := K.convexHull_subset_space hs hx
    have hyK := K.convexHull_subset_space hs hy
    rw [hfeq x hxK, hfeq y hyK] at hxy
    exact congrArg Subtype.val (interpolateVertices_injOn_face K hK w ⟨s, hs⟩
      (hw s hs) (x₁ := ⟨x, hxK⟩) (x₂ := ⟨y, hyK⟩) hx hy hxy)
  obtain ⟨L, P, hL, hspace, href, hdim, hP, hPL, hPspace, hPdim⟩ :=
    exists_subdivision_preimage_complex K hK f hf hinj T hT hd he
  refine ⟨L, P, hL, hspace, href, hdim, hP, hPL, hPspace.trans ?_, hPdim⟩
  ext x
  constructor
  · rintro ⟨hx, hfx⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    change interpolateVertices K hK w ⟨x, hx⟩ ∈ T.space
    rw [← hfeq x hx]
    exact hfx
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    change f y.1 ∈ T.space
    rw [hfeq y.1 y.2]
    exact hy

omit [DecidableEq E] in
theorem face_subset_of_centroid_mem (K : SimplicialComplex ℝ E) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hc : s.centroid ℝ id ∈ convexHull ℝ (t : Set E)) : s ⊆ t := by
  classical
  let : Nonempty s := (K.nonempty_of_mem_faces hs).to_subtype
  let R : Finset s := Finset.univ.filter (fun v => (v : E) ∈ t)
  have hr : ((↑) : s → E) '' (R : Set s) = (s : Set E) ∩ (t : Set E) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.2, (Finset.mem_filter.mp hv).2⟩
    · rintro ⟨hxs, hxt⟩
      exact ⟨⟨x, hxs⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxt⟩, rfl⟩
  have hcspan : Finset.univ.centroid ℝ ((↑) : s → E) ∈
      affineSpan ℝ (((↑) : s → E) '' (R : Set s)) := by
    rw [Finset.centroid_univ, hr]
    apply convexHull_subset_affineSpan
    exact K.inter_subset_convexHull hs ht
      ⟨s.centroid_mem_convexHull (K.nonempty_of_mem_faces hs), hc⟩
  intro v hv
  by_contra hvt
  exact centroid_notMem_affineSpan (K.indep hs) Finset.univ_nonempty
    (Finset.mem_univ (⟨v, hv⟩ : s)) (by simpa only [R, Finset.mem_filter,
      Finset.mem_univ, true_and] using hvt) hcspan

omit [DecidableEq E] in
theorem exists_subcomplex_containing_face_of_cover {ι : Type*}
    (K : SimplicialComplex ℝ E) (J : ι → SimplicialComplex ℝ E)
    (hJ : ∀ i, (J i).faces ⊆ K.faces)
    (hcover : ∀ x ∈ K.space, ∃ i, x ∈ (J i).space)
    {s : Finset E} (hs : s ∈ K.faces) : ∃ i, s ∈ (J i).faces := by
  classical
  obtain ⟨i, hi⟩ := hcover (s.centroid ℝ id)
    (K.convexHull_subset_space hs (s.centroid_mem_convexHull (K.nonempty_of_mem_faces hs)))
  obtain ⟨t, ht, hct⟩ := SimplicialComplex.mem_space_iff.mp hi
  exact ⟨i, (J i).down_closed ht
    (face_subset_of_centroid_mem K hs (hJ i ht) hct) (K.nonempty_of_mem_faces hs)⟩

omit [DecidableEq E] in
theorem exists_subdivision_mapping_faces [FiniteDimensional ℝ F]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (T : SimplicialComplex ℝ F) (hT : T.faces.Finite) (hmap : MapsTo f K.space T.space)
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ (∀ s ∈ L.faces, s.card ≤ d + 1) ∧
      ∀ s ∈ L.faces, ∃ t ∈ T.faces,
        MapsTo f (convexHull ℝ (s : Set E)) (convexHull ℝ (t : Set F)) := by
  classical
  let := hT.fintype
  obtain ⟨L, hL, hspace, href, hdim, hrestr⟩ := exists_subdivision_pullback_simplices
    K hK f hf (fun t : T.faces => t.1) (fun t => T.indep t.2) hd
  let J : T.faces → SimplicialComplex ℝ E :=
    fun t => vertexRestriction L (f ⁻¹' convexHull ℝ (t.1 : Set F))
  have hJ (i : T.faces) : (J i).faces ⊆ L.faces := fun _ h => h.1
  have hcover : ∀ x ∈ L.space, ∃ i, x ∈ (J i).space := by
    intro x hx
    have hxK : x ∈ K.space := hspace ▸ hx
    obtain ⟨t, ht, hft⟩ := SimplicialComplex.mem_space_iff.mp (hmap hxK)
    refine ⟨⟨t, ht⟩, ?_⟩
    change x ∈ (vertexRestriction L (f ⁻¹' convexHull ℝ (t : Set F))).space
    rw [hrestr ⟨t, ht⟩]
    exact ⟨hxK, hft⟩
  refine ⟨L, hL, hspace, href, hdim, ?_⟩
  intro s hs
  obtain ⟨i, hi⟩ := exists_subcomplex_containing_face_of_cover L J hJ hcover hs
  refine ⟨i.1, i.2, fun x hx => ?_⟩
  have hm := (J i).convexHull_subset_space hi hx
  change x ∈ (vertexRestriction L (f ⁻¹' convexHull ℝ (i.1 : Set F))).space at hm
  rw [hrestr i] at hm
  exact hm.2

omit [DecidableEq E] in
theorem exists_subdivision_piecewise_affine_comp {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ F]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (T : SimplicialComplex ℝ F) (hT : T.faces.Finite) (hmap : MapsTo f K.space T.space)
    (g : F → G)
    (hg : ∀ t ∈ T.faces, ∃ B : F →ᵃ[ℝ] G, EqOn g B (convexHull ℝ (t : Set F)))
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧ (∀ s ∈ L.faces, s.card ≤ d + 1) ∧
      ∀ s ∈ L.faces, ∃ C : E →ᵃ[ℝ] G,
        EqOn (g ∘ f) C (convexHull ℝ (s : Set E)) := by
  classical
  obtain ⟨L, hL, hspace, href, hdim, hmapface⟩ :=
    exists_subdivision_mapping_faces K hK f hf T hT hmap hd
  refine ⟨L, hL, hspace, href, hdim, ?_⟩
  intro s hs
  obtain ⟨r, hr, hsr⟩ := href s hs
  obtain ⟨A, hA⟩ := hf r hr
  obtain ⟨t, ht, hst⟩ := hmapface s hs
  obtain ⟨B, hB⟩ := hg t ht
  exact ⟨B.comp A, fun x hx => (hB (hst hx)).trans (congrArg B (hA (hsr hx)))⟩

end DifferentialGeometry.Topology.Engulfing
