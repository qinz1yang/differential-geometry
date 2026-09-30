import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.PolyhedralMap
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Geometry.FinitePolyhedra

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [DecidableEq E] [DecidableEq F]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [DecidableEq E] in
theorem facewise_image_independent (K : SimplicialComplex ℝ E) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ K.faces, InjOn f (convexHull ℝ (s : Set E)))
    {s : Finset E} (hs : s ∈ K.faces) :
    AffineIndependent ℝ (Subtype.val : s.image f → F) := by
  classical
  obtain ⟨A, hA⟩ := hf s hs
  have hAi : InjOn A (convexHull ℝ (s : Set E)) := by
    intro x hx y hy hxy
    exact hinj s hs hx hy ((hA hx).trans (hxy.trans (hA hy).symm))
  have hindex : AffineIndependent ℝ (fun x : s => f x) := by
    convert affineIndependent_of_injOn_convexHull (K.indep hs) A hAi using 1
    funext x
    exact hA (subset_convexHull ℝ _ x.property)
  have hr : Set.range (fun x : s => f x) = (s.image f : Set F) := by
    ext y
    exact ⟨fun ⟨x, hx⟩ => Finset.mem_image.mpr ⟨x.val, x.property, hx⟩,
      fun hy => by obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy; exact ⟨⟨x, hx⟩, hxy⟩⟩
  have h := hindex.range
  rwa [hr] at h

omit [DecidableEq E] [DecidableEq F] in
theorem exists_compatible_image_triangulation [FiniteDimensional ℝ F]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ K.faces, InjOn f (convexHull ℝ (s : Set E)))
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ T : SimplicialComplex ℝ F, T.faces.Finite ∧ T.space = f '' K.space ∧
      (∀ t ∈ T.faces, t.card ≤ d + 1) ∧
      (∀ s ∈ K.faces, (vertexRestriction T (f '' convexHull ℝ (s : Set E))).space =
        f '' convexHull ℝ (s : Set E)) ∧
      (∀ t ∈ T.faces, ∃ s ∈ K.faces,
        convexHull ℝ (t : Set F) ⊆ f '' convexHull ℝ (s : Set E)) := by
  classical
  let := hK.fintype
  let V : K.faces → Finset F := fun s => s.val.image f
  have hV (s : K.faces) : AffineIndependent ℝ (Subtype.val : V s → F) :=
    facewise_image_independent K f hf hinj s.property
  have himage (s : K.faces) : f '' convexHull ℝ (s.val : Set E) = convexHull ℝ (V s : Set F) := by
    obtain ⟨A, hA⟩ := hf s.val s.property
    simpa only [V, Finset.coe_image] using image_convexHull_eq_of_eqOn_affineMap f A hA
  obtain ⟨T₀, hT₀, hspace₀, hparent₀⟩ := exists_complex_finite_convexHulls V
  have hdim₀ : ∀ t ∈ T₀.faces, t.card ≤ d + 1 := by
    intro t ht
    obtain ⟨s, hts⟩ := hparent₀ t ht
    exact ((T₀.indep ht).card_le_card_of_subset_affineSpan
      (fun x hx => convexHull_subset_affineSpan _ (hts (subset_convexHull ℝ _ hx)))).trans
      (Finset.card_image_le.trans (hd s.val s.property))
  obtain ⟨T, hT, hspace, href, hdim, hrestr⟩ :=
    exists_subdivision_containing_simplices T₀ hT₀ V hV hdim₀
  have hT₀image : T₀.space = f '' K.space := by
    rw [hspace₀]
    ext y
    constructor
    · intro hy
      obtain ⟨s, hs⟩ := mem_iUnion.mp hy
      rw [← himage s] at hs
      exact image_mono (K.convexHull_subset_space s.property) hs
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
      exact mem_iUnion.mpr ⟨⟨s, hs⟩, (himage ⟨s, hs⟩).subset (mem_image_of_mem _ hxs)⟩
  refine ⟨T, hT, hspace.trans hT₀image, hdim, ?_, ?_⟩
  · intro s hs
    rw [himage ⟨s, hs⟩, hrestr ⟨s, hs⟩, inter_eq_right.mpr]
    rw [hspace₀]
    exact subset_iUnion (fun i => convexHull ℝ (V i : Set F)) ⟨s, hs⟩
  · intro t ht
    obtain ⟨u, hu, htu⟩ := href t ht
    obtain ⟨s, hus⟩ := hparent₀ u hu
    exact ⟨s.val, s.property, (htu.trans hus).trans (himage s).symm.subset⟩

structure FacewiseAffineInverse (K : SimplicialComplex ℝ E) (f : E → F) where
  inverse : K.faces → F →ᵃ[ℝ] E
  left_inverse : ∀ s : K.faces, ∀ x ∈ convexHull ℝ (s.val : Set E), inverse s (f x) = x

namespace FacewiseAffineInverse

variable {K : SimplicialComplex ℝ E} {f : E → F}

omit [DecidableEq E] [DecidableEq F] in
theorem map_mem (B : FacewiseAffineInverse K f) (s : K.faces)
    {y : F} (hy : y ∈ f '' convexHull ℝ (s.val : Set E)) :
    B.inverse s y ∈ convexHull ℝ (s.val : Set E) := by
  classical
  obtain ⟨x, hx, rfl⟩ := hy
  rwa [B.left_inverse s x hx]

omit [DecidableEq E] [DecidableEq F] in
theorem right_inverse (B : FacewiseAffineInverse K f) (s : K.faces)
    {y : F} (hy : y ∈ f '' convexHull ℝ (s.val : Set E)) :
    f (B.inverse s y) = y := by
  classical
  obtain ⟨x, hx, rfl⟩ := hy
  rw [B.left_inverse s x hx]

omit [DecidableEq E] [DecidableEq F] in
theorem injOn (B : FacewiseAffineInverse K f) (s : K.faces) :
    InjOn (B.inverse s) (f '' convexHull ℝ (s.val : Set E)) := by
  classical
  intro x hx y hy hxy
  have he := congrArg f hxy
  rwa [B.right_inverse s hx, B.right_inverse s hy] at he

end FacewiseAffineInverse

omit [DecidableEq E] [DecidableEq F] in
theorem exists_facewiseAffineInverse (K : SimplicialComplex ℝ E) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ K.faces, InjOn f (convexHull ℝ (s : Set E))) :
    Nonempty (FacewiseAffineInverse K f) := by
  classical
  have hex (s : K.faces) : ∃ B : F →ᵃ[ℝ] E,
      ∀ x ∈ convexHull ℝ (s.val : Set E), B (f x) = x := by
    obtain ⟨A, hA⟩ := hf s.val s.property
    have hAi : InjOn A (convexHull ℝ (s.val : Set E)) := by
      intro x hx y hy hxy
      exact hinj s.val s.property hx hy ((hA hx).trans (hxy.trans (hA hy).symm))
    obtain ⟨B, hBA, _⟩ := exists_affine_inverse_on_affineSpan (K.nonempty_of_mem_faces s.property)
      A (affineIndependent_of_injOn_convexHull (K.indep s.property) A hAi)
    exact ⟨B, fun x hx => by rw [hA hx]; exact hBA x (convexHull_subset_affineSpan _ hx)⟩
  choose B hB using hex
  exact ⟨⟨B, hB⟩⟩

end

end DifferentialGeometry.Topology.Engulfing
