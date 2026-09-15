import DifferentialGeometry.Topology.PiecewiseLinear.SimplexCornerExtension
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexPush
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexAffine

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem simplexAvoiding_erase_eq_coneComplex [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) {a : E} (ha : a ∈ T)
    (hne : (T.erase a).Nonempty)
    (hB : IsConeBase a (simplexBoundary (T.erase a)
      (affineIndependent_of_subset hT (Finset.erase_subset a T)))) :
    simplexAvoiding T hT {T.erase a} = coneComplex hB := by
  have hB' : IsConeBase a (simplexAvoiding (T.erase a)
      (affineIndependent_of_subset hT (Finset.erase_subset a T)) {T.erase a}) := by
    rw [simplexAvoiding_singleton_self]
    exact hB
  have h := simplexAvoiding_singleton_eq_coneComplex hT ha (Finset.notMem_erase a T) hne hB'
  simpa only [simplexAvoiding_singleton_self] using h

open Classical in
theorem isPLHomeomorphOn_simplicialMap_simplex_vertex_star [FiniteDimensional ℝ E] [dE : DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : 3 ≤ T.card)
    {a : E} (ha : a ∈ T) :
    IsPLHomeomorphOn
      (simplicialMap (starComplex (simplexBoundary T hT) a)
        (Function.update id a ((T.erase a).centroid ℝ id)))
      (starComplex (simplexBoundary T hT) a).space
      (convexHull ℝ ((T.erase a : Finset E) : Set E)) := by
  cases Subsingleton.elim dE (Classical.decEq E)
  let F := T.erase a
  let hF := affineIndependent_of_subset hT (Finset.erase_subset a T)
  let B := simplexBoundary F hF
  let c := F.centroid ℝ id
  let φ : E → E := Function.update id a c
  have hFcard : 2 ≤ F.card := by
    dsimp [F]
    rw [Finset.card_erase_of_mem ha]
    omega
  have hFne : F.Nonempty := Finset.card_pos.mp (by omega)
  have haF : a ∉ F := Finset.notMem_erase a T
  have hind : AffineIndependent ℝ ((↑) : ↥(insert a F : Finset E) → E) := by
    dsimp [F]
    rw [Finset.insert_erase ha]
    exact hT
  let haB : IsConeBase a B := (isConeBase_simplexComplex F hF haF hind).of_faces_subset
    (simplexBoundary_faces_subset_simplexComplex F hF)
  have hc : c ∈ openSimplex F := centroid_mem_openSimplex hFne
  let hcB : IsConeBase c B := isConeBase_simplexBoundary hF hFcard hc
  have : Finite B.faces := (simplexBoundary_faces_finite F hF).to_subtype
  have hidpl : IsPiecewiseAffineOn (id : E → E) B.space :=
    (isPiecewiseAffineOn_id isOpen_univ).mono_of_isPolyhedron (isPolyhedron_space B) (subset_univ _)
  have hid : IsPLHomeomorphOn (id : E → E) B.space B.space :=
    ⟨bijOn_id _, hidpl, hidpl.congr fun _ hx => (bijOn_id B.space).invOn_invFunOn.1 hx⟩
  obtain ⟨g, hg, -, hga, hgrad⟩ := exists_isPLHomeomorphOn_coneComplex haB hcB hid
  have hφa : φ a = c := Function.update_self _ _ _
  have hφB : ∀ σ ∈ B.faces, ∀ v ∈ σ, φ v = id v := by
    intro σ hσ v hv
    exact Function.update_of_ne (ne_of_mem_of_not_mem hv (haB.notMem_face hσ)) _ _
  have hgφ : EqOn (simplicialMap (coneComplex haB) φ) g (coneComplex haB).space := by
    intro x hx
    rcases (mem_coneComplex_space_iff haB).mp hx with hxa | ⟨z, hz, r, hr, hr', rfl⟩
    · rw [hxa, hga, simplicialMap_coneComplex_apex haB hφa]
    · rw [hgrad z hz r hr.le hr']
      exact simplicialMap_coneComplex_eq_of_mem_space haB hφa
        (fun _ _ => ⟨AffineMap.id ℝ E, fun _ _ => rfl⟩) hφB hz hr.le hr'
  have hpl := hg.congr hgφ
  have hsource : starComplex (simplexBoundary T hT) a = coneComplex haB := by
    rw [← simplexAvoiding_erase_eq_starComplex T hT ha]
    exact simplexAvoiding_erase_eq_coneComplex T hT ha hFne haB
  have htarget : (coneComplex hcB).space = convexHull ℝ (F : Set E) :=
    coneComplex_simplexBoundary_space hF hFcard hc
  rw [← hsource, htarget] at hpl
  exact hpl

theorem eqOn_simplicialMap_simplex_vertex_star_boundary [DecidableEq E]
    (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) {a : E} (ha : a ∈ T) :
    EqOn (simplicialMap (starComplex (simplexBoundary T hT) a)
      (Function.update id a ((T.erase a).centroid ℝ id))) id
      (simplexBoundary (T.erase a)
        (affineIndependent_of_subset hT (Finset.erase_subset a T))).space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := (simplexBoundary (T.erase a) _).mem_space_iff.mp hx
  have hsL : s ∈ (starComplex (simplexBoundary T hT) a).faces := by
    rw [← simplexAvoiding_erase_eq_starComplex T hT ha]
    exact simplexBoundary_erase_faces_subset_simplexAvoiding T hT a hs
  rw [simplicialMap_eq_of_mem _ _ hsL hxs]
  change ∑ v ∈ s, weights s x v • Function.update id a ((T.erase a).centroid ℝ id) v = x
  rw [Finset.sum_congr rfl (fun v hv => by
    rw [Function.update_of_ne (Finset.mem_erase.mp (hs.1 hv)).1, id_eq])]
  exact sum_weights_smul hxs

theorem exists_isPLHomeomorphOn_simplex_vertex_star_conjugate [FiniteDimensional ℝ E]
    [DecidableEq E] (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : 3 ≤ T.card) (hspan : affineSpan ℝ (T : Set E) = ⊤) {a : E} (ha : a ∈ T)
    {f : E → E} (hf : IsPLHomeomorphOn f (convexHull ℝ ((T.erase a : Finset E) : Set E))
      (convexHull ℝ ((T.erase a : Finset E) : Set E)))
    (hfix : EqOn f id (simplexBoundary (T.erase a)
      (affineIndependent_of_subset hT (Finset.erase_subset a T))).space)
    {U : Set E} (hU : IsOpen U) (hTU : convexHull ℝ (T : Set E) ⊆ U) :
    let g := simplicialMap (starComplex (simplexBoundary T hT) a)
      (Function.update id a ((T.erase a).centroid ℝ id))
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧
      h '' convexHull ℝ (T : Set E) = convexHull ℝ (T : Set E) ∧
      EqOn h (Function.invFunOn g (starComplex (simplexBoundary T hT) a).space ∘ f ∘ g)
        (starComplex (simplexBoundary T hT) a).space ∧ EqOn h id Uᶜ := by
  intro g
  have hg := isPLHomeomorphOn_simplicialMap_simplex_vertex_star T hT hcard ha
  have hgfix := eqOn_simplicialMap_simplex_vertex_star_boundary T hT ha
  have hBL : (simplexBoundary (T.erase a)
      (affineIndependent_of_subset hT (Finset.erase_subset a T))).space ⊆
      (starComplex (simplexBoundary T hT) a).space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := (simplexBoundary (T.erase a) _).mem_space_iff.mp hx
    rw [← simplexAvoiding_erase_eq_starComplex T hT ha]
    exact (simplexAvoiding T hT {T.erase a}).convexHull_subset_space
      (simplexBoundary_erase_faces_subset_simplexAvoiding T hT a hs) hxs
  have hconj := (hg.trans hf).trans hg.symm
  have hconjfix : EqOn
      (Function.invFunOn g (starComplex (simplexBoundary T hT) a).space ∘ f ∘ g) id
      (simplexBoundary (T.erase a)
        (affineIndependent_of_subset hT (Finset.erase_subset a T))).space := by
    intro x hx
    change Function.invFunOn g (starComplex (simplexBoundary T hT) a).space (f (g x)) = x
    have hgx : g x = x := hgfix hx
    rw [hgx, hfix hx, id_eq]
    have hinv : Function.invFunOn g (starComplex (simplexBoundary T hT) a).space (g x) = x :=
      hg.bijOn.invOn_invFunOn.1 (hBL hx)
    rwa [hgx] at hinv
  exact exists_isPLHomeomorphOn_extension_simplex_vertex_star T hT (by omega) hspan ha
    hconj hconjfix hU hTU

theorem exists_isPLHomeomorphOn_simplex_vertex_star_to_simplex {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [DecidableEq E] (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    {n : ℕ} (hTcard : T.card = n + 3) {a : E} (ha : a ∈ T)
    (S : Finset F) (hS : AffineIndependent ℝ ((↑) : S → F)) (hScard : S.card = n + 2) :
    ∃ f : E → F, IsPLHomeomorphOn f (starComplex (simplexBoundary T hT) a).space
      (convexHull ℝ (S : Set F)) ∧
      (∀ s ∈ (starComplex (simplexBoundary T hT) a).faces,
        ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E))) ∧
      f '' (simplexBoundary (T.erase a)
        (affineIndependent_of_subset hT (Finset.erase_subset a T))).space =
        (simplexBoundary S hS).space ∧
      f '' openStar (simplexBoundary T hT) a = openSimplex S := by
  let L := starComplex (simplexBoundary T hT) a
  let g := simplicialMap L (Function.update id a ((T.erase a).centroid ℝ id))
  have hFcard : (T.erase a).card = n + 2 := by
    rw [Finset.card_erase_of_mem ha, hTcard]
    omega
  have hg : IsPLHomeomorphOn g L.space (convexHull ℝ ((T.erase a : Finset E) : Set E)) :=
    isPLHomeomorphOn_simplicialMap_simplex_vertex_star T hT (by omega) ha
  obtain ⟨A, hA⟩ := exists_isPLHomeomorphOn_affine_of_card_eq
    (affineIndependent_of_subset hT (Finset.erase_subset a T)) hS (hFcard.trans hScard.symm)
  let B := (simplexBoundary (T.erase a)
    (affineIndependent_of_subset hT (Finset.erase_subset a T))).space
  have hfix := eqOn_simplicialMap_simplex_vertex_star_boundary T hT ha
  have hgB : g '' B = B := by rw [hfix.image_eq, image_id]
  have hboundary : (A ∘ g) '' B = (simplexBoundary S hS).space := by
    have himage := image_simplexBoundary_of_isPLHomeomorphOn
      (affineIndependent_of_subset hT (Finset.erase_subset a T)) hS hFcard hScard hA
    calc
      (A ∘ g) '' B = A '' (g '' B) := (image_image A g B).symm
      _ = A '' B := congrArg (Set.image A) hgB
      _ = _ := himage
  have hpl := hg.trans hA
  refine ⟨A ∘ g, hpl, ?_, hboundary, ?_⟩
  · intro s hs
    obtain ⟨C, hC⟩ := exists_affineMap_eqOn_simplicialMap L
      (Function.update id a ((T.erase a).centroid ℝ id)) hs
    exact ⟨A.comp C, fun x hx => congrArg A (hC hx)⟩
  · have hBL : B ⊆ L.space := by
      rw [show L = simplexAvoiding T hT {T.erase a} from
        (simplexAvoiding_erase_eq_starComplex T hT ha).symm]
      exact space_mono_of_faces_subset (simplexBoundary_erase_faces_subset_simplexAvoiding T hT a)
    rw [openStar_simplexBoundary_eq_sdiff_boundary T hT (by omega) ha,
      hpl.bijOn.injOn.image_sdiff_subset hBL, hpl.image_eq, hboundary,
      ← openSimplex_eq_sdiff_simplexBoundary S hS]

theorem exists_isPLHomeomorphOn_extension_simplex_vertex_star_of_chart {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [DecidableEq E] (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : 2 ≤ T.card) (hspan : affineSpan ℝ (T : Set E) = ⊤) {a : E} (ha : a ∈ T)
    {f : E → F} {Q : Set F}
    (hf : IsPLHomeomorphOn f (starComplex (simplexBoundary T hT) a).space Q)
    {g : F → F} (hg : IsPLHomeomorphOn g Q Q)
    (hfix : ∀ x ∈ (simplexBoundary (T.erase a)
      (affineIndependent_of_subset hT (Finset.erase_subset a T))).space, g (f x) = f x)
    {U : Set E} (hU : IsOpen U) (hTU : convexHull ℝ (T : Set E) ⊆ U) :
    ∃ h : E ≃ₜ E, IsPLHomeomorphOn h univ univ ∧
      h '' convexHull ℝ (T : Set E) = convexHull ℝ (T : Set E) ∧
      EqOn h (Function.invFunOn f (starComplex (simplexBoundary T hT) a).space ∘ g ∘ f)
        (starComplex (simplexBoundary T hT) a).space ∧
      EqOn h id (convexHull ℝ ((T.erase a : Finset E) : Set E)) ∧ EqOn h id Uᶜ ∧
      ∀ D : Set E, D ⊆ (simplexBoundary T hT).space →
        h '' D = Function.invFunOn f (starComplex (simplexBoundary T hT) a).space ''
          (g '' (f '' (D ∩ (starComplex (simplexBoundary T hT) a).space))) ∪
            (D \ (starComplex (simplexBoundary T hT) a).space) := by
  have hBL : (simplexBoundary (T.erase a)
      (affineIndependent_of_subset hT (Finset.erase_subset a T))).space ⊆
      (starComplex (simplexBoundary T hT) a).space := by
    rw [← simplexAvoiding_erase_eq_starComplex T hT ha]
    exact space_mono_of_faces_subset (simplexBoundary_erase_faces_subset_simplexAvoiding T hT a)
  have hconj := (hf.trans hg).trans hf.symm
  have hconjfix : EqOn
      (Function.invFunOn f (starComplex (simplexBoundary T hT) a).space ∘ g ∘ f) id
      (simplexBoundary (T.erase a)
        (affineIndependent_of_subset hT (Finset.erase_subset a T))).space := by
    intro x hx
    change Function.invFunOn f (starComplex (simplexBoundary T hT) a).space (g (f x)) = x
    rw [hfix x hx]
    exact hf.bijOn.invOn_invFunOn.1 (hBL hx)
  obtain ⟨h, hh, hC, hhf, hhF, hhU⟩ :=
    exists_isPLHomeomorphOn_extension_simplex_vertex_star_fixing_opposite_face
      T hT hcard hspan ha hconj hconjfix hU hTU
  refine ⟨h, hh, hC, hhf, hhF, hhU, ?_⟩
  intro D hD
  let L := (starComplex (simplexBoundary T hT) a).space
  have hleft : h '' (D ∩ L) = Function.invFunOn f L '' (g '' (f '' (D ∩ L))) := by
    rw [(hhf.mono inter_subset_right).image_eq]
    simp only [image_image, Function.comp_def, L]
  have hrightfix : EqOn h id (D \ L) := by
    intro x hx
    apply hhF
    have hxB := hD hx.1
    rw [simplexBoundary_space_eq_starComplex_union_opposite_face T hT hcard ha] at hxB
    exact hxB.resolve_left hx.2
  have hright : h '' (D \ L) = D \ L := by rw [hrightfix.image_eq, image_id]
  calc
    h '' D = h '' ((D ∩ L) ∪ (D \ L)) :=
      congrArg (Set.image h) (inter_union_sdiff D L).symm
    _ = _ := by rw [image_union, hleft, hright]

theorem exists_isPLHomeomorphOn_simplex_vertex_star_euclidean [FiniteDimensional ℝ E]
    [DecidableEq E] (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    {n : ℕ} (hTcard : T.card = n + 3) {a : E} (ha : a ∈ T) :
    ∃ (S : Finset (EuclideanSpace ℝ (Fin (n + 1)))) (f : E → EuclideanSpace ℝ (Fin (n + 1))),
      AffineIndependent ℝ ((↑) : S → EuclideanSpace ℝ (Fin (n + 1))) ∧ S.card = n + 2 ∧
      IsPLHomeomorphOn f (starComplex (simplexBoundary T hT) a).space (convexHull ℝ (S : Set _)) ∧
      (∀ s ∈ (starComplex (simplexBoundary T hT) a).faces,
        ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin (n + 1)), EqOn f A (convexHull ℝ (s : Set E))) ∧
      f '' (simplexBoundary (T.erase a)
        (affineIndependent_of_subset hT (Finset.erase_subset a T))).space =
        frontier (convexHull ℝ (S : Set _)) ∧
      f '' openStar (simplexBoundary T hT) a = interior (convexHull ℝ (S : Set _)) := by
  obtain ⟨S, hS, hScard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (n := n) (by simp) (0 : EuclideanSpace ℝ (Fin (n + 1))) Filter.univ_mem
  obtain ⟨f, hf, hAff, hB, hopen⟩ :=
    exists_isPLHomeomorphOn_simplex_vertex_star_to_simplex T hT hTcard ha S hS hScard
  have hspan : affineSpan ℝ (S : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ⊤ := by
    have h := hS.affineSpan_eq_top_iff_card_eq_finrank_add_one
    rw [Subtype.range_coe] at h
    exact h.mpr (by simpa using hScard)
  have hfront : (simplexBoundary S hS).space = frontier (convexHull ℝ (S : Set _)) := by
    classical
    rw [simplexBoundary_space S hS (by omega), frontier_convexHull_eq_biUnion_erase S hS hspan]
  have hopenS : openSimplex S = interior (convexHull ℝ (S : Set _)) := by
    rw [openSimplex_eq_sdiff_simplexBoundary S hS, hfront,
      (S.finite_toSet.isCompact_convexHull ℝ).isClosed.frontier_eq]
    ext x
    constructor
    · rintro ⟨hx, hnot⟩
      by_contra hxi
      exact hnot ⟨hx, hxi⟩
    · intro hx
      exact ⟨interior_subset hx, fun h => h.2 hx⟩
  exact ⟨S, f, hS, hScard, hf, hAff, hB.trans hfront, hopen.trans hopenS⟩

end DifferentialGeometry.Topology.PiecewiseLinear
