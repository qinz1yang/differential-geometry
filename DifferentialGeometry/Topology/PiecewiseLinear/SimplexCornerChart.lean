import DifferentialGeometry.Topology.PiecewiseLinear.SimplexCornerExtension
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexPush

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

end DifferentialGeometry.Topology.PiecewiseLinear
