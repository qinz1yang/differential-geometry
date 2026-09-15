import DifferentialGeometry.Topology.PiecewiseLinear.SingularLocal
import DifferentialGeometry.Topology.PiecewiseLinear.ChartConjugate

open Set Topology Metric
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_small_isPL_homeomorph_generalPosition_in_chart
    {X : Type*} [MetricSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [HasGroupoid X (plGroupoid 3)]
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3)))
    (he : e ∈ (plGroupoid 3).maximalAtlas X)
    (K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    {U : Set X} (hU : IsOpen U) (hKU : K.space ⊆ e '' (e.source ∩ U))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (h : X ≃ₜ X) (G : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      IsPL 3 3 h ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
        MapsTo h e.source e.source ∧
        IsPLHomeomorphOn (e ∘ h ∘ e.symm) K.space ((e ∘ h ∘ e.symm) '' K.space) ∧
        G.faces.Finite ∧ G.space = (e ∘ h ∘ e.symm) '' K.space ∩ L.space ∧
        IsCombinatorialManifoldWithBoundary 1 G ∧
          ∀ z ∈ G.space, HasPLCrossingAt ((e ∘ h ∘ e.symm) '' K.space) L.space z := by
  let V := e '' (e.source ∩ U)
  have hV : IsOpen V := e.isOpen_image_source_inter hU
  have hVt : V ⊆ e.target := by
    rintro z ⟨x, hx, rfl⟩
    exact e.map_source hx.1
  have hcompact : IsCompact K.space := (isPolyhedron_space K).isCompact
  obtain ⟨r, hr, hrV⟩ := hcompact.exists_cthickening_subset_open hV hKU
  let C := cthickening r K.space
  let O := thickening r K.space
  have hC : IsCompact C := isCompact_of_isClosed_isBounded isClosed_cthickening
    hcompact.isBounded.cthickening
  have hCt : C ⊆ e.target := hrV.trans hVt
  have hOC : O ⊆ C := thickening_subset_cthickening r K.space
  obtain ⟨δ, hδ, hδbound⟩ := e.exists_uniform_conjugateMap_radius hC hCt hε
  obtain ⟨k, G, hk, hkclose, hkfix, hGfinite, hGspace, hGman, hGcross⟩ :=
    exists_small_homeomorph_generalPosition K L hK hL (by simp)
      (U := O) isOpen_thickening (self_subset_thickening hr K.space) hδ
  let k₀ : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3) :=
    { toFun := k
      invFun := Function.invFunOn k univ
      left_inv := fun z => hk.bijOn.invOn_invFunOn.1 (mem_univ z)
      right_inv := fun z => hk.bijOn.invOn_invFunOn.2 (mem_univ z)
      continuous_toFun := continuousOn_univ.mp hk.isPiecewiseAffineOn.continuousOn
      continuous_invFun := continuousOn_univ.mp hk.isPiecewiseAffineOn_invFunOn.continuousOn }
  have hkC : EqOn k₀ id Cᶜ := fun z hz => hkfix (fun hzO => hz (hOC hzO))
  obtain ⟨hkmap, hclose⟩ := hδbound k₀ (fun z _ => hkclose z) hkC
  let h := e.conjugateHomeomorph k₀ hC hCt hkC
  have hmap : MapsTo h e.source e.source := by
    intro x hx
    rw [show h x = e.conjugateMap k₀ x from rfl, e.conjugateMap_of_mem k₀ hx]
    exact e.map_target (hkmap (e.map_source hx))
  have hcoord : EqOn (e ∘ h ∘ e.symm) k K.space := by
    intro z hz
    have hzt := hVt (hKU hz)
    change e (e.conjugateMap k₀ (e.symm z)) = k z
    rw [e.conjugateMap_of_mem k₀ (e.map_target hzt), e.right_inv hzt, e.right_inv (hkmap hzt)]
    rfl
  have himage : (e ∘ h ∘ e.symm) '' K.space = k '' K.space := hcoord.image_eq
  refine ⟨h, G, isPL_conjugateHomeomorph e he k₀ hk.isPiecewiseAffineOn hC hCt hkC,
    hclose, ?_, hmap, ?_, hGfinite, hGspace.trans ?_, hGman, ?_⟩
  · intro x hx
    apply e.conjugateMap_eqOn_compl hkC
    rintro ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwz⟩ := hrV hz
    have heq : e.symm z = w := by rw [← hwz, e.left_inv hw.1]
    exact hx (heq.symm ▸ hw.2)
  · rw [himage]
    exact (hk.restrict (isPolyhedron_space K) (subset_univ _)).congr hcoord
  · rw [himage]
  · intro z hz
    rw [himage]
    exact hGcross z (hGspace ▸ hz)

open Classical in
theorem exists_small_isPLOn_doublePointSet_crossing_neighborhood_in_chart
    {d : ℕ} {X : Type*} [MetricSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [HasGroupoid X (plGroupoid 3)]
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin d))) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (f : EuclideanSpace ℝ (Fin d) → X)
    (hf : IsPLOn d 3 f K.space) (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ z, (K.space ∩ f ⁻¹' {z}).encard ≤ 2)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3)))
    (he : e ∈ (plGroupoid 3).maximalAtlas X)
    {y : X} (hy : y ∈ doublePointSet f K.space) (hye : y ∈ e.source)
    {V : Set X} (hV : V ∈ 𝓝 y) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : EuclideanSpace ℝ (Fin d) → X) (W : Set X)
      (G : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      IsPLOn d 3 g K.space ∧ (∀ x, dist (g x) (f x) < ε) ∧
        IsLocallyInjective (K.space.domRestrict g) ∧ (∀ z, (K.space ∩ g ⁻¹' {z}).encard ≤ 2) ∧
        (∀ z ∉ V, g ⁻¹' {z} = f ⁻¹' {z}) ∧ IsOpen W ∧ y ∈ W ∧ closure W ⊆ V ∧ W ⊆ e.source ∧
        G.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 1 G ∧
        (∀ z ∈ W, z ∈ doublePointSet g K.space ↔ e z ∈ G.space) ∧
          ∀ z ∈ W ∩ doublePointSet g K.space,
            HasPLDoubleCrossingAt (e ∘ g) (K.space ∩ g ⁻¹' e.source) (e z) := by
  have hfc : ContinuousOn f K.space := fun x hx => (hf x hx).continuousWithinAt
  obtain ⟨a, ha, b, hb, hab, hfa, hfb⟩ := hy
  obtain ⟨P, Q, B₀, U, hPQ, hP, hQ, _, hB₀Q, hPB₀, hinjP, _, hU, hyU, hUV, hseam, hinjQ,
    _, houter, _, _, _, _, hPa, hB₀b⟩ := exists_isPLBall_patches_at_fiber_pair K hK f hfc hloc hcard
      ha hb hab hfa hfb (A₀ := univ) (B₀ := univ) Filter.univ_mem Filter.univ_mem
      (Filter.inter_mem hV (e.open_source.mem_nhds hye))
  obtain ⟨A, Q₁, B, U₁, _, hA, _, hB, _, hAB, hinjA, hinjB, hU₁, hyU₁, hU₁U, _, _,
    hinner, hmapsU, hAP, hBB₀, _, _, _, _⟩ := exists_isPLBall_patches_at_fiber_pair K hK f hfc
      hloc hcard ha hb hab hfa hfb hPa hB₀b (hU.mem_nhds hyU)
  have hPK : P ⊆ K.space := hPQ ▸ subset_union_left
  have hQK : Q ⊆ K.space := hPQ ▸ subset_union_right
  have hAK : A ⊆ K.space := hAP.trans hPK
  have hBQ : B ⊆ Q := hBB₀.trans hB₀Q
  have hBK : B ⊆ K.space := hBQ.trans hQK
  have hPe : MapsTo f P e.source := fun x hx => (houter (Or.inl hx)).2
  have hAe : MapsTo f A e.source := fun x hx => hPe (hAP hx)
  have hBe : MapsTo f B e.source := fun x hx => (houter (Or.inr (hBB₀ hx))).2
  obtain ⟨M, hMfinite, _, hfA, _⟩ :=
    (hf.mono_of_isPolyhedron hA.isPolyhedron hAK).exists_isPLHomeomorphOn_chart_image
      hA.isPolyhedron hinjA e he hAe
  obtain ⟨N, hNfinite, _, hfB, _⟩ :=
    (hf.mono_of_isPolyhedron hB.isPolyhedron hBK).exists_isPLHomeomorphOn_chart_image
      hB.isPolyhedron hinjB e he hBe
  have : Finite M.faces := hMfinite.to_subtype
  have : Finite N.faces := hNfinite.to_subtype
  have hMman : IsCombinatorialManifoldWithBoundary 2 M :=
    (hA.of_isPLHomeomorphOn hfA).isCombinatorialManifoldWithBoundary
  have hNman : IsCombinatorialManifoldWithBoundary 2 N :=
    (hB.of_isPLHomeomorphOn hfB).isCombinatorialManifoldWithBoundary
  have hMU : M.space ⊆ e '' (e.source ∩ U) := by
    rw [← hfA.image_eq]
    rintro z ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨hAe hx, hmapsU (Or.inl hx)⟩, rfl⟩
  obtain ⟨η, hη, hηU⟩ := Metric.mem_nhds_iff.mp (hU₁.mem_nhds hyU₁)
  obtain ⟨h, G, hh, hclose, hfix, hmap, hcoord, hGfinite, hGspace, hGman, hcross⟩ :=
    exists_small_isPL_homeomorph_generalPosition_in_chart e he M N hMman hNman hU hMU (lt_min hε hη)
  have hfPQ : IsPLOn d 3 f (P ∪ Q) := by rwa [hPQ]
  have hlocPQ : IsLocallyInjective ((P ∪ Q).domRestrict f) := by rwa [hPQ]
  have hcardPQ : ∀ z, ((P ∪ Q) ∩ f ⁻¹' {z}).encard ≤ 2 := by rwa [hPQ]
  obtain ⟨g, hg, hgloc, hgcard, hgP, hgQ, hgOffP, hgfiber⟩ :=
    exists_isPLOn_postcomp_on_polyhedron_of_locallyInjective hfPQ hP.isPolyhedron hQ
      hlocPQ hcardPQ hinjP hh h.injective hfix hseam hinjQ
  rw [hPQ] at hg hgloc hgcard
  have hgAe : MapsTo g A e.source := by
    intro x hx
    rw [hgP (hAP hx)]
    exact hmap (hAe hx)
  have hgBe : MapsTo g B e.source := by
    intro x hx
    rw [hgQ (hBQ hx)]
    exact hBe hx
  have hgA : IsPLHomeomorphOn (e ∘ g) A ((e ∘ h ∘ e.symm) '' M.space) := by
    apply (hfA.trans hcoord).congr
    intro x hx
    change e (g x) = e (h (e.symm (e (f x))))
    rw [hgP (hAP hx), e.left_inv (hAe hx)]
    rfl
  have hgB : IsPLHomeomorphOn (e ∘ g) B N.space := by
    apply hfB.congr
    intro x hx
    exact congrArg e (hgQ (hBQ hx))
  let W := U₁ ∩ h.symm ⁻¹' U₁
  have hW : IsOpen W := hU₁.inter (hU₁.preimage h.symm.continuous)
  have hyj : h.symm y ∈ U₁ := by
    apply hηU
    rw [Metric.mem_ball, dist_comm]
    simpa only [h.apply_symm_apply] using (hclose (h.symm y)).trans_le (min_le_right _ _)
  have hWe : W ⊆ e.source := fun z hz => (hUV (subset_closure (hU₁U (subset_closure hz.1)))).2
  have hcover : ∀ z ∈ W, K.space ∩ g ⁻¹' {z} ⊆ A ∪ B := by
    intro z hz x hx
    by_cases hxP : x ∈ P
    · have hfx : f x = h.symm z := by
        apply h.injective
        rw [h.apply_symm_apply]
        exact (hgP hxP).symm.trans hx.2
      have hxAB := hinner (h.symm z) (subset_closure (show h.symm z ∈ U₁ from hz.2)) ⟨hx.1, hfx⟩
      rcases hxAB with hxA | hxB
      · exact Or.inl hxA
      · exact False.elim (Set.disjoint_left.mp hPB₀ hxP (hBB₀ hxB))
    · have hfx : f x = z := (hgOffP hxP).symm.trans hx.2
      exact Or.inr ((hinner z (subset_closure hz.1) ⟨hx.1, hfx⟩).resolve_left
        (fun hxA => hxP (hAP hxA)))
  let S := K.space ∩ g ⁻¹' e.source
  have hAS : A ⊆ S := fun x hx => ⟨hAK hx, hgAe hx⟩
  have hBS : B ⊆ S := fun x hx => ⟨hBK hx, hgBe hx⟩
  have hdouble (z : X) (hz : z ∈ e.source) :
      e z ∈ doublePointSet (e ∘ g) S ↔ z ∈ doublePointSet g K.space := by
    constructor
    · rintro ⟨a, ha, b, hb, hab, hga, hgb⟩
      exact ⟨a, ha.1, b, hb.1, hab, e.injOn ha.2 hz hga, e.injOn hb.2 hz hgb⟩
    · rintro ⟨a, ha, b, hb, hab, hga, hgb⟩
      exact ⟨a, ⟨ha, show g a ∈ e.source from hga.symm ▸ hz⟩,
        b, ⟨hb, show g b ∈ e.source from hgb.symm ▸ hz⟩, hab,
        congrArg e hga, congrArg e hgb⟩
  have hcovercoord (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ e.target) (hzW : e.symm z ∈ W) :
      S ∩ (e ∘ g) ⁻¹' {z} ⊆ A ∪ B := by
    rintro x ⟨hx, hxe⟩
    apply hcover (e.symm z) hzW
    exact ⟨hx.1, e.injOn hx.2 (e.map_target hz) (hxe.trans (e.right_inv hz).symm)⟩
  have hGdouble : ∀ z ∈ W, z ∈ doublePointSet g K.space ↔ e z ∈ G.space := by
    intro z hz
    rw [← hdouble z (hWe hz), hGspace, ← hgA.image_eq, ← hgB.image_eq]
    apply mem_doublePointSet_iff_mem_image_inter_of_injOn (e ∘ g) hAS hBS hAB
      hgA.bijOn.injOn hgB.bijOn.injOn
    exact hcovercoord (e z) (e.map_source (hWe hz)) (by rwa [e.left_inv (hWe hz)])
  refine ⟨g, W, G, hg, ?_, hgloc, hgcard, ?_, hW, ⟨hyU₁, hyj⟩, ?_, hWe,
    hGfinite, hGman, hGdouble, ?_⟩
  · intro x
    by_cases hxP : x ∈ P
    · rw [hgP hxP]
      exact (hclose (f x)).trans_le (min_le_left _ _)
    · rw [hgOffP hxP, dist_self]
      exact hε
  · intro z hz
    exact hgfiber z (fun hzU => hz (hUV (subset_closure hzU)).1)
  · intro z hz
    exact (hUV (subset_closure (hU₁U ((closure_mono inter_subset_left) hz)))).1
  · intro z hz
    have hgcont : ContinuousOn (e ∘ g) S := e.continuousOn.comp
      (fun x hx => (hg x hx.1).continuousWithinAt.mono inter_subset_left) (fun _ hx => hx.2)
    have hcrossz := hcross (e z) ((hGdouble z hz.1).mp hz.2)
    rw [← hgA.image_eq, ← hgB.image_eq] at hcrossz
    apply hasPLDoubleCrossingAt_of_crossing_and_eventually_fiber_subset hgcont hAS hBS
      hA.isPolyhedron.isClosed hB.isPolyhedron.isClosed hAB
      (by rwa [hgA.image_eq]) (by rwa [hgB.image_eq]) ((hdouble z (hWe hz.1)).mpr hz.2) hcrossz
    have hsym : ContinuousAt e.symm (e z) := e.continuousAt_symm (e.map_source (hWe hz.1))
    have hWneigh : W ∈ 𝓝 (e.symm (e z)) := by
      rw [e.left_inv (hWe hz.1)]
      exact hW.mem_nhds hz.1
    filter_upwards [hsym.preimage_mem_nhds hWneigh,
      e.open_target.mem_nhds (e.map_source (hWe hz.1))] with w hw hwt
    exact hcovercoord w hwt hw

end DifferentialGeometry.Topology.PiecewiseLinear
