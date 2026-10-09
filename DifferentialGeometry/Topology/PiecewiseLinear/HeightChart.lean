/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingStability

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_height_preserving_chart_of_transverse_face
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    (ℓ : E →L[ℝ] ℝ) {s : Finset E} (hs : s ∈ K.faces) {x d : E}
    (hx : x ∈ openSimplex s) (hd : d ∈ vectorSpan ℝ (s : Set E)) (hℓd : ℓ d ≠ 0) :
    ∃ (h : E ≃ₜ E) (P : Submodule ℝ E), IsPLHomeomorphOn h univ univ ∧ h 0 = x ∧
      Module.finrank ℝ P = 2 ∧ (∃ v ∈ P, ℓ v ≠ 0) ∧
      (∀ y, ℓ (h y) = ℓ y + ℓ x) ∧
      ∀ᶠ y in 𝓝 x, y ∈ K.space ↔ y ∈ h '' (P : Set E) := by
  classical
  let V := vectorSpan ℝ (s : Set E)
  have hVrank : Module.finrank ℝ V + 1 = s.card := by
    obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
    let _ : Nonempty s := ⟨⟨v, hv⟩⟩
    have h := (K.indep hs).finrank_vectorSpan_add_one
    have hrange : Set.range ((↑) : s → E) = (s : Set E) := by ext y; simp
    change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : s → E))) + 1 = Fintype.card s at h
    rw [hrange] at h
    simpa only [Fintype.card_coe] using h
  have hVpos : 1 ≤ Module.finrank ℝ V := Submodule.one_le_finrank_iff.mpr (by
    intro hz
    have hd0 : d = 0 := by
      have hdV : d ∈ V := hd
      rwa [hz, Submodule.mem_bot] at hdV
    exact hℓd (by rw [hd0, map_zero]))
  have hcases : s.card = 2 ∨ s.card = 3 := by
    have hb := hK.card_le K hs
    omega
  rcases hcases with hsc | hsc
  · have hVdim : Module.finrank ℝ V = 1 := by omega
    let T := LinearMap.ker ℓ.toLinearMap
    have hℓ : ℓ.toLinearMap ≠ 0 := fun hz => hℓd (by
      change ℓ.toLinearMap d = 0
      rw [hz, LinearMap.zero_apply])
    have hker : Module.finrank ℝ T + 1 = Module.finrank ℝ E :=
      Module.Dual.finrank_ker_add_one_of_ne_zero hℓ
    have hsup : V ⊔ T = ⊤ := sup_ker_eq_top_of_apply_ne_zero V ℓ.toLinearMap hd hℓd
    have hinf : Module.finrank ℝ (V ⊓ T : Submodule ℝ E) = 0 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq V T
      rw [hsup, finrank_top, hVdim] at h
      omega
    have hcompl : IsCompl V T := IsCompl.of_eq (Submodule.finrank_eq_zero.mp hinf) hsup
    obtain ⟨a, b, hab, hpair⟩ := hK.codimension_one_cofaces K hs hsc
    have hbound : ∀ t ∈ K.faces, s ⊆ t → t.card ≤ s.card + 1 := by
      intro t ht _
      rw [hsc]
      exact hK.card_le K ht
    obtain ⟨u, F, huT, hu, hF, hFx, -, hlocal, hFdiff⟩ :=
      exists_isPLHomeomorphOn_linearize_coface_pair_sub_mem K hs hbound hx hab hpair T hcompl
    let P : Submodule ℝ E := V ⊔ Submodule.span ℝ {u}
    have huV : u ∉ V := fun huV => hu (Submodule.disjoint_def.mp hcompl.disjoint u huV huT)
    have hspan : Module.finrank ℝ (Submodule.span ℝ ({u} : Set E)) = 1 := finrank_span_singleton hu
    have hI0 : Module.finrank ℝ (V ⊓ Submodule.span ℝ {u} : Submodule ℝ E) = 0 :=
      Submodule.finrank_eq_zero.mpr (disjoint_iff.mp (Submodule.disjoint_span_singleton_of_notMem
          huV))
    have hPdim : Module.finrank ℝ P = 2 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq V (Submodule.span ℝ {u})
      change Module.finrank ℝ P + _ = _ at h
      omega
    let g := (Homeomorph.Set.univ E).symm.trans (hF.homeomorph.trans (Homeomorph.Set.univ E))
    have hg : IsPLHomeomorphOn g univ univ := hF
    have hgx : g x = 0 := hFx
    have hgs0 : g.symm 0 = x := g.injective ((g.apply_symm_apply 0).trans hgx.symm)
    have hlevel : ∀ y, ℓ (g y) = ℓ y - ℓ x := by
      intro y
      have hdiff : ℓ (g y - (y - x)) = 0 := hFdiff y
      rw [map_sub, map_sub, sub_eq_zero] at hdiff
      exact hdiff
    refine ⟨g.symm, P, hg.homeomorph_symm, hgs0, hPdim,
      ⟨d, Submodule.mem_sup_left hd, hℓd⟩, ?_, ?_⟩
    · intro y
      have h := hlevel (g.symm y)
      rw [g.apply_symm_apply] at h
      linarith
    · filter_upwards [hlocal] with y hy
      refine hy.trans ⟨fun hyp => ?_, ?_⟩
      · exact ⟨g y, hyp, g.symm_apply_apply y⟩
      · rintro ⟨z, hz, rfl⟩
        change g (g.symm z) ∈ P
        rw [g.apply_symm_apply]
        exact hz
  · have hVdim : Module.finrank ℝ V = 2 := by omega
    have hg := isPLHomeomorphOn_add_const x
    let h := (Homeomorph.Set.univ E).symm.trans (hg.homeomorph.trans (Homeomorph.Set.univ E))
    have hh0 : h 0 = x := zero_add x
    have himage : h '' (V : Set E) = {y | y - x ∈ V} := by
      apply Subset.antisymm
      · rintro _ ⟨z, hz, rfl⟩
        change (z + x) - x ∈ V
        rwa [add_sub_cancel_right]
      · intro y hy
        exact ⟨y - x, hy, sub_add_cancel y x⟩
    have hsmax : ∀ t ∈ K.faces, s ⊆ t → t.card ≤ s.card := by
      intro t ht _
      rw [hsc]
      exact hK.card_le K ht
    refine ⟨h, V, hg, hh0, hVdim, ⟨d, hd, hℓd⟩, fun y => ℓ.map_add y x, ?_⟩
    rw [himage]
    exact eventually_mem_space_iff_sub_mem_vectorSpan K hs hsmax hx

theorem eventually_hasPLCrossingAt_image_fiber_of_transverse_face
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ) {s : Finset E} (hs : s ∈ K.faces)
    {x d : E} (hx : x ∈ openSimplex s) (hd : d ∈ vectorSpan ℝ (s : Set E)) (hℓd : ℓ d ≠ 0)
    (H : E ≃ₜ E) (hH : IsPLHomeomorphOn H univ univ) (hheight : ∀ y, ℓ (H y) = ℓ y) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, HasPLCrossingAt (H '' K.space) {y | f y = f (H x)} (H x) := by
  obtain ⟨g, P, hg, hg0, hP, ⟨v, hv, hℓv⟩, hglevel, hlocal⟩ :=
    exists_height_preserving_chart_of_transverse_face K hK ℓ hs hx hd hℓd
  let e : E ≃ₜ E := g.trans H
  have he : IsPLHomeomorphOn e univ univ := hg.trans hH
  have he0 : e 0 = H x := by change H (g 0) = H x; rw [hg0]
  have heP : e '' (P : Set E) = H '' (g '' (P : Set E)) := image_comp H g P
  have heheight : ∀ᶠ y in 𝓝 0, ℓ (e y) = ℓ y + ℓ (e 0) :=
    Filter.Eventually.of_forall fun y => by
      change ℓ (H (g y)) = ℓ y + ℓ (H (g 0))
      rw [hheight, hheight, hg0, hglevel]
  have hinv : Filter.Tendsto H.symm (𝓝 (H x)) (𝓝 x) := by
    simpa only [H.symm_apply_apply] using (H.symm.continuous.continuousAt (x := H x)).tendsto
  have hS : ∀ᶠ y in 𝓝 (e 0), y ∈ H '' K.space ↔ y ∈ e '' (P : Set E) := by
    rw [he0, heP]
    filter_upwards [hinv.eventually hlocal] with y hy
    have himage (A : Set E) : y ∈ H '' A ↔ H.symm y ∈ A := by
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa only [H.symm_apply_apply] using hz
      · intro hz
        exact ⟨H.symm y, hz, H.apply_symm_apply y⟩
    rwa [himage, himage]
  have hc := eventually_hasPLCrossingAt_of_height_preserving_chart e he P hP hdimE ℓ hv hℓv heheight
      hS
  rwa [he0] at hc

theorem eventually_hasPLCrossingAt_image_fiber_of_notMem_vertices
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ) (hinj : Set.InjOn ℓ K.vertices)
    {x : E} (hx : x ∈ K.space) (hxv : x ∉ K.vertices)
    (H : E ≃ₜ E) (hH : IsPLHomeomorphOn H univ univ) (hheight : ∀ y, ℓ (H y) = ℓ y) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, HasPLCrossingAt (H '' K.space) {y | f y = f (H x)} (H x) := by
  classical
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hx
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp
    (one_lt_card_of_mem_openSimplex_of_notMem_vertices K hs hxs hxv)
  have habspan : a - b ∈ vectorSpan ℝ (s : Set E) := vsub_mem_vectorSpan ℝ ha hb
  have hne : ℓ (a - b) ≠ 0 := by
    rw [map_sub, sub_ne_zero]
    intro heq
    exact hab (hinj (K.down_closed hs (Finset.singleton_subset_iff.mpr ha)
        (Finset.singleton_nonempty a)) (K.down_closed hs (Finset.singleton_subset_iff.mpr hb)
        (Finset.singleton_nonempty b)) heq)
  exact eventually_hasPLCrossingAt_image_fiber_of_transverse_face K hK hdimE ℓ hs hxs habspan hne H
      hH hheight

end DifferentialGeometry.Topology.PiecewiseLinear
