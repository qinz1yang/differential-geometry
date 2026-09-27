/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorSpan_sup_ker_eq_top_of_mem_convexHull_level {s : Finset E} (ℓ : E →ₗ[ℝ] ℝ)
    {r : ℝ} (hs : ∀ v ∈ s, ℓ v ≠ r) {x : E} (hx : x ∈ convexHull ℝ (s : Set E))
    (hxr : ℓ x = r) : vectorSpan ℝ (s : Set E) ⊔ LinearMap.ker ℓ = ⊤ := by
  have hne : (s : Set E).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, convexHull_empty] at hx
    exact hx
  obtain ⟨v, hv⟩ := hne
  by_cases hconst : ∀ w ∈ s, ℓ w = ℓ v
  · have hconv : Convex ℝ {y : E | ℓ y = ℓ v} := by
      have h := convex_hyperplane (f := fun y : E => ℓ y) ℓ.isLinear (ℓ v)
      exact h
    have hsub : (s : Set E) ⊆ {y : E | ℓ y = ℓ v} := fun w hw => hconst w hw
    have hxv : ℓ x = ℓ v := convexHull_min hsub hconv hx
    exact absurd (hxv.symm.trans hxr) (hs v hv)
  · push Not at hconst
    obtain ⟨w, hw, hwv⟩ := hconst
    apply sup_ker_eq_top_of_apply_ne_zero _ ℓ
      (show w - v ∈ vectorSpan ℝ (s : Set E) from vsub_mem_vectorSpan ℝ hw hv)
    rw [map_sub]
    exact sub_ne_zero.mpr hwv

theorem card_le_one_of_subset_convexHull_level {s u : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) (hscard : s.card = 2) (ℓ : E →ₗ[ℝ] ℝ) {r : ℝ}
    (hsr : ∀ v ∈ s, ℓ v ≠ r) (hu : (u : Set E) ⊆ convexHull ℝ (s : Set E))
    (hur : ∀ y ∈ u, ℓ y = r) : u.card ≤ 1 := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hscard
  by_contra hcard
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (not_le.mp hcard)
  have hpab := hu hp
  have hqab := hu hq
  rw [Finset.coe_pair, convexHull_pair, segment_eq_image_lineMap] at hpab hqab
  obtain ⟨t, -, rfl⟩ := hpab
  obtain ⟨t', -, rfl⟩ := hqab
  have hpr := hur _ hp
  have hqr := hur _ hq
  simp only [AffineMap.lineMap_apply_module, map_add, map_smul, smul_eq_mul] at hpr hqr
  have har := hsr a (by simp)
  have hbr := hsr b (by simp)
  by_cases hla : ℓ a = ℓ b
  · rw [hla] at hpr
    have : ℓ b = r := by linarith
    exact hbr this
  · have htt : t = t' := by
      have h1 : (t - t') * (ℓ b - ℓ a) = 0 := by linarith
      rcases mul_eq_zero.mp h1 with h | h
      · linarith
      · exact absurd (by linarith) hla
    exact hpq (by rw [htt])

open Classical in
theorem exists_levelComplex_of_cofaces [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {n : ℕ} (hdimE : Module.finrank ℝ E = n + 1) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) {r : ℝ}
    (hr : ∀ v ∈ K.vertices, ℓ v ≠ r)
    (hcard : ∀ s ∈ K.faces, (convexHull ℝ (s : Set E) ∩ {x | ℓ x = r}).Nonempty → s.card ≤ 3)
    (W : Set E)
    (hcof : ∀ s ∈ K.faces, s.card = 2 → ∀ x ∈ openSimplex s, ℓ x = r →
      (x ∈ W → ∃ a, {w | w ∉ s ∧ insert w s ∈ K.faces} = {a}) ∧
      (x ∉ W → ∃ a b, a ≠ b ∧ {w | w ∉ s ∧ insert w s ∈ K.faces} = {a, b}))
    (htri : ∀ s ∈ K.faces, s.card = 3 → ∀ x ∈ openSimplex s, ℓ x = r → x ∉ W) :
    ∃ G : Geometry.SimplicialComplex ℝ E, G.faces.Finite ∧
      G.space = K.space ∩ {x | ℓ x = r} ∧ (∀ u ∈ G.faces, u.card ≤ 2) ∧
      (∀ x ∈ G.space ∩ W, {x} ∈ G.faces) ∧
      ∀ x, {x} ∈ G.faces →
        (x ∈ W → ∃ a, {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a}) ∧
        (x ∉ W → ∃ a b, a ≠ b ∧ {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a, b}) := by
  obtain ⟨T, hT, hTcard, hspace, hKT, -, hspan⟩ := exists_simplex_containing_fiber K hdimE ℓ hℓ r
  let L := simplexComplex T hT
  have : Finite L.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have ht : T ∈ L.faces := ⟨hTne, Finset.Subset.refl T⟩
  have hLspace : L.space = convexHull ℝ (T : Set E) := simplexComplex_space T hT hTne
  obtain ⟨G, hGfin, hGspace, hGcarrier⟩ := exists_triangulation_inter K L
  have : Finite G.faces := hGfin.to_subtype
  have hGlevel : G.space = K.space ∩ {x | ℓ x = r} := by rw [hGspace, hLspace, hspace]
  have htmax : ∀ u ∈ L.faces, T ⊆ u → u.card ≤ T.card := fun _ hu _ => Finset.card_le_card hu.2
  have hvert : ∀ v ∈ K.faces, ∀ w ∈ v, ℓ w ≠ r := fun v hv w hw =>
    hr w (K.down_closed hv (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty w))
  have hTrank : Module.finrank ℝ (vectorSpan ℝ (T : Set E)) = n := by
    have h := hT.finrank_vectorSpan (show Fintype.card T = n + 1 by
      simpa only [Fintype.card_coe] using hTcard)
    have hrange : Set.range ((↑) : T → E) = (T : Set E) := by ext y; simp
    rwa [hrange] at h
  have hfaceRank : ∀ v ∈ K.faces, Module.finrank ℝ (vectorSpan ℝ (v : Set E)) + 1 = v.card := by
    intro v hv
    obtain ⟨w, hw⟩ := K.nonempty_of_mem_faces hv
    have : Nonempty v := ⟨⟨w, hw⟩⟩
    have hrange : Set.range ((↑) : v → E) = (v : Set E) := by ext y; simp
    have h := (K.indep hv).finrank_vectorSpan_add_one
    change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : v → E))) + 1 = Fintype.card v at h
    rw [hrange] at h
    simpa only [Fintype.card_coe] using h
  have hsup : ∀ v ∈ K.faces, ∀ x ∈ convexHull ℝ (v : Set E), ℓ x = r →
      vectorSpan ℝ (v : Set E) ⊔ vectorSpan ℝ (T : Set E) = ⊤ := by
    intro v hv x hx hxr
    rw [hspan]
    exact vectorSpan_sup_ker_eq_top_of_mem_convexHull_level ℓ (hvert v hv) hx hxr
  have hGr : ∀ y ∈ G.space, ℓ y = r := fun y hy => by
    rw [hGlevel] at hy
    exact hy.2
  have hGcard : ∀ u ∈ G.faces, u.card ≤ 2 := by
    intro u hu
    obtain ⟨v, hv, z, hz, hsub⟩ := hGcarrier u hu
    obtain ⟨p, hp⟩ := G.nonempty_of_mem_faces hu
    have hpG : p ∈ G.space := G.subset_space hu hp
    have hpv : p ∈ convexHull ℝ (v : Set E) := (hsub (subset_convexHull ℝ _ hp)).1
    have htrans := hsup v hv p hpv (hGr p hpG)
    have huT : (u : Set E) ⊆ convexHull ℝ (T : Set E) :=
      ((subset_convexHull ℝ _).trans (hsub.trans inter_subset_right)).trans
        (convexHull_mono (Finset.coe_subset.mpr hz.2))
    have hus : (u : Set E) ⊆ convexHull ℝ (v : Set E) :=
      (subset_convexHull ℝ _).trans (hsub.trans inter_subset_left)
    have hsub' : (u : Set E) ⊆ (fun x : E => x + 0) '' convexHull ℝ (v : Set E) ∩
        convexHull ℝ (T : Set E) := by
      simpa only [add_zero, Set.image_id'] using Set.subset_inter hus huT
    have hbound := card_add_finrank_le_of_subset_transverse_faces K L hv ht
      (G.indep hu) (G.nonempty_of_mem_faces hu) 0 hsub' htrans
    have hvc := hcard v hv ⟨p, hpv, hGr p hpG⟩
    omega
  have hcarrierK : ∀ x ∈ G.space,
      ∃ s ∈ K.faces, x ∈ openSimplex s ∧ (s.card = 2 ∨ s.card = 3) := by
    intro x hx
    have hxK : x ∈ K.space := by
      rw [hGlevel] at hx
      exact hx.1
    obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hxK
    refine ⟨s, hs, hxs, ?_⟩
    have hs3 := hcard s hs ⟨x, openSimplex_subset_convexHull s hxs, hGr x hx⟩
    have hs1 : s.card ≠ 1 := by
      intro h1
      obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h1
      have hxw : x = w := by
        have h := openSimplex_subset_convexHull _ hxs
        simpa only [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] using h
      exact hr w hs (hxw ▸ hGr x hx)
    have hs0 : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
    omega
  refine ⟨G, hGfin, hGlevel, hGcard, ?_, ?_⟩
  · rintro x ⟨hx, hxW⟩
    obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex G hx
    obtain ⟨s, hs, hxs, hs23⟩ := hcarrierK x hx
    have hs2 : s.card = 2 := hs23.resolve_right fun h3 => htri s hs h3 x hxs (hGr x hx) hxW
    obtain ⟨v, hv, z, hz, hsub⟩ := hGcarrier u hu
    have hxv : x ∈ convexHull ℝ (v : Set E) :=
      (hsub (openSimplex_subset_convexHull u hxu)).1
    have hsv : s ⊆ v := face_subset_of_mem_openSimplex_of_mem_convexHull K hs hv hxs hxv
    have hus : (u : Set E) ⊆ convexHull ℝ (v : Set E) :=
      (subset_convexHull ℝ _).trans (hsub.trans inter_subset_left)
    have hus' : (u : Set E) ⊆ convexHull ℝ (s : Set E) :=
      subset_convexHull_of_mem_openSimplex (K.indep hv) hsv hus hxu
        (openSimplex_subset_convexHull s hxs)
    have hule := card_le_one_of_subset_convexHull_level (K.indep hs) hs2 ℓ (hvert s hs) hus'
      (fun y hy => hGr y (G.subset_space hu hy))
    obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp
      (le_antisymm hule (Finset.card_pos.mpr (G.nonempty_of_mem_faces hu)))
    have hxw : x = w := by
      have h := openSimplex_subset_convexHull _ hxu
      simpa only [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] using h
    rw [hxw]
    exact hu
  · intro x hxG
    have hx : x ∈ G.space := G.subset_space hxG (Finset.mem_singleton_self x)
    have hxr := hGr x hx
    have hxt : x ∈ openSimplex T := hKT (by rw [← hGlevel]; exact hx)
    obtain ⟨s, hs, hxs, hs23⟩ := hcarrierK x hx
    have hxsv : x ∈ convexHull ℝ (s : Set E) := openSimplex_subset_convexHull s hxs
    have hst := hsup s hs x hxsv hxr
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq
      (vectorSpan ℝ (s : Set E)) (vectorSpan ℝ (T : Set E))
    rw [hst, finrank_top, hTrank, hdimE] at hdim
    have hsR := hfaceRank s hs
    have hsbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1 := by
      intro u hu hsu
      have := hcard u hu ⟨x, convexHull_mono (Finset.coe_subset.mpr hsu) hxsv, hxr⟩
      omega
    rcases hs23 with hs2 | hs3
    · have hinf : Module.finrank ℝ
          (vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (T : Set E) : Submodule ℝ E) = 0 := by omega
      have htrans : IsCompl (vectorSpan ℝ (s : Set E)) (vectorSpan ℝ (T : Set E)) :=
        IsCompl.of_eq (Submodule.finrank_eq_zero.mp hinf) hst
      obtain ⟨hW, hnW⟩ := hcof s hs hs2 x hxs hxr
      refine ⟨fun hxW => ?_, fun hxW => ?_⟩
      · obtain ⟨a, ha⟩ := hW hxW
        have hac : a ∉ s ∧ insert a s ∈ K.faces := by
          change a ∈ {w | w ∉ s ∧ insert w s ∈ K.faces}
          rw [ha]
          exact Set.mem_singleton a
        obtain ⟨y, hy, hyuniq⟩ := existsUnique_neighbor_mem_transverse_coface K L G
          hGcard hGspace hGcarrier ht hsbound htmax hxs hxt hxG hac.1 hac.2 htrans
        refine ⟨y, Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hy.1, hy.2.1⟩, ?_⟩⟩
        rintro q ⟨hqx, hqG⟩
        obtain ⟨w, hw, -⟩ := existsUnique_transverse_coface_of_neighbor K L G hGcarrier hs ht
          hsbound htmax hxs hxt hqx hqG htrans.disjoint
        have hwa : w = a := by
          have hmem : w ∈ {w | w ∉ s ∧ insert w s ∈ K.faces} := ⟨hw.1, hw.2.1⟩
          rw [ha] at hmem
          exact hmem
        subst hwa
        exact hyuniq q ⟨hqx, hqG, hw.2.2⟩
      · obtain ⟨a, b, hab, habset⟩ := hnW hxW
        exact neighbors_eq_pair_of_transverse_cofaces K L G hGcard hGspace hGcarrier hs ht
          hsbound htmax hxs hxt hxG htrans hab habset
    · have hxW : x ∉ W := htri s hs hs3 x hxs hxr
      refine ⟨fun h => absurd h hxW, fun _ => ?_⟩
      have hinf : Module.finrank ℝ
          (vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (T : Set E) : Submodule ℝ E) = 1 := by omega
      have hsmax : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card := by
        intro u hu hsu
        have := hcard u hu ⟨x, convexHull_mono (Finset.coe_subset.mpr hsu) hxsv, hxr⟩
        omega
      exact neighbors_eq_pair_of_finrank_inter_eq_one K L G hGcard hGspace hGcarrier hs ht
        hsmax htmax hxs hxt hxG hinf

end DifferentialGeometry.Topology.PiecewiseLinear
