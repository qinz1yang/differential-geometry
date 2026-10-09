/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeSimplexSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialImage
import DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldConnectivity
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexComplex
import Mathlib.Topology.Algebra.Module.PerfectSpace

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
private theorem centroid_notMem_vertices (K : Geometry.SimplicialComplex ℝ E)
    {t : Finset E} (ht : t ∈ K.faces) (hcard : 1 < t.card) :
    t.centroid ℝ id ∉ K.vertices := by
  intro hp
  have hsub := face_subset_of_mem_openSimplex_of_mem_convexHull K ht hp
    (centroid_mem_openSimplex (K.nonempty_of_mem_faces ht))
    (by simp)
  have := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at this
  omega

open Classical in
theorem image_convexHull_simplicialMap_of_finiteDimensional [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (φ : E → F)
    {s : Finset E} (hs : s ∈ K.faces) :
    simplicialMap K φ '' convexHull ℝ (s : Set E) =
      convexHull ℝ ((s.image φ : Finset F) : Set F) := by
  obtain ⟨A, hA⟩ := exists_affineMap_eqOn_simplicialMap K φ hs
  have hvertices : EqOn A φ (s : Set E) := by
    intro v hv
    have hvK := K.down_closed hs (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v)
    exact (hA (subset_convexHull ℝ _ hv)).symm.trans (simplicialMap_vertex K φ hvK)
  rw [image_congr hA, A.image_convexHull, image_congr hvertices, Finset.coe_image]

open Classical in
theorem image_simplicialMap_eq_of_faces_image [FiniteDimensional ℝ E]
    (K R : Geometry.SimplicialComplex ℝ E) (q : E → E)
    (hmap : ∀ s ∈ R.faces, s.image q ∈ K.faces)
    (hsurj : ∀ s ∈ K.faces, ∃ r ∈ R.faces, r.image q = s) (φ : E → F) :
    simplicialMap R (φ ∘ q) '' R.space = simplicialMap K φ '' K.space := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := R.mem_space_iff.mp hx
    have hmem := simplicialMap_mem_convexHull_image R (φ ∘ q) hs hxs
    rw [← Finset.image_image,
      ← image_convexHull_simplicialMap_of_finiteDimensional K φ (hmap s hs)] at hmem
    exact image_mono (K.convexHull_subset_space (hmap s hs)) hmem
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
    obtain ⟨r, hr, hrq⟩ := hsurj s hs
    have hmem := simplicialMap_mem_convexHull_image K φ hs hxs
    rw [← hrq, Finset.image_image,
      ← image_convexHull_simplicialMap_of_finiteDimensional R (φ ∘ q) hr] at hmem
    exact image_mono (R.convexHull_subset_space hr) hmem

open Classical in
theorem exists_stellar_collapse_of_facet [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {t : Finset E} (ht : t ∈ K.facets) (hcard : 1 < t.card) {a : E} (ha : a ∈ t) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (q : E → E),
      IsSubdivision R K ∧ R.faces.Finite ∧
      (∀ s, s ∈ R.faces ↔ (s ∈ K.faces ∧ s ≠ t) ∨
        ∃ u : Finset E, u ⊂ t ∧ s = insert (t.centroid ℝ id) u) ∧
      EqOn q id K.vertices ∧ q (t.centroid ℝ id) = a ∧
      (∀ s ∈ R.faces, s.image q ∈ K.faces) ∧
      (∀ s ∈ K.faces, ∃ r ∈ R.faces, r.image q = s) ∧
      IsPiecewiseAffineOn (simplicialMap R q) K.space ∧
      simplicialMap R q '' K.space = K.space ∧
      EqOn (simplicialMap R q) id (SimplicialComplex.geometricFaceCostar K t).space := by
  classical
  obtain ⟨R, hR, hfin, hfaces⟩ := exists_isSubdivision_stellar_of_facet K ht
  let _ : Finite R.faces := hfin.to_subtype
  let p := t.centroid ℝ id
  let q := Function.update id p a
  have hp : p ∉ K.vertices := centroid_notMem_vertices K ht.1 hcard
  have hq (v : E) (hv : v ∈ K.vertices) : q v = v := by
    have hvp : v ≠ p := fun heq => hp (heq ▸ hv)
    exact Function.update_of_ne hvp _ _
  have hqp : q p = a := Function.update_self _ _ _
  have hvK (s : Finset E) (hs : s ∈ K.faces) {v : E} (hv : v ∈ s) : v ∈ K.vertices :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hqimage (s : Finset E) (hs : s ∈ K.faces) : s.image q = s := by
    exact (Finset.image_congr fun v hv => hq v (hvK s hs hv)).trans Finset.image_id
  have hmap (s : Finset E) (hs : s ∈ R.faces) : s.image q ∈ K.faces := by
    rcases (hfaces s).mp hs with ⟨hsK, -⟩ | ⟨u, hut, rfl⟩
    · rwa [hqimage s hsK]
    · apply K.down_closed ht.1 _ ((R.nonempty_of_mem_faces hs).image q)
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hqp ▸ ha
      · rw [hq w (hvK t ht.1 (hut.subset hw))]
        exact hut.subset hw
  have hsurj (s : Finset E) (hs : s ∈ K.faces) : ∃ r ∈ R.faces, r.image q = s := by
    by_cases hst : s = t
    · subst s
      have hproper : t.erase a ⊂ t := Finset.erase_ssubset ha
      refine ⟨insert p (t.erase a), (hfaces _).mpr (Or.inr ⟨_, hproper, rfl⟩), ?_⟩
      rw [Finset.image_insert, hqp]
      have herase : (t.erase a).image q = t.erase a := by
        exact (Finset.image_congr fun v hv => hq v
          (hvK t ht.1 (Finset.mem_of_mem_erase hv))).trans Finset.image_id
      rw [herase, Finset.insert_erase ha]
    · exact ⟨s, (hfaces s).mpr (Or.inl ⟨hs, hst⟩), hqimage s hs⟩
  have hid : EqOn (simplicialMap K id) id K.space := by
    intro x hx
    exact sum_weights_smul (mem_convexHull_carrierFace hx)
  refine ⟨R, q, hR, hfin, hfaces, hq, hqp, hmap, hsurj, ?_, ?_, ?_⟩
  · rw [← hR.space_eq]
    exact isPiecewiseAffineOn_simplicialMap R q
  · rw [← hR.space_eq, ← Function.id_comp q,
      image_simplicialMap_eq_of_faces_image K R q hmap hsurj id,
      image_congr hid, image_id]
    exact hR.space_eq.symm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := (SimplicialComplex.geometricFaceCostar K t).mem_space_iff.mp hx
    have hsR : s ∈ R.faces := (hfaces s).mpr
      (Or.inl ⟨hs.1, fun heq => hs.2 (heq ▸ Finset.Subset.refl t)⟩)
    rw [simplicialMap_eq_of_mem R q hsR hxs]
    calc
      ∑ v ∈ s, weights s x v • q v = ∑ v ∈ s, weights s x v • v :=
        Finset.sum_congr rfl fun v hv => by rw [hq v (hvK s hs.1 hv)]
      _ = x := sum_weights_smul hxs

open Classical in
private theorem vertices_subset_of_stellar_faces
    (K R : Geometry.SimplicialComplex ℝ E) {t : Finset E} (hcard : 1 < t.card)
    (hfaces : ∀ s, s ∈ R.faces ↔ (s ∈ K.faces ∧ s ≠ t) ∨
      ∃ u : Finset E, u ⊂ t ∧ s = insert (t.centroid ℝ id) u) :
    K.vertices ⊆ R.vertices := by
  intro v hv
  exact (hfaces {v}).mpr (Or.inl ⟨hv, fun heq => by
    have := congrArg Finset.card heq
    simp only [Finset.card_singleton] at this
    omega⟩)

open Classical in
theorem frontier_subset_geometricFaceCostar [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {t : Finset E}
    (ht : t ∈ K.faces) (hcard : t.card = Module.finrank ℝ E + 1) :
    frontier K.space ⊆ (SimplicialComplex.geometricFaceCostar K t).space := by
  intro x hx
  have hxK : x ∈ K.space := (isPolyhedron_space K).isCompact.isClosed.closure_eq ▸ hx.1
  have hface := carrierFace_mem hxK
  have hnot : ¬t ⊆ carrierFace K x := by
    intro hsub
    have heq : t = carrierFace K x := Finset.eq_of_subset_of_card_le hsub (by
      rw [hcard]
      exact card_le_finrank_succ_of_mem_faces K hface)
    have hopen : x ∈ interior (convexHull ℝ (t : Set E)) := by
      rw [interior_convexHull_eq_openSimplex (K.indep ht) hcard, heq]
      exact mem_openSimplex_carrierFace hxK
    exact hx.2 (interior_mono (K.convexHull_subset_space ht) hopen)
  exact (SimplicialComplex.geometricFaceCostar K t).convexHull_subset_space
    ⟨hface, hnot⟩ (mem_convexHull_carrierFace hxK)

open Classical in
theorem infinite_fiber_and_not_locally_injective_of_constant_triangle
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 2)
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = 3) {X : Type*} {f : E → X} {y : X}
    (hconst : EqOn f (fun _ => y) (convexHull ℝ (s : Set E))) :
    (K.space ∩ f ⁻¹' {y}).Infinite ∧
      ¬∀ x ∈ K.space, ∃ U ∈ 𝓝[K.space] x, InjOn f U := by
  obtain ⟨a, b, c, hab, -, -, -⟩ := Finset.card_eq_three.mp hcard
  let _ : Nontrivial E := nontrivial_of_ne a b hab
  let _ : PerfectSpace E := perfectSpace_of_module ℝ E
  let x := s.centroid ℝ id
  have hx : x ∈ interior (convexHull ℝ (s : Set E)) := by
    rw [interior_convexHull_eq_openSimplex (K.indep hs) (by omega)]
    exact centroid_mem_openSimplex (K.nonempty_of_mem_faces hs)
  have hnhds : convexHull ℝ (s : Set E) ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hx
  refine ⟨(infinite_of_mem_nhds x hnhds).mono (fun z hz =>
    ⟨K.convexHull_subset_space hs hz, hconst hz⟩), ?_⟩
  intro hlocal
  obtain ⟨U, hU, hinj⟩ := hlocal x (K.convexHull_subset_space hs (interior_subset hx))
  have hKnhds : K.space ∈ 𝓝 x := Filter.mem_of_superset hnhds (K.convexHull_subset_space hs)
  rw [nhdsWithin_eq_nhds.mpr hKnhds] at hU
  have hfinite : (U ∩ convexHull ℝ (s : Set E)).Finite := by
    apply Set.Subsingleton.finite
    intro v hv w hw
    exact hinj hv.1 hw.1 ((hconst hv.2).trans (hconst hw.2).symm)
  exact (infinite_of_mem_nhds x (Filter.inter_mem hU hnhds)) hfinite

open Classical in
private theorem ncard_triangles_stellar
    (K R : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {t : Finset E} (ht : t ∈ K.faces) (hcard : t.card = 3)
    (hfaces : ∀ s, s ∈ R.faces ↔ (s ∈ K.faces ∧ s ≠ t) ∨
      ∃ u : Finset E, u ⊂ t ∧ s = insert (t.centroid ℝ id) u) :
    {s ∈ R.faces | s.card = 3}.ncard = {s ∈ K.faces | s.card = 3}.ncard + 2 := by
  classical
  let p := t.centroid ℝ id
  have hp : p ∉ K.vertices := centroid_notMem_vertices K ht (by omega)
  have hpT : p ∉ t := fun h => hp (K.down_closed ht (Finset.singleton_subset_iff.mpr h)
    (Finset.singleton_nonempty p))
  let A := {s ∈ K.faces | s.card = 3}
  let B := (fun v => insert p (t.erase v)) '' (t : Set E)
  have htriangles : {s ∈ R.faces | s.card = 3} = (A \ {t}) ∪ B := by
    ext s
    constructor
    · rintro ⟨hs, hsc⟩
      rcases (hfaces s).mp hs with ⟨hsK, hst⟩ | ⟨u, hut, rfl⟩
      · exact Or.inl ⟨⟨hsK, hsc⟩, hst⟩
      · have hpu : p ∉ u := fun h => hpT (hut.subset h)
        have huc : u.card = 2 := by
          rw [Finset.card_insert_of_notMem hpu] at hsc
          omega
        obtain ⟨v, hvt, hvu⟩ := Finset.exists_of_ssubset hut
        have heq : u = t.erase v := Finset.eq_of_subset_of_card_le
          (Finset.subset_erase.mpr ⟨hut.subset, hvu⟩) (by
            rw [Finset.card_erase_of_mem hvt, hcard, huc])
        exact Or.inr ⟨v, hvt, by rw [heq]⟩
    · rintro (⟨⟨hs, hsc⟩, hst⟩ | ⟨v, hvt, rfl⟩)
      · exact ⟨(hfaces s).mpr (Or.inl ⟨hs, hst⟩), hsc⟩
      · refine ⟨(hfaces _).mpr (Or.inr ⟨t.erase v, Finset.erase_ssubset hvt, rfl⟩), ?_⟩
        rw [Finset.card_insert_of_notMem (fun h => hpT (Finset.mem_of_mem_erase h)),
          Finset.card_erase_of_mem hvt, hcard]
  have hinj : InjOn (fun v => insert p (t.erase v)) (t : Set E) := by
    intro v hv w _ heq
    change insert p (t.erase v) = insert p (t.erase w) at heq
    by_contra hvw
    have hvp : v ≠ p := fun h => hpT (h ▸ hv)
    have hmem : v ∈ insert p (t.erase w) :=
      Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hvw, hv⟩)
    rw [← heq] at hmem
    simp [hvp] at hmem
  have hdis : Disjoint (A \ {t}) B := by
    apply Set.disjoint_left.mpr
    rintro s ⟨hs, -⟩ ⟨v, -, rfl⟩
    exact hp (K.down_closed hs.1 (Finset.singleton_subset_iff.mpr
      (Finset.mem_insert_self p _)) (Finset.singleton_nonempty p))
  have hAfin : A.Finite := (Set.toFinite K.faces).subset fun _ hs => hs.1
  have hBfin : B.Finite := t.finite_toSet.image _
  have hremove : (A \ {t}).ncard + 1 = A.ncard :=
    Set.ncard_sdiff_singleton_add_one ⟨ht, hcard⟩ hAfin
  have hBcard : B.ncard = 3 := by
    rw [hinj.ncard_image, Set.ncard_coe_finset, hcard]
  rw [htriangles, Set.ncard_union_eq hdis hAfin.sdiff hBfin, hBcard]
  change (A \ {t}).ncard + 3 = A.ncard + 2
  omega

open Classical in
theorem exists_inner_triangle_collapse [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 2) (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {a b c : E} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ht : ({a, b, c} : Finset E) ∈ K.faces) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (q : E → E) (u : Finset E),
      IsSubdivision R K ∧ R.faces.Finite ∧
      {s ∈ R.faces | s.card = 3}.ncard = {s ∈ K.faces | s.card = 3}.ncard + 6 ∧
      EqOn q id K.vertices ∧
      (∀ s ∈ R.faces, s.image q ∈ K.faces) ∧
      (∀ s ∈ K.faces, ∃ r ∈ R.faces, r.image q = s) ∧
      (∀ s ∈ K.faces, s ≠ {a, b, c} → s ∈ R.faces) ∧
      IsPiecewiseAffineOn (simplicialMap R q) K.space ∧
      simplicialMap R q '' K.space = K.space ∧
      EqOn (simplicialMap R q) id
        (SimplicialComplex.geometricFaceCostar K {a, b, c}).space ∧
      u ∈ R.faces ∧ u.card = 3 ∧
      convexHull ℝ (u : Set E) ⊆ openSimplex {a, b, c} ∧
      EqOn (simplicialMap R q) (fun _ => a) (convexHull ℝ (u : Set E)) := by
  classical
  have hfacet (L : Geometry.SimplicialComplex ℝ E) {s : Finset E}
      (hs : s ∈ L.faces) (hscard : s.card = 3) : s ∈ L.facets := by
    refine ⟨hs, fun t ht hst => ?_⟩
    have hbound := card_le_finrank_succ_of_mem_faces L ht
    rw [hdim] at hbound
    exact Finset.eq_of_subset_of_card_le hst (by omega)
  have hvertex (L : Geometry.SimplicialComplex ℝ E) {s : Finset E}
      (hs : s ∈ L.faces) {v : E} (hv : v ∈ s) : v ∈ L.vertices :=
    L.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  let t : Finset E := {a, b, c}
  have htc : t.card = 3 := by simp [t, hab, hac, hbc]
  obtain ⟨R₁, q₁, hR₁, hf₁, hd₁, he₁, hq₁, hm₁, hs₁, -, -, -⟩ :=
    exists_stellar_collapse_of_facet K (hfacet K ht htc) (by change 1 < t.card; omega)
      (show a ∈ t by simp [t])
  change ∀ ⦃v : E⦄, v ∈ K.vertices → q₁ v = v at he₁
  let _ : Finite R₁.faces := hf₁.to_subtype
  let p₁ := t.centroid ℝ id
  have hp₁ : p₁ ∉ K.vertices := centroid_notMem_vertices K ht (by omega)
  have hv₁ := vertices_subset_of_stellar_faces K R₁ (by omega : 1 < t.card) hd₁
  have haK : a ∈ K.vertices := hvertex K ht (by simp)
  have hbK : b ∈ K.vertices := hvertex K ht (by simp)
  have hp₁a : p₁ ≠ a := fun h => hp₁ (h.symm ▸ haK)
  have hp₁b : p₁ ≠ b := fun h => hp₁ (h.symm ▸ hbK)
  let t₁ : Finset E := {p₁, a, b}
  have ht₁c : t₁.card = 3 := by simp [t₁, hp₁a, hp₁b, hab]
  have ht₁ : t₁ ∈ R₁.faces := by
    apply (hd₁ _).mpr
    refine Or.inr ⟨{a, b}, ?_, rfl⟩
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨by simp, fun heq => ?_⟩
    have : c ∈ ({a, b} : Finset E) := heq.symm ▸ (show c ∈ t by simp [t])
    simp [hac.symm, hbc.symm] at this
  obtain ⟨R₂, q₂, hR₂, hf₂, hd₂, he₂, hq₂, hm₂, hs₂, -, -, -⟩ :=
    exists_stellar_collapse_of_facet R₁ (hfacet R₁ ht₁ ht₁c) (by omega)
      (show a ∈ t₁ by simp [t₁])
  change ∀ ⦃v : E⦄, v ∈ R₁.vertices → q₂ v = v at he₂
  let _ : Finite R₂.faces := hf₂.to_subtype
  let p₂ := t₁.centroid ℝ id
  have hp₂ : p₂ ∉ R₁.vertices := centroid_notMem_vertices R₁ ht₁ (by omega)
  have hv₂ := vertices_subset_of_stellar_faces R₁ R₂ (by omega : 1 < t₁.card) hd₂
  have hp₁R₁ : p₁ ∈ R₁.vertices := hvertex R₁ ht₁ (by simp [t₁])
  have hp₂a : p₂ ≠ a := fun h => hp₂ (h.symm ▸ hv₁ haK)
  have hp₂p₁ : p₂ ≠ p₁ := fun h => hp₂ (h.symm ▸ hp₁R₁)
  let t₂ : Finset E := {p₂, p₁, a}
  have ht₂c : t₂.card = 3 := by simp [t₂, hp₂p₁, hp₂a, hp₁a]
  have ht₂ : t₂ ∈ R₂.faces := by
    apply (hd₂ _).mpr
    refine Or.inr ⟨{p₁, a}, ?_, rfl⟩
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨by simp [t₁], fun heq => ?_⟩
    have : b ∈ ({p₁, a} : Finset E) := heq.symm ▸ (show b ∈ t₁ by simp [t₁])
    simp [hp₁b.symm, hab.symm] at this
  obtain ⟨R₃, q₃, hR₃, hf₃, hd₃, he₃, hq₃, hm₃, hs₃, -, -, -⟩ :=
    exists_stellar_collapse_of_facet R₂ (hfacet R₂ ht₂ ht₂c) (by omega)
      (show a ∈ t₂ by simp [t₂])
  change ∀ ⦃v : E⦄, v ∈ R₂.vertices → q₃ v = v at he₃
  let _ : Finite R₃.faces := hf₃.to_subtype
  let p₃ := t₂.centroid ℝ id
  have hp₃ : p₃ ∉ R₂.vertices := centroid_notMem_vertices R₂ ht₂ (by omega)
  have hp₂R₂ : p₂ ∈ R₂.vertices := hvertex R₂ ht₂ (by simp [t₂])
  have hp₃p₁ : p₃ ≠ p₁ := fun h => hp₃ (h.symm ▸ hv₂ hp₁R₁)
  have hp₃p₂ : p₃ ≠ p₂ := fun h => hp₃ (h.symm ▸ hp₂R₂)
  let u : Finset E := {p₃, p₂, p₁}
  have huc : u.card = 3 := by simp [u, hp₃p₂, hp₃p₁, hp₂p₁]
  have hu : u ∈ R₃.faces := by
    apply (hd₃ _).mpr
    refine Or.inr ⟨{p₂, p₁}, ?_, rfl⟩
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨by simp [t₂], fun heq => ?_⟩
    have : a ∈ ({p₂, p₁} : Finset E) := heq.symm ▸ (show a ∈ t₂ by simp [t₂])
    simp [hp₂a.symm, hp₁a.symm] at this
  let q := q₁ ∘ q₂ ∘ q₃
  have heq : EqOn q id K.vertices := by
    intro v hv
    change q₁ (q₂ (q₃ v)) = v
    rw [he₃ (hv₂ (hv₁ hv)), he₂ (hv₁ hv), he₁ hv]
  have hmap (s : Finset E) (hs : s ∈ R₃.faces) : s.image q ∈ K.faces := by
    change s.image (q₁ ∘ q₂ ∘ q₃) ∈ K.faces
    rw [← Finset.image_image, ← Finset.image_image]
    exact hm₁ _ (hm₂ _ (hm₃ _ hs))
  have hsurj (s : Finset E) (hs : s ∈ K.faces) : ∃ r ∈ R₃.faces, r.image q = s := by
    obtain ⟨s₁, hs₁', h₁⟩ := hs₁ s hs
    obtain ⟨s₂, hs₂', h₂⟩ := hs₂ s₁ hs₁'
    obtain ⟨s₃, hs₃', h₃⟩ := hs₃ s₂ hs₂'
    refine ⟨s₃, hs₃', ?_⟩
    change s₃.image (q₁ ∘ q₂ ∘ q₃) = s
    rw [← Finset.image_image, ← Finset.image_image, h₃, h₂, h₁]
  have hpres (s : Finset E) (hs : s ∈ K.faces) (hst : s ≠ t) : s ∈ R₃.faces := by
    have hs₁' : s ∈ R₁.faces := (hd₁ s).mpr (Or.inl ⟨hs, hst⟩)
    have hst₁ : s ≠ t₁ := by
      intro h
      exact hp₁ (hvertex K hs (h.symm ▸ (show p₁ ∈ t₁ by simp [t₁])))
    have hs₂' : s ∈ R₂.faces := (hd₂ s).mpr (Or.inl ⟨hs₁', hst₁⟩)
    have hst₂ : s ≠ t₂ := by
      intro h
      exact hp₂ (hvertex R₁ hs₁' (h.symm ▸ (show p₂ ∈ t₂ by simp [t₂])))
    exact (hd₃ s).mpr (Or.inl ⟨hs₂', hst₂⟩)
  have hR := hR₃.trans (hR₂.trans hR₁)
  have hqconst : EqOn q (fun _ => a) (u : Set E) := by
    intro v hv
    simp only [u, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · change q₁ (q₂ (q₃ p₃)) = a
      rw [hq₃, he₂ (hv₁ haK), he₁ haK]
    · change q₁ (q₂ (q₃ p₂)) = a
      rw [he₃ hp₂R₂, hq₂, he₁ haK]
    · change q₁ (q₂ (q₃ p₁)) = a
      rw [he₃ (hv₂ hp₁R₁), he₂ hp₁R₁, hq₁]
  have hmem₁ : p₁ ∈ openSimplex t := centroid_mem_openSimplex (K.nonempty_of_mem_faces ht)
  have hmem₂ : p₂ ∈ openSimplex t₁ :=
    centroid_mem_openSimplex (R₁.nonempty_of_mem_faces ht₁)
  have hmem₃ : p₃ ∈ openSimplex t₂ :=
    centroid_mem_openSimplex (R₂.nonempty_of_mem_faces ht₂)
  have hsub₁ : convexHull ℝ (t₁ : Set E) ⊆ convexHull ℝ (t : Set E) := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    intro v hv
    simp only [t₁, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact openSimplex_subset_convexHull _ hmem₁
    · exact subset_convexHull ℝ _ (by simp [t])
    · exact subset_convexHull ℝ _ (by simp [t])
  have hsub₂ : convexHull ℝ (t₂ : Set E) ⊆ convexHull ℝ (t₁ : Set E) := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    intro v hv
    simp only [t₂, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact openSimplex_subset_convexHull _ hmem₂
    · exact subset_convexHull ℝ _ (by simp [t₁])
    · exact subset_convexHull ℝ _ (by simp [t₁])
  have hopen : interior (convexHull ℝ (t : Set E)) = openSimplex t :=
    interior_convexHull_eq_openSimplex (K.indep ht) (by omega)
  have hopen₁ : interior (convexHull ℝ (t₁ : Set E)) = openSimplex t₁ :=
    interior_convexHull_eq_openSimplex (R₁.indep ht₁) (by omega)
  have hopen₂ : interior (convexHull ℝ (t₂ : Set E)) = openSimplex t₂ :=
    interior_convexHull_eq_openSimplex (R₂.indep ht₂) (by omega)
  have hopenSub₁ : openSimplex t₁ ⊆ openSimplex t := by
    rw [← hopen₁, ← hopen]
    exact interior_mono hsub₁
  have hopenSub₂ : openSimplex t₂ ⊆ openSimplex t₁ := by
    rw [← hopen₂, ← hopen₁]
    exact interior_mono hsub₂
  have hinner : convexHull ℝ (u : Set E) ⊆ openSimplex t := by
    apply convexHull_min _
      (show Convex ℝ (openSimplex t) from hopen ▸ (convex_convexHull ℝ _).interior)
    intro v hv
    simp only [u, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hopenSub₁ (hopenSub₂ hmem₃)
    · exact hopenSub₁ hmem₂
    · exact hmem₁
  have hcount₁ := ncard_triangles_stellar K R₁ ht htc hd₁
  have hcount₂ := ncard_triangles_stellar R₁ R₂ ht₁ ht₁c hd₂
  have hcount₃ := ncard_triangles_stellar R₂ R₃ ht₂ ht₂c hd₃
  refine ⟨R₃, q, u, hR, hf₃, by omega, heq, hmap, hsurj, hpres,
    ?_, ?_, ?_, hu, huc, hinner, ?_⟩
  · rw [← hR.space_eq]
    exact isPiecewiseAffineOn_simplicialMap R₃ q
  · have hid : EqOn (simplicialMap K id) id K.space := fun _ hx =>
      sum_weights_smul (mem_convexHull_carrierFace hx)
    rw [← hR.space_eq, ← Function.id_comp q,
      image_simplicialMap_eq_of_faces_image K R₃ q hmap hsurj id, image_congr hid, image_id]
    exact hR.space_eq.symm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := (SimplicialComplex.geometricFaceCostar K t).mem_space_iff.mp hx
    have hst : s ≠ t := fun heq => hs.2 (heq ▸ Finset.Subset.refl t)
    change simplicialMap R₃ q x = x
    rw [simplicialMap_eq_of_mem R₃ q (hpres s hs.1 hst) hxs]
    exact (Finset.sum_congr rfl fun v hv => by
      rw [heq (hvertex K hs.1 hv)]; rfl).trans (sum_weights_smul hxs)
  · intro x hx
    rw [simplicialMap_eq_of_mem R₃ q hu hx]
    calc
      ∑ v ∈ u, weights u x v • q v = ∑ v ∈ u, weights u x v • a :=
        Finset.sum_congr rfl fun v hv => by rw [hqconst hv]
      _ = a := by rw [← Finset.sum_smul, sum_weights hx, one_smul]

open Classical in
theorem exists_boundary_fixed_collapse_of_triangle [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 2) {t : Finset E}
    (hind : AffineIndependent ℝ ((↑) : t → E)) (hcard : t.card = 3) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (q : E → E) (u : Finset E) (a : E),
      IsSubdivision R (simplexComplex t hind) ∧ R.faces.Finite ∧ a ∈ t ∧
      R.space = convexHull ℝ (t : Set E) ∧ {s ∈ R.faces | s.card = 3}.ncard = 7 ∧
      (∀ s ∈ R.faces, ∃ v ∈ R.faces, s ⊆ v ∧ v.card = 3) ∧
      (∀ s ∈ R.faces, ∃ A : E →ᵃ[ℝ] E, EqOn q A (convexHull ℝ (s : Set E))) ∧
      IsPiecewiseAffineOn q R.space ∧ ContinuousOn q R.space ∧ q '' R.space = R.space ∧
      EqOn q id (frontier R.space) ∧
      u ∈ R.faces ∧ u.card = 3 ∧
      ({s ∈ R.faces | s.card = 3} \ {u}).ncard = 6 ∧
      (∀ v ∈ R.faces, v.card = 3 → v ≠ u →
        Disjoint (convexHull ℝ (v : Set E)) (openSimplex u)) ∧
      convexHull ℝ (u : Set E) ⊆ interior R.space ∧
      EqOn q (fun _ => a) (convexHull ℝ (u : Set E)) ∧
      (R.space ∩ q ⁻¹' {a}).Infinite ∧
      (¬∀ x ∈ R.space, ∃ U ∈ 𝓝[R.space] x, InjOn q U) ∧
      ∃ x ∈ R.space, ∃ y ∈ R.space, ∃ z ∈ R.space,
        x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ q x = a ∧ q y = a ∧ q z = a := by
  classical
  let K := simplexComplex t hind
  let _ : Finite K.faces := (simplexComplex_faces_finite _ _).to_subtype
  have ht : t ∈ K.faces := ⟨Finset.card_pos.mp (by omega), Finset.Subset.refl _⟩
  obtain ⟨a, b, c, hab, hac, hbc, htabc⟩ := Finset.card_eq_three.mp hcard
  obtain ⟨R, φ, u, hR, hfin, hcount, -, -, -, -, hPL, himage, hfix,
    hu, huc, hinner, hconst⟩ := exists_inner_triangle_collapse hdim K hab hac hbc (htabc ▸ ht)
  let _ : Finite R.faces := hfin.to_subtype
  have hspace : R.space = convexHull ℝ (t : Set E) :=
    hR.space_eq.trans (simplexComplex_space _ _ (Finset.card_pos.mp (by omega)))
  have hsingle : {s ∈ K.faces | s.card = 3} = {t} := by
    ext s
    constructor
    · rintro ⟨hs, hsc⟩
      exact Finset.eq_of_subset_of_card_le hs.2 (by omega)
    · rintro rfl
      exact ⟨ht, hcard⟩
  have hseven : {s ∈ R.faces | s.card = 3}.ncard = 7 := by
    rw [hsingle, Set.ncard_singleton] at hcount
    exact hcount
  have hball : IsPLBall 2 R.space := by
    rw [hspace]
    exact isPLBall_convexHull_of_affineIndependent t hind hcard
  have hboundary : EqOn (simplicialMap R φ) id (frontier R.space) := by
    rw [hR.space_eq]
    apply hfix.mono
    rw [← htabc]
    exact frontier_subset_geometricFaceCostar K ht (by omega)
  have hinner' : convexHull ℝ (u : Set E) ⊆ interior R.space := by
    rw [hspace, interior_convexHull_eq_openSimplex hind (by omega), htabc]
    exact hinner
  have hPL' : IsPiecewiseAffineOn (simplicialMap R φ) R.space := hR.space_eq.symm ▸ hPL
  have hdeg := infinite_fiber_and_not_locally_injective_of_constant_triangle hdim R hu huc hconst
  have hremove := Set.ncard_sdiff_singleton_add_one
    (s := {s ∈ R.faces | s.card = 3}) ⟨hu, huc⟩ (hfin.subset fun _ hs => hs.1)
  have hdis (v : Finset E) (hv : v ∈ R.faces) (hvc : v.card = 3) (hvu : v ≠ u) :
      Disjoint (convexHull ℝ (v : Set E)) (openSimplex u) := by
    apply Set.disjoint_left.mpr
    intro x hxv hxu
    have huv := face_subset_of_mem_openSimplex_of_mem_convexHull R hu hv hxu hxv
    exact hvu (Finset.eq_of_subset_of_card_le huv (by omega)).symm
  refine ⟨R, simplicialMap R φ, u, a, hR, hfin, by simp [htabc], hspace, hseven,
    fun s hs => hball.isCombinatorialManifoldWithBoundary.exists_face_superset_card_eq hs,
    fun s hs => exists_affineMap_eqOn_simplicialMap R φ hs, hPL', hPL'.continuousOn,
    hR.space_eq.symm ▸ himage, hboundary, hu, huc, by omega, hdis,
    hinner', hconst, hdeg.1, hdeg.2, ?_⟩
  obtain ⟨x, y, z, hxy, hxz, hyz, huxyz⟩ := Finset.card_eq_three.mp huc
  have hx : x ∈ convexHull ℝ (u : Set E) := subset_convexHull ℝ _ (by simp [huxyz])
  have hy : y ∈ convexHull ℝ (u : Set E) := subset_convexHull ℝ _ (by simp [huxyz])
  have hz : z ∈ convexHull ℝ (u : Set E) := subset_convexHull ℝ _ (by simp [huxyz])
  exact ⟨x, R.convexHull_subset_space hu hx, y, R.convexHull_subset_space hu hy,
    z, R.convexHull_subset_space hu hz, hxy, hxz, hyz, hconst hx, hconst hy, hconst hz⟩

end DifferentialGeometry.Topology.PiecewiseLinear
