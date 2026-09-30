/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.Section33ExtensionLabels

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C Cpp : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3}

theorem IsHandleDecompositionOfTube.vertex_image_notMem_pseudoCell
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) {v : E3}
    (hv : v ∈ K.vertices) {e : Finset E3} (he : e ∈ K.faces) (hc : e.card = 2) :
    h v ∉ Ec e := by
  intro hve
  have ht := hd.tube
  have hKN : K.space ⊆ N :=
    (subset_interior_iff_mem_nhdsSet.mpr ht.isNeighborhood).trans interior_subset
  have hvK : ∀ w ∈ K.vertices, w ∈ K.space := fun w hw =>
    K.convexHull_subset_space hw (subset_convexHull ℝ _ (Finset.mem_singleton_self w))
  obtain ⟨a, hae, b, hbe, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < e.card)
  have ha : a ∈ K.vertices :=
    K.down_closed he (Finset.singleton_subset_iff.mpr hae) (Finset.singleton_nonempty a)
  have hb : b ∈ K.vertices :=
    K.down_closed he (Finset.singleton_subset_iff.mpr hbe) (Finset.singleton_nonempty b)
  have hva : h v = h a := by
    have hva' : h v ∈ Cpp a ∩ h '' K.vertices :=
      ⟨hd.pseudoCell_subset_handlePiece he hc hae hve, mem_image_of_mem h hv⟩
    rw [hd.oneVertex a ha] at hva'
    exact hva'
  have hvb : h v = h b := by
    have hvb' : h v ∈ Cpp b ∩ h '' K.vertices :=
      ⟨hd.pseudoCell_subset_handlePiece he hc hbe hve, mem_image_of_mem h hv⟩
    rw [hd.oneVertex b hb] at hvb'
    exact hvb'
  exact hab (ht.injOn (hKN (hvK a ha)) (hKN (hvK b hb)) (hva.symm.trans hvb))

theorem IsHandleDecompositionOfTube.exists_freeFace_image_notMem_pseudoCell
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) {X : Set E3}
    {g : E3 → E3} (hg : IsPLHomeomorphOn g (frontier N) X)
    (hgA : ∀ v ∈ K.vertices, g '' (frontier (C v) ∩ frontier N) = Cpp v ∩ X)
    (hgD : ∀ e ∈ K.faces, e.card = 2 → g '' Dbd e = Ec e ∩ X) {v : E3} (hv : v ∈ K.vertices) :
    ∃ y ∈ Cpp v ∩ X, ∀ e ∈ K.faces, e.card = 2 → y ∉ Ec e := by
  obtain ⟨x, hxA, hxD⟩ := (hd.tube.freeFaceConnected v hv).nonempty
  refine ⟨g x, by rw [← hgA v hv]; exact mem_image_of_mem g hxA, fun e he hc hxe => ?_⟩
  by_cases hve : v ∈ e
  · have hxe' : g x ∈ Ec e ∩ X := ⟨hxe, (hg.bijOn.mapsTo hxA.2)⟩
    rw [← hgD e he hc] at hxe'
    obtain ⟨x', hx', hx'x⟩ := hxe'
    have hx'N : x' ∈ frontier N := by
      rw [← hd.tube.splitProper e he hc] at hx'
      exact hx'.2
    have hxx' : x' = x := hg.bijOn.injOn hx'N hxA.2 hx'x
    exact hxD (mem_iUnion₂.mpr ⟨e, ⟨he, hc, hve⟩, hxx' ▸ hx'⟩)
  · have hmem : g x ∈ Cpp v ∩ Ec e := by
      refine ⟨?_, hxe⟩
      have hgx : g x ∈ Cpp v ∩ X := by
        rw [← hgA v hv]
        exact mem_image_of_mem g hxA
      exact hgx.1
    rw [hd.handlePiece_inter_pseudoCell_eq_empty hv he hc hve] at hmem
    exact hmem

open Classical in
theorem IsHandleDecompositionOfTube.exists_sphere_maps
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) {X : Set E3}
    {g : E3 → E3} (hg : IsPLHomeomorphOn g (frontier N) X)
    (hgA : ∀ v ∈ K.vertices, g '' (frontier (C v) ∩ frontier N) = Cpp v ∩ X)
    (hgD : ∀ e ∈ K.faces, e.card = 2 → g '' Dbd e = Ec e ∩ X)
    (hApoly : ∀ v ∈ K.vertices, IsPolyhedron (Cpp v ∩ X)) {F : Finset E3 → Set E3}
    (hF : ∀ e ∈ K.faces, e.card = 2 → ∃ r : (Fin 3 → ℝ) → E3,
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (F e) ∧ r '' stdSimplexBoundary 2 = Ec e ∩ X)
    (hFX : ∀ e ∈ K.faces, e.card = 2 → F e ∩ X = Ec e ∩ X)
    (hFdisj : ∀ e ∈ K.faces, e.card = 2 → ∀ e' ∈ K.faces, e'.card = 2 → e ≠ e' →
      Disjoint (F e) (F e')) :
    ∃ ψ : E3 → E3, EqOn ψ g (frontier N) ∧
      (∀ e ∈ K.faces, e.card = 2 → IsPLHomeomorphOn ψ (D e) (F e)) ∧
      ∀ v ∈ K.vertices,
        IsPLHomeomorphOn ψ (frontier (C v)) ((Cpp v ∩ X) ∪ ⋃ e ∈ edgesAt K v, F e) := by
  have ht := hd.tube
  have hφ : ∀ e : Finset E3, ∃ φ : E3 → E3, e ∈ K.faces → e.card = 2 →
      IsPLHomeomorphOn φ (D e) (F e) ∧ EqOn φ g (Dbd e) := by
    intro e
    by_cases he : e ∈ K.faces ∧ e.card = 2
    · obtain ⟨R, hR, hRb⟩ := ht.splitCell e he.1 he.2
      obtain ⟨r, hr, hrb⟩ := hF e he.1 he.2
      have hDbdN : Dbd e ⊆ frontier N := by
        rw [← ht.splitProper e he.1 he.2]
        exact inter_subset_right
      have hDbdpoly : IsPolyhedron (Dbd e) := by
        rw [hRb]
        exact (hR.isPLSphere_image_stdSimplexBoundary (n := 1)).isPolyhedron
      have hb := hg.restrict hDbdpoly hDbdN
      rw [hgD e he.1 he.2, ← hrb, hRb] at hb
      obtain ⟨φ, hφ, hφb⟩ := exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary hR hr hb
      exact ⟨φ, fun _ _ => ⟨hφ, hRb ▸ hφb⟩⟩
    · exact ⟨id, fun h1 h2 => absurd ⟨h1, h2⟩ he⟩
  choose φ hφ using hφ
  let ψ : E3 → E3 := fun x =>
    if hx : ∃ e, (e ∈ K.faces ∧ e.card = 2) ∧ x ∈ D e then φ hx.choose x else g x
  have hψD : ∀ e ∈ K.faces, e.card = 2 → EqOn ψ (φ e) (D e) := by
    intro e he hc x hx
    have hex : ∃ e, (e ∈ K.faces ∧ e.card = 2) ∧ x ∈ D e := ⟨e, ⟨he, hc⟩, hx⟩
    have hch := hex.choose_spec
    have heq : hex.choose = e := by
      by_contra hne
      exact disjoint_left.mp (ht.splitDisjoint hch.1.1 hch.1.2 he hc hne) hch.2 hx
    change (if hx : ∃ e, (e ∈ K.faces ∧ e.card = 2) ∧ x ∈ D e then φ hx.choose x else g x) =
      φ e x
    rw [dite_eq_left hex, heq]
  have hψg : EqOn ψ g (frontier N) := by
    intro x hx
    by_cases hex : ∃ e, (e ∈ K.faces ∧ e.card = 2) ∧ x ∈ D e
    · obtain ⟨e, ⟨he, hc⟩, hxe⟩ := hex
      rw [hψD e he hc hxe]
      have hxb : x ∈ Dbd e := by
        rw [← ht.splitProper e he hc]
        exact ⟨hxe, hx⟩
      exact (hφ e he hc).2 hxb
    · change (if hx : ∃ e, (e ∈ K.faces ∧ e.card = 2) ∧ x ∈ D e then φ hx.choose x else g x) =
        g x
      rw [dite_eq_right hex]
  have hψDF : ∀ e ∈ K.faces, e.card = 2 → IsPLHomeomorphOn ψ (D e) (F e) :=
    fun e he hc => (hφ e he hc).1.congr (hψD e he hc)
  refine ⟨ψ, hψg, hψDF, fun v hv => ?_⟩
  have hAsub : frontier (C v) ∩ frontier N ⊆ frontier N := inter_subset_right
  have hApolyv : IsPolyhedron (frontier (C v) ∩ frontier N) := by
    have hpre := hg.isPolyhedron_preimage (hApoly v hv) inter_subset_right
    convert hpre using 1
    ext x
    constructor
    · intro hx
      refine ⟨hx.2, ?_⟩
      rw [mem_preimage, ← hgA v hv]
      exact mem_image_of_mem g hx
    · rintro ⟨hxN, hxg⟩
      rw [mem_preimage, ← hgA v hv] at hxg
      obtain ⟨a, ha, hax⟩ := hxg
      rwa [← hg.bijOn.injOn (hAsub ha) hxN hax]
  have hA0 : IsPLHomeomorphOn ψ (frontier (C v) ∩ frontier N) (Cpp v ∩ X) := by
    have h1 := hg.restrict hApolyv hAsub
    rw [hgA v hv] at h1
    exact h1.congr (hψg.mono hAsub)
  have hDpoly : ∀ e' ∈ edgesAt K v, IsPolyhedron (D e') := fun e' he' => by
    obtain ⟨R, hR, -⟩ := ht.splitCell e' he'.1 he'.2.1
    exact IsPLBall.isPolyhedron ⟨R, hR⟩
  have hind : ∀ s : Finset (Finset E3), (↑s : Set (Finset E3)) ⊆ edgesAt K v →
      IsPolyhedron ((frontier (C v) ∩ frontier N) ∪ ⋃ e ∈ s, D e) ∧
      IsPLHomeomorphOn ψ ((frontier (C v) ∩ frontier N) ∪ ⋃ e ∈ s, D e)
        ((Cpp v ∩ X) ∪ ⋃ e ∈ s, F e) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, union_empty]
      exact ⟨hApolyv, hA0⟩
    | insert e s hes ih =>
      intro hs
      have he : e ∈ edgesAt K v := hs (Finset.mem_coe.mpr (Finset.mem_insert_self e s))
      have hs' : (↑s : Set (Finset E3)) ⊆ edgesAt K v := fun e' he' =>
        hs (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp he')))
      obtain ⟨hPpoly, hIH⟩ := ih hs'
      have hL : ((frontier (C v) ∩ frontier N) ∪ ⋃ e' ∈ s, D e') ∩ D e = Dbd e := by
        apply Subset.antisymm
        · rintro x ⟨hx | hx, hxe⟩
          · rw [← ht.splitProper e he.1 he.2.1]
            exact ⟨hxe, hx.2⟩
          · obtain ⟨e', he', hxe'⟩ := mem_iUnion₂.mp hx
            have hne : e' ≠ e := fun h' => hes (h' ▸ he')
            have he's := hs' (Finset.mem_coe.mpr he')
            exact absurd hxe
              (disjoint_left.mp (ht.splitDisjoint he's.1 he's.2.1 he.1 he.2.1 hne) hxe')
        · intro x hx
          exact ⟨Or.inl (ht.rim_subset_freeFace he.1 he.2.1 hv he.2.2 hx),
            ht.rim_subset_splitDisk he.1 he.2.1 hx⟩
      have hR : ((Cpp v ∩ X) ∪ ⋃ e' ∈ s, F e') ∩ F e = Ec e ∩ X := by
        apply Subset.antisymm
        · rintro x ⟨hx | hx, hxF⟩
          · have hx' : x ∈ F e ∩ X := ⟨hxF, hx.2⟩
            rw [hFX e he.1 he.2.1] at hx'
            exact hx'
          · obtain ⟨e', he', hxe'⟩ := mem_iUnion₂.mp hx
            have hne : e' ≠ e := fun h' => hes (h' ▸ he')
            have he's := hs' (Finset.mem_coe.mpr he')
            exact absurd hxF
              (disjoint_left.mp (hFdisj e' he's.1 he's.2.1 e he.1 he.2.1 hne) hxe')
        · intro x hx
          have hxF : x ∈ F e := by
            rw [← hFX e he.1 he.2.1] at hx
            exact hx.1
          exact ⟨Or.inl ⟨hd.pseudoCell_subset_handlePiece he.1 he.2.1 he.2.2 hx.1, hx.2⟩, hxF⟩
      have hDbdN : Dbd e ⊆ frontier N := by
        rw [← ht.splitProper e he.1 he.2.1]
        exact inter_subset_right
      have hmeet : ψ '' (((frontier (C v) ∩ frontier N) ∪ ⋃ e' ∈ s, D e') ∩ D e) =
          ((Cpp v ∩ X) ∪ ⋃ e' ∈ s, F e') ∩ F e := by
        rw [hL, hR, ← hgD e he.1 he.2.1]
        exact image_congr (hψg.mono hDbdN)
      have hU := hIH.union (hψDF e he.1 he.2.1) hPpoly (hDpoly e he) hmeet
      have hdom : (frontier (C v) ∩ frontier N) ∪ ⋃ e' ∈ insert e s, D e' =
          ((frontier (C v) ∩ frontier N) ∪ ⋃ e' ∈ s, D e') ∪ D e := by
        rw [Finset.set_biUnion_insert]
        ext x
        simp only [mem_union]
        tauto
      have hcod : (Cpp v ∩ X) ∪ ⋃ e' ∈ insert e s, F e' =
          ((Cpp v ∩ X) ∪ ⋃ e' ∈ s, F e') ∪ F e := by
        rw [Finset.set_biUnion_insert]
        ext x
        simp only [mem_union]
        tauto
      rw [hdom, hcod]
      exact ⟨hPpoly.union (hDpoly e he), hU⟩
  have hEv : (edgesAt K v).Finite := ht.facesFinite.subset fun e he => he.1
  obtain ⟨-, hfin⟩ := hind hEv.toFinset (by simp)
  have hdom : (frontier (C v) ∩ frontier N) ∪ ⋃ e ∈ hEv.toFinset, D e = frontier (C v) := by
    apply Subset.antisymm
    · refine union_subset inter_subset_left (iUnion₂_subset fun e he => ?_)
      have he' : e ∈ edgesAt K v := hEv.mem_toFinset.mp he
      exact ht.splitDisk_subset_frontier hv he'.1 he'.2.1 he'.2.2
    · intro x hx
      by_cases hxD : x ∈ ⋃ e : {e // e ∈ edgesAt K v}, (D e.1 \ Dbd e.1)
      · obtain ⟨⟨e, he⟩, hxe⟩ := mem_iUnion.mp hxD
        exact Or.inr (mem_iUnion₂.mpr ⟨e, hEv.mem_toFinset.mpr he, hxe.1⟩)
      · left
        rw [ht.freeFace_eq_sdiff hv]
        exact ⟨hx, hxD⟩
  have hcod : (Cpp v ∩ X) ∪ ⋃ e ∈ hEv.toFinset, F e = (Cpp v ∩ X) ∪ ⋃ e ∈ edgesAt K v, F e := by
    simp only [Set.Finite.mem_toFinset]
  rw [hdom, hcod] at hfin
  exact hfin

theorem IsTube.exists_isPLHomeomorphOn_glue {D Dbd : Finset E3 → Set E3}
    (ht : IsTube K N C D Dbd h N') {B : E3 → Set E3} {ψ : E3 → E3} {fv : E3 → E3 → E3}
    (hfv : ∀ v ∈ K.vertices, IsPLHomeomorphOn (fv v) (C v) (B v))
    (hfvψ : ∀ v ∈ K.vertices, EqOn (fv v) ψ (frontier (C v)))
    (hmeet : ∀ u ∈ K.vertices, ∀ v ∈ K.vertices, u ≠ v → B u ∩ B v ⊆ ψ '' (C u ∩ C v)) :
    ∃ f : E3 → E3, IsPLHomeomorphOn f N (⋃ v ∈ K.vertices, B v) ∧
      ∀ v ∈ K.vertices, EqOn f (fv v) (C v) := by
  classical
  let f : E3 → E3 := fun x =>
    if hx : ∃ v, v ∈ K.vertices ∧ x ∈ C v then fv hx.choose x else x
  have hfC : ∀ v ∈ K.vertices, EqOn f (fv v) (C v) := by
    intro v hv x hx
    have hex : ∃ v, v ∈ K.vertices ∧ x ∈ C v := ⟨v, hv, hx⟩
    have hch := hex.choose_spec
    change (if hx : ∃ v, v ∈ K.vertices ∧ x ∈ C v then fv hx.choose x else x) = fv v x
    rw [dite_eq_left hex]
    by_cases heq : hex.choose = v
    · rw [heq]
    · have h1 : x ∈ frontier (C hex.choose) :=
        ht.dualCell_inter_subset_frontier hch.1 hv heq ⟨hch.2, hx⟩
      have h2 : x ∈ frontier (C v) :=
        ht.dualCell_inter_subset_frontier hv hch.1 (Ne.symm heq) ⟨hx, hch.2⟩
      rw [hfvψ _ hch.1 h1, hfvψ v hv h2]
  have hind : ∀ W : Finset E3, (↑W : Set E3) ⊆ K.vertices →
      IsPolyhedron (⋃ v ∈ W, C v) ∧ IsPLHomeomorphOn f (⋃ v ∈ W, C v) (⋃ v ∈ W, B v) := by
    intro W
    induction W using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty]
      exact ⟨IsPolyhedron.empty, bijOn_empty f, fun x hx => absurd hx (notMem_empty x),
        fun x hx => absurd hx (notMem_empty x)⟩
    | insert a W haW ih =>
      intro hW
      have ha : a ∈ K.vertices := hW (Finset.mem_coe.mpr (Finset.mem_insert_self a W))
      have hW' : (↑W : Set E3) ⊆ K.vertices := fun w hw =>
        hW (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hw)))
      obtain ⟨hPpoly, hIH⟩ := ih hW'
      have hfa : IsPLHomeomorphOn f (C a) (B a) := (hfv a ha).congr (hfC a ha)
      have hmeet' : f '' (C a ∩ ⋃ w ∈ W, C w) = B a ∩ ⋃ w ∈ W, B w := by
        apply Subset.antisymm
        · rintro _ ⟨x, ⟨hxa, hxW⟩, rfl⟩
          obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp hxW
          have hw' := hW' (Finset.mem_coe.mpr hw)
          refine ⟨hfa.bijOn.mapsTo hxa, mem_iUnion₂.mpr ⟨w, hw, ?_⟩⟩
          rw [hfC w hw' hxw]
          exact (hfv w hw').bijOn.mapsTo hxw
        · rintro y ⟨hya, hyW⟩
          obtain ⟨w, hw, hyw⟩ := mem_iUnion₂.mp hyW
          have hw' := hW' (Finset.mem_coe.mpr hw)
          have haw : a ≠ w := fun h' => haW (h' ▸ hw)
          obtain ⟨x, ⟨hxa, hxw⟩, rfl⟩ := hmeet a ha w hw' haw ⟨hya, hyw⟩
          refine ⟨x, ⟨hxa, mem_iUnion₂.mpr ⟨w, hw, hxw⟩⟩, ?_⟩
          rw [hfC a ha hxa]
          exact hfvψ a ha (ht.dualCell_inter_subset_frontier ha hw' haw ⟨hxa, hxw⟩)
      have hU := hfa.union hIH (ht.dualBall a ha).isPolyhedron hPpoly hmeet'
      rw [Finset.set_biUnion_insert, Finset.set_biUnion_insert]
      exact ⟨(ht.dualBall a ha).isPolyhedron.union hPpoly, hU⟩
  obtain ⟨-, hfin⟩ := hind ht.finite_vertices.toFinset (by simp)
  simp only [Set.Finite.mem_toFinset] at hfin
  rw [ht.unionEq]
  exact ⟨f, hfin, hfC⟩

end DifferentialGeometry.Topology.PiecewiseLinear
