/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.OpenEmbeddingFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import DifferentialGeometry.Topology.PiecewiseLinear.HandlePieceSubsetOfEdgeCollars

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem interior_image_eq_image_interior_of_isCompact {f : E → E} {A : Set E}
    (hA : IsCompact A) (hf : ContinuousOn f A) (hinj : InjOn f A) :
    interior (f '' A) = f '' interior A := by
  rw [← range_domRestrict f A,
    interior_range_eq_image_preimage_interior hA _ hf.domRestrict hinj.injective]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, interior_subset hx⟩, hx, rfl⟩

theorem frontier_image_eq_image_frontier_of_isCompact {f : E → E} {A : Set E}
    (hA : IsCompact A) (hf : ContinuousOn f A) (hinj : InjOn f A) :
    frontier (f '' A) = f '' frontier A := by
  rw [(hA.image_of_continuousOn hf).isClosed.frontier_eq, hA.isClosed.frontier_eq,
    interior_image_eq_image_interior_of_isCompact hA hf hinj,
    image_sdiff_interior hinj subset_rfl]

end General

theorem exists_isOpen_inter_image_eq_of_isCompact {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {g : X → Y} {S : Set X} (hS : IsCompact S)
    (hg : ContinuousOn g S) (hinj : InjOn g S) {U : Set X} (hU : IsOpen U) :
    ∃ O : Set Y, IsOpen O ∧ O ∩ g '' S = g '' (U ∩ S) := by
  have _ : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hind : IsInducing (S.domRestrict g) :=
    (hg.domRestrict.isClosedEmbedding hinj.injective).isEmbedding.isInducing
  obtain ⟨O, hO, hOeq⟩ := hind.isOpen_iff.mp (hU.preimage continuous_subtype_val)
  refine ⟨O, hO, Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨hyO, x, hxS, rfl⟩
    have hmem : (⟨x, hxS⟩ : S) ∈ S.domRestrict g ⁻¹' O := hyO
    rw [hOeq] at hmem
    exact ⟨x, ⟨hmem, hxS⟩, rfl⟩
  · rintro _ ⟨x, ⟨hxU, hxS⟩, rfl⟩
    have hmem : (⟨x, hxS⟩ : S) ∈ ((↑) : S → X) ⁻¹' U := hxU
    rw [← hOeq] at hmem
    exact ⟨hmem, x, hxS, rfl⟩

theorem stdSimplex_subset_closure_openSimplex (n : ℕ) :
    Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2)) ⊆ closure (openSimplex (stdVertices n)) := by
  rw [← convexHull_stdVertices]
  exact convexHull_subset_closure_openSimplex
    (Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) (two_le_card_stdVertices n)))

section TubeTopology

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3}

theorem IsTube.injOn (ht : IsTube K N C D Dbd h N') : InjOn h N := by
  intro x hx y hy hxy
  have hxy' : N.domRestrict h ⟨x, hx⟩ = N.domRestrict h ⟨y, hy⟩ := hxy
  exact congrArg Subtype.val (ht.isEmbedding.injective hxy')

theorem IsTube.continuousOn (ht : IsTube K N C D Dbd h N') : ContinuousOn h N :=
  continuousOn_iff_continuous_domRestrict.mpr ht.isEmbedding.continuous

theorem IsTube.finite_vertices (ht : IsTube K N C D Dbd h N') : K.vertices.Finite :=
  Set.Finite.preimage Finset.singleton_injective.injOn ht.facesFinite

theorem IsTube.dualCell_subset (ht : IsTube K N C D Dbd h N') {v : E3} (hv : v ∈ K.vertices) :
    C v ⊆ N := by
  rw [ht.unionEq]
  exact subset_biUnion_of_mem (u := C) hv

theorem IsTube.isClosed (ht : IsTube K N C D Dbd h N') : IsClosed N := by
  rw [ht.unionEq]
  exact ht.finite_vertices.isClosed_biUnion fun v hv => (ht.dualBall v hv).isPolyhedron.isClosed

theorem IsTube.mem_dualCell (ht : IsTube K N C D Dbd h N') {v : E3} (hv : v ∈ K.vertices) :
    v ∈ C v := by
  have hmem : v ∈ C v ∩ K.vertices := by
    rw [ht.dualVertex hv]
    exact mem_singleton v
  exact hmem.1

theorem IsTube.card_eq_two_of_mem (ht : IsTube K N C D Dbd h N') {f : Finset E3}
    (hf : f ∈ K.faces) {a b : E3} (haf : a ∈ f) (hbf : b ∈ f) (hab : a ≠ b) : f.card = 2 :=
  le_antisymm (ht.oneDimensional f hf) (Finset.one_lt_card.mpr ⟨a, haf, b, hbf, hab⟩)

theorem IsTube.splitDisk_subset_frontier (ht : IsTube K N C D Dbd h N') {v : E3}
    (hv : v ∈ K.vertices) {e : Finset E3} (he : e ∈ K.faces) (hc : e.card = 2) (hve : v ∈ e) :
    D e ⊆ frontier (C v) := by
  obtain ⟨w, hwe, hwv⟩ := Finset.exists_mem_ne (by omega : 1 < e.card) v
  have hw : w ∈ K.vertices :=
    K.down_closed he (Finset.singleton_subset_iff.mpr hwe) (Finset.singleton_nonempty w)
  obtain ⟨r, hr, -⟩ := ht.splitCell e he hc
  have heq := ht.inter_eq_of_mem_faces hv hw hwv.symm he hve hwe
  have hI : IsPLBall 2 (C v ∩ C w) := by
    rw [heq]
    exact ⟨r, hr⟩
  rw [← heq]
  exact IsPLBall.inter_subset_frontier_of_isPLBall (n := 2) (ht.dualBall w hw) hI (by norm_num)

theorem IsTube.dualCell_inter_subset_frontier (ht : IsTube K N C D Dbd h N') {a b : E3}
    (ha : a ∈ K.vertices) (hb : b ∈ K.vertices) (hab : a ≠ b) :
    C a ∩ C b ⊆ frontier (C a) := by
  by_cases hadj : ∃ f ∈ K.faces, a ∈ f ∧ b ∈ f
  · obtain ⟨f, hf, haf, hbf⟩ := hadj
    rw [ht.inter_eq_of_mem_faces ha hb hab hf haf hbf]
    exact ht.splitDisk_subset_frontier ha hf (ht.card_eq_two_of_mem hf haf hbf hab) haf
  · rw [ht.inter_eq_empty_of_forall_notMem_faces ha hb hab
      fun f hf haf hbf => hadj ⟨f, hf, haf, hbf⟩]
    exact empty_subset _

theorem IsTube.splitDisk_sdiff_subset_interior (ht : IsTube K N C D Dbd h N') {u v : E3}
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v) {e : Finset E3}
    (he : e ∈ K.faces) (hue : u ∈ e) (hve : v ∈ e) : D e \ Dbd e ⊆ interior (C u ∪ C v) := by
  have hc : e.card = 2 := ht.card_eq_two_of_mem he hue hve huv
  rintro x ⟨hxD, hxb⟩
  have hxu : x ∈ C u := by
    rw [← ht.inter_eq_of_mem_faces hu hv huv he hue hve] at hxD
    exact hxD.1
  have hxint : x ∈ interior N := by
    by_contra hni
    apply hxb
    rw [← ht.splitProper e he hc]
    exact ⟨hxD, subset_closure (ht.dualCell_subset hu hxu), hni⟩
  have hfin : {w | w ∈ K.vertices ∧ w ≠ u ∧ w ≠ v}.Finite :=
    ht.finite_vertices.subset fun w hw => hw.1
  have hFcl : IsClosed (⋃ w ∈ {w | w ∈ K.vertices ∧ w ≠ u ∧ w ≠ v}, C w) :=
    hfin.isClosed_biUnion fun w hw => (ht.dualBall w hw.1).isPolyhedron.isClosed
  have hxF : x ∉ ⋃ w ∈ {w | w ∈ K.vertices ∧ w ≠ u ∧ w ≠ v}, C w := by
    intro hx
    obtain ⟨w, ⟨hw, hwu, hwv⟩, hxw⟩ := mem_iUnion₂.mp hx
    by_cases hadj : ∃ f ∈ K.faces, u ∈ f ∧ w ∈ f
    · obtain ⟨f, hf, huf, hwf⟩ := hadj
      have hxf : x ∈ D f := by
        rw [← ht.inter_eq_of_mem_faces hu hw (Ne.symm hwu) hf huf hwf]
        exact ⟨hxu, hxw⟩
      have hfe : e ≠ f := by
        rintro rfl
        rcases eq_or_eq_of_mem_of_card_eq_two hc hue hve huv hwf with h1 | h1
        · exact hwu h1
        · exact hwv h1
      exact disjoint_left.mp (ht.splitDisjoint he hc hf
        (ht.card_eq_two_of_mem hf huf hwf (Ne.symm hwu)) hfe) hxD hxf
    · have hmem : x ∈ C u ∩ C w := ⟨hxu, hxw⟩
      rw [ht.inter_eq_empty_of_forall_notMem_faces hu hw (Ne.symm hwu)
        fun f hf huf hwf => hadj ⟨f, hf, huf, hwf⟩] at hmem
      exact hmem
  refine mem_interior.mpr ⟨interior N \ ⋃ w ∈ {w | w ∈ K.vertices ∧ w ≠ u ∧ w ≠ v}, C w,
    ?_, isOpen_interior.sdiff hFcl, hxint, hxF⟩
  rintro y ⟨hyN, hyF⟩
  have hyN' := interior_subset hyN
  rw [ht.unionEq] at hyN'
  obtain ⟨w, hw, hyw⟩ := mem_iUnion₂.mp hyN'
  by_cases hwu : w = u
  · rw [hwu] at hyw
    exact Or.inl hyw
  by_cases hwv : w = v
  · rw [hwv] at hyw
    exact Or.inr hyw
  exact absurd (mem_iUnion₂.mpr ⟨w, ⟨hw, hwu, hwv⟩, hyw⟩) hyF

theorem IsTube.exists_dualCell_model (ht : IsTube K N C D Dbd h N') {a : E3}
    (ha : a ∈ K.vertices) :
    ∃ g : (Fin 4 → ℝ) → E3, ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) ∧
      InjOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 4)) ∧ g '' Convexity.StdSimplex.coordinateSet ℝ (Fin 4) = h '' C a ∧
      g '' stdSimplexBoundary 3 = frontier (h '' C a) ∧
      g '' openSimplex (stdVertices 2) = interior (h '' C a) := by
  obtain ⟨f, hf⟩ := ht.dualBall a ha
  have hCN := ht.dualCell_subset ha
  have hCc : IsCompact (C a) := (ht.dualBall a ha).isPolyhedron.isCompact
  have hbd : f '' stdSimplexBoundary 3 = frontier (C a) :=
    IsPLHomeomorphOn.image_stdSimplexBoundary_eq_frontier (n := 2) hf
  have hopen : f '' openSimplex (stdVertices 2) = interior (C a) := by
    have h1 : f '' openSimplex (stdVertices 2) = C a \ f '' stdSimplexBoundary 3 :=
      IsPLHomeomorphOn.image_openSimplex_stdVertices (n := 2) hf
    rw [h1, hbd, self_sdiff_frontier]
  have hcont : ContinuousOn h (C a) := ht.continuousOn.mono hCN
  have hinj : InjOn h (C a) := ht.injOn.mono hCN
  refine ⟨h ∘ f, hcont.comp hf.isPiecewiseAffineOn.continuousOn hf.bijOn.mapsTo,
    hinj.comp hf.bijOn.injOn hf.bijOn.mapsTo, ?_, ?_, ?_⟩
  · calc (h ∘ f) '' Convexity.StdSimplex.coordinateSet ℝ (Fin 4) = h '' (f '' Convexity.StdSimplex.coordinateSet ℝ (Fin (3 + 1))) :=
          image_comp _ _ _
      _ = h '' C a := by rw [hf.image_eq]
  · calc (h ∘ f) '' stdSimplexBoundary 3 = h '' (f '' stdSimplexBoundary 3) := image_comp _ _ _
      _ = h '' frontier (C a) := by rw [hbd]
      _ = frontier (h '' C a) :=
          (frontier_image_eq_image_frontier_of_isCompact hCc hcont hinj).symm
  · calc (h ∘ f) '' openSimplex (stdVertices 2) = h '' (f '' openSimplex (stdVertices 2)) :=
          image_comp _ _ _
      _ = h '' interior (C a) := by rw [hopen]
      _ = interior (h '' C a) :=
          (interior_image_eq_image_interior_of_isCompact hCc hcont hinj).symm

end TubeTopology

section Leaves

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' H B Jlo Jhi : ℤ → Set E3}

theorem exists_compact_connected_to_freeFace (ht : IsTube K N C D Dbd h N')
    (hv : v ∈ K.vertices) {e : Finset E3} (he : e ∈ K.faces) (hc : e.card = 2) (hve : v ∈ e) :
    ∃ Bv : Set E3, IsCompact Bv ∧ IsConnected Bv ∧ h v ∈ Bv ∧ Bv ⊆ h '' C v ∧
      Disjoint Bv (h '' D e) ∧
      (Bv ∩ h '' ((frontier (C v) ∩ frontier N) \
        ⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2 ∧ v ∈ f}, Dbd f)).Nonempty := by
  obtain ⟨p, hp⟩ := (ht.freeFaceConnected v hv).nonempty
  obtain ⟨g, hgc, -, hgim, -, hgint⟩ := ht.exists_dualCell_model hv
  have hCN := ht.dualCell_subset hv
  have hCc : IsCompact (C v) := (ht.dualBall v hv).isPolyhedron.isCompact
  have hcont : ContinuousOn h (C v) := ht.continuousOn.mono hCN
  have hinj : InjOn h (C v) := ht.injOn.mono hCN
  have hpC : p ∈ C v := hCc.isClosed.frontier_subset hp.1.1
  have hDC : D e ⊆ frontier (C v) := ht.splitDisk_subset_frontier hv he hc hve
  have hDsub : D e ⊆ C v := hDC.trans hCc.isClosed.frontier_subset
  have hpD : h p ∉ h '' D e := by
    rintro ⟨x, hxD, hxp⟩
    have hxp' : x = p := hinj (hDsub hxD) hpC hxp
    subst hxp'
    have hmem : x ∈ D e ∩ frontier N := ⟨hxD, hp.1.2⟩
    rw [ht.splitProper e he hc] at hmem
    exact hp.2 (mem_iUnion₂.mpr ⟨e, ⟨he, hc, hve⟩, hmem⟩)
  have hvint : h v ∈ interior (h '' C v) := by
    rw [interior_image_eq_image_interior_of_isCompact hCc hcont hinj]
    exact ⟨v, ht.mem_interior_dualCell hv, rfl⟩
  rw [← hgint] at hvint
  obtain ⟨q, hq, hgq⟩ := hvint
  have hpimg : h p ∈ g '' Convexity.StdSimplex.coordinateSet ℝ (Fin 4) := by
    rw [hgim]
    exact ⟨p, hpC, rfl⟩
  obtain ⟨s, hs, hgs⟩ := hpimg
  have hqΔ : q ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 4) := openSimplex_stdVertices_subset_stdSimplex hq
  have hseg : segment ℝ q s ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 4) :=
    (Convexity.StdSimplex.convex_coordinateSet ℝ _).segment_subset hqΔ hs
  have hqpos : ∀ i, 0 < q i := ((mem_openSimplex_stdVertices_iff 2).mp hq).1
  have hsegc : IsCompact (segment ℝ q s) := by
    rw [← Path.range_segment]
    exact isCompact_range (Path.segment q s).continuous
  have hfr : h '' D e ⊆ frontier (h '' C v) := by
    rw [frontier_image_eq_image_frontier_of_isCompact hCc hcont hinj]
    exact image_mono hDC
  refine ⟨g '' segment ℝ q s, hsegc.image_of_continuousOn (hgc.mono hseg),
    ((convex_segment q s).isConnected ⟨q, left_mem_segment ℝ q s⟩).image g (hgc.mono hseg),
    ⟨q, left_mem_segment ℝ q s, hgq⟩, ?_, ?_,
    ⟨h p, ⟨s, right_mem_segment ℝ q s, hgs⟩, p, hp, rfl⟩⟩
  · rw [← hgim]
    exact image_mono hseg
  · rw [disjoint_left]
    rintro _ ⟨z, ⟨a, b, ha, hb, hab, rfl⟩, rfl⟩ hzD
    rcases ha.eq_or_lt with ha0 | ha0
    · have hb1 : b = 1 := by linarith
      rw [← ha0, hb1, zero_smul, zero_add, one_smul, hgs] at hzD
      exact hpD hzD
    · have hzopen : a • q + b • s ∈ openSimplex (stdVertices 2) := by
        refine (mem_openSimplex_stdVertices_iff 2).mpr ⟨fun i => ?_, ?_⟩
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          have h1 := mul_pos ha0 (hqpos i)
          have h2 := mul_nonneg hb (hs.1 i)
          linarith
        · exact (hseg ⟨a, b, ha, hb, hab, rfl⟩).2
      have hzint : g (a • q + b • s) ∈ interior (h '' C v) := by
        rw [← hgint]
        exact ⟨_, hzopen, rfl⟩
      exact (hfr hzD).2 hzint

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
