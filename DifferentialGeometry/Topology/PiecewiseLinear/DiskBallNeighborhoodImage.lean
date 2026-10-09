/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.Simplex.NormedBall
import DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldOfLocallyFinitePLPieceIn
import DifferentialGeometry.Topology.PiecewiseLinear.LinkDimension
import DifferentialGeometry.Topology.PiecewiseLinear.LocalDiskBallNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere
import DifferentialGeometry.Topology.PiecewiseLinear.TopologicalCellNestedShell

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {Ea : Type*} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}

open Classical in
theorem LocallyFinitePLPieceIn.card_le_four (𝒦 : LocallyFinitePLPieceIn Ea 3 M U)
    (hK : IsCombinatorialManifold 3 𝒦.complex) {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) :
    t.card ≤ 4 := by
  obtain ⟨v, hv⟩ := 𝒦.complex.nonempty_of_mem_faces ht
  have hcard := Finset.card_erase_of_mem hv
  have hv' : ({v} : Finset Ea) ∈ 𝒦.complex.faces :=
    𝒦.complex.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  rcases (t.erase v).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.card_empty] at hcard
    omega
  · have hmem : t.erase v ∈ (SimplicialComplex.geometricLink 𝒦.complex {v}).faces :=
      (SimplicialComplex.mem_geometricLink_singleton 𝒦.complex v _).mpr
        ⟨hne, Finset.notMem_erase v t, by rwa [Finset.insert_erase hv]⟩
    have : Finite (SimplicialComplex.geometricLink 𝒦.complex {v}).faces :=
      (𝒦.geometricLink_faces_finite hv').to_subtype
    have hle : (t.erase v).card ≤ 2 + 1 :=
      card_le_of_isPLSphere (m := 2) (SimplicialComplex.geometricLink 𝒦.complex {v})
        (hK v hv') hmem
    omega

omit [FiniteDimensional ℝ Ea] in
theorem LocallyFinitePLPieceIn.finite_faces_inter_of_isCompact
    (𝒦 : LocallyFinitePLPieceIn Ea 3 M U) {C : Set Ea} (hC : IsCompact C)
    (hC𝒦 : C ⊆ 𝒦.complex.space) :
    {t : Finset Ea | t ∈ 𝒦.complex.faces ∧ (convexHull ℝ (t : Set Ea) ∩ C).Nonempty}.Finite := by
  have hCsub : IsCompact ((Subtype.val : 𝒦.complex.space → Ea) ⁻¹' C) := by
    rw [Subtype.isCompact_iff, image_preimage_eq_iff.mpr]
    · exact hC
    · intro x hx
      exact ⟨⟨x, hC𝒦 hx⟩, rfl⟩
  have hfin := 𝒦.locallyFinite.finite_nonempty_inter_compact hCsub
  refine (hfin.image fun i : 𝒦.complex.faces => (i : Finset Ea)).subset ?_
  rintro t ⟨ht, x, hxt, hxC⟩
  exact ⟨⟨t, ht⟩, ⟨⟨x, hC𝒦 hxC⟩, hxt, hxC⟩, rfl⟩

open Classical in
theorem LocallyFinitePLPieceIn.exists_isPLBall_nhdsWithin_space_of_isPLBall_two
    (𝒦 : LocallyFinitePLPieceIn Ea 3 M U) (hK : IsCombinatorialManifold 3 𝒦.complex)
    {D : Set Ea} (hD : IsPLBall 2 D) (hD𝒦 : D ⊆ 𝒦.complex.space) {O : Set Ea} (hO : IsOpen O)
    (hDO : D ⊆ O) :
    ∃ N : Set Ea, IsPLBall 3 N ∧ D ⊆ N ∧ N ⊆ 𝒦.complex.space ∩ O ∧
      ∀ x ∈ D, N ∈ 𝓝[𝒦.complex.space] x := by
  have hDc : IsCompact D := hD.isPolyhedron.isCompact
  obtain ⟨F₁, hF₁⟩ : ∃ F₁ : Set (Finset Ea),
      F₁ = {t | t ∈ 𝒦.complex.faces ∧ (convexHull ℝ (t : Set Ea) ∩ D).Nonempty} := ⟨_, rfl⟩
  have hF₁fin : F₁.Finite := by
    rw [hF₁]
    exact 𝒦.finite_faces_inter_of_isCompact hDc hD𝒦
  obtain ⟨V₁, hV₁⟩ : ∃ V₁ : Set Ea, V₁ = ⋃ t ∈ F₁, (t : Set Ea) := ⟨_, rfl⟩
  have hV₁fin : V₁.Finite := by
    rw [hV₁]
    exact hF₁fin.biUnion fun t _ => t.finite_toSet
  have hV₁v : ∀ v ∈ V₁, ({v} : Finset Ea) ∈ 𝒦.complex.faces := by
    intro v hv
    rw [hV₁] at hv
    obtain ⟨t, ht, hvt⟩ := mem_iUnion₂.mp hv
    rw [hF₁] at ht
    exact 𝒦.complex.down_closed ht.1 (Finset.singleton_subset_iff.mpr hvt)
      (Finset.singleton_nonempty v)
  obtain ⟨X, hX⟩ : ∃ X : Set Ea, X = ⋃ v ∈ V₁, closedStar 𝒦.complex v := ⟨_, rfl⟩
  have hstarfin : ∀ v ∈ V₁,
      {s | s ∈ 𝒦.complex.faces ∧ v ∈ convexHull ℝ (s : Set Ea)}.Finite := by
    intro v hv
    refine ((𝒦.cofaces_finite (hV₁v v hv)).image
      fun i : 𝒦.complex.faces => (i : Finset Ea)).subset ?_
    rintro s ⟨hs, hvs⟩
    exact ⟨⟨s, hs⟩, Finset.singleton_subset_iff.mpr
      (mem_of_mem_convexHull_of_singleton_mem 𝒦.complex (hV₁v v hv) hs hvs), rfl⟩
  have hXc : IsCompact X := by
    rw [hX]
    refine hV₁fin.isCompact_biUnion fun v hv => ?_
    exact (hstarfin v hv).isCompact_biUnion fun s _ =>
      s.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hX𝒦 : X ⊆ 𝒦.complex.space := by
    rw [hX]
    refine iUnion₂_subset fun v _ => ?_
    exact iUnion₂_subset fun s hs => 𝒦.complex.convexHull_subset_space hs.1
  have hTfin : (restrict 𝒦.complex X).faces.Finite := by
    refine (𝒦.finite_faces_inter_of_isCompact hXc hX𝒦).subset fun t ht => ⟨ht.1, ?_⟩
    obtain ⟨v, hv⟩ := 𝒦.complex.nonempty_of_mem_faces ht.1
    have hvt : v ∈ convexHull ℝ (t : Set Ea) := subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)
    exact ⟨v, hvt, ht.2 hvt⟩
  have : Finite (restrict 𝒦.complex X).faces := hTfin.to_subtype
  have hTcard : ∀ s ∈ (restrict 𝒦.complex X).faces, s.card ≤ 4 :=
    fun s hs => 𝒦.card_le_four hK hs.1
  have hmeetT : ∀ t ∈ 𝒦.complex.faces, (convexHull ℝ (t : Set Ea) ∩ D).Nonempty →
      t ∈ (restrict 𝒦.complex X).faces := by
    intro t ht hmeet
    have htF : t ∈ F₁ := by
      rw [hF₁]
      exact ⟨ht, hmeet⟩
    refine ⟨ht, ?_⟩
    obtain ⟨v, hv⟩ := 𝒦.complex.nonempty_of_mem_faces ht
    have hvV : v ∈ V₁ := by
      rw [hV₁]
      exact mem_iUnion₂.mpr ⟨t, htF, hv⟩
    intro y hy
    rw [hX]
    exact mem_iUnion₂.mpr ⟨v, hvV, mem_iUnion₂.mpr
      ⟨t, ⟨ht, subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)⟩, hy⟩⟩
  have hlkV : ∀ w ∈ V₁,
      IsPLSphere 2 (SimplicialComplex.geometricLink (restrict 𝒦.complex X) {w}).space := by
    intro w hw
    have heq : SimplicialComplex.geometricLink (restrict 𝒦.complex X) {w} =
        SimplicialComplex.geometricLink 𝒦.complex {w} := by
      ext u
      rw [SimplicialComplex.mem_geometricLink_singleton,
        SimplicialComplex.mem_geometricLink_singleton]
      constructor
      · rintro ⟨hne, hwu, hins⟩
        exact ⟨hne, hwu, hins.1⟩
      · rintro ⟨hne, hwu, hins⟩
        refine ⟨hne, hwu, hins, ?_⟩
        intro y hy
        rw [hX]
        exact mem_iUnion₂.mpr ⟨w, hw, mem_iUnion₂.mpr
          ⟨insert w u, ⟨hins, subset_convexHull ℝ _ (by simp)⟩, hy⟩⟩
    rw [heq]
    exact hK w (hV₁v w hw)
  obtain ⟨Bad, hBad⟩ : ∃ Bad : Set Ea, Bad = ⋃ t ∈ {t | t ∈ (restrict 𝒦.complex X).faces ∧
      ¬ ((t : Set Ea) ⊆ V₁)}, convexHull ℝ (t : Set Ea) := ⟨_, rfl⟩
  have hBadc : IsClosed Bad := by
    rw [hBad]
    exact ((hTfin.subset fun t ht => ht.1).isCompact_biUnion
      fun t _ => t.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed
  have hDBad : ∀ x ∈ D, x ∉ Bad := by
    intro x hx hxB
    rw [hBad] at hxB
    obtain ⟨t, ⟨htT, hnot⟩, hxt⟩ := mem_iUnion₂.mp hxB
    apply hnot
    intro v hv
    rw [hV₁]
    refine mem_iUnion₂.mpr ⟨t, ?_, hv⟩
    rw [hF₁]
    exact ⟨htT.1, x, hxt, hx⟩
  have hO' : IsOpen (O ∩ Badᶜ) := hO.inter hBadc.isOpen_compl
  have hDO' : D ⊆ O ∩ Badᶜ := fun x hx => ⟨hDO hx, hDBad x hx⟩
  have hlk : ∀ t ∈ (restrict 𝒦.complex X).faces,
      (convexHull ℝ (t : Set Ea) ∩ (O ∩ Badᶜ)).Nonempty → ∀ w ∈ t,
        IsPLSphere 2 (SimplicialComplex.geometricLink (restrict 𝒦.complex X) {w}).space := by
    intro t ht hmeet w hw
    apply hlkV w
    by_contra hwV
    obtain ⟨y, hyt, -, hyB⟩ := hmeet
    apply hyB
    rw [hBad]
    exact mem_iUnion₂.mpr ⟨t, ⟨ht, fun h => hwV (h hw)⟩, hyt⟩
  have hDT : D ⊆ (restrict 𝒦.complex X).space := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := 𝒦.complex.mem_space_iff.mp (hD𝒦 hx)
    exact (restrict 𝒦.complex X).convexHull_subset_space (hmeetT t ht ⟨x, hxt, hx⟩) hxt
  obtain ⟨N, hN, hDN, hNT, hNn⟩ :=
    exists_isPLBall_nhdsWithin_of_isPLBall_two hTcard hO' hlk hD hDT hDO'
  have hTn : ∀ x ∈ D, (restrict 𝒦.complex X).space ∈ 𝓝[𝒦.complex.space] x := by
    intro x hx
    let F : 𝒦.complex.faces → Set 𝒦.complex.space := fun s =>
      (Subtype.val : 𝒦.complex.space → Ea) ⁻¹' convexHull ℝ ((s : Finset Ea) : Set Ea)
    have hFclosed (s : 𝒦.complex.faces) : IsClosed (F s) :=
      (s.1.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed.preimage continuous_subtype_val
    have hFloc : LocallyFinite F := by
      simpa only [F] using 𝒦.locallyFinite
    let I := {s : 𝒦.complex.faces // (s : Finset Ea) ∉ (restrict 𝒦.complex X).faces}
    have hWclosed : IsClosed (⋃ i : I, F i.val) :=
      (hFloc.comp_injective Subtype.val_injective).isClosed_iUnion fun i => hFclosed i.val
    have hxnot : (⟨x, hD𝒦 hx⟩ : 𝒦.complex.space) ∉ ⋃ i : I, F i.val := by
      intro h
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      exact i.property (hmeetT i.val.1 i.val.2 ⟨x, hi, hx⟩)
    have hpre : (Subtype.val : 𝒦.complex.space → Ea) ⁻¹' (restrict 𝒦.complex X).space ∈
        𝓝 (⟨x, hD𝒦 hx⟩ : 𝒦.complex.space) := by
      refine Filter.mem_of_superset (hWclosed.isOpen_compl.mem_nhds hxnot) ?_
      intro z hz
      obtain ⟨s, hs, hzs⟩ := 𝒦.complex.mem_space_iff.mp z.property
      have hsT : s ∈ (restrict 𝒦.complex X).faces := by
        by_contra hsT
        exact hz (mem_iUnion.mpr ⟨⟨⟨s, hs⟩, hsT⟩, hzs⟩)
      exact (restrict 𝒦.complex X).convexHull_subset_space hsT hzs
    exact preimage_coe_mem_nhds_subtype.mp hpre
  refine ⟨N, hN, hDN, fun y hy =>
    ⟨space_mono_of_faces_subset (restrict_faces_subset 𝒦.complex X) (hNT hy).1, (hNT hy).2.1⟩,
    fun x hx => nhdsWithin_le_of_mem (hTn x hx) (hNn x hx)⟩

theorem Moise305Tame.exists_isPLCellOn_superset_image_of_isPLBall_two
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
    (hU : IsOpen U) (𝒦 : LocallyFinitePLPieceIn Ea 3 M U)
    (hK : IsCombinatorialManifold 3 𝒦.complex) {h : M → M₂} (hhc : ContinuousOn h U)
    (hhi : InjOn h U) {D : Set Ea} (hD : IsPLBall 2 D) (hD𝒦 : D ⊆ 𝒦.complex.space)
    {c : OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M₂) {W : Set M₂} (hW : IsOpen W) (hWc : W ⊆ c.source)
    (hDW : h '' (𝒦.map '' D) ⊆ W) :
    ∃ C B : Set M₂, IsPLCellOn 3 C B ∧ h '' (𝒦.map '' D) ⊆ interior C ∧ C ⊆ W := by
  have hmapU : MapsTo 𝒦.map 𝒦.complex.space U := 𝒦.bijOn.mapsTo
  have hGc : ContinuousOn (h ∘ 𝒦.map) 𝒦.complex.space := hhc.comp 𝒦.continuousOn hmapU
  obtain ⟨O, hO, hOeq⟩ := continuousOn_iff'.mp hGc W hW
  have hDO : D ⊆ O := by
    intro x hx
    have hx' : x ∈ (h ∘ 𝒦.map) ⁻¹' W ∩ 𝒦.complex.space :=
      ⟨hDW ⟨𝒦.map x, ⟨x, hx, rfl⟩, rfl⟩, hD𝒦 hx⟩
    rw [hOeq] at hx'
    exact hx'.1
  obtain ⟨N, hN, hDN, hN𝒦O, hNn⟩ :=
    𝒦.exists_isPLBall_nhdsWithin_space_of_isPLBall_two hK hD hD𝒦 hO hDO
  have hNW : ∀ y ∈ N, h (𝒦.map y) ∈ W := by
    intro y hy
    have hy' : y ∈ O ∩ 𝒦.complex.space := ⟨(hN𝒦O hy).2, (hN𝒦O hy).1⟩
    rw [← hOeq] at hy'
    exact hy'.1
  have hYW : h '' (𝒦.map '' N) ⊆ W := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact hNW y hy
  have hYc : h '' (𝒦.map '' N) ⊆ c.source := hYW.trans hWc
  have hNc : IsCompact N := hN.isPolyhedron.isCompact
  have hN𝒦 : N ⊆ 𝒦.complex.space := fun y hy => (hN𝒦O hy).1
  have hcell : IsTopologicalCell 3 (c '' (h '' (𝒦.map '' N))) := by
    obtain ⟨r, hr⟩ := hN
    have : CompactSpace N := isCompact_iff_compactSpace.mp hNc
    have hcomp : ContinuousOn (c ∘ (h ∘ 𝒦.map)) N :=
      c.continuousOn.comp (hGc.mono hN𝒦) fun y hy => hYc ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    let G : N → c '' (h '' (𝒦.map '' N)) := fun y =>
      ⟨c (h (𝒦.map y)), ⟨_, ⟨_, ⟨y, y.2, rfl⟩, rfl⟩, rfl⟩⟩
    have hGcont : Continuous G :=
      (hcomp.comp_continuous continuous_subtype_val Subtype.property).subtype_mk _
    have hGbij : Function.Bijective G := by
      refine ⟨fun y z hyz => ?_, fun w => ?_⟩
      · have h1 : c (h (𝒦.map y)) = c (h (𝒦.map z)) := congrArg Subtype.val hyz
        have h2 := c.injOn (hYc ⟨_, ⟨y, y.2, rfl⟩, rfl⟩) (hYc ⟨_, ⟨z, z.2, rfl⟩, rfl⟩) h1
        have h3 := hhi (hmapU (hN𝒦 y.2)) (hmapU (hN𝒦 z.2)) h2
        exact Subtype.ext (𝒦.bijOn.injOn (hN𝒦 y.2) (hN𝒦 z.2) h3)
      · obtain ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, hw⟩ := w.2
        exact ⟨⟨y, hy⟩, Subtype.ext hw⟩
    let ψ := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective G hGbij) hGcont
    exact ⟨(ψ.symm.trans hr.homeomorph.symm).trans
      (DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph
        (EuclideanSpace.equiv (Fin 3) ℝ).symm)⟩
  have hKY : h '' (𝒦.map '' D) ⊆ interior (h '' (𝒦.map '' N)) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨V, hV, hVN⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hNn x hx)
    obtain ⟨V', hV'V, hV'o, hxV'⟩ := mem_nhds_iff.mp hV
    have hopen1 : IsOpen (𝒦.map '' (V' ∩ 𝒦.complex.space)) := by
      obtain ⟨Z, hZ, hZeq⟩ :=
        𝒦.isEmbedding.isInducing.isOpen_iff.mp (hV'o.preimage continuous_subtype_val)
      have heq : 𝒦.map '' (V' ∩ 𝒦.complex.space) = Z ∩ U := by
        ext y
        constructor
        · rintro ⟨z, ⟨hzV, hz𝒦⟩, rfl⟩
          refine ⟨?_, hmapU hz𝒦⟩
          have hz : (⟨z, hz𝒦⟩ : 𝒦.complex.space) ∈
              (fun w : 𝒦.complex.space => 𝒦.map w) ⁻¹' Z := by
            rw [hZeq]
            exact hzV
          exact hz
        · rintro ⟨hyZ, hyU⟩
          obtain ⟨z, hz𝒦, rfl⟩ := 𝒦.bijOn.surjOn hyU
          have hz : (⟨z, hz𝒦⟩ : 𝒦.complex.space) ∈
              (fun w : 𝒦.complex.space => 𝒦.map w) ⁻¹' Z := hyZ
          rw [hZeq] at hz
          exact ⟨z, ⟨hz, hz𝒦⟩, rfl⟩
      rw [heq]
      exact hZ.inter hU
    have hsub1 : 𝒦.map '' (V' ∩ 𝒦.complex.space) ⊆ U := by
      rintro _ ⟨z, hz, rfl⟩
      exact hmapU hz.2
    have hopen2 : IsOpen (h '' (𝒦.map '' (V' ∩ 𝒦.complex.space))) :=
      isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 3)) hopen1
        (hhc.mono hsub1) (hhi.mono hsub1)
    have hsub2 : h '' (𝒦.map '' (V' ∩ 𝒦.complex.space)) ⊆ h '' (𝒦.map '' N) :=
      image_mono (image_mono fun y hy => hVN ⟨hV'V hy.1, hy.2⟩)
    exact interior_maximal hsub2 hopen2 ⟨_, ⟨x, ⟨hxV', hD𝒦 hx⟩, rfl⟩, rfl⟩
  have hKc : IsCompact (h '' (𝒦.map '' D)) :=
    (hD.isPolyhedron.isCompact.image_of_continuousOn
      (𝒦.continuousOn.mono hD𝒦)).image_of_continuousOn
        (hhc.mono (image_subset_iff.mpr fun x hx => hmapU (hD𝒦 hx)))
  obtain ⟨C, B, hCB, hKC, hCY⟩ :=
    Moise305Tame.exists_isPLCellOn_of_isTopologicalCell hc hYc hcell hKc hKY
  exact ⟨C, B, hCB, hKC, hCY.trans (interior_subset.trans hYW)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
