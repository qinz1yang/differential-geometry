/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskBallNeighborhoodImage
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnInterior
import DifferentialGeometry.Topology.PiecewiseLinear.CompactEmbeddingApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.MarkedCircleTorus
import DifferentialGeometry.Topology.PiecewiseLinear.Section34OuterTorusTransport

open Set Topology

universe u

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type*} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]

private theorem exists_spine_image_inside_ball {N R : Set Ea} (hN : IsPLBall 3 N)
    (hR : IsPLSphere 1 R) (hRN : R ⊆ N) {f : Ea → E3}
    (hfc : ContinuousOn f N) (hfi : InjOn f N) (hRi : f '' R ⊆ interior (f '' N)) :
    ∃ S : Set E3, IsSpine S (f '' R) ∧ f '' R ⊆ interior S ∧ S ⊆ f '' N := by
  obtain ⟨Q, ρ, -, hρ⟩ := exists_isPLHomeomorphOn_euclidean_of_isPLBall hN
  let v := ρ ∘ Function.invFunOn f N
  have hfb := hfi.bijOn_image
  have hvc : ContinuousOn v (f '' N) := hρ.isPiecewiseAffineOn.continuousOn.comp
    (continuousOn_invFunOn_image_of_isCompact hN.isPolyhedron.isCompact hfc hfi)
    hfb.surjOn.mapsTo_invFunOn
  have hvi : InjOn v (f '' N) := by
    intro x hx y hy hxy
    have hi := hρ.bijOn.injOn (hfb.surjOn.mapsTo_invFunOn hx)
      (hfb.surjOn.mapsTo_invFunOn hy) hxy
    exact (hfb.invOn_invFunOn.2 hx).symm.trans
      ((congrArg f hi).trans (hfb.invOn_invFunOn.2 hy))
  have hvQ : v '' interior (f '' N) ⊆ Q := by
    rintro _ ⟨x, hx, rfl⟩
    exact hρ.bijOn.mapsTo (hfb.surjOn.mapsTo_invFunOn (interior_subset hx))
  have hvopen : IsOpen (v '' interior (f '' N)) :=
    invariance_of_domain_isOpen_image isOpen_interior (hvc.mono interior_subset)
      (hvi.mono interior_subset)
  have hρRi : ρ '' R ⊆ interior Q := by
    rintro _ ⟨x, hx, rfl⟩
    apply interior_maximal hvQ hvopen
    refine ⟨f x, hRi ⟨x, hx, rfl⟩, ?_⟩
    change ρ (Function.invFunOn f N (f x)) = ρ x
    rw [hfi.leftInvOn_invFunOn (hRN hx)]
  have hρR : IsPLSphere 1 (ρ '' R) :=
    hR.of_isPLHomeomorphOn (hρ.restrict hR.isPolyhedron hRN)
  obtain ⟨T, hTfin, -, hTQ, hRT, hspine⟩ :=
    hρR.exists_solid_torus_neighborhood_with_spine_subset_of_isOpen isOpen_interior hρRi
  let _ : Finite T.faces := hTfin.to_subtype
  let g := f ∘ Function.invFunOn ρ N
  have hgc : ContinuousOn g Q := hfc.comp hρ.isPiecewiseAffineOn_invFunOn.continuousOn
    hρ.symm.bijOn.mapsTo
  have hgi : InjOn g Q := fun x hx y hy hxy =>
    hρ.symm.bijOn.injOn hx hy
      (hfi (hρ.symm.bijOn.mapsTo hx) (hρ.symm.bijOn.mapsTo hy) hxy)
  have hTsub : T.space ⊆ Q := hTQ.trans interior_subset
  have hge : IsEmbedding (T.space.domRestrict g) := by
    let _ : CompactSpace T.space :=
      isCompact_iff_compactSpace.mp (SimplicialComplex.isCompact_geometricSpace T)
    exact ((hgc.mono hTsub).domRestrict.isClosedEmbedding
      (injOn_iff_injective.mp (hgi.mono hTsub))).isEmbedding
  have hgr : g '' (ρ '' R) = f '' R := by
    rw [image_image]
    apply EqOn.image_eq
    intro x hx
    change f (Function.invFunOn ρ N (ρ x)) = f x
    rw [hρ.bijOn.invOn_invFunOn.1 (hRN hx)]
  refine ⟨g '' T.space, hgr ▸ hspine.image_of_isEmbedding hge, ?_, ?_⟩
  · rw [← hgr]
    refine (image_mono hRT).trans (interior_maximal (image_mono interior_subset) ?_)
    exact invariance_of_domain_isOpen_image isOpen_interior
      (hgc.mono (interior_subset.trans hTsub)) (hgi.mono (interior_subset.trans hTsub))
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨Function.invFunOn ρ N x, hρ.symm.bijOn.mapsTo (hTsub hx), rfl⟩

variable {M₁ M₂ : Type*} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [TopologicalSpace M₂] [ChartedSpace E3 M₂] {U : Set M₁} {h : M₁ → M₂}

open Classical in
theorem exists_section34_source_rim_torus
    (hU : IsOpen U) (hh : IsEmbedding (U.domRestrict h))
    (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U) (hK : IsCombinatorialManifold 3 𝒦.complex)
    (s : Section34SimplexIndex 𝒦 3) (c : OpenPartialHomeomorph M₂ E3)
    (hbodyc : h '' simplexBody 𝒦 s.1 ⊆ c.source) :
    ∃ (S : Set E3) (O : Set M₁), IsSpine S (c '' (h '' simplexRim 𝒦 s.1)) ∧
      IsOpen O ∧ simplexRim 𝒦 s.1 ⊆ O ∧ O ⊆ U ∧
      h '' O ⊆ c.source ∧ c '' (h '' O) ⊆ interior S := by
  have hhc : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hhi : InjOn h U := fun x hx y hy hxy =>
    congrArg Subtype.val (@hh.injective ⟨x, hx⟩ ⟨y, hy⟩ hxy)
  let D := convexHull ℝ (s.1 : Set Ea)
  let R : Set Ea := ⋃ v ∈ s.1, convexHull ℝ ((s.1.erase v : Finset Ea) : Set Ea)
  have hD : IsPLBall 2 D :=
    isPLBall_convexHull_of_affineIndependent s.1 (𝒦.complex.indep s.2.1) s.2.2
  have hR : IsPLSphere 1 R :=
    isPLSphere_biUnion_erase s.1 (𝒦.complex.indep s.2.1) s.2.2
  have hRD : R ⊆ D := iUnion₂_subset fun v _ =>
    convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset v s.1))
  have hDK : D ⊆ 𝒦.complex.space := 𝒦.complex.convexHull_subset_space s.2.1
  have hrim : simplexRim 𝒦 s.1 = 𝒦.map '' R := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨τ, hτ, a, ha, rfl⟩ := mem_iUnion₂.mp hx
      obtain ⟨v, hvs, hvτ⟩ := Finset.exists_of_ssubset hτ
      refine ⟨a, mem_iUnion₂.mpr ⟨v, hvs, convexHull_mono ?_ ha⟩, rfl⟩
      intro z hz
      rw [Finset.coe_erase]
      exact ⟨Finset.coe_subset.mpr hτ.subset hz,
        fun hzv => hvτ ((mem_singleton_iff.mp hzv) ▸ hz)⟩
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨v, hv, hav⟩ := mem_iUnion₂.mp ha
      exact mem_iUnion₂.mpr ⟨s.1.erase v, Finset.erase_ssubset hv, a, hav, rfl⟩
  have hmapU : MapsTo 𝒦.map 𝒦.complex.space U := 𝒦.bijOn.mapsTo
  have hGc : ContinuousOn (h ∘ 𝒦.map) 𝒦.complex.space := hhc.comp 𝒦.continuousOn hmapU
  obtain ⟨V, hV, hVeq⟩ := continuousOn_iff'.mp hGc c.source c.open_source
  have hDV : D ⊆ V := by
    intro x hx
    have hx' : x ∈ (h ∘ 𝒦.map) ⁻¹' c.source ∩ 𝒦.complex.space :=
      ⟨hbodyc ⟨𝒦.map x, ⟨x, hx, rfl⟩, rfl⟩, hDK hx⟩
    rw [hVeq] at hx'
    exact hx'.1
  obtain ⟨N, hN, hDN, hNK', hNn⟩ :=
    𝒦.exists_isPLBall_nhdsWithin_space_of_isPLBall_two hK hD hDK hV hDV
  have hNK : N ⊆ 𝒦.complex.space := fun x hx => (hNK' hx).1
  have hNc : h '' (𝒦.map '' N) ⊆ c.source := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hx' : x ∈ V ∩ 𝒦.complex.space := ⟨(hNK' hx).2, hNK hx⟩
    rw [← hVeq] at hx'
    exact hx'.1
  have hNU : 𝒦.map '' N ⊆ U := image_subset_iff.mpr fun x hx => hmapU (hNK hx)
  have hDint : 𝒦.map '' D ⊆ interior (𝒦.map '' N) := by
    rintro _ ⟨x, hx, rfl⟩
    have hpre : (Subtype.val : 𝒦.complex.space → Ea) ⁻¹' N ∈
        𝓝 (⟨x, hDK hx⟩ : 𝒦.complex.space) := preimage_coe_mem_nhds_subtype.mpr (hNn x hx)
    have himage := 𝒦.isEmbedding.isInducing.image_mem_nhdsWithin hpre
    have hrange : range (fun z : 𝒦.complex.space => 𝒦.map z) = U := by
      change range (𝒦.map ∘ (Subtype.val : 𝒦.complex.space → Ea)) = U
      rw [range_comp, Subtype.range_coe, 𝒦.bijOn.image_eq]
    rw [hrange, nhdsWithin_eq_nhds.mpr (hU.mem_nhds (hmapU (hDK hx)))] at himage
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset himage (by rintro _ ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩)
  let f := c ∘ h ∘ 𝒦.map
  have hfc : ContinuousOn f N := c.continuousOn.comp (hGc.mono hNK)
    (fun x hx => hNc ⟨_, ⟨x, hx, rfl⟩, rfl⟩)
  have hfi : InjOn f N := by
    intro x hx y hy hxy
    exact 𝒦.bijOn.injOn (hNK hx) (hNK hy) (hhi (hmapU (hNK hx)) (hmapU (hNK hy))
      (c.injOn (hNc ⟨_, ⟨x, hx, rfl⟩, rfl⟩) (hNc ⟨_, ⟨y, hy, rfl⟩, rfl⟩) hxy))
  have hRi : f '' R ⊆ interior (f '' N) := by
    have hsrc : h '' interior (𝒦.map '' N) ⊆ c.source :=
      (image_mono interior_subset).trans hNc
    have hopen : IsOpen (c '' (h '' interior (𝒦.map '' N))) :=
      c.isOpen_image_of_subset_source
        (isOpen_image_of_continuousOn_injOn (E := E3) isOpen_interior
          (hhc.mono (interior_subset.trans hNU)) (hhi.mono (interior_subset.trans hNU))) hsrc
    have hsub : c '' (h '' interior (𝒦.map '' N)) ⊆ f '' N := by
      simpa only [f, image_comp] using image_mono (f := c) (image_mono (f := h)
        (interior_subset : interior (𝒦.map '' N) ⊆ 𝒦.map '' N))
    rintro _ ⟨x, hx, rfl⟩
    exact interior_maximal hsub hopen ⟨_, ⟨_, hDint ⟨x, hRD hx, rfl⟩, rfl⟩, rfl⟩
  obtain ⟨S, hspine, hRint, -⟩ := exists_spine_image_inside_ball hN hR (hRD.trans hDN) hfc hfi hRi
  have hfr : f '' R = c '' (h '' simplexRim 𝒦 s.1) := by rw [hrim]; simp only [f, image_comp]
  rw [hfr] at hspine hRint
  let O := U ∩ h ⁻¹' (c.source ∩ c ⁻¹' interior S)
  refine ⟨S, O, hspine, hhc.isOpen_inter_preimage hU (c.isOpen_inter_preimage isOpen_interior),
    ?_, inter_subset_left, ?_, ?_⟩
  · intro x hx
    have hxD : x ∈ simplexBody 𝒦 s.1 := by rw [hrim] at hx; exact image_mono hRD hx
    obtain ⟨z, hz, rfl⟩ := hxD
    exact ⟨hmapU (hDK hz), hbodyc ⟨_, ⟨z, hz, rfl⟩, rfl⟩,
      hRint ⟨_, ⟨_, hx, rfl⟩, rfl⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hx.2.1
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact hx.2.2

section CarrierFamily

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  {X Y : Type u} [TopologicalSpace X] [ChartedSpace E3 X]
  [MetricSpace Y] [ChartedSpace E3 Y] {V : Set X} {g : X → Y}

open Classical in
theorem exists_section34_source_rim_tori
    (hV : IsOpen V) (hg : IsEmbedding (V.domRestrict g))
    (𝒦 : LocallyFinitePLPieceIn A 3 X V) (hK : IsCombinatorialManifold 3 𝒦.complex)
    {η : X → ℝ} {H : Finset A → Set Y} (hH : Section34CarrierControl V 𝒦 g η H) :
    ∃ (ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph Y E3)
      (Sd : Section34SimplexIndex 𝒦 3 → Set E3)
      (O : Section34SimplexIndex 𝒦 3 → Set X),
      (∀ s, ct s ∈ (plGroupoid 3).maximalAtlas Y ∧ H s.1 ⊆ (ct s).source) ∧
      (∀ s, IsSpine (Sd s) (ct s '' (g '' simplexRim 𝒦 s.1))) ∧
      (∀ s, IsOpen (O s)) ∧ (∀ s, simplexRim 𝒦 s.1 ⊆ O s) ∧
      (∀ s, O s ⊆ V) ∧ (∀ s, g '' O s ⊆ (ct s).source) ∧
      ∀ s, ct s '' (g '' O s) ⊆ interior (Sd s) := by
  have hchart : ∀ s : Section34SimplexIndex 𝒦 3,
      ∃ c ∈ (plGroupoid 3).maximalAtlas Y, H s.1 ⊆ c.source :=
    fun s => hH.2.2.2.2.2 s.1 s.2.1
  choose ct hct hHct using hchart
  have hbody : ∀ s : Section34SimplexIndex 𝒦 3,
      g '' simplexBody 𝒦 s.1 ⊆ (ct s).source := by
    intro s
    apply Subset.trans _ (hHct s)
    apply Subset.trans _ interior_subset
    apply Subset.trans _ (hH.1 s.1 s.2.1)
    apply image_mono
    obtain ⟨a, ha⟩ := 𝒦.complex.nonempty_of_mem_faces s.2.1
    exact fun x hx => mem_iUnion₂.mpr ⟨a, ha, mem_iUnion₂.mpr ⟨s.1, ⟨s.2.1, ha⟩, hx⟩⟩
  have htorus := fun s => exists_section34_source_rim_torus hV hg 𝒦 hK s (ct s) (hbody s)
  choose Sd O hspine hOopen hRO hOV hOct hOSd using htorus
  exact ⟨ct, Sd, O, fun s => ⟨hct s, hHct s⟩, hspine, hOopen, hRO, hOV, hOct, hOSd⟩

end CarrierFamily

end DifferentialGeometry.Topology.PiecewiseLinear
