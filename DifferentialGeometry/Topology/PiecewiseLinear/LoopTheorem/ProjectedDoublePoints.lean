/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.DoublePointCover
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem hasDoublePointSheetsAt_of_isLocallyInjective [T2Space X] [T2Space Y]
    {P : Set X} (hP : IsCompact P) {f : X → Y} (hf : ContinuousOn f P)
    (hloc : IsLocallyInjective (P.domRestrict f))
    (hcard : ∀ y, (P ∩ f ⁻¹' {y}).encard ≤ 2)
    {y : Y} (hy : y ∈ doublePointSet f P) : HasDoublePointSheetsAt f P y := by
  let _ : CompactSpace P := isCompact_iff_compactSpace.mp hP
  obtain ⟨a, ha, b, hb, hab, hay, hby⟩ := hy
  let a' : P := ⟨a, ha⟩
  let b' : P := ⟨b, hb⟩
  have hab' : a' ≠ b' := fun h => hab (congrArg Subtype.val h)
  obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := t2_separation hab'
  obtain ⟨Ua, hUa, haUa, hinja⟩ := hloc a'
  obtain ⟨Ub, hUb, hbUb, hinjb⟩ := hloc b'
  obtain ⟨A', hA'nhds, hA'compact, hA'sub⟩ :=
    exists_mem_nhds_isCompact_mapsTo (continuous_id : Continuous (id : P → P))
      ((hUa.inter hU).mem_nhds ⟨haUa, haU⟩)
  obtain ⟨B', hB'nhds, hB'compact, hB'sub⟩ :=
    exists_mem_nhds_isCompact_mapsTo (continuous_id : Continuous (id : P → P))
      ((hUb.inter hV).mem_nhds ⟨hbUb, hbV⟩)
  let A : Set X := Subtype.val '' A'
  let B : Set X := Subtype.val '' B'
  have hAP : A ⊆ P := by rintro x ⟨z, hz, rfl⟩; exact z.2
  have hBP : B ⊆ P := by rintro x ⟨z, hz, rfl⟩; exact z.2
  have hAnhds : A ∈ 𝓝[P] a := mem_nhds_subtype_iff_nhdsWithin.mp hA'nhds
  have hBnhds : B ∈ 𝓝[P] b := mem_nhds_subtype_iff_nhdsWithin.mp hB'nhds
  have hinjA : InjOn f A := by
    rintro x ⟨x', hx', rfl⟩ z ⟨z', hz', rfl⟩ hxz
    exact congrArg Subtype.val (hinja (hA'sub hx').1 (hA'sub hz').1 hxz)
  have hinjB : InjOn f B := by
    rintro x ⟨x', hx', rfl⟩ z ⟨z', hz', rfl⟩ hxz
    exact congrArg Subtype.val (hinjb (hB'sub hx').1 (hB'sub hz').1 hxz)
  have hAB : Disjoint A B := by
    apply disjoint_left.mpr
    rintro x ⟨x', hx', rfl⟩ ⟨z', hz', hzx⟩
    have hzx' : z' = x' := Subtype.ext hzx
    exact disjoint_left.mp hUV (hA'sub hx').2 (hzx' ▸ (hB'sub hz').2)
  have hAemb : IsEmbedding (A.domRestrict f) := by
    let _ : CompactSpace A :=
      isCompact_iff_compactSpace.mp (hA'compact.image continuous_subtype_val)
    exact ((hf.mono hAP).domRestrict.isClosedEmbedding
      (injOn_iff_injective.mp hinjA)).isEmbedding
  have hBemb : IsEmbedding (B.domRestrict f) := by
    let _ : CompactSpace B :=
      isCompact_iff_compactSpace.mp (hB'compact.image continuous_subtype_val)
    exact ((hf.mono hBP).domRestrict.isClosedEmbedding
      (injOn_iff_injective.mp hinjB)).isEmbedding
  have hfiber : P ∩ f ⁻¹' {y} = {a, b} :=
    fiber_eq_pair_of_encard_le_two f P ha hb hab hay hby (hcard y)
  exact ⟨a, b, A, B, ⟨a', mem_of_mem_nhds hA'nhds, rfl⟩,
    ⟨b', mem_of_mem_nhds hB'nhds, rfl⟩, hay, hby, hAP, hBP, hAB, hAnhds, hBnhds,
    hAemb, hBemb, eventually_preimage_subset_union_of_fiber_eq_pair f hP hf hfiber hAnhds hBnhds⟩

theorem isCompact_doublePointPreimage_of_isLocallyInjective [T2Space X] [T2Space Y]
    {P : Set X} (hP : IsCompact P) {f : X → Y} (hf : ContinuousOn f P)
    (hloc : IsLocallyInjective (P.domRestrict f)) : IsCompact (doublePointPreimage f P) := by
  have hclosed := (isCompact_doublePointSet_of_isLocallyInjective hP hf hloc).isClosed
  exact hP.of_isClosed_subset (hf.preimage_isClosed_of_isClosed hP.isClosed hclosed)
    inter_subset_left

theorem isCoveringMap_doublePointProjection_of_isLocallyInjective [T2Space X] [T2Space Y]
    {P : Set X} (hP : IsCompact P) {f : X → Y} (hf : ContinuousOn f P)
    (hloc : IsLocallyInjective (P.domRestrict f))
    (hcard : ∀ y, (P ∩ f ⁻¹' {y}).encard ≤ 2) :
    IsCoveringMap (doublePointProjection f P) := by
  let _ : CompactSpace (doublePointPreimage f P) := isCompact_iff_compactSpace.mp
    (isCompact_doublePointPreimage_of_isLocallyInjective hP hf hloc)
  apply isLocalHomeomorph_iff_isCoveringMap.mp
  exact isLocalHomeomorph_doublePointProjection
    (fun _ hy => hasDoublePointSheetsAt_of_isLocallyInjective hP hf hloc hcard hy)

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem encard_fiber_doublePointProjection
    {P : Set X} {f : X → Y} (hcard : ∀ y, (P ∩ f ⁻¹' {y}).encard ≤ 2)
    (y : doublePointSet f P) : ((doublePointProjection f P) ⁻¹' {y}).encard = 2 := by
  let Q := doublePointPreimage f P
  have himage : Subtype.val '' ((doublePointProjection f P) ⁻¹' {y}) =
      P ∩ f ⁻¹' {(y : Y)} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2.1, congrArg Subtype.val hz⟩
    · rintro ⟨hx, hfx⟩
      have hxy : f x = (y : Y) := hfx
      have hxQ : x ∈ Q := ⟨hx, by change f x ∈ doublePointSet f P; rw [hxy]; exact y.2⟩
      exact ⟨⟨x, hxQ⟩, Subtype.ext hfx, rfl⟩
  obtain ⟨a, ha, b, hb, hab, hay, hby⟩ := y.2
  rw [← Subtype.val_injective.encard_image, himage,
    fiber_eq_pair_of_encard_le_two f P ha hb hab hay hby (hcard y), encard_pair hab]

namespace NormalSystem

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem DoubleCoverDiagram.exists_projected_map_of_embeddedDisk
    {S : NormalSystem E} {T : NormalSystem F} (R : DoubleCoverDiagram S T)
    (D : EmbeddedDisk T) :
    ∃ (f : EuclideanSpace ℝ (Fin 2) → E) (γ : freeLoop S.boundaryNeighborhoodSpace)
      (q : Path S.basepoint (γ 0)),
      f = R.projection ∘ D.map ∧ γ = R.boundaryMap.comp D.boundaryLoop ∧
      IsPiecewiseAffineOn f D.domain ∧ MapsTo f D.domain S.manifoldComplex.space ∧
      IsLocallyInjective (D.domain.domRestrict f) ∧
      (∀ y, (D.domain ∩ f ⁻¹' {y}).encard ≤ 2) ∧
      D.domain ∩ f ⁻¹' S.boundaryComplex.space = frontier D.domain ∧
      f '' D.domain ∩ S.boundaryComplex.space = f '' frontier D.domain ∧
      range (fun θ => (γ θ : E)) = f '' frontier D.domain ∧
      ¬conjugacyClassMeets (normalSystemLoopConjugacyClass S.basepoint γ q) S.normalSubgroup ∧
      IsCoveringMap (doublePointProjection f D.domain) ∧
      ∀ y : doublePointSet f D.domain, ((doublePointProjection f D.domain) ⁻¹' {y}).encard = 2 := by
  let f := R.projection ∘ D.map
  have hmap : MapsTo D.map D.domain T.ambientComplex.space :=
    fun _ hx => T.manifoldComplex_space_subset_ambient (D.mapsTo hx)
  have hpl : IsPiecewiseAffineOn f D.domain := by
    have h := R.isPiecewiseAffineOn_projection.comp D.isPLHomeomorphOn.isPiecewiseAffineOn
    have hinter : D.domain ∩ D.map ⁻¹' T.ambientComplex.space = D.domain :=
      inter_eq_left.mpr hmap
    rwa [hinter] at h
  obtain ⟨hloc, hcard⟩ := Covering.locally_injective_fiber_le_of_isCoveringMap_restrict
    R.isCoveringMap (fun _ => rfl) D.isPLHomeomorphOn.isPiecewiseAffineOn.continuousOn
    D.isPLHomeomorphOn.bijOn.injOn hmap (fun y => (R.fiber_card y).le)
  have hlocal : IsLocallyInjective (D.domain.domRestrict f) :=
    Covering.isLocallyInjective_domRestrict_iff.mpr hloc
  let γ := R.boundaryMap.comp D.boundaryLoop
  let q : Path S.basepoint (γ 0) :=
    (D.connector.map R.boundaryMap.continuous).cast R.basepoint_eq.symm rfl
  have hboundary : range (fun θ => (γ θ : E)) = f '' frontier D.domain := by
    calc
      range (fun θ => (γ θ : E)) =
          range (R.projection ∘ fun θ => (D.boundaryLoop θ : F)) := by
        congr 1
        funext θ
        exact R.boundaryMap_eq (D.boundaryLoop θ)
      _ = R.projection '' range (fun θ => (D.boundaryLoop θ : F)) := range_comp _ _
      _ = f '' frontier D.domain := by rw [D.boundary_range, image_comp]
  have hpre : D.domain ∩ f ⁻¹' S.boundaryComplex.space = frontier D.domain := by
    apply Subset.antisymm
    · rintro x ⟨hx, hfx⟩
      exact D.boundary_preimage.subset
        ⟨hx, R.preimage_boundaryComplex_subset ⟨D.mapsTo hx, hfx⟩⟩
    · intro x hx
      obtain ⟨θ, hθ⟩ := hboundary.symm.subset (mem_image_of_mem f hx)
      refine ⟨D.boundary_preimage.superset hx |>.1, ?_⟩
      change f x ∈ S.boundaryComplex.space
      rw [← hθ]
      exact derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex (γ θ).2
  have hinter : f '' D.domain ∩ S.boundaryComplex.space = f '' frontier D.domain := by
    rw [← image_inter_preimage, hpre]
  let _ : S.normalSubgroup.Normal := S.normal
  have havoid : ¬conjugacyClassMeets
      (normalSystemLoopConjugacyClass T.basepoint D.boundaryLoop D.connector)
      (S.normalSubgroup.comap (FundamentalGroup.mapOfEq R.boundaryMap R.basepoint_eq)) := by
    rw [← R.normalSubgroup_eq]
    exact D.loopClass_avoids_normal
  exact ⟨f, γ, q, rfl, rfl, hpl, R.projection_mapsTo.comp hmap, hlocal, hcard,
    hpre, hinter, hboundary, normalSystemLoopConjugacyClass_map_avoids
      R.boundaryMap R.basepoint_eq D.boundaryLoop D.connector S.normalSubgroup havoid,
    isCoveringMap_doublePointProjection_of_isLocallyInjective
      D.isPLBall_domain.isPolyhedron.isCompact
      hpl.continuousOn hlocal hcard, encard_fiber_doublePointProjection hcard⟩

end NormalSystem

end DifferentialGeometry.Topology.PiecewiseLinear
