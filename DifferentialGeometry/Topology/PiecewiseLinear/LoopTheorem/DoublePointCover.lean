/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCarrier
import DifferentialGeometry.Topology.Covering.TwoSheetComponents

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def doublePointPreimage {X Y : Type*} (f : X → Y) (P : Set X) : Set X :=
  P ∩ f ⁻¹' doublePointSet f P

def doublePointProjection {X Y : Type*} (f : X → Y) (P : Set X) :
    doublePointPreimage f P → doublePointSet f P :=
  fun x ↦ ⟨f x, x.2.2⟩

def HasDoublePointSheetsAt
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (P : Set X) (y : Y) : Prop :=
  ∃ (a b : X) (A B : Set X), a ∈ A ∧ b ∈ B ∧ f a = y ∧ f b = y ∧
    A ⊆ P ∧ B ⊆ P ∧ Disjoint A B ∧ A ∈ nhdsWithin a P ∧
      B ∈ nhdsWithin b P ∧ IsEmbedding (A.domRestrict f) ∧
        IsEmbedding (B.domRestrict f) ∧ ∀ᶠ z in nhds y, P ∩ f ⁻¹' {z} ⊆ A ∪ B

theorem isLocalHomeomorph_of_isEmbedding_image_mem_nhds
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (h : ∀ x, ∃ A : Set X, A ∈ nhds x ∧ IsEmbedding (A.domRestrict f) ∧
      f '' A ∈ nhds (f x)) :
    IsLocalHomeomorph f := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro x
  obtain ⟨A, hA, hAemb, hAimage⟩ := h x
  let V := interior (f '' A)
  let U := f ⁻¹' V ∩ A
  have hxA : x ∈ A := mem_of_mem_nhds hA
  have hxV : f x ∈ V := mem_interior_iff_mem_nhds.mpr hAimage
  have hVopen : IsOpen V := isOpen_interior
  have hpre_subtype :
      ((↑) : A → X) ⁻¹' (f ⁻¹' V) ∈ nhds (⟨x, hxA⟩ : A) :=
    hAemb.continuous.continuousAt (hVopen.mem_nhds hxV)
  have hpre_within : f ⁻¹' V ∈ nhdsWithin x A :=
    preimage_coe_mem_nhds_subtype.mp hpre_subtype
  have hpre : f ⁻¹' V ∈ nhds x := by
    rwa [nhdsWithin_eq_nhds.mpr hA] at hpre_within
  have hU : U ∈ nhds x := Filter.inter_mem hpre hA
  refine ⟨U, hU, ?_⟩
  have hUA : U ⊆ A := inter_subset_right
  have hUemb : IsEmbedding (U.domRestrict f) := by
    simpa only [Set.domRestrict_eq, Function.comp_def] using
      hAemb.comp (IsEmbedding.inclusion hUA)
  refine ⟨hUemb, ?_⟩
  rw [Set.range_domRestrict]
  have hVA : V ⊆ f '' A := interior_subset
  have himage : f '' U = V := by
    apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      exact hz.1
    · intro y hy
      obtain ⟨z, hzA, hzy⟩ := hVA hy
      refine ⟨z, ⟨?_, hzA⟩, hzy⟩
      change f z ∈ V
      rw [hzy]
      exact hy
  rw [himage]
  exact hVopen

theorem mem_nhdsWithin_of_mem_nhdsWithin_of_mem_nhdsWithin
    {X : Type*} [TopologicalSpace X] {A P Q : Set X} {x : X}
    (hA : A ∈ nhdsWithin x P) (hP : P ∈ nhdsWithin x Q) : A ∈ nhdsWithin x Q := by
  obtain ⟨U, hU, hUA⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hA
  obtain ⟨V, hV, hVP⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hP
  apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
  refine ⟨U ∩ V, Filter.inter_mem hU hV, ?_⟩
  rintro z ⟨⟨hzU, hzV⟩, hzQ⟩
  exact hUA ⟨hzU, hVP ⟨hzV, hzQ⟩⟩

theorem isLocalHomeomorph_doublePointProjection
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} {P : Set X}
    (h : ∀ y ∈ doublePointSet f P, HasDoublePointSheetsAt f P y) :
    IsLocalHomeomorph (doublePointProjection f P) := by
  apply isLocalHomeomorph_of_isEmbedding_image_mem_nhds
  intro x
  let S := doublePointSet f P
  let Q := doublePointPreimage f P
  let p := doublePointProjection f P
  have hy : f x ∈ S := x.2.2
  obtain ⟨a, b, A₁, A₂, ha, hb, hfa, hfb, hA₁P, hA₂P, hdisjoint,
    hA₁nhds, hA₂nhds, hA₁emb, hA₂emb, heventually⟩ := h (f x) hy
  have hcover := heventually.self_of_nhds
  have hxSheets : (x : X) ∈ A₁ ∪ A₂ :=
    hcover ⟨x.2.1, rfl⟩
  have hinj₁ : InjOn f A₁ := Set.injOn_iff_injective.mpr hA₁emb.injective
  have hinj₂ : InjOn f A₂ := Set.injOn_iff_injective.mpr hA₂emb.injective
  have himage₁ : f '' A₁ ∈ nhdsWithin (f x) S := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds heventually,
      @self_mem_nhdsWithin Y _ (f x) S] with z hzcover hzS
    exact (mem_doublePointSet_iff_mem_image_inter_of_injOn f hA₁P
      hA₂P hdisjoint hinj₁ hinj₂ hzcover).mp hzS |>.1
  have himage₂ : f '' A₂ ∈ nhdsWithin (f x) S := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds heventually,
      @self_mem_nhdsWithin Y _ (f x) S] with z hzcover hzS
    exact (mem_doublePointSet_iff_mem_image_inter_of_injOn f hA₁P
      hA₂P hdisjoint hinj₁ hinj₂ hzcover).mp hzS |>.2
  rcases hxSheets with hx₁ | hx₂
  · have hxa : (x : X) = a := hinj₁ hx₁ ha hfa.symm
    let A : Set Q := ((↑) : Q → X) ⁻¹' A₁
    have hPWithinQ : P ∈ nhdsWithin (x : X) Q :=
      Filter.mem_of_superset self_mem_nhdsWithin inter_subset_left
    have hAWithinQ : A₁ ∈ nhdsWithin (x : X) Q :=
      mem_nhdsWithin_of_mem_nhdsWithin_of_mem_nhdsWithin
        (by
          rw [congrArg (fun z ↦ nhdsWithin z P) hxa]
          exact hA₁nhds)
        hPWithinQ
    have hA : A ∈ nhds x := preimage_coe_mem_nhds_subtype.mpr hAWithinQ
    have hmaps : MapsTo (fun z : Q ↦ (z : X)) A A₁ := fun _ hz ↦ hz
    have htoSheet : IsEmbedding hmaps.restrict :=
      IsEmbedding.subtypeVal.restrict hmaps
    have htoY : IsEmbedding (fun z : A ↦ f (z : X)) := by
      change IsEmbedding (A₁.domRestrict f ∘ hmaps.restrict)
      exact hA₁emb.comp htoSheet
    have hAemb : IsEmbedding (A.domRestrict p) := by
      apply (IsEmbedding.of_comp_iff IsEmbedding.subtypeVal).mp
      simpa only [p, doublePointProjection, Set.domRestrict_eq, Function.comp_def] using htoY
    have hpimage : p '' A = ((↑) : S → Y) ⁻¹' (f '' A₁) := by
      ext z
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨q, hq, rfl⟩
      · intro hz
        change (z : Y) ∈ f '' A₁ at hz
        obtain ⟨a, ha, hfa⟩ := hz
        have hfaS : a ∈ f ⁻¹' S := by
          change f a ∈ S
          rw [hfa]
          exact z.2
        have haQ : a ∈ Q := ⟨hA₁P ha, hfaS⟩
        refine ⟨(⟨a, haQ⟩ : Q), ha, ?_⟩
        apply Subtype.ext
        exact hfa
    refine ⟨A, hA, hAemb, ?_⟩
    rw [hpimage]
    exact preimage_coe_mem_nhds_subtype.mpr himage₁
  · have hxb : (x : X) = b := hinj₂ hx₂ hb hfb.symm
    let A : Set Q := ((↑) : Q → X) ⁻¹' A₂
    have hPWithinQ : P ∈ nhdsWithin (x : X) Q :=
      Filter.mem_of_superset self_mem_nhdsWithin inter_subset_left
    have hAWithinQ : A₂ ∈ nhdsWithin (x : X) Q :=
      mem_nhdsWithin_of_mem_nhdsWithin_of_mem_nhdsWithin
        (by
          rw [congrArg (fun z ↦ nhdsWithin z P) hxb]
          exact hA₂nhds)
        hPWithinQ
    have hA : A ∈ nhds x := preimage_coe_mem_nhds_subtype.mpr hAWithinQ
    have hmaps : MapsTo (fun z : Q ↦ (z : X)) A A₂ := fun _ hz ↦ hz
    have htoSheet : IsEmbedding hmaps.restrict :=
      IsEmbedding.subtypeVal.restrict hmaps
    have htoY : IsEmbedding (fun z : A ↦ f (z : X)) := by
      change IsEmbedding (A₂.domRestrict f ∘ hmaps.restrict)
      exact hA₂emb.comp htoSheet
    have hAemb : IsEmbedding (A.domRestrict p) := by
      apply (IsEmbedding.of_comp_iff IsEmbedding.subtypeVal).mp
      simpa only [p, doublePointProjection, Set.domRestrict_eq, Function.comp_def] using htoY
    have hpimage : p '' A = ((↑) : S → Y) ⁻¹' (f '' A₂) := by
      ext z
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨q, hq, rfl⟩
      · intro hz
        change (z : Y) ∈ f '' A₂ at hz
        obtain ⟨a, ha, hfa⟩ := hz
        have hfaS : a ∈ f ⁻¹' S := by
          change f a ∈ S
          rw [hfa]
          exact z.2
        have haQ : a ∈ Q := ⟨hA₂P ha, hfaS⟩
        refine ⟨(⟨a, haQ⟩ : Q), ha, ?_⟩
        apply Subtype.ext
        exact hfa
    refine ⟨A, hA, hAemb, ?_⟩
    rw [hpimage]
    exact preimage_coe_mem_nhds_subtype.mpr himage₂

theorem doublePointSheetsAt_of_hasPLDoubleCrossingAt_chart
    {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [TopologicalSpace M] {f : E → M} {P : Set E} {y : M}
    (hf : ContinuousOn f P) (e : OpenPartialHomeomorph M F) (hy : y ∈ e.source)
    (hcross : HasPLDoubleCrossingAt (e ∘ f) (P ∩ f ⁻¹' e.source) (e y)) :
    HasDoublePointSheetsAt f P y := by
  obtain ⟨a, b, A, B, ha, hb, hfa, hfb, hAP, hBP, hAB, hAnhds, hBnhds,
    hApl, hBpl, _, hcover⟩ := hcross
  have hfaSource : f a ∈ e.source := (hAP ha).2
  have hfbSource : f b ∈ e.source := (hBP hb).2
  have hfay : f a = y := by
    apply e.injOn hfaSource hy
    exact hfa
  have hfby : f b = y := by
    apply e.injOn hfbSource hy
    exact hfb
  have hAP' : A ⊆ P := fun _ hx ↦ (hAP hx).1
  have hBP' : B ⊆ P := fun _ hx ↦ (hBP hx).1
  have hPnhdsA : P ∩ f ⁻¹' e.source ∈ nhdsWithin a P := by
    apply Filter.inter_mem self_mem_nhdsWithin
    exact (hf a (hAP' ha)).preimage_mem_nhdsWithin
      (e.open_source.mem_nhds hfaSource)
  have hPnhdsB : P ∩ f ⁻¹' e.source ∈ nhdsWithin b P := by
    apply Filter.inter_mem self_mem_nhdsWithin
    exact (hf b (hBP' hb)).preimage_mem_nhdsWithin
      (e.open_source.mem_nhds hfbSource)
  have hAnhds' : A ∈ nhdsWithin a P :=
    mem_nhdsWithin_of_mem_nhdsWithin_of_mem_nhdsWithin hAnhds hPnhdsA
  have hBnhds' : B ∈ nhdsWithin b P :=
    mem_nhdsWithin_of_mem_nhdsWithin_of_mem_nhdsWithin hBnhds hPnhdsB
  have hemb : IsEmbedding (fun z : e.source ↦ e z) := by
    change IsEmbedding (((↑) : e.target → F) ∘ e.toHomeomorphSourceTarget)
    exact IsEmbedding.subtypeVal.comp e.toHomeomorphSourceTarget.isEmbedding
  have hAmap : MapsTo f A e.source := fun _ hx ↦ (hAP hx).2
  have hBmap : MapsTo f B e.source := fun _ hx ↦ (hBP hx).2
  have hAcomp : IsEmbedding (A.domRestrict (e ∘ f)) := by
    change IsEmbedding (((↑) : ((e ∘ f) '' A) → F) ∘ hApl.homeomorph)
    exact IsEmbedding.subtypeVal.comp hApl.homeomorph.isEmbedding
  have hBcomp : IsEmbedding (B.domRestrict (e ∘ f)) := by
    change IsEmbedding (((↑) : ((e ∘ f) '' B) → F) ∘ hBpl.homeomorph)
    exact IsEmbedding.subtypeVal.comp hBpl.homeomorph.isEmbedding
  have hAtoSource : IsEmbedding hAmap.restrict := by
    apply hemb.of_comp_iff.mp
    change IsEmbedding (A.domRestrict (e ∘ f))
    exact hAcomp
  have hBtoSource : IsEmbedding hBmap.restrict := by
    apply hemb.of_comp_iff.mp
    change IsEmbedding (B.domRestrict (e ∘ f))
    exact hBcomp
  have hAemb : IsEmbedding (A.domRestrict f) := by
    change IsEmbedding (((↑) : e.source → M) ∘ hAmap.restrict)
    exact IsEmbedding.subtypeVal.comp hAtoSource
  have hBemb : IsEmbedding (B.domRestrict f) := by
    change IsEmbedding (((↑) : e.source → M) ∘ hBmap.restrict)
    exact IsEmbedding.subtypeVal.comp hBtoSource
  have hcover' : ∀ᶠ z in nhds y, P ∩ f ⁻¹' {z} ⊆ A ∪ B := by
    filter_upwards [e.open_source.mem_nhds hy, (e.continuousAt hy) hcover]
      with z hzSource hzcover
    intro x hx
    have hfx : f x = z := hx.2
    apply hzcover
    constructor
    · exact ⟨hx.1, by change f x ∈ e.source; rw [hfx]; exact hzSource⟩
    · change e (f x) = e z
      rw [hfx]
  exact ⟨a, b, A, B, ha, hb, hfay, hfby, hAP', hBP', hAB,
    hAnhds', hBnhds', hAemb, hBemb, hcover'⟩

theorem doublePointSheetsAt_of_hasPLBoundaryDoubleCrossingAt_chart
    {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [TopologicalSpace M] {f : E → M} {P : Set E} {y : M}
    (hf : ContinuousOn f P) (e : OpenPartialHomeomorph M F) (hy : y ∈ e.source)
    {N : Set F}
    (hcross : HasPLBoundaryDoubleCrossingAt (e ∘ f)
      (P ∩ f ⁻¹' e.source) N (e y)) :
    HasDoublePointSheetsAt f P y := by
  obtain ⟨a, b, A, B, ha, hb, hfa, hfb, hAP, hBP, hAB, hAnhds, hBnhds,
    hApl, hBpl, -, hcover⟩ := hcross
  have hfaSource : f a ∈ e.source := (hAP ha).2
  have hfbSource : f b ∈ e.source := (hBP hb).2
  have hfay : f a = y := by
    apply e.injOn hfaSource hy
    exact hfa
  have hfby : f b = y := by
    apply e.injOn hfbSource hy
    exact hfb
  have hAP' : A ⊆ P := fun _ hx ↦ (hAP hx).1
  have hBP' : B ⊆ P := fun _ hx ↦ (hBP hx).1
  have hPnhdsA : P ∩ f ⁻¹' e.source ∈ nhdsWithin a P := by
    apply Filter.inter_mem self_mem_nhdsWithin
    exact (hf a (hAP' ha)).preimage_mem_nhdsWithin
      (e.open_source.mem_nhds hfaSource)
  have hPnhdsB : P ∩ f ⁻¹' e.source ∈ nhdsWithin b P := by
    apply Filter.inter_mem self_mem_nhdsWithin
    exact (hf b (hBP' hb)).preimage_mem_nhdsWithin
      (e.open_source.mem_nhds hfbSource)
  have hAnhds' : A ∈ nhdsWithin a P :=
    mem_nhdsWithin_of_mem_nhdsWithin_of_mem_nhdsWithin hAnhds hPnhdsA
  have hBnhds' : B ∈ nhdsWithin b P :=
    mem_nhdsWithin_of_mem_nhdsWithin_of_mem_nhdsWithin hBnhds hPnhdsB
  have hemb : IsEmbedding (fun z : e.source ↦ e z) := by
    change IsEmbedding (((↑) : e.target → F) ∘ e.toHomeomorphSourceTarget)
    exact IsEmbedding.subtypeVal.comp e.toHomeomorphSourceTarget.isEmbedding
  have hAmap : MapsTo f A e.source := fun _ hx ↦ (hAP hx).2
  have hBmap : MapsTo f B e.source := fun _ hx ↦ (hBP hx).2
  have hAcomp : IsEmbedding (A.domRestrict (e ∘ f)) := by
    change IsEmbedding (((↑) : ((e ∘ f) '' A) → F) ∘ hApl.homeomorph)
    exact IsEmbedding.subtypeVal.comp hApl.homeomorph.isEmbedding
  have hBcomp : IsEmbedding (B.domRestrict (e ∘ f)) := by
    change IsEmbedding (((↑) : ((e ∘ f) '' B) → F) ∘ hBpl.homeomorph)
    exact IsEmbedding.subtypeVal.comp hBpl.homeomorph.isEmbedding
  have hAtoSource : IsEmbedding hAmap.restrict := by
    apply hemb.of_comp_iff.mp
    change IsEmbedding (A.domRestrict (e ∘ f))
    exact hAcomp
  have hBtoSource : IsEmbedding hBmap.restrict := by
    apply hemb.of_comp_iff.mp
    change IsEmbedding (B.domRestrict (e ∘ f))
    exact hBcomp
  have hAemb : IsEmbedding (A.domRestrict f) := by
    change IsEmbedding (((↑) : e.source → M) ∘ hAmap.restrict)
    exact IsEmbedding.subtypeVal.comp hAtoSource
  have hBemb : IsEmbedding (B.domRestrict f) := by
    change IsEmbedding (((↑) : e.source → M) ∘ hBmap.restrict)
    exact IsEmbedding.subtypeVal.comp hBtoSource
  have hcover' : ∀ᶠ z in nhds y, P ∩ f ⁻¹' {z} ⊆ A ∪ B := by
    filter_upwards [e.open_source.mem_nhds hy, (e.continuousAt hy) hcover]
      with z hzSource hzcover
    intro x hx
    have hfx : f x = z := hx.2
    apply hzcover
    constructor
    · exact ⟨hx.1, by change f x ∈ e.source; rw [hfx]; exact hzSource⟩
    · change e (f x) = e z
      rw [hfx]
  exact ⟨a, b, A, B, ha, hb, hfay, hfby, hAP', hBP', hAB,
    hAnhds', hBnhds', hAemb, hBemb, hcover'⟩

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem doublePointProjection_isLocalHomeomorph
    (hD : NormalSingularCellData D BdM B) :
    IsLocalHomeomorph (doublePointProjection D D.domain) := by
  apply isLocalHomeomorph_doublePointProjection
  intro y hy
  obtain ⟨e, _, hye, hcross⟩ := hD.crossing y hy
  rcases hcross with ⟨-, N, hcross⟩ | ⟨-, hcross⟩
  · exact doublePointSheetsAt_of_hasPLBoundaryDoubleCrossingAt_chart
      D.continuousOn e hye hcross
  · exact doublePointSheetsAt_of_hasPLDoubleCrossingAt_chart D.continuousOn e hye hcross

theorem doublePointPreimage_isCompact [T2Space M]
    (hD : NormalSingularCellData D BdM B) :
    IsCompact (doublePointPreimage D D.domain) := by
  have hPcompact : IsCompact D.domain := D.isPLBall_domain.isPolyhedron.isCompact
  have hPlocal : IsLocallyInjective (D.domain.domRestrict D) := by
    rw [isLocallyInjective_iff_nhds]
    intro x
    obtain ⟨U, hU, hinj⟩ := hD.locallyInjective x x.2
    let V : Set D.domain := ((↑) : D.domain → EuclideanSpace ℝ (Fin 2)) ⁻¹' U
    refine ⟨V, preimage_coe_mem_nhds_subtype.mpr hU, ?_⟩
    intro a ha b hb hab
    apply Subtype.ext
    exact hinj ha hb hab
  have hScompact : IsCompact (doublePointSet D D.domain) :=
    isCompact_doublePointSet_of_isLocallyInjective hPcompact D.continuousOn hPlocal
  have hSclosed : IsClosed (doublePointSet D D.domain) := hScompact.isClosed
  have hPclosed : IsClosed D.domain := hPcompact.isClosed
  have hQclosed : IsClosed (doublePointPreimage D D.domain) :=
    D.continuousOn.preimage_isClosed_of_isClosed hPclosed hSclosed
  exact hPcompact.of_isClosed_subset hQclosed inter_subset_left

theorem doublePointProjection_isCoveringMap [T2Space M]
    (hD : NormalSingularCellData D BdM B) :
    IsCoveringMap (doublePointProjection D D.domain) := by
  let _ : CompactSpace (doublePointPreimage D D.domain) :=
    isCompact_iff_compactSpace.mp hD.doublePointPreimage_isCompact
  exact isLocalHomeomorph_iff_isCoveringMap.mp hD.doublePointProjection_isLocalHomeomorph

theorem doublePointProjection_isClosedMap [T2Space M]
    (hD : NormalSingularCellData D BdM B) :
    IsClosedMap (doublePointProjection D D.domain) := by
  let _ : CompactSpace (doublePointPreimage D D.domain) :=
    isCompact_iff_compactSpace.mp hD.doublePointPreimage_isCompact
  exact hD.doublePointProjection_isCoveringMap.continuous.isClosedMap

theorem doublePointProjection_fiber_encard_eq_two
    (hD : NormalSingularCellData D BdM B)
    (y : doublePointSet D D.domain) :
    ((doublePointProjection D D.domain) ⁻¹' {y}).encard = 2 := by
  let Q := doublePointPreimage D D.domain
  let fiber : Set Q := (doublePointProjection D D.domain) ⁻¹' {y}
  have himage : ((↑) : Q → EuclideanSpace ℝ (Fin 2)) '' fiber =
      D.domain ∩ D ⁻¹' {(y : M)} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hpzy : doublePointProjection D D.domain z = y := hz
      exact ⟨z.2.1, congrArg Subtype.val hpzy⟩
    · rintro ⟨hxD, hDxy⟩
      have hxS : x ∈ D ⁻¹' doublePointSet D D.domain := by
        change D x ∈ doublePointSet D D.domain
        change D x = (y : M) at hDxy
        rw [hDxy]
        exact y.2
      have hxQ : x ∈ Q := ⟨hxD, hxS⟩
      refine ⟨(⟨x, hxQ⟩ : Q), ?_, rfl⟩
      apply Subtype.ext
      exact hDxy
  calc
    fiber.encard = (((↑) : Q → EuclideanSpace ℝ (Fin 2)) '' fiber).encard :=
      (Subtype.val_injective.encard_image fiber).symm
    _ = (D.domain ∩ D ⁻¹' {(y : M)}).encard := congrArg Set.encard himage
    _ = 2 := hD.fiber_encard_eq_two y.2

theorem doublePointProjection_connected_or_two_components [T2Space M]
    (hD : NormalSingularCellData D BdM B)
    (J : Set (doublePointSet D D.domain)) [ConnectedSpace J] :
    ConnectedSpace ((doublePointProjection D D.domain) ⁻¹' J) ∨
      ∃ x y : (doublePointProjection D D.domain) ⁻¹' J,
        Disjoint (connectedComponent x) (connectedComponent y) ∧
        connectedComponent x ∪ connectedComponent y = univ ∧
        (∃ e : connectedComponent x ≃ₜ J,
          ∀ z : connectedComponent x,
            e z = J.restrictPreimage (doublePointProjection D D.domain) z) ∧
        ∃ e : connectedComponent y ≃ₜ J,
          ∀ z : connectedComponent y,
            e z = J.restrictPreimage (doublePointProjection D D.domain) z := by
  apply Topology.Covering.connectedSpace_or_exists_exactly_two_components_restrictPreimage
    J hD.doublePointProjection_isCoveringMap hD.doublePointProjection_isClosedMap
  intro y
  exact hD.doublePointProjection_fiber_encard_eq_two y

theorem doublePointProjection_branch_connected_or_two_components [T2Space M]
    (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch) :
    ConnectedSpace
        ((doublePointProjection D D.domain) ⁻¹' hD.singularSet.branchSet c) ∨
      ∃ x y :
          (doublePointProjection D D.domain) ⁻¹' hD.singularSet.branchSet c,
        Disjoint (connectedComponent x) (connectedComponent y) ∧
        connectedComponent x ∪ connectedComponent y = univ ∧
        (∃ e : connectedComponent x ≃ₜ hD.singularSet.branchSet c,
          ∀ z : connectedComponent x,
            e z = (hD.singularSet.branchSet c).restrictPreimage
              (doublePointProjection D D.domain) z) ∧
        ∃ e : connectedComponent y ≃ₜ hD.singularSet.branchSet c,
          ∀ z : connectedComponent y,
            e z = (hD.singularSet.branchSet c).restrictPreimage
              (doublePointProjection D D.domain) z := by
  let _ : ConnectedSpace (hD.singularSet.branchSet c) :=
    Subtype.connectedSpace (hD.singularSet.branchSet_isConnected c)
  exact hD.doublePointProjection_connected_or_two_components
    (hD.singularSet.branchSet c)

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
