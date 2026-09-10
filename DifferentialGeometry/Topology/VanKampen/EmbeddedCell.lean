/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import DifferentialGeometry.Topology.Attachment.Union
import DifferentialGeometry.Topology.Manifold.SameDimensionImmersion
import DifferentialGeometry.Topology.VanKampen.CellAttachmentFundamentalGroup

set_option autoImplicit false

open Set
open scoped ContinuousMap Manifold ContDiff

universe u

namespace DifferentialGeometry.Topology.ThreeManifold

open DifferentialGeometry.Topology


instance cellInteriorNonempty (n : ℕ) : Nonempty (CellInterior n) :=
  ⟨⟨0, by simp⟩⟩

noncomputable instance cellInteriorChartedSpace (n : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (CellInterior n) := by
  exact @Topology.IsOpenEmbedding.singletonChartedSpace
    (EuclideanSpace ℝ (Fin n)) _ (CellInterior n) _ (cellInteriorNonempty n)
    Subtype.val (isOpen_lt continuous_norm continuous_const).isOpenEmbedding_subtypeVal


def embeddedCellInteriorImage {M : Type u}
    (c : ClosedCell 3 → M) : Set M :=
  c '' Set.range (cellInteriorInclusion 3)


def embeddedCellInteriorMap {M : Type u}
    (c : ClosedCell 3 → M) : CellInterior 3 → M :=
  c ∘ cellInteriorInclusion 3


theorem range_embeddedCellInteriorMap {M : Type u}
    (c : ClosedCell 3 → M) :
    Set.range (embeddedCellInteriorMap c) = embeddedCellInteriorImage c := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨cellInteriorInclusion 3 a, ⟨a, rfl⟩, rfl⟩
  · rintro ⟨d, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩

theorem isOpen_embeddedCellInteriorImage_of_isLocalHomeomorph
    {M : Type u} [TopologicalSpace M] (c : ClosedCell 3 → M)
    (hlocal : IsLocalHomeomorph (embeddedCellInteriorMap c)) :
    IsOpen (embeddedCellInteriorImage c) := by
  rw [← range_embeddedCellInteriorMap c]
  exact hlocal.isOpenMap.isOpen_range

theorem isOpen_embeddedCellInteriorImage_of_isImmersion
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (c : ClosedCell 3 → M)
    (himm : Manifold.IsImmersion
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (embeddedCellInteriorMap c)) :
    IsOpen (embeddedCellInteriorImage c) :=
  isOpen_embeddedCellInteriorImage_of_isLocalHomeomorph c
    (DifferentialGeometry.Topology.isLocalHomeomorph_of_isImmersion_modelSelf himm)

theorem isOpen_embeddedCellInteriorImage_of_isSmoothEmbedding
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (c : ClosedCell 3 → M)
    (hsmooth : Manifold.IsSmoothEmbedding
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (embeddedCellInteriorMap c)) :
    IsOpen (embeddedCellInteriorImage c) :=
  isOpen_embeddedCellInteriorImage_of_isImmersion c hsmooth.isImmersion


def embeddedCellComplement {M : Type u}
    (c : ClosedCell 3 → M) : Set M :=
  (embeddedCellInteriorImage c)ᶜ


def embeddedCellBoundaryMap {M : Type u}
    (c : ClosedCell 3 → M) (hc : Function.Injective c) :
    CellBoundary 3 → embeddedCellComplement c :=
  fun b => ⟨c (cellBoundaryInclusion 3 b), by
    intro hb
    rcases hb with ⟨d, ⟨a, rfl⟩, hda⟩
    have hcell : cellInteriorInclusion 3 a = cellBoundaryInclusion 3 b := hc hda
    have hval : (a : EuclideanSpace ℝ (Fin 3)) = b := by
      simpa [cellInteriorInclusion, cellBoundaryInclusion] using
        congrArg (fun z : ClosedCell 3 => (z : EuclideanSpace ℝ (Fin 3))) hcell
    have := a.2
    rw [hval, b.2] at this
    exact (lt_irrefl (1 : ℝ)) this⟩


theorem continuous_embeddedCellBoundaryMap {M : Type u} [TopologicalSpace M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c) :
    Continuous (embeddedCellBoundaryMap c hc) := by
  apply Continuous.subtype_mk
  exact hcont.comp (continuous_cellBoundaryInclusion 3)


theorem embeddedCellComplement_union_range {M : Type u}
    (c : ClosedCell 3 → M) :
    embeddedCellComplement c ∪ Set.range c = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  by_cases hy : y ∈ embeddedCellInteriorImage c
  · rcases hy with ⟨d, hd, rfl⟩
    exact Or.inr ⟨d, rfl⟩
  · exact Or.inl hy


theorem cellBoundary_of_image_mem_embeddedCellComplement {M : Type u}
    (c : ClosedCell 3 → M) (d : ClosedCell 3)
    (hd : c d ∈ embeddedCellComplement c) :
    d ∈ Set.range (cellBoundaryInclusion 3) := by
  have hnot : ¬ ‖(d : EuclideanSpace ℝ (Fin 3))‖ < 1 := by
    intro hlt
    exact hd ⟨cellInteriorInclusion 3
      (⟨d, hlt⟩ : CellInterior 3), ⟨⟨d, hlt⟩, rfl⟩, rfl⟩
  have hEq : ‖(d : EuclideanSpace ℝ (Fin 3))‖ = 1 :=
    le_antisymm d.2 (le_of_not_gt hnot)
  exact ⟨⟨d, hEq⟩, by ext; rfl⟩


noncomputable def cellAdjunctionHomeomorphOfEmbeddedCell
    {M : Type u} [TopologicalSpace M] [T2Space M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (hopen : IsOpen (embeddedCellInteriorImage c)) :
    CellAdjunctionSpace 3 (embeddedCellBoundaryMap c hc) ≃ₜ M :=
  (adjunctionHomeomorphUnionImage (cellBoundaryInclusion 3)
      (embeddedCellBoundaryMap c hc) c (fun _ => rfl) hc hcont
      (cellBoundary_of_image_mem_embeddedCellComplement c) hopen.isClosed_compl).trans
    ((Homeomorph.setCongr (embeddedCellComplement_union_range c)).trans
      (Homeomorph.Set.univ M))


theorem cellAdjunctionHomeomorphOfEmbeddedCell_lower
    {M : Type u} [TopologicalSpace M] [T2Space M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (hopen : IsOpen (embeddedCellInteriorImage c)) (x : embeddedCellComplement c) :
    cellAdjunctionHomeomorphOfEmbeddedCell c hc hcont hopen
        (adjunctionLower (embeddedCellBoundaryMap c hc) x) = (x : M) := by
  simp only [cellAdjunctionHomeomorphOfEmbeddedCell, Homeomorph.trans_apply,
    Homeomorph.Set.univ_apply]
  exact congrArg Subtype.val
    (adjunctionHomeomorphUnionImage_lower (cellBoundaryInclusion 3)
      (embeddedCellBoundaryMap c hc) c (fun _ => rfl) hc hcont
      (cellBoundary_of_image_mem_embeddedCellComplement c) hopen.isClosed_compl x)

theorem connectedSpace_embeddedCellComplement
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (hopen : IsOpen (embeddedCellInteriorImage c))
    [LocallyConnectedSpace (embeddedCellComplement c)] :
    ConnectedSpace (embeddedCellComplement c) := by
  rw [connectedSpace_iff_connectedComponent]
  let z₀ : embeddedCellComplement c :=
    embeddedCellBoundaryMap c hc DifferentialGeometry.Topology.CellAttachment.cellBoundaryThreeNorth
  refine ⟨z₀, Set.eq_univ_of_forall fun x => ?_⟩
  by_contra hx
  have hne : connectedComponent x ≠ connectedComponent z₀ := by
    intro heq
    apply hx
    rw [← heq]
    exact mem_connectedComponent
  have hdisj : Disjoint (connectedComponent x) (connectedComponent z₀) :=
    connectedComponent_disjoint hne
  let _ : SimplyConnectedSpace (CellBoundary 3) :=
    DifferentialGeometry.Topology.CellAttachment.simplyConnectedSpace_cellBoundaryThree
  have hboundary : Set.range (embeddedCellBoundaryMap c hc) ⊆ connectedComponent z₀ :=
    (isPreconnected_range (continuous_embeddedCellBoundaryMap c hc hcont)).subset_connectedComponent
      ⟨DifferentialGeometry.Topology.CellAttachment.cellBoundaryThreeNorth, rfl⟩
  let C : Set M := Subtype.val '' connectedComponent x
  have hCrange : C ⊆ (Set.range c)ᶜ := by
    rintro y ⟨q, hqC, rfl⟩ ⟨d, hd⟩
    have hdK : c d ∈ embeddedCellComplement c := by
      rw [hd]
      exact q.2
    rcases cellBoundary_of_image_mem_embeddedCellComplement c d hdK with ⟨b, hb⟩
    have hqB : q ∈ Set.range (embeddedCellBoundaryMap c hc) := by
      refine ⟨b, Subtype.ext ?_⟩
      change c (cellBoundaryInclusion 3 b) = (q : M)
      rw [show cellBoundaryInclusion 3 b = d from hb, hd]
    exact Set.disjoint_left.mp hdisj hqC (hboundary hqB)
  have hrangeClosed : IsClosed (Set.range c) := by
    rw [← Set.image_univ]
    exact (isCompact_univ.image hcont).isClosed
  have hCopen : IsOpen C := by
    rcases isOpen_induced_iff.mp (isOpen_connectedComponent (x := x)) with
      ⟨O, hO, hOeq⟩
    have hCO : C = O ∩ (Set.range c)ᶜ := by
      ext y
      constructor
      · rintro ⟨q, hqC, rfl⟩
        have hqO : q ∈ Subtype.val ⁻¹' O := by
          rw [hOeq]
          exact hqC
        exact ⟨hqO, hCrange ⟨q, hqC, rfl⟩⟩
      · rintro ⟨hyO, hyRange⟩
        have hyK : y ∈ embeddedCellComplement c := by
          intro hyInterior
          exact hyRange ⟨Classical.choose hyInterior,
            Classical.choose_spec hyInterior |>.2⟩
        let q : embeddedCellComplement c := ⟨y, hyK⟩
        have hqC : q ∈ connectedComponent x := by
          rw [← hOeq]
          exact hyO
        exact ⟨q, hqC, rfl⟩
    rw [hCO]
    exact hO.inter hrangeClosed.isOpen_compl
  have hCclosed : IsClosed C := by
    exact hopen.isClosed_compl.isClosedEmbedding_subtypeVal.isClosedMap
      (connectedComponent x) isClosed_connectedComponent
  have hCuniv : C = Set.univ := (show IsClopen C from ⟨hCclosed, hCopen⟩).eq_univ
    ⟨x, ⟨x, mem_connectedComponent, rfl⟩⟩
  have hzC : (z₀ : M) ∈ C := by
    rw [hCuniv]
    trivial
  rcases hzC with ⟨q, hqC, hqz⟩
  have hqz' : q = z₀ := Subtype.ext hqz
  subst q
  exact Set.disjoint_left.mp hdisj hqC mem_connectedComponent

theorem pathConnectedSpace_embeddedCellComplement
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (hopen : IsOpen (embeddedCellInteriorImage c))
    [LocallyPathConnectedSpace (embeddedCellComplement c)] :
    PathConnectedSpace (embeddedCellComplement c) := by
  let _ : ConnectedSpace (embeddedCellComplement c) :=
    connectedSpace_embeddedCellComplement c hc hcont hopen
  exact PathConnectedSpace.of_locallyPathConnectedSpace


noncomputable def embeddedCellComplementInclusion
    {M : Type u} [TopologicalSpace M] (c : ClosedCell 3 → M) :
    C(embeddedCellComplement c, M) :=
  ⟨Subtype.val, continuous_subtype_val⟩


theorem fundamentalGroup_embeddedCellComplementInclusion_bijective
    {M : Type u} [TopologicalSpace M] [T2Space M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (hopen : IsOpen (embeddedCellInteriorImage c))
    [PathConnectedSpace (embeddedCellComplement c)] (x : embeddedCellComplement c) :
    Function.Bijective
      (FundamentalGroup.map (embeddedCellComplementInclusion c) x) := by
  let φ := embeddedCellBoundaryMap c hc
  let l := DifferentialGeometry.Topology.CellAttachment.cellAdjunctionLowerContinuousMap 3 φ
  let e := cellAdjunctionHomeomorphOfEmbeddedCell c hc hcont hopen
  let emap : C(CellAdjunctionSpace 3 φ, M) := e
  have hi : embeddedCellComplementInclusion c = emap.comp l := by
    ext y
    exact (cellAdjunctionHomeomorphOfEmbeddedCell_lower c hc hcont hopen y).symm
  rw [hi]
  have hmap : FundamentalGroup.map (emap.comp l) x =
      (FundamentalGroup.map emap (l x)).comp
        (FundamentalGroup.map l x) := by
    ext g
    exact Path.Homotopic.Quotient.map_comp
  rw [hmap]
  have heq : FundamentalGroup.mapOfEq emap rfl =
      FundamentalGroup.map emap (l x) := by
    apply MonoidHom.ext
    intro g
    exact eq_of_heq
      (DifferentialGeometry.Topology.VanKampen.fundamentalGroup_mapOfEq_heq_map
        emap (l x) (emap (l x)) rfl g)
  have he := DifferentialGeometry.Topology.fundamentalGroup_mapOfEq_bijective_of_homotopyEquiv
    e.toHomotopyEquiv (l x) (e (l x)) rfl
  change Function.Bijective (FundamentalGroup.mapOfEq emap rfl) at he
  rw [heq] at he
  exact he.comp
    (DifferentialGeometry.Topology.CellAttachment.fundamentalGroup_cellAdjunctionLower_bijective
      φ (continuous_embeddedCellBoundaryMap c hc hcont) x)

noncomputable def fundamentalGroupEmbeddedCellComplementEquiv
    {M : Type u} [TopologicalSpace M] [T2Space M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (hopen : IsOpen (embeddedCellInteriorImage c))
    [PathConnectedSpace (embeddedCellComplement c)] (x : embeddedCellComplement c) :
    FundamentalGroup (embeddedCellComplement c) x ≃* FundamentalGroup M (x : M) :=
  MulEquiv.ofBijective (FundamentalGroup.map (embeddedCellComplementInclusion c) x)
    (fundamentalGroup_embeddedCellComplementInclusion_bijective c hc hcont hopen x)

theorem fundamentalGroupEmbeddedCellComplementEquiv_toMonoidHom
    {M : Type u} [TopologicalSpace M] [T2Space M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (hopen : IsOpen (embeddedCellInteriorImage c))
    [PathConnectedSpace (embeddedCellComplement c)] (x : embeddedCellComplement c) :
    (↑(fundamentalGroupEmbeddedCellComplementEquiv c hc hcont hopen x) :
      FundamentalGroup (embeddedCellComplement c) x →* FundamentalGroup M (x : M)) =
      FundamentalGroup.map (embeddedCellComplementInclusion c) x := by
  rfl

noncomputable def fundamentalGroupEmbeddedCellComplementEquivOfConnected
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (hopen : IsOpen (embeddedCellInteriorImage c))
    [LocallyPathConnectedSpace (embeddedCellComplement c)] (x : embeddedCellComplement c) :
    FundamentalGroup (embeddedCellComplement c) x ≃* FundamentalGroup M (x : M) := by
  let _ : PathConnectedSpace (embeddedCellComplement c) :=
    pathConnectedSpace_embeddedCellComplement c hc hcont hopen
  exact fundamentalGroupEmbeddedCellComplementEquiv c hc hcont hopen x

noncomputable def fundamentalGroupEmbeddedCellComplementEquivOfLocalHomeomorph
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (hlocal : IsLocalHomeomorph (embeddedCellInteriorMap c))
    [LocallyPathConnectedSpace (embeddedCellComplement c)] (x : embeddedCellComplement c) :
    FundamentalGroup (embeddedCellComplement c) x ≃* FundamentalGroup M (x : M) :=
  fundamentalGroupEmbeddedCellComplementEquivOfConnected c hc hcont
    (isOpen_embeddedCellInteriorImage_of_isLocalHomeomorph c hlocal) x

noncomputable def fundamentalGroupEmbeddedCellComplementEquivOfImmersion
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (himm : Manifold.IsImmersion
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (embeddedCellInteriorMap c))
    [LocallyPathConnectedSpace (embeddedCellComplement c)] (x : embeddedCellComplement c) :
    FundamentalGroup (embeddedCellComplement c) x ≃* FundamentalGroup M (x : M) :=
  fundamentalGroupEmbeddedCellComplementEquivOfConnected c hc hcont
    (isOpen_embeddedCellInteriorImage_of_isImmersion c himm) x


noncomputable def fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbedding
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (hsmooth : Manifold.IsSmoothEmbedding
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (embeddedCellInteriorMap c))
    [LocallyPathConnectedSpace (embeddedCellComplement c)] (x : embeddedCellComplement c) :
    FundamentalGroup (embeddedCellComplement c) x ≃* FundamentalGroup M (x : M) :=
  fundamentalGroupEmbeddedCellComplementEquivOfImmersion c hc hcont hsmooth.isImmersion x


theorem fundamentalGroupEmbeddedCellComplementEquivOfConnected_toMonoidHom
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (hopen : IsOpen (embeddedCellInteriorImage c))
    [LocallyPathConnectedSpace (embeddedCellComplement c)] (x : embeddedCellComplement c) :
    (↑(fundamentalGroupEmbeddedCellComplementEquivOfConnected c hc hcont hopen x) :
      FundamentalGroup (embeddedCellComplement c) x →* FundamentalGroup M (x : M)) =
      FundamentalGroup.map (embeddedCellComplementInclusion c) x := by
  rfl


theorem fundamentalGroupEmbeddedCellComplementEquivOfLocalHomeomorph_toMonoidHom
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (hlocal : IsLocalHomeomorph (embeddedCellInteriorMap c))
    [LocallyPathConnectedSpace (embeddedCellComplement c)] (x : embeddedCellComplement c) :
    (↑(fundamentalGroupEmbeddedCellComplementEquivOfLocalHomeomorph
        c hc hcont hlocal x) :
      FundamentalGroup (embeddedCellComplement c) x →* FundamentalGroup M (x : M)) =
      FundamentalGroup.map (embeddedCellComplementInclusion c) x := by
  rfl


theorem fundamentalGroupEmbeddedCellComplementEquivOfImmersion_toMonoidHom
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (himm : Manifold.IsImmersion
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (embeddedCellInteriorMap c))
    [LocallyPathConnectedSpace (embeddedCellComplement c)] (x : embeddedCellComplement c) :
    (↑(fundamentalGroupEmbeddedCellComplementEquivOfImmersion
        c hc hcont himm x) :
      FundamentalGroup (embeddedCellComplement c) x →* FundamentalGroup M (x : M)) =
      FundamentalGroup.map (embeddedCellComplementInclusion c) x := by
  rfl


theorem fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbedding_toMonoidHom
    {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (c : ClosedCell 3 → M) (hc : Function.Injective c) (hcont : Continuous c)
    (hsmooth : Manifold.IsSmoothEmbedding
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (embeddedCellInteriorMap c))
    [LocallyPathConnectedSpace (embeddedCellComplement c)] (x : embeddedCellComplement c) :
    (↑(fundamentalGroupEmbeddedCellComplementEquivOfSmoothEmbedding
        c hc hcont hsmooth x) :
      FundamentalGroup (embeddedCellComplement c) x →* FundamentalGroup M (x : M)) =
      FundamentalGroup.map (embeddedCellComplementInclusion c) x := by
  rfl

end DifferentialGeometry.Topology.ThreeManifold
