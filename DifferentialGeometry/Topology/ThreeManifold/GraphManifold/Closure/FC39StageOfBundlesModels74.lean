import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageOfBundlesCircle74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRestrictOCL
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Edges
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecCertFields2

/-!
# Draft 74, G5 step 4: the edge component models over `⊤` from an existing edge bundle

Lane S-JUNCTIONS2 (suffix `_JN74`). `edgeModels_ofBundles74`: an `EdgeComponentModels P` of an
existing edge bundle gives the `EdgeComponentModels` of the restricted bundle of the whole-base cut
(`edgeBundle74` over `⊤`): the components, endpoints and parametrizations are carried along the open
embedding `val : ↥⊤ → P.Base` (`actualComponentEquiv_OCL`, `isSmoothEmbedding_codRestrict_opens`),
the handles and circle trivializations are literally the same maps. Set lemmas: over `⊤` the disk,
rim, whole component and whole vertical of the restricted bundle are those of `P`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsModelsJN74 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

section Setup

variable (Z : ZeroDomains W) (C : CuspCores W E) (Sl : SlimStage74 W)
  (P : EdgeBundle W) (R : CircleBundle W) (hP : P.cbase.Nonempty) (K₃ D₃ : Set Sl.Base)
  (hK : IsCompact K₃) (hD : IsCompact D₃) (hD₃ : D₃ = K₃ ∩ Sl.C₃)
  (hreq : Sl.slabImage ∪ Sl.facePoints ⊆ interior K₃)
  (hfaces : Disjoint (frontier K₃) Sl.facePoints)

/-- The restricted edge bundle of the whole-base cut of an existing edge bundle. -/
abbrev edgeBundleOfBundles74 : EdgeBundle W :=
  edgeBundle74 (SmoothStageGeometry74.ofBundles74 Z C Sl P R)
    (StageCutChoice74.ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces)
    (edgeCutFacts_ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces)

/-- The disk of the restricted bundle is the disk of `P`. -/
theorem disk_ofBundles74 (c : (⊤ : TopologicalSpace.Opens P.Base)) :
    (edgeBundleOfBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces).disk c = P.disk c.1 := by
  ext z
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨(EdgeStage74.ofBundle74 P).restrictIncl ⊤ x, ⟨congrArg Subtype.val h1, h2⟩, rfl⟩
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨y.1, (EdgeStage74.ofBundle74 P).mem_restrictParent_of y.2
      (TopologicalSpace.Opens.mem_top _)⟩, ⟨Subtype.ext h1, h2⟩, rfl⟩

/-- The rim of the restricted bundle is the rim of `P`. -/
theorem rim_ofBundles74 (c : (⊤ : TopologicalSpace.Opens P.Base)) :
    (edgeBundleOfBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces).rim c = P.rim c.1 := by
  ext z
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨(EdgeStage74.ofBundle74 P).restrictIncl ⊤ x, ⟨congrArg Subtype.val h1, h2⟩, rfl⟩
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨y.1, (EdgeStage74.ofBundle74 P).mem_restrictParent_of y.2
      (TopologicalSpace.Opens.mem_top _)⟩, ⟨Subtype.ext h1, h2⟩, rfl⟩

/-- The edge piece of the restricted bundle is the edge piece of `P`. -/
theorem edgePiece_ofBundles74 :
    (edgeBundleOfBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces).edgePiece = P.edgePiece := by
  ext z
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨(EdgeStage74.ofBundle74 P).restrictIncl ⊤ x, ⟨h1, h2⟩, rfl⟩
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨y.1, (EdgeStage74.ofBundle74 P).mem_restrictParent_of y.2
      (TopologicalSpace.Opens.mem_top _)⟩, ⟨h1, h2⟩, rfl⟩

/-- The vertical face of the restricted bundle is the vertical face of `P`. -/
theorem vertical_ofBundles74 :
    (edgeBundleOfBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces).vertical = P.vertical := by
  ext z
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨(EdgeStage74.ofBundle74 P).restrictIncl ⊤ x, ⟨h1, h2⟩, rfl⟩
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨y.1, (EdgeStage74.ofBundle74 P).mem_restrictParent_of y.2
      (TopologicalSpace.Opens.mem_top _)⟩, ⟨h1, h2⟩, rfl⟩

end Setup

section Components

/-- Over `⊤` the components of `val⁻¹ S` are the preimages of the components of `S`. -/
def baseComponentEquiv74 {B : Type u} [TopologicalSpace B] (S : Set B) :
    ActualComponent S ≃ ActualComponent (Subtype.val ⁻¹' S : Set (⊤ : TopologicalSpace.Opens B)) :=
  (actualComponentEquivOfEq_OCL (image_preimage_eq_of_subset
    (fun c _ => ⟨⟨c, TopologicalSpace.Opens.mem_top c⟩, rfl⟩) :
      Subtype.val '' (Subtype.val ⁻¹' S : Set (⊤ : TopologicalSpace.Opens B)) = S).symm).trans
    (actualComponentEquiv_OCL Subtype.val
      (⊤ : TopologicalSpace.Opens B).isOpen.isOpenEmbedding_subtypeVal.isEmbedding _).symm

theorem baseComponentEquiv74_val {B : Type u} [TopologicalSpace B] (S : Set B)
    (C : ActualComponent S) : (baseComponentEquiv74 S C).1 = Subtype.val ⁻¹' C.1 := by
  change Subtype.val ⁻¹' (actualComponentEquivOfEq_OCL _ C).1 = _
  rw [actualComponentEquivOfEq_OCL_val]

/-- The frontier points of `val⁻¹ S` over `⊤` are the frontier points of `S`. -/
def frontierTopEquiv74 {B : Type u} [TopologicalSpace B] (S : Set B) :
    {c : B // c ∈ frontier S} ≃
      {c : (⊤ : TopologicalSpace.Opens B) // c ∈ frontier (Subtype.val ⁻¹' S : Set _)} :=
  have hopen : IsOpenMap (Subtype.val : (⊤ : TopologicalSpace.Opens B) → B) :=
    (⊤ : TopologicalSpace.Opens B).isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  have h := hopen.preimage_frontier_eq_frontier_preimage continuous_subtype_val S
  { toFun := fun e => ⟨⟨e.1, TopologicalSpace.Opens.mem_top _⟩, by
      rw [← h]
      exact e.2⟩
    invFun := fun e => ⟨e.1.1, by
      have h2 : e.1 ∈ Subtype.val ⁻¹' frontier S := by
        rw [h]
        exact e.2
      exact h2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem frontierTopEquiv74_val {B : Type u} [TopologicalSpace B] (S : Set B)
    (e : {c : B // c ∈ frontier S}) : ((frontierTopEquiv74 S e).1 : B) = e.1 :=
  rfl

end Components

section Models

variable (Z : ZeroDomains W) (C : CuspCores W E) (Sl : SlimStage74 W)
  (P : EdgeBundle W) (R : CircleBundle W) (hP : P.cbase.Nonempty) (K₃ D₃ : Set Sl.Base)
  (hK : IsCompact K₃) (hD : IsCompact D₃) (hD₃ : D₃ = K₃ ∩ Sl.C₃)
  (hreq : Sl.slabImage ∪ Sl.facePoints ⊆ interior K₃)
  (hfaces : Disjoint (frontier K₃) Sl.facePoints)

/-- The whole component of the restricted bundle over the carried component. -/
theorem wholeComponent_ofBundles74 (C' : ActualComponent P.cbase) :
    (edgeBundleOfBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces).wholeComponent
      (baseComponentEquiv74 P.cbase C') = P.wholeComponent C' := by
  have hv := Set.ext_iff.1 (baseComponentEquiv74_val P.cbase C')
  ext z
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨(EdgeStage74.ofBundle74 P).restrictIncl ⊤ x, ⟨(hv _).1 h1, h2⟩, rfl⟩
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨y.1, (EdgeStage74.ofBundle74 P).mem_restrictParent_of y.2
      (TopologicalSpace.Opens.mem_top _)⟩, ⟨(hv _).2 h1, h2⟩, rfl⟩


/-- The whole vertical face of the restricted bundle over the carried component. -/
theorem wholeVertical_ofBundles74 (C' : ActualComponent P.cbase) :
    (edgeBundleOfBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces).wholeVertical
      (baseComponentEquiv74 P.cbase C') = P.wholeVertical C' := by
  have hv := Set.ext_iff.1 (baseComponentEquiv74_val P.cbase C')
  ext z
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨(EdgeStage74.ofBundle74 P).restrictIncl ⊤ x, ⟨(hv _).1 h1, h2⟩, rfl⟩
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨y.1, (EdgeStage74.ofBundle74 P).mem_restrictParent_of y.2
      (TopologicalSpace.Opens.mem_top _)⟩, ⟨(hv _).2 h1, h2⟩, rfl⟩

/-- The fibres of the restricted circle bundle over `⊤`. -/
theorem fibre_ofBundles74
    (hsat : (StageCutChoice74.ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces).M₃ =
      (StageCutChoice74.ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces).circleRegion)
    (c : (⊤ : TopologicalSpace.Opens R.Base)) :
    (circleBundle74 (SmoothStageGeometry74.ofBundles74 Z C Sl P R)
      (StageCutChoice74.ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces)
      (circleCutFacts_ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces hsat)).fibre c =
        R.fibre c.1 := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(StageProj74.ofCircleBundle74 R).restrictIncl ⊤ x, congrArg Subtype.val hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y.1, (StageProj74.ofCircleBundle74 R).mem_restrictParent_of y.2
      (TopologicalSpace.Opens.mem_top _)⟩, Subtype.ext hy, rfl⟩

/-- **The component models of the restricted bundle** from those of the bundle. -/
def edgeModels_ofBundles74 (M : EdgeComponentModels P) :
    EdgeComponentModels (edgeBundleOfBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces) where
  intervalCount := M.intervalCount
  circleCount := M.circleCount
  componentEquiv := M.componentEquiv.trans (baseComponentEquiv74 P.cbase)
  intervalBase i t := ⟨M.intervalBase i t, TopologicalSpace.Opens.mem_top _⟩
  intervalBase_embedding i :=
    isSmoothEmbedding_codRestrict_opens (M.intervalBase_embedding i) ⊤
      (fun t => TopologicalSpace.Opens.mem_top _)
  intervalBase_range i := by
    have hv : ((M.componentEquiv.trans (baseComponentEquiv74 P.cbase)) (.inl i)).1 =
        Subtype.val ⁻¹' (M.componentEquiv (.inl i)).1 := baseComponentEquiv74_val _ _
    refine Eq.trans ?_ hv.symm
    ext c
    constructor
    · rintro ⟨t, rfl⟩
      change M.intervalBase i t ∈ (M.componentEquiv (.inl i)).1
      rw [← M.intervalBase_range i]
      exact ⟨t, rfl⟩
    · intro hc
      have hc' : c.1 ∈ range (M.intervalBase i) := by
        rw [M.intervalBase_range i]
        exact hc
      obtain ⟨t, ht⟩ := hc'
      exact ⟨t, Subtype.ext ht⟩
  circleBase j z := ⟨M.circleBase j z, TopologicalSpace.Opens.mem_top _⟩
  circleBase_embedding j :=
    isSmoothEmbedding_codRestrict_opens (M.circleBase_embedding j) ⊤
      (fun t => TopologicalSpace.Opens.mem_top _)
  circleBase_range j := by
    have hv : ((M.componentEquiv.trans (baseComponentEquiv74 P.cbase)) (.inr j)).1 =
        Subtype.val ⁻¹' (M.componentEquiv (.inr j)).1 := baseComponentEquiv74_val _ _
    refine Eq.trans ?_ hv.symm
    ext c
    constructor
    · rintro ⟨t, rfl⟩
      change M.circleBase j t ∈ (M.componentEquiv (.inr j)).1
      rw [← M.circleBase_range j]
      exact ⟨t, rfl⟩
    · intro hc
      have hc' : c.1 ∈ range (M.circleBase j) := by
        rw [M.circleBase_range j]
        exact hc
      obtain ⟨t, ht⟩ := hc'
      exact ⟨t, Subtype.ext ht⟩
  endpointEquiv := M.endpointEquiv.trans (frontierTopEquiv74 P.cbase)
  endpointEquiv_apply i b := Subtype.ext (M.endpointEquiv_apply i b)
  intervalTriv := M.intervalTriv
  intervalTriv_range i := (M.intervalTriv_range i).trans
    (wholeComponent_ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces
      (M.componentEquiv (.inl i))).symm
  intervalTriv_proj i w t := by
    obtain ⟨hx, h⟩ := M.intervalTriv_proj i w t
    exact ⟨(EdgeStage74.ofBundle74 P).mem_restrictParent_of hx
      (TopologicalSpace.Opens.mem_top _), Subtype.ext h⟩
  intervalTriv_disk i t := (M.intervalTriv_disk i t).trans
    (disk_ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces
      ⟨M.intervalBase i t, TopologicalSpace.Opens.mem_top _⟩).symm
  intervalTriv_rim i t := (M.intervalTriv_rim i t).trans
    (rim_ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces
      ⟨M.intervalBase i t, TopologicalSpace.Opens.mem_top _⟩).symm
  circleTriv := M.circleTriv
  circleTriv_smooth := M.circleTriv_smooth
  circleTriv_mfderiv := M.circleTriv_mfderiv
  circleTriv_injective := M.circleTriv_injective
  circleTriv_range j := (M.circleTriv_range j).trans
    (wholeComponent_ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces
      (M.componentEquiv (.inr j))).symm
  circleTriv_proj j w z := by
    obtain ⟨hx, h⟩ := M.circleTriv_proj j w z
    exact ⟨(EdgeStage74.ofBundle74 P).mem_restrictParent_of hx
      (TopologicalSpace.Opens.mem_top _), Subtype.ext h⟩
  circleTriv_disk j z := (M.circleTriv_disk j z).trans
    (disk_ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces
      ⟨M.circleBase j z, TopologicalSpace.Opens.mem_top _⟩).symm
  circleTriv_rim j z := (M.circleTriv_rim j z).trans
    (rim_ofBundles74 Z C Sl P R hP K₃ D₃ hK hD hD₃ hreq hfaces
      ⟨M.circleBase j z, TopologicalSpace.Opens.mem_top _⟩).symm

end Models

end GC.GraphManifold.Assembly.FC39P0
