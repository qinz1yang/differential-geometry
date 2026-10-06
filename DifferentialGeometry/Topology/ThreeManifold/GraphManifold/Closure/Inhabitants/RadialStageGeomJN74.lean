import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialStageRowsJN74

/-!
# Draft 74, G5 (X135 radial `D² × S¹`): the cover, face and rim facts

Lane S-JUNCTIONS2 (suffix `_JN74`). `CutCoverFacts74`, `JunctionFaceFacts74` and
`JunctionRimFacts74` of the cut `radialCut74` over the rows `radialRows74`, from the X135 identities
(`radial_first_remainder`, `radial_M2_height`, `radial_frontier_boundary`, `radial_slim_M2`,
`radial_shared_removed`, `radial_region_boundary`, `radial_rim_fibre`, `radial_edge_region`,
`radial_local_faces`' face functions), carried over the identification of the restricted bases
over `⊤`. The restricted edge bundle has no endpoint (`C₂ = ℝ`-circle is all of its base).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

local instance carrierCharts_StageGeomJN74 :
    ChartedSpace (EuclideanHalfSpace 3) carrier.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_StageGeomJN74 : IsManifold (𝓡∂ 3) ∞ carrier.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

/-- The restricted edge bundle of the radial cut has no endpoint. -/
theorem radialEdgeEnd_isEmpty74 : IsEmpty radialRows74.edge.EdgeEnd :=
  ⟨fun e => by
    have h : e.1 ∈ frontier (Subtype.val ⁻¹' (univ : Set Circle) :
        Set (⊤ : TopologicalSpace.Opens Circle)) := e.2
    rw [preimage_univ, frontier_univ] at h
    exact h⟩

/-- **The cover facts** (FDC04) of the radial cut. -/
theorem radialCover74 : CutCoverFacts74 radialStage74 radialCut74 where
  cover := by
    refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ interior ((⋃ i, range (radialZeros.piece i).map) ∪
        ⋃ b, range (radialCuspCores.piece b).map)
    · exact Or.inl (Or.inl (interior_subset hx))
    · by_cases h2 : x ∈ relInt (regionM1 radialZeros radialCuspCores) radialCut74.slimSet
      · exact Or.inl (Or.inr (relInt_subset_JN74 h2))
      · exact Or.inr ⟨hx, h2⟩
  slimSet_subset_M₁ := by
    intro x hx
    rw [radialCut74_slimSet, radial_slim_union, slimToCarrier_range] at hx
    change x ∈ regionM1 radialZeros radialCuspCores
    rw [radial_first_remainder]
    exact hx.2
  edgeSet_subset_M₂ := by
    intro x hx
    rw [radialCut74_edgeSet, radial_edge_height] at hx
    rw [radialCut74_M₂, radial_M2_height]
    change height x ≤ -(1 / 2 : ℝ)
    have h : height x ≤ -(3 / 4 : ℝ) := hx
    linarith
  zero_cusp_disjoint i _ := Fin.elim0 i

local instance radialEdgeEndEmpty_JN74 : IsEmpty radialRows74.edge.EdgeEnd :=
  radialEdgeEnd_isEmpty74

theorem radialHorizontalDisks74 : radialRows74.edge.horizontalDisks = ∅ :=
  eq_empty_of_forall_notMem fun x hx => by
    obtain ⟨e, -⟩ := mem_iUnion.1 hx
    exact isEmptyElim e

/-- **The face facts** (EDP05 horizontal exit, ZSP05, FDC03 LastFaces) of the radial cut: no
endpoint, so no horizontal disk; the rest are the X135 identities. -/
def radialFaces74 : JunctionFaceFacts74 radialStage74 radialCut74 radialRows74 where
  horizontal e := isEmptyElim e
  horizontal_disk e := isEmptyElim e
  edge_faces F := by
    have h1 : radialCut74.edgeSet ∩ radialRows74.slimPieces.residualSet F = ∅ := by
      rw [radialCut74_edgeSet]
      exact radial_edge_residual_disjoint F
    rw [h1]
    symm
    exact eq_empty_of_forall_notMem fun x hx => by
      obtain ⟨e, -⟩ := mem_iUnion.1 hx
      exact isEmptyElim e
  frontier_M2 := by
    rw [radialCut74_M₂]
    exact radial_frontier_boundary
  region_boundary := by
    rw [radialHorizontalDisks74, radialCut74_M₃]
    have h := radial_region_boundary
    rw [radial_horizontal_empty] at h
    exact h
  slim_M2 := by
    rw [radialCut74_slimSet, radialCut74_M₂]
    exact radial_slim_M2
  shared_removed σ := by
    rw [radialCut74_slimSet]
    exact radial_shared_removed σ

/-- Relabelling the vertical faces along an equivalence of base components. -/
def circleLabelEquiv74 {Hor V V' : Type*} (e : V ≃ V') : CircleFaceLabel Hor V ≃
    CircleFaceLabel Hor V' where
  toFun f := match f with
    | .horizontal F => .horizontal F
    | .vertical c => .vertical (e c)
  invFun f := match f with
    | .horizontal F => .horizontal F
    | .vertical c => .vertical (e.symm c)
  left_inv f := by cases f <;> simp
  right_inv f := by cases f <;> simp

/-- The face labels of the restricted base: the X135 labels, carried over `⊤`. -/
def radialFaceEquiv74 : Fin 2 ≃ CircleFaceLabel radialSlims.ResidualFace
    radialRows74.edge.EdgeBaseComponent :=
  radialFaceEquiv.trans (circleLabelEquiv74 (baseComponentEquiv74 radialEdgeBundle.cbase))

theorem radialRim74 (c : radialRows74.edge.Base) :
    radialRows74.edge.rim c = radialEdgeBundle.rim c.1 :=
  rim_ofBundles74 radialZeros radialCuspCores radialSlimStage74 radialEdgeBundle
    radialCircleBundle ⟨(1 : Circle), mem_univ _⟩ radialK3_74 radialK3_74 radialK3_74_compact
    radialK3_74_compact (inter_univ _).symm radialReq74 (disjoint_empty _) c

theorem radialFibre74 (c : radialRows74.circle.Base) :
    radialRows74.circle.fibre c = radialCircleBundle.fibre c.1 :=
  fibre_ofBundles74 radialZeros radialCuspCores radialSlimStage74 radialEdgeBundle
    radialCircleBundle ⟨(1 : Circle), mem_univ _⟩ radialK3_74 radialK3_74 radialK3_74_compact
    radialK3_74_compact (inter_univ _).symm radialReq74 (disjoint_empty _)
    (radialCut74_M₃.trans radialCut74_circleRegion.symm) c

theorem radialVertical74 :
    radialRows74.edge.vertical = radialEdgeBundle.vertical :=
  vertical_ofBundles74 radialZeros radialCuspCores radialSlimStage74 radialEdgeBundle
    radialCircleBundle ⟨(1 : Circle), mem_univ _⟩ radialK3_74 radialK3_74 radialK3_74_compact
    radialK3_74_compact (inter_univ _).symm radialReq74 (disjoint_empty _)

theorem radialWholeVertical74 (C' : ActualComponent radialEdgeBundle.cbase) :
    radialRows74.edge.wholeVertical (baseComponentEquiv74 radialEdgeBundle.cbase C') =
      radialEdgeBundle.wholeVertical C' :=
  wholeVertical_ofBundles74 radialZeros radialCuspCores radialSlimStage74 radialEdgeBundle
    radialCircleBundle ⟨(1 : Circle), mem_univ _⟩ radialK3_74 radialK3_74 radialK3_74_compact
    radialK3_74_compact (inter_univ _).symm radialReq74 (disjoint_empty _) C'

theorem radialFaceSet74 (l : Fin 2) :
    circleFaceSet radialRows74.slimPieces radialRows74.edge (radialFaceEquiv74 l) =
      circleFaceSet radialSlims radialEdgeBundle (radialFaceEquiv l) := by
  fin_cases l
  · rfl
  · exact radialWholeVertical74 radialBaseComponent

/-- **The corner model of the circle base** (FDC03 `local_faces`) of the radial cut: at every
frontier point of `C₁` exactly one of the two X135 face functions is active (one face, no
corner). -/
theorem radialLocalFaces74 : ∀ c ∈ frontier radialRows74.circle.cbase,
    ∃ U : TopologicalSpace.Opens radialRows74.circle.Base, c ∈ U ∧
      ∃ (L : Finset (CircleFaceLabel radialRows74.slimPieces.ResidualFace
          radialRows74.edge.EdgeBaseComponent))
        (φ : CircleFaceLabel radialRows74.slimPieces.ResidualFace
          radialRows74.edge.EdgeBaseComponent → radialRows74.circle.Base → ℝ),
        1 ≤ L.card ∧ L.card ≤ 2 ∧
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f c = 0 ∧
          {c' | c' ∈ U ∧ c' ∈ radialRows74.circle.cbase ∧ φ f c' = 0} =
            {c' | c' ∈ U ∧ c' ∈ radialRows74.circle.cbase ∧
              radialRows74.circle.fibre c' ⊆
                circleFaceSet radialRows74.slimPieces radialRows74.edge f}) ∧
        (Surjective fun w : TangentSpace (𝓡 2) c =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) ∧
        radialRows74.circle.cbase ∩ (U : Set radialRows74.circle.Base) =
          {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} := by
  classical
  intro c hc
  have hopen : IsOpenMap (Subtype.val : (⊤ : TopologicalSpace.Opens radialCircleBase) →
      radialCircleBase) :=
    (⊤ : TopologicalSpace.Opens radialCircleBase).isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  have hfr : c.1 ∈ frontier radialCircleBundle.cbase := by
    have h := hopen.preimage_frontier_eq_frontier_preimage continuous_subtype_val
      radialCircleBundle.cbase
    exact (h ▸ hc : c ∈ Subtype.val ⁻¹' frontier radialCircleBundle.cbase)
  obtain ⟨l, hl⟩ := radial_frontier_active c.1 hfr
  have hm : c.1 ∈ radialCircleBundle.cbase :=
    radialCircleCornerBase_compact.isClosed.frontier_subset hfr
  let φ : CircleFaceLabel radialRows74.slimPieces.ResidualFace
      radialRows74.edge.EdgeBaseComponent → radialRows74.circle.Base → ℝ :=
    fun f b => radialCircleDefining (radialFaceEquiv74.symm f) b.1
  have hφ : φ (radialFaceEquiv74 l) = fun b => radialCircleDefining l b.1 := by
    funext b
    change radialCircleDefining (radialFaceEquiv74.symm (radialFaceEquiv74 l)) b.1 = _
    rw [radialFaceEquiv74.symm_apply_apply]
  refine ⟨⟨Subtype.val ⁻¹' (radialFaceNeighbourhood l : Set radialCircleBase),
    (radialFaceNeighbourhood l).isOpen.preimage continuous_subtype_val⟩,
    radial_active_neighbourhood c.1 l hm hl, {radialFaceEquiv74 l}, φ, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_of_eq (Finset.card_singleton _).symm
  · exact (Finset.card_singleton _).le.trans (by norm_num)
  · intro f hf
    have he : f = radialFaceEquiv74 l := Finset.mem_singleton.mp hf
    subst f
    rw [hφ]
    refine ⟨((radialCircleDefining_smooth l).comp contMDiff_subtype_val).contMDiffOn, hl, ?_⟩
    ext b
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hU, hcb, hz⟩
      refine ⟨hU, hcb, ?_⟩
      rw [radialFibre74, radialFaceSet74]
      exact radial_fibre_face_iff.mpr hz
    · rintro ⟨hU, hcb, hsub⟩
      refine ⟨hU, hcb, ?_⟩
      rw [radialFibre74, radialFaceSet74] at hsub
      exact radial_fibre_face_iff.mp hsub
  · intro g
    let k : ({radialFaceEquiv74 l} : Finset (CircleFaceLabel radialRows74.slimPieces.ResidualFace
        radialRows74.edge.EdgeBaseComponent)) := ⟨radialFaceEquiv74 l, Finset.mem_singleton_self _⟩
    obtain ⟨w, hw⟩ := radial_defining_onto l c.1 (g k)
    refine ⟨w, ?_⟩
    funext f
    have he : f = k := Subtype.ext (Finset.mem_singleton.mp f.property)
    rw [he]
    change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ (radialFaceEquiv74 l)) c w = g k
    have h := DifferentialGeometry.mfderiv_restrict_open (I := 𝓡 2) (J := 𝓘(ℝ, ℝ))
      (radialCircleDefining l) (⊤ : TopologicalSpace.Opens radialCircleBase) c
    rw [hφ]
    exact (congrArg (fun L => L w) h).trans hw
  · ext b
    have h := Set.ext_iff.1 (radial_local_cbase l) b.1
    simp only [mem_ofPred_eq, mem_inter_iff] at h ⊢
    constructor
    · rintro ⟨hb, hn⟩
      refine ⟨hn, fun f hf => ?_⟩
      have he : f = radialFaceEquiv74 l := Finset.mem_singleton.mp hf
      rw [he]
      have hle := (h.1 ⟨hb, hn⟩).2
      change radialCircleDefining (radialFaceEquiv74.symm (radialFaceEquiv74 l)) b.1 ≤ 0
      rw [radialFaceEquiv74.symm_apply_apply]
      exact hle
    · rintro ⟨hn, hle⟩
      have hle' := hle (radialFaceEquiv74 l) (Finset.mem_singleton_self _)
      change radialCircleDefining (radialFaceEquiv74.symm (radialFaceEquiv74 l)) b.1 ≤ 0 at hle'
      rw [radialFaceEquiv74.symm_apply_apply] at hle'
      exact ⟨(h.2 ⟨hn, hle'⟩).1, hn⟩

/-- **The rim facts** (EDP06 whole rim agreement, FDC03 surface-with-corners exit) of the radial
cut. -/
def radialRims74 : JunctionRimFacts74 radialStage74 radialCut74 radialRows74 where
  rimBase c := ⟨radialRimBase c.1, TopologicalSpace.Opens.mem_top _⟩
  rimBase_smooth :=
    ((DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff
      (⊤ : TopologicalSpace.Opens radialCircleBase) _).mp
        (radialRimBase_smooth.comp contMDiff_subtype_val)).contMDiffOn
  rim_fibre c _ := (radialRim74 c).trans ((radial_rim_fibre c.1).trans
    (radialFibre74 ⟨radialRimBase c.1, TopologicalSpace.Opens.mem_top _⟩).symm)
  edge_region := by
    rw [radialCut74_edgeSet, radialCut74_M₃, radialVertical74]
    exact radial_edge_region
  local_faces := radialLocalFaces74

/-- **The corner facts** of the radial cut: there is no endpoint. -/
def radialCorners74 : CornerCutFacts74 radialFaces74 radialRims74 where
  descent e := isEmptyElim e
  rank e := isEmptyElim e
  descended e := isEmptyElim e

/-- **`H` of the radial solid torus** (draft 74 §4.1): the first stage geometry with a non-empty
edge piece, a non-empty circle region and a non-empty slim band in the A0 / J1 contracts. -/
def radialGeometry74 : StageCutGeometry74 radialStage74 radialCut74 where
  rows := radialRows74
  cover := radialCover74
  faces := radialFaces74
  rims := radialRims74
  corners := radialCorners74

end GC.GraphManifold.Assembly.FC39P0.X135Radial
