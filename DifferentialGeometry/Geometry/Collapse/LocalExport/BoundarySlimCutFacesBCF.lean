import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceV2Corollaries
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryNoClosedBaseComponentBCF

/-!
# BCF01 on the v2 objects: G0 (no closed slim component) and G3 (the three face identities on ANY
slim cut) (lane B-BCF134; text v3 §G, review 74 D74-9)

Text v3 (`docs/geometrization/chapter14/evidence/boundary/TargetsBoundary-v3.lean.txt`, §G):

* G0 `no_closed_slimBase_component_BCF01`: `B₃` has no nonempty compact relatively open subset
  (proved for every `B_st`, `st ≠ 1`, without the connectedness and `⊆ D₃` hypotheses of the frozen
  text, which is kept verbatim as an `example`): the source misses `∂W` (`source_buffered`), `f_st`
  is continuous (rank field) and proper on `X_st`, and `M` is connected. This is the BOUNDARY
  exclusion of circle components of the shared kernel's `K₃` (D74-9: a corollary of the separated
  binding, not a kernel restriction).
* G3 `bcf01_faces_BCF01`: for the actual zero domains `Z` (saturation `S_K ⊆ M₁`, BIFACEd F4d) and ANY
  slim cut `K` (old faces in `int_{B₃} K`, regular piece), `S ∩ M₂ = ∂S \ ∂M₁`,
  `∂M₂ = (∂M₁ \ S) ∪ (∂S \ ∂M₁)` and the disjointness, from the ZSP05 kernel
  `relative_interior_removal`; the collar `S ∩ ∂M₁ ⊆ int_{M₁} S` is
  `BoundarySlimCut_BIFc.piece_inter_frontier_subset_BCF`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}

namespace BoundaryGaf02BasesV2

variable (Bs : BoundaryGaf02BasesV2 C)

/-- **The stage map is continuous on its v2 source domain** (rank field: `d f_j ≠ 0` there). -/
theorem continuousAt_stageMap_BCF {st : Fin 3} {p : W.Carrier} (hp : p ∈ Bs.source st) :
    ContinuousAt (C.stageMap st) p := by
  have hne : mvfderiv W.model (C.stageMap st) p ≠ 0 :=
    ne_zero_of_finrank_range_BCF _ (gafStageDim_ne_zero_BCF st) (Bs.rank_eq st p hp)
  by_contra hc
  have hnd : ¬ MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) (C.stageMap st) p :=
    fun h => hc h.continuousAt
  apply hne
  simp [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hnd]

/-- `f_j` is continuous on the v2 source `X_j`. -/
theorem continuousOn_stageMap_BCF (st : Fin 3) : ContinuousOn (C.stageMap st) (Bs.source st) :=
  fun _ hp => (Bs.continuousAt_stageMap_BCF hp).continuousWithinAt

/-- **Every v2 source domain misses `∂W`**: `X_st ⊆ {D > 10}` and `∂W ≠ ∅`. -/
theorem source_ne_univ_BCF (WF : BoundaryWholeFiberSpecV2 C Bs) (st : Fin 3) :
    Bs.source st ≠ univ := by
  intro h
  obtain ⟨x, hx⟩ := (B.connected ⟨0, B.count_pos⟩).nonempty
  have hxb : x ∈ W.model.boundary W.Carrier := B.covers ▸ mem_iUnion.mpr ⟨_, hx⟩
  have hlt := WF.source_buffered st (h ▸ mem_univ x)
  have hle : distanceToBoundary W g x ≤ 0 := by
    unfold distanceToBoundary
    calc (⨅ q : W.model.boundary W.Carrier, riemannianEDistOf g x q) ≤
          riemannianEDistOf g x (⟨x, hxb⟩ : W.model.boundary W.Carrier) := iInf_le _ _
      _ = 0 := riemannianEDistOf_self _ _
  exact absurd (hlt.trans_le hle) (by simp)

/-- **No closed component of a v2 open-stage base** (`st ≠ 1`): a compact relatively open subset of
`B_st` is empty. -/
theorem no_closed_base_component_BCF (WF : BoundaryWholeFiberSpecV2 C Bs) {st : Fin 3}
    (hst : st ≠ 1)
    {Γ : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))} (hΓB : Γ ⊆ Bs.base st)
    (hΓc : IsCompact Γ) (hΓo : ∃ O, IsOpen O ∧ O ∩ Bs.base st = Γ) : Γ = ∅ := by
  have hmaps : MapsTo (C.stageMap st) (Bs.source st) (Bs.base st) :=
    fun p hp => Bs.image_eq st ▸ mem_image_of_mem _ hp
  have h0 := no_clopen_compact_base_part_BCF (C.stageMap st) (Bs.source st) (Bs.base st)
    (Bs.isOpen_source st hst) (Bs.source_ne_univ_BCF WF st) (Bs.continuousOn_stageMap_BCF st)
    hmaps (Bs.proper st) hΓB hΓc hΓo
  refine eq_empty_of_forall_notMem fun y hy => ?_
  obtain ⟨p, hp, rfl⟩ : y ∈ C.stageMap st '' Bs.source st := (Bs.image_eq st).symm ▸ hΓB hy
  exact (eq_empty_iff_forall_notMem.mp h0) p ⟨hp, hy⟩

/-- **G0 BCF01 (text v3), strengthened**: no nonempty compact relatively open subset of `B₃`
(the frozen hypotheses `Y ⊆ D₃` and `IsConnected Y` are not needed; verbatim form below). -/
theorem no_closed_slimBase_component_BCF01 (WF : BoundaryWholeFiberSpecV2 C Bs)
    {Y : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))} (hYB : Y ⊆ Bs.base 2)
    (hYc : IsCompact Y) (hYne : Y.Nonempty) :
    ¬ ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
      IsOpen O ∧ O ∩ Bs.base 2 = Y := fun hYo =>
  hYne.ne_empty (Bs.no_closed_base_component_BCF WF (st := 2) (by decide) hYB hYc hYo)

/-- G0 in the verbatim frozen form of text v3. -/
example (WF : BoundaryWholeFiberSpecV2 C Bs) :
    ∀ Y ⊆ Bs.base 2 ∩ Bs.slimBaseDomain_BIFc, IsCompact Y → IsConnected Y →
      Y.Nonempty → ¬ ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
        IsOpen O ∧ O ∩ Bs.base 2 = Y := fun _ hY hYc _ hYne =>
  Bs.no_closed_slimBase_component_BCF01 WF (fun _ hy => (hY hy).1) hYc hYne

end BoundaryGaf02BasesV2

/-- `M₁` (v2) is closed. -/
theorem BoundaryGaf02Chain.isClosed_M₁_BCF (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) :
    IsClosed C.M₁_BIFc :=
  isOpen_interior.isClosed_compl

namespace BoundarySlimCut_BIFc

variable {Bs : BoundaryGaf02BasesV2 C}
  {Kset : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))}
  (hK : BoundarySlimCut_BIFc Bs Kset)
include hK

/-- **The collar of a slim cut**: `S_K ∩ ∂M₁ ⊆ int_{M₁} S_K` (the old faces lie in `int_{B₃} K`). -/
theorem piece_inter_frontier_subset_BCF :
    Bs.slimPieceOf_BIFc Kset ∩ frontier C.M₁_BIFc ⊆
      relInterior_BIF C.M₁_BIFc (Bs.slimPieceOf_BIFc Kset) := by
  rintro x ⟨hxS, hxf⟩
  have hxX : x ∈ Bs.source 2 := hxS.1
  have hy : C.stageMap 2 x ∈ relInterior_BIF (Bs.base 2) Kset :=
    hK.faces_subset ⟨x, ⟨hxf, hxX⟩, rfl⟩
  obtain ⟨-, O, hO, hyO, hOK⟩ := mem_relInterior_iff_BCF.mp hy
  have hnhds : Bs.source 2 ∩ C.stageMap 2 ⁻¹' O ∈ 𝓝 x :=
    inter_mem ((Bs.isOpen_source 2 (by decide)).mem_nhds hxX)
      ((Bs.continuousAt_stageMap_BCF hxX).preimage_mem_nhds (hO.mem_nhds hyO))
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hnhds
  have hxM : x ∈ C.M₁_BIFc := C.isClosed_M₁_BCF.frontier_subset hxf
  refine mem_relInterior_iff_BCF.mpr ⟨hxM, U, hU, hxU, ?_⟩
  rintro z ⟨hzU, hzM⟩
  have hzX : z ∈ Bs.source 2 := (hUsub hzU).1
  have hzB : C.stageMap 2 z ∈ Bs.base 2 := Bs.image_eq 2 ▸ mem_image_of_mem _ hzX
  exact ⟨hzX, hOK ⟨(hUsub hzU).2, hzB⟩, z, ⟨hzM, hzX⟩, rfl⟩

end BoundarySlimCut_BIFc

/-- **G3 BCF01 (text v3): the three face identities on ANY slim cut.** -/
theorem bcf01_faces_BCF01 {Bs : BoundaryGaf02BasesV2 C} (Z : BoundaryActualZeroDomains_BIFc C Bs)
    {Kset : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))}
    (hK : BoundarySlimCut_BIFc Bs Kset) :
    Bs.slimPieceOf_BIFc Kset ∩ Bs.M₂Of_BIFc Kset =
        frontier (Bs.slimPieceOf_BIFc Kset) \ frontier C.M₁_BIFc ∧
      frontier (Bs.M₂Of_BIFc Kset) = (frontier C.M₁_BIFc \ Bs.slimPieceOf_BIFc Kset) ∪
        (frontier (Bs.slimPieceOf_BIFc Kset) \ frontier C.M₁_BIFc) ∧
      Disjoint (frontier C.M₁_BIFc \ Bs.slimPieceOf_BIFc Kset)
        (frontier (Bs.slimPieceOf_BIFc Kset) \ frontier C.M₁_BIFc) := by
  obtain ⟨-, -, hfr, hdis, hfive, -⟩ := relative_interior_removal
    ((⋃ k, C.actualZeroDomain_BIFc k) ∪ C.cuspCores_BIF) (Bs.slimPieceOf_BIFc Kset)
    (Z.slimPieceOf_subset_M₁_BIF Kset) hK.piece_regular hK.piece_inter_frontier_subset_BCF
  exact ⟨hfive, hfr, hdis⟩

end DifferentialGeometry.Geometry.Collapse
