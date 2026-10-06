import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRimSmoothJN74
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeFrontierRelIntJN74
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageHorizontalDisksJN74

/-!
# Draft 74, FDC03's `region_boundary` at `D_R` (field g5 of `JunctionFaceFacts74`)

Lane S-JUNCTIONS (by S-JUNCTIONS3), G17 (suffix `_JN74`). On the produced stage geometry
`P = S.closedStagesAt_OCL B hT hεr A zero`:

* `horizontalDisks_at_JN74`: the rows' horizontal disks are `M.ψ(H)`,
  `H = ∂M₂ ∩ {x ∈ source | T ≤ 4Δ}` (`edgeHorizontalDisks_JN74`; `edge_frontier_H_EFE`);
* **`region_boundary_at_JN74`**: given `frontier P.cut.M₂ = B` (field g4 `frontier_M2` with
  `B = boundaryM2`), `P.cut.M₃ ∩ B = B \ relInt B (edge.horizontalDisks)` (transport of
  `frontier_inter_cutM3_JN74` by `M.ψ`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology.Manifold
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2)

/-- **Frontier of the image of a closed set under an open embedding** (the image also closed). -/
theorem frontier_image_openEmbedding_JN74 {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {j : α → β} (hj : Topology.IsOpenEmbedding j) {s : Set α} (hs : IsClosed s)
    (hjs : IsClosed (j '' s)) {a : α} : j a ∈ frontier (j '' s) ↔ a ∈ frontier s := by
  have hint : interior (j '' s) = j '' interior s := by
    refine Subset.antisymm ?_ (hj.isOpenMap.image_interior_subset s)
    intro x hx
    have hxs : x ∈ j '' s := interior_subset hx
    obtain ⟨a', ha', rfl⟩ := hxs
    refine ⟨a', ?_, rfl⟩
    rw [mem_interior]
    refine ⟨j ⁻¹' interior (j '' s), fun y hy => ?_, isOpen_interior.preimage hj.continuous, hx⟩
    obtain ⟨y', hy', hyy⟩ := interior_subset hy
    rw [← hj.injective hyy]
    exact hy'
  rw [frontier, frontier, hjs.closure_eq, hs.closure_eq, hint]
  constructor
  · rintro ⟨⟨a', ha', haa'⟩, hn⟩
    rw [hj.injective haa'] at ha'
    exact ⟨ha', fun hi => hn ⟨a, hi, rfl⟩⟩
  · rintro ⟨ha, hn⟩
    exact ⟨⟨a, ha, rfl⟩, fun ⟨a', hi, haa'⟩ => hn (hj.injective haa' ▸ hi)⟩

/-- The inclusion of the good open edge base of `D_R` into the chain's `B₂`. -/
theorem edgeBaseOpen_le_JN74 :
    (S.goodCut_OCL B hT hεr).edgeBaseOpens_R74 ≤ S.chain.toGaf02ChainE.edgeBaseOpens_EFE :=
  fun _ hb => ((S.goodCut_bases_OCL B hT hεr).1 hb).2

variable {S B hT hεr} in
/-- **`C₂` of the chain is `C₂(D_R)`**: for `cc ∈ B₂`, `cc ∈ edgeC2_EFE ↔ cc ∈ C₂(D_R)`. -/
theorem mem_edgeC2_iff_JN74 {cc : S.chain.toGaf02ChainE.edgeBaseOpens_EFE} :
    cc ∈ S.chain.edgeC2_EFE (S.goodCut_OCL B hT hεr).K₃ ↔
      ((cc : S.chain.toChain.finalBase_BAS 1) : S.blockSpace_R74) ∈
        (S.goodCut_OCL B hT hεr).C₂ := by
  constructor
  · rintro ⟨x, ⟨hxM, hxT⟩, rfl⟩
    exact ⟨x.1, ⟨hxM, S.chain.mem_edgeRegion_of_source_JN74 x.2 hxT⟩, rfl⟩
  · rintro ⟨x, hxE, hxq⟩
    obtain ⟨hxT, hxsrc⟩ := S.chain.cutEdgeSet_height_le_JN74 R.two_le_Δ_EDP23
      (S.goodCut_OCL B hT hεr).K₃ hxE
    refine ⟨⟨x, hxsrc⟩, ⟨hxE.1, hxT⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hxq

/-- **The rows' horizontal disks are `M.ψ(H)`**, `H = ∂M₂ ∩ {x ∈ source | T ≤ 4Δ}`. -/
theorem horizontalDisks_at_JN74 (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (F : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) :
    (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).horizontalDisks =
      M.ψ '' (S.chain.edgeHorizontalDisks_JN74 (S.goodCut_OCL B hT hεr).K₃) := by
  have hE := R.edpE_numerics_RGC hT hNb hcw
  let _ := A.edgeChartedSpace1
  have := A.edge_isManifold1.1
  let j : (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).Base →
      S.chain.toGaf02ChainE.edgeBaseOpens_EFE :=
    TopologicalSpace.Opens.inclusion (S.edgeBaseOpen_le_JN74 B hT hεr)
  have hjo : Topology.IsOpenEmbedding j :=
    TopologicalSpace.Opens.isOpenEmbedding_of_le (S.edgeBaseOpen_le_JN74 B hT hεr)
  have hcb : j '' (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).cbase =
      S.chain.edgeC2_EFE (S.goodCut_OCL B hT hεr).K₃ := by
    ext cc
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine (mem_edgeC2_iff_JN74 (S := S) (B := B) (hT := hT) (hεr := hεr) (cc := j c)).2 ?_
      rw [← (S.closedStagesAt_OCL B hT hεr A zero).cut_C₂]
      exact ⟨c.1, hc, rfl⟩
    · intro hcc
      have h := (mem_edgeC2_iff_JN74 (S := S) (B := B) (hT := hT) (hεr := hεr) (cc := cc)).1 hcc
      rw [← (S.closedStagesAt_OCL B hT hεr A zero).cut_C₂] at h
      obtain ⟨b, hb, hbq⟩ := h
      exact ⟨⟨b, (S.closedStagesAt_OCL B hT hεr A zero).cut.C₂_sub hb⟩, hb,
        Subtype.ext (Subtype.ext hbq)⟩
  have hcl : IsClosed (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).cbase := F.cbase_compact.isClosed
  have hjcl : IsClosed (j '' (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).cbase) :=
    (F.cbase_compact.image hjo.continuous).isClosed
  have hfr : ∀ c : (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut F).Base,
      c ∈ frontier (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
        (S.closedStagesAt_OCL B hT hεr A zero).cut F).cbase ↔
      j c ∈ frontier (S.chain.edgeC2_EFE (S.goodCut_OCL B hT hεr).K₃) := fun c => by
    rw [← hcb]
    exact (frontier_image_openEmbedding_JN74 hjo hcl hjcl (a := c)).symm
  have hcpt : IsCompact (S.chain.edgeM2_EFE (S.goodCut_OCL B hT hεr).K₃ ∩
      Subtype.val '' {x : S.chain.edgeSource_EFE | S.chain.edgeHeight_EFE x ≤
        4 * R.later.excl.Δ}) := by
    have h := Htail.edge_compact
    convert h using 1
    ext y
    constructor
    · rintro ⟨hyM, x, hxT, rfl⟩
      exact ⟨hyM, S.chain.mem_edgeRegion_of_source_JN74 x.2 hxT⟩
    · intro hyE
      obtain ⟨hyT, hysrc⟩ := S.chain.cutEdgeSet_height_le_JN74 R.two_le_Δ_EDP23
        (S.goodCut_OCL B hT hεr).K₃ hyE
      exact ⟨hyE.1, ⟨y, hysrc⟩, hyT, rfl⟩
  have hD := (S.goodCut_OCL B hT hεr).D₃_eq
  have hKs := (S.goodCut_OCL B hT hεr).K₃_req
  have hKF := (S.goodCut_OCL B hT hεr).K₃_faces
  have hDreg := S.goodCut_D₃_reg_OCL B hT hεr
  have hdD := S.goodCut_D₃_bdry_OCL B hT hεr
  have hH := S.chain.edge_frontier_H_EFE A hεr R.two_le_Δ_EDP23 hE.2.2.1 hE.2.2.2.1
    hE.2.2.2.2.1 hE.2.2.2.2.2.1 R.later.μ_lt_VAL6.le R.later.τ_lt_VAL6.le R.qe_le_thousandth_OCL
    (R.b_mul_le_OCL hT) hE.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2
    (S.goodCut_OCL B hT hεr).K₃ (S.goodCut_OCL B hT hεr).D₃ hD hKs hKF hDreg hdD hcpt
  rw [edgeBundle74_horizontalDisks_eq_JN74 (S.closedStagesAt_OCL B hT hεr A zero).cut
    M.ψ.toEquiv (S.chain.toGaf02ChainE.cutQ_R74 1)
    (S.closedStagesAt_OCL B hT hεr A zero).ιedge S.toE_RGC.toRowsSource_RGC.height F
    (S.closedStagesAt_OCL B hT hεr A zero).edge_ident.proj_eq
    (S.closedStagesAt_OCL B hT hεr A zero).edge_ident.emb.injective
    (S.edge_parent_of_below_JN74 B hT hεr A zero)
    (S.closedStagesAt_OCL B hT hεr A zero).edge_height]
  refine congrArg (Set.image M.ψ.toEquiv) ?_
  ext y
  constructor
  · rintro ⟨⟨c, hcF, hq⟩, hy⟩
    have hyT : S.chain.edgeHeightGlobal_EFE y ≤ 4 * R.later.excl.Δ := by
      have h1 : S.toE_RGC.toRowsSource_RGC.height y ≤ R.edgeLevel_R74 := by
        rw [← (S.closedStagesAt_OCL B hT hεr A zero).edge_level]
        exact hy
      rw [S.height_eq_OCL, ClosedRegisterV4.edgeLevel_R74] at h1
      exact h1
    have hcB : (c.1 : S.chain.toChain.finalBase_BAS 1) ∈
        S.chain.toGaf02ChainE.edgeBaseOpens_EFE := S.edgeBaseOpen_le_JN74 B hT hεr c.2
    have hR : S.chain.toGaf02ChainE.cutQ_R74 1 y ∈
        edgeRatio_R74 S.F.family.toLocalChartPacketsC14 := by
      rw [hq]
      exact hcB
    have hysrc : y ∈ S.chain.edgeSource_EFE :=
      S.chain.toGaf02ChainE.mem_edgeSource_EFE R.two_le_Δ_EDP23 hR hyT
    have hxj : S.chain.edgeProj_EFE ⟨y, hysrc⟩ = j c := by
      apply Subtype.ext
      apply Subtype.ext
      exact hq
    exact (Set.ext_iff.1 hH y).2 ⟨⟨y, hysrc⟩, ⟨hyT, by rw [hxj]; exact (hfr c).1 hcF⟩, rfl⟩
  · rintro ⟨hyF, x, hxT, rfl⟩
    obtain ⟨x', ⟨hx'T, hx'F⟩, hx'y⟩ := (Set.ext_iff.1 hH x.1).1 ⟨hyF, ⟨x, hxT, rfl⟩⟩
    have hx'x : x' = x := Subtype.ext hx'y
    rw [hx'x] at hx'F
    have hx'F' : S.chain.edgeProj_EFE x ∈ frontier (j '' (edgeBundle74
        (S.closedStagesAt_OCL B hT hεr A zero).A
        (S.closedStagesAt_OCL B hT hεr A zero).cut F).cbase) := by
      rw [hcb]
      exact hx'F
    obtain ⟨c, -, hcj⟩ := hjcl.frontier_subset hx'F'
    have hcF := (hfr c).2 (Eq.subst (motive := fun v : S.chain.toGaf02ChainE.edgeBaseOpens_EFE =>
      v ∈ frontier (S.chain.edgeC2_EFE (S.goodCut_OCL B hT hεr).K₃)) hcj.symm hx'F)
    have hq1 : S.chain.toGaf02ChainE.cutQ_R74 1 x.1 =
        (S.closedStagesAt_OCL B hT hεr A zero).ιedge c.1 :=
      (congrArg (fun v : S.chain.toGaf02ChainE.edgeBaseOpens_EFE =>
        ((v : S.chain.toChain.finalBase_BAS 1) : S.blockSpace_R74)) hcj).symm
    refine ⟨⟨c, hcF, hq1⟩, ?_⟩
    · rw [S.height_eq_OCL, (S.closedStagesAt_OCL B hT hεr A zero).edge_level,
        ClosedRegisterV4.edgeLevel_R74]
      exact hxT

/-- **FDC03's `region_boundary` at `D_R`** (field g5 of `JunctionFaceFacts74`), given the field g4
`frontier P.cut.M₂ = Bd` for the boundary set `Bd = boundaryM2`:
`P.cut.M₃ ∩ Bd = Bd \ relInt Bd (horizontal disks)`. -/
theorem region_boundary_at_JN74 (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (F : EdgeCutFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C) (Bd : Set W.Carrier)
    (hBd : frontier (S.closedStagesAt_OCL B hT hεr A zero).cut.M₂ = Bd) :
    (S.closedStagesAt_OCL B hT hεr A zero).cut.M₃ ∩ Bd =
      Bd \ relInt Bd (edgeBundle74 (S.closedStagesAt_OCL B hT hεr A zero).A
        (S.closedStagesAt_OCL B hT hεr A zero).cut F).horizontalDisks := by
  have hE := R.edpE_numerics_RGC hT hNb hcw
  have hg7 := R.gaf07_numerics_OCL hT
  rw [← hBd, S.cut_M₃_at_JN74 B hT hεr A zero hNb hcw,
    S.horizontalDisks_at_JN74 B hT hεr A zero Htail F hNb hcw, S.M₂_at_OCL B hT hεr A zero,
    ← image_frontier_R74 M.ψ, relInt_image_R74 M.ψ,
    ← image_inter (f := (M.ψ : M.X → W.Carrier)) M.ψ.injective,
    ← image_sdiff (f := (M.ψ : M.X → W.Carrier)) M.ψ.injective]
  refine congrArg (Set.image M.ψ) ?_
  have hD := (S.goodCut_OCL B hT hεr).D₃_eq
  have hKs := (S.goodCut_OCL B hT hεr).K₃_req
  have hKF := (S.goodCut_OCL B hT hεr).K₃_faces
  have hDreg := S.goodCut_D₃_reg_OCL B hT hεr
  have hdD := S.goodCut_D₃_bdry_OCL B hT hεr
  have h := S.chain.frontier_inter_cutM3_JN74 A hεr R.two_le_Δ_EDP23 hE.2.2.1 hE.2.2.2.1
    hE.2.2.2.2.1 hE.2.2.2.2.2.1 hE.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2
    (S.goodCut_OCL B hT hεr).K₃ (S.goodCut_OCL B hT hεr).D₃ hD hKs hKF hDreg hdD
  exact (inter_comm _ _).trans h

/-- **The face facts of the produced stage geometry from the primitives g1–g4, g6, g7**:
the field g5 `region_boundary` is PRODUCED from `frontier_M2` by `region_boundary_at_JN74`
(O-CL1's head `faces`; the remaining primitives are the explicit inputs, residual-table items
g1–g4, g6, g7). -/
def junctionFaceFacts_ofPrimitives_JN74 (A : SmoothStageBases74 S) (zero : ZSP02SmoothExit74 S)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Rw : StageCutRows74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut)
    (horizontal : Rw.edge.EdgeEnd → Rw.slimPieces.ResidualFace)
    (horizontal_disk : ∀ e, Rw.edge.disk e.1 ⊆ Rw.slimPieces.residualSet (horizontal e))
    (edge_faces : ∀ Fc, (S.closedStagesAt_OCL B hT hεr A zero).cut.edgeSet ∩
        Rw.slimPieces.residualSet Fc =
      ⋃ (e : Rw.edge.EdgeEnd) (_ : horizontal e = Fc), Rw.edge.disk e.1)
    (frontier_M2 : frontier (S.closedStagesAt_OCL B hT hεr A zero).cut.M₂ =
      Rw.slimPieces.boundaryM2)
    (slim_M2 : (S.closedStagesAt_OCL B hT hεr A zero).cut.slimSet ∩
        (S.closedStagesAt_OCL B hT hεr A zero).cut.M₂ =
      ⋃ e : Rw.slimPieces.NewEnd, Rw.slimPieces.endSet e.1)
    (shared_removed : ∀ σ : ActualSharedFace Rw.slimPieces,
      Rw.slimPieces.endSet σ.1 ⊆ relInt (regionM1 (S.closedStagesAt_OCL B hT hεr A zero).A.zero
        (S.closedStagesAt_OCL B hT hεr A zero).A.cusp)
        (S.closedStagesAt_OCL B hT hεr A zero).cut.slimSet) :
    JunctionFaceFacts74 (S.closedStagesAt_OCL B hT hεr A zero).A
      (S.closedStagesAt_OCL B hT hεr A zero).cut Rw where
  horizontal := horizontal
  horizontal_disk := horizontal_disk
  edge_faces := edge_faces
  frontier_M2 := frontier_M2
  region_boundary :=
    S.region_boundary_at_JN74 B hT hεr A zero Htail Rw.edgeFacts hNb hcw _ frontier_M2
  slim_M2 := slim_M2
  shared_removed := shared_removed

end At

end ClosedChainEZRowsSource_RGC

end DifferentialGeometry.Geometry.Collapse
