import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFdc04Fc39FinalJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GeometryFiniteFCP

/-!
# Draft 74, FDC04's finite lists of `C₁` and `M₃` at `D_R`

Lane S-JUNCTIONS (by S-JUNCTIONS5), G35 (suffix `_JN74`). The cut geometry `H = (rows, cover,
faces, rims, corners)` of the produced stage geometry at `D_R` (exit `slimExitAt3_OCL`), assembled
as `ClosedStageGeometryU74.geometry` does, with EVERY component produced: the rows `rows3At_JN74`,
the cover `cover_at_OCL`, the faces `faces3_JN74`, the rims `exists_rims_of_faces3_JN74`, the corner
descent `cornerDescent_at3_JN74` and the corner rank `cornerRankDescended_of_prim_JN74` with
`hprim_at_JN74`:

* `geometryAt3_JN74 : StageCutGeometry74 …`;
* `fdc04_finite_lists_at_OCL_JN74`: `StageCutGeometry74.finite_lists_FCP` (S-FINCOMP): the circle
  base `C₁` and the region `M₃` of the SAME cut (`K₃, D₃` of `D_R`, carried by `ψ`) are finite
  disjoint unions of compact connected pieces;
* `fdc04_fc39_finite_final_at_OCL_JN74`: the statement of `fdc04_fc39_final_at_OCL_JN74` (G34)
  together with the finite lists;
* `register_yields_fdc04_fc39_finite_final_JN74`: the register form.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{0}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

section At

variable (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
  (hT : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)))
  (hεr : εr < 1 / 2) (A : SmoothStageBases74 S) (hK : 5 ≤ K)

/-- **Corner rank and descended data at every endpoint of `D_R`, produced** (from `hprim_at_JN74`
through `cornerRankDescended_of_prim_JN74`, for any rim facts). -/
theorem hrankAt3_JN74 (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (rims : JunctionRimFacts74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut
      (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail)) :
    ∀ e, ∃ Kr : CornerRank74 (S.facesAt3_JN74 B hT hεr A hK hNb hcw Htail).facts rims e,
      Nonempty (CornerDescended74 Kr) := fun e => by
  obtain ⟨b, U, heU, hb, hbreg, hCU, hN⟩ := S.hprim_at_JN74 B hT hεr A hK hNb hcw Htail e
  exact StageCutRows74.cornerRankDescended_of_prim_JN74
    (S.zeroFace_slim_relInt_at_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr)) e
    (S.cornerDescent_at3_JN74 B hT hεr A hK _ _ _ rfl
      (S.facesAt3_JN74 B hT hεr A hK hNb hcw Htail).facts rims e) b U heU hb hbreg hCU hN

open Classical in
/-- **The corner facts at `D_R`**: descent, rank and descended data at every endpoint, produced. -/
def cornersAt3_JN74 (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr))
    (rims : JunctionRimFacts74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut
      (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail)) :
    CornerCutFacts74 (S.facesAt3_JN74 B hT hεr A hK hNb hcw Htail).facts rims where
  descent := fun e => S.cornerDescent_at3_JN74 B hT hεr A hK _ _ _ rfl
    (S.facesAt3_JN74 B hT hεr A hK hNb hcw Htail).facts rims e
  rank := fun e => (S.hrankAt3_JN74 B hT hεr A hK hNb hcw Htail rims e).choose
  descended := fun e => (S.hrankAt3_JN74 B hT hεr A hK hNb hcw Htail rims e).choose_spec.some

/-- **The rim facts at `D_R`, produced** (a chosen inhabitant of `exists_rims_of_faces3_JN74`). -/
def rimsAt3_JN74 (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    JunctionRimFacts74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut
      (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail) :=
  Classical.choice (S.exists_rims_of_faces3_JN74 B hT hεr A hK
    (S.edgeExitAtZ_OCL B hT hNb hcw hεr A Htail)
    (S.finalExitAtZ_OCL B hT hNb hcw hεr A Htail
      (S.cut_M₃_eq_circleRegion_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) hNb hcw))
    hNb hcw (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail) rfl
    (S.facesAt3_JN74 B hT hεr A hK hNb hcw Htail).facts
    (S.hprim_at_JN74 B hT hεr A hK hNb hcw Htail))

/-- **The cut geometry `H` at `D_R`, every component produced**: rows, cover (FDC04's point-set
cover), faces (g1–g7), rims and corners. -/
def geometryAt3_JN74 (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    StageCutGeometry74 (S.stagesAtZ_OCL B hT hεr A).A (S.stagesAtZ_OCL B hT hεr A).cut where
  rows := S.rows3At_JN74 B hT hεr A hK hNb hcw Htail
  cover := S.cover_at_OCL B hT hεr A (S.zsp02SmoothExit74 hεr)
    (S.goodCut_edgeSet_eq_OCL B hT hεr hNb hcw)
  faces := (S.facesAt3_JN74 B hT hεr A hK hNb hcw Htail).facts
  rims := S.rimsAt3_JN74 B hT hεr A hK hNb hcw Htail
  corners := S.cornersAt3_JN74 B hT hεr A hK hNb hcw Htail
    (S.rimsAt3_JN74 B hT hεr A hK hNb hcw Htail)

/-- **FDC04's finite lists at `D_R`**: the circle base `C₁` of the rows and the region `M₃` of the
produced cut (the carried `K₃, D₃` of `D_R`) are finite disjoint unions of compact connected
pieces (`StageCutGeometry74.finite_lists_FCP` on `geometryAt3_JN74`). -/
theorem fdc04_finite_lists_at_OCL_JN74 (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    (∃ (m : ℕ) (Bc : Fin m → Set (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).circle.Base),
      (∀ i, IsCompact (Bc i)) ∧ (∀ i, IsConnected (Bc i)) ∧ Pairwise (Disjoint on Bc) ∧
      (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).circle.cbase = ⋃ i, Bc i) ∧
    (∃ (m : ℕ) (Bm : Fin m → Set W.Carrier), (∀ i, IsCompact (Bm i)) ∧
      (∀ i, IsConnected (Bm i)) ∧ Pairwise (Disjoint on Bm) ∧
      (S.stagesAtZ_OCL B hT hεr A).cut.M₃ = ⋃ i, Bm i) :=
  (S.geometryAt3_JN74 B hT hεr A hK hNb hcw Htail).finite_lists_FCP

include A hK in
/-- **The region `M₃` of `D_R` on the model `M.X`: finite list** (the pull-back of the list of the
carried cut through `ψ`). -/
theorem fdc04_finite_M₃_chain_at_OCL_JN74 (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    ∃ (m : ℕ) (Bm : Fin m → Set M.X), (∀ i, IsCompact (Bm i)) ∧ (∀ i, IsConnected (Bm i)) ∧
      Pairwise (Disjoint on Bm) ∧ (S.goodCut_OCL B hT hεr).M₃ = ⋃ i, Bm i := by
  obtain ⟨m, Bm, hc, hco, hd, hu⟩ :=
    (S.fdc04_finite_lists_at_OCL_JN74 B hT hεr A hK hNb hcw Htail).2
  have hψ : Continuous (M.ψ.symm : W.Carrier → M.X) := M.ψ.symm.continuous
  refine ⟨m, fun i => (M.ψ.symm : W.Carrier → M.X) '' Bm i, fun i => (hc i).image hψ,
    fun i => (hco i).image _ hψ.continuousOn, fun i i' hii' => ?_, ?_⟩
  · exact (Set.disjoint_image_iff M.ψ.symm.injective).2 (hd hii')
  · rw [← image_iUnion, ← hu, S.cut_M₃_at_JN74 B hT hεr A (S.zsp02SmoothExit74 hεr) hNb hcw]
    ext x
    constructor
    · intro hx
      exact ⟨M.ψ x, ⟨x, hx, rfl⟩, M.ψ.symm_apply_apply x⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa using hy

include A hK in
/-- **The circle base `C₁` of `D_R` in the block space: finite list** (the image of the list of
the rows' circle base under the identification embedding of the circle stage). -/
theorem fdc04_finite_C₁_chain_at_OCL_JN74 (hNb : T.Nb = maxNb_V4C) (hcw : T.cw = maxCw_V4C)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B hT hεr)) :
    ∃ (m : ℕ) (Bc : Fin m → Set S.blockSpace_R74), (∀ i, IsCompact (Bc i)) ∧
      (∀ i, IsConnected (Bc i)) ∧ Pairwise (Disjoint on Bc) ∧
      (S.goodCut_OCL B hT hεr).C₁ = ⋃ i, Bc i := by
  obtain ⟨m, Bc, hc, hco, hd, hu⟩ :=
    (S.fdc04_finite_lists_at_OCL_JN74 B hT hεr A hK hNb hcw Htail).1
  let j : (S.rows3At_JN74 B hT hεr A hK hNb hcw Htail).circle.Base → S.blockSpace_R74 :=
    fun c => (S.stagesAtZ_OCL B hT hεr A).ιcircle c.1
  have hjc : Continuous j := (S.stagesAtZ_OCL B hT hεr A).circle_ident.emb.continuous.comp
    continuous_subtype_val
  have hji : Injective j := (S.stagesAtZ_OCL B hT hεr A).circle_ident.emb.injective.comp
    Subtype.val_injective
  refine ⟨m, fun i => j '' Bc i, fun i => (hc i).image hjc,
    fun i => (hco i).image _ hjc.continuousOn, fun i i' hii' => ?_, ?_⟩
  · exact (Set.disjoint_image_iff hji).2 (hd hii')
  · rw [← image_iUnion, ← hu]
    have hC := (S.stagesAtZ_OCL B hT hεr A).cut_C₁
    have hsub := (S.stagesAtZ_OCL B hT hεr A).cut.C₁_sub
    rw [← hC]
    ext x
    constructor
    · rintro ⟨c, hc1, rfl⟩
      exact ⟨⟨c, hsub hc1⟩, hc1, rfl⟩
    · rintro ⟨c, hc1, rfl⟩
      exact ⟨c.1, hc1, rfl⟩

end At

/-- **FDC04's complete row, the FC39 fields and the finite lists of `C₁` and `M₃` at one source at
`D_R`** (G34's statement and the finite lists for the same `K₃, D₃`). -/
theorem fdc04_fc39_finite_final_at_OCL_JN74 (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (B : ClosedBases74 S) (N : ClosedRowsNumericsAt74 S) (hK : 5 ≤ K) (A : SmoothStageBases74 S)
    (Htail : ClosedFdcFacts74 (S.goodCut_OCL B N.strategy_below N.eps_lt)) :
    type_of% (S.fdc04_row_complete_at_OCL_FD4 B N hK A Htail) ∧
      (∃ Rw : FC39RowsV2 W (BoundaryTori.empty W),
        ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw ∧
        Nonempty (StrongCertificate W (BoundaryTori.empty W))) ∧
      (∃ (m : ℕ) (Bc : Fin m → Set S.blockSpace_R74), (∀ i, IsCompact (Bc i)) ∧
        (∀ i, IsConnected (Bc i)) ∧ Pairwise (Disjoint on Bc) ∧
        (S.goodCut_OCL B N.strategy_below N.eps_lt).C₁ = ⋃ i, Bc i) ∧
      (∃ (m : ℕ) (Bm : Fin m → Set M.X), (∀ i, IsCompact (Bm i)) ∧
        (∀ i, IsConnected (Bm i)) ∧ Pairwise (Disjoint on Bm) ∧
        (S.goodCut_OCL B N.strategy_below N.eps_lt).M₃ = ⋃ i, Bm i) :=
  ⟨S.fdc04_row_complete_at_OCL_FD4 B N hK A Htail,
    S.closed_rows_gate_final_OCL B N.strategy_below N.eps_lt A hK N.nb_eq N.cw_eq Htail,
    S.fdc04_finite_C₁_chain_at_OCL_JN74 B N.strategy_below N.eps_lt A hK N.nb_eq N.cw_eq Htail,
    S.fdc04_finite_M₃_chain_at_OCL_JN74 B N.strategy_below N.eps_lt A hK N.nb_eq N.cw_eq Htail⟩

end ClosedChainEZRowsSource_RGC

/-- **Consumer: the register yields FDC04's complete row, the FC39 fields and the finite lists of
`C₁`, `M₃` at `D_R`** (as `register_yields_fdc04_fc39_final_JN74` with the lists added). -/
theorem register_yields_fdc04_fc39_finite_final_JN74 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{0})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, 0 < εr ∧ εr < 1 / 4 ∧
        ∃ n : ℕ, ∀ m, n ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧
          ∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            ∃ N : ClosedRowsNumericsAt74 S, ∃ Hm : ∀ B : ClosedBases74 S,
              ClosedFdcMemberFacts74 S B, ∀ (B : ClosedBases74 S) (Ab : SmoothStageBases74 S),
              type_of% (S.fdc04_row_complete_at_OCL_FD4 B N (le_trans (by norm_num) hK) Ab
                ((Hm B).facts _)) ∧
              (∃ Rw : FC39RowsV2 (Wseq m) (BoundaryTori.empty (Wseq m)),
                ClosedRowsLinkAtU74 S B (S.goodCut_OCL B N.strategy_below N.eps_lt) Rw ∧
                Nonempty (StrongCertificate (Wseq m) (BoundaryTori.empty (Wseq m)))) ∧
              (∃ (m' : ℕ) (Bc : Fin m' → Set S.blockSpace_R74), (∀ i, IsCompact (Bc i)) ∧
                (∀ i, IsConnected (Bc i)) ∧ Pairwise (Disjoint on Bc) ∧
                (S.goodCut_OCL B N.strategy_below N.eps_lt).C₁ = ⋃ i, Bc i) ∧
              (∃ (m' : ℕ) (Bm : Fin m' → Set M.X), (∀ i, IsCompact (Bm i)) ∧
                (∀ i, IsConnected (Bm i)) ∧ Pairwise (Disjoint on Bm) ∧
                (S.goodCut_OCL B N.strategy_below N.eps_lt).M₃ = ⋃ i, Bm i) :=
  (register_yields_fdcFacts_RNUM K hK A hA Wseq gseq hf hg).imp fun T hT R =>
    (hT.2.2.2 R).imp fun εr h1 => h1.imp fun δ h2 => h2.imp fun Λz h3 =>
      ⟨h3.1, h3.2.1, h3.2.2.imp fun n hn m hm => (hn m hm).imp fun M h4 =>
        ⟨h4.1, fun x₀ => (h4.2 x₀).imp fun S h5 =>
          ⟨h5.1, h5.2.1.elim fun N => ⟨N, h5.2.2, fun B Ab =>
            S.fdc04_fc39_finite_final_at_OCL_JN74 B N (le_trans (by norm_num) hK) Ab
              ((h5.2.2 B).facts _)⟩⟩⟩⟩

end DifferentialGeometry.Geometry.Collapse
