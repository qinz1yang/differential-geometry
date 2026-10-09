import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeParentOWF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeDiskCompositionOED
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimFibreLevel
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleChart
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLocalRecord
import DifferentialGeometry.Topology.Manifold.SubmersionOpenMap

/-!
# O-WF G7: the edge-stage whole-fibre disk charts of the boundary chain

**`BoundaryGaf02ChainE.edge_chart_OWF`**: at every point `y` of the edge base
`B₁ = C.baseSet_BBP 1`, the final stage map `f₁` on the (non-open) source
`X₁ = C.baseSource_BBP 1 = U ∩ {T ≤ 4Δ}` has a smooth local disk-bundle chart with the vertical rim
at `T = 4Δ` (`SmoothDiskChartAt_BIFc W.model 1 f₁ T (4Δ) X₁ B₁ y`), the `edge_chart` field of the
whole-fibre layer (G19b's `hedge`). Route:

1. a chart `j` of the ratio piece of `y`, a source point `q₀ ∈ Y_j` over `y`, the active slot `O`
   and the local inverse of `κ¹_j = e ∘ κ_j` on `Z₁` at `f₁⁰(q₀)` (`edge_localInverse_OWF`);
2. the open mapping of `κ¹_j ∘ f₁ ∘ val` at `q₀` (`edge_submersion_interior_OWF`);
3. the local record on the OPEN parent `U = C.edgeParentSet_OWF` (`exists_localRecord_OWF`): the
   native image of `U` is the native image of `X₁` (`edgeParent_native_image_OWF`, the shifted disks
   of G6), so `Θ₁` embeds it (`edge_later_isEmbedding_OWF`);
4. lane O-EDGEDISK's packaging `smoothDiskChartAt_of_localRecord_OED` with the cross-model
   composition `isSmoothEmbedding_val_comp_diskChart_OED`, the whole fibre over `y` as the smooth
   disk of `edge_wholeDisk_OWF` (`edge_fibre_eq_disk_OWF`), and the rim submersion
   (`rim_surjective_wdeg_BAUGD`, through `edge_rim_pair_interior_OWF`).

Register premises: those of G6 (`μ, τ ≤ 10⁻⁸`, `σc ≤ 10⁻³`, `b ≤ 1/(1000Δ)`, `c₃ < 10⁻⁵`, N76-9,
`0 ≤ ε < 1`, `0 < γc ≤ 1/100`, `βc ≤ 10⁻⁵`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- The `ℝ¹`-valued edge chart coordinate `κ¹_j = e ∘ κ_j`. -/
def edgeKappa1_OWF (j : S.EdgeIdx_BAUGD) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ¹ :=
  (realToFin1_OWF : ℝ →L[ℝ] ℝ¹).comp (S.edgeKappa_BBP j)

theorem edgeKappa1_apply_OWF (j : S.EdgeIdx_BAUGD)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.edgeKappa1_OWF j y = realToFin1_OWF (S.edgeKappa_BBP j y) :=
  rfl

end BoundarySupplyCore

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- The `ℝ¹`-valued adjusted edge coordinate is smooth on `W°`. -/
theorem edge_adjusted1_contMDiff_OWF (j : S.EdgeIdx_BAUGD) :
    ContMDiff (𝓡 3) (𝓡 1) ∞
      (fun q : W.pieceInterior ⊤ => S.edgeKappa1_OWF j (C.toChain.stageMap 1 q.val)) :=
  ((S.edgeKappa1_OWF j).comp ((actualSlotsV2_BAUGD S).stageProj 1)).contDiff.comp_contMDiff
    ((C.stage_smooth_BAUGD 3).comp (isLocalDiffeomorph_pieceInterior_val W ⊤).contMDiff)

/-- **The final edge submersion on `W°`** (`ℝ¹`-valued) at every point with `T ≤ 4Δ` whose value
lies in the ratio piece of chart `j`. -/
theorem edge_submersion_interior_OWF (hσ : σc ≤ 1 / 4) (hb : b ≤ 1 / (1000 * Δ))
    (j : S.EdgeIdx_BAUGD) (x : W.pieceInterior ⊤)
    (hx : C.toChain.stageMap 1 x.val ∈
      ratioPiece_BBP (S.edgeKappa_BBP j) (S.edgeMarker_BAUGD j) (S.rho j.1) Δ)
    (hT : C.toChain.heightRatio x.val ≤ 4 * Δ) :
    Surjective (mfderiv (𝓡 3) (𝓡 1)
      (fun x : W.pieceInterior ⊤ => S.edgeKappa1_OWF j (C.toChain.stageMap 1 x.val)) x) := by
  obtain ⟨-, hΔ, -⟩ := C.std
  obtain ⟨q, hq, hd, hη, ht⟩ := C.edge_final_loc_BBP j hx hT
  have hqx : q = x := Subtype.ext hq
  subst hqx
  have hfd : MDifferentiableAt W.model 𝓘(ℝ, ℝ)
      (fun p => S.edgeKappa_BBP j (C.toChain.stageMap 1 p)) q.val :=
    ((S.edgeKappa_BBP j).comp ((actualSlotsV2_BAUGD S).stageProj 1)).differentiableAt
      |>.comp_mdifferentiableAt (((C.stage_smooth_BAUGD 3) q.val).mdifferentiableAt (by simp))
  have h1 := surjective_mfderiv_clm_comp_OWF realToFin1_OWF hfd
    (C.final_submersion_edge_BBP hσ hb j hd (by linarith) (by linarith))
  have hfd1 : MDifferentiableAt W.model 𝓘(ℝ, ℝ¹)
      (fun p => S.edgeKappa1_OWF j (C.toChain.stageMap 1 p)) q.val :=
    ((S.edgeKappa1_OWF j).comp ((actualSlotsV2_BAUGD S).stageProj 1)).differentiableAt
      |>.comp_mdifferentiableAt (((C.stage_smooth_BAUGD 3) q.val).mdifferentiableAt (by simp))
  exact surjective_mfderiv_comp_val_OWF q hfd1 h1

/-- **Local one-sheet, edge stage** (`κ¹_j` on `Z₁` near `f₁⁰(q)`). -/
theorem edge_localInverse_OWF (hσ : σc ≤ 1 / 4) (hb : b ≤ 1 / (1000 * Δ))
    (O : Cfs15StageOutput (gafStageDim 1) Kj (Ξ 1) (cw 1)
      ((actualSlotsV2_BAUGD S).stageCloud 1) ((actualSlotsV2_BAUGD S).stageCloudEnlarged 1)
      (DP.stageRadius 1 (Sg 1)) (DP.stagePlane 1))
    (hO : C.toChain.slot 1 = .active O) (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 6 * Δ) (hh : S.edgeHeightRaw q < 6 * Δ) :
    ∃ (V : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) (δ : ℝ)
      (ζ : ℝ¹ → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
      IsOpen V ∧ C.toChain.nativeStageMap_BIFc 1 q.val ∈ V ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ ζ (ball (S.edgeKappa1_OWF j (C.toChain.nativeStageMap_BIFc 1 q.val)) δ) ∧
      (∀ b ∈ ball (S.edgeKappa1_OWF j (C.toChain.nativeStageMap_BIFc 1 q.val)) δ,
        ζ b ∈ O.Z ∩ V ∧ S.edgeKappa1_OWF j (ζ b) = b) ∧
      (∀ w ∈ O.Z ∩ V,
        S.edgeKappa1_OWF j w ∈ ball (S.edgeKappa1_OWF j (C.toChain.nativeStageMap_BIFc 1 q.val))
          δ ∧ ζ (S.edgeKappa1_OWF j w) = w) := by
  have hnd : MDifferentiableAt W.model 𝓘(ℝ, ℝ)
      (fun p => S.edgeKappa_BBP j (C.toChain.nativeStageMap_BIFc 1 p)) q.val :=
    ((S.edgeKappa_BBP j).comp ((actualSlotsV2_BAUGD S).stageProj 1)).differentiableAt
      |>.comp_mdifferentiableAt (((C.stage_smooth_BAUGD 2) q.val).mdifferentiableAt (by simp))
  exact C.native_localInverse_OWF 1 (S.edgeKappa1_OWF j)
    (fun y => congrArg realToFin1_OWF (edgeKappa_stageProj_BBP j y)) (by simp [gafStageDim])
    O hO (S.edge_plateau_mem_nhds_BBP j hq hη hh)
    (fun q' hq' => C.edge_plateau_cutoff_BBP j hq'.1 hq'.2.1 hq'.2.2)
    (surjective_mfderiv_clm_comp_OWF realToFin1_OWF hnd
      (C.stage_submersion_edge_BBP hσ hb j hq hη hh))

include C in
/-- **The native image of the open parent is the native image of the source**:
`f₁⁰(U) = f₁⁰(X₁)` (the shifted adjusted disks of G6). -/
theorem edgeParent_native_image_OWF (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000) :
    C.toChain.nativeStageMap_BIFc 1 '' C.edgeParentSet_OWF =
      C.toChain.nativeStageMap_BIFc 1 '' C.baseSource_BBP 1 := by
  obtain ⟨-, hΔ0, -⟩ := C.std
  refine Subset.antisymm ?_ (image_mono fun p hp =>
    (C.baseSource_one_eq_edgeParent_OWF ▸ hp : p ∈ C.edgeParentSet_OWF ∩ _).1)
  rintro _ ⟨p, hp, rfl⟩
  by_cases hT4 : C.toChain.heightRatio p ≤ 4 * Δ
  · exact ⟨p, ⟨hp.1, fun _ => hT4⟩, rfl⟩
  push Not at hT4
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp.1
  obtain ⟨q, rfl, hqY, hη⟩ := C.edge_loc41_OWF hc hC j hj hp.2
  set a := S.edgeKappa_BBP j (C.toChain.stageMap 1 q.val) with ha_def
  have hga : S.edgeRatio_BAUGD j (C.toChain.E q.val) = a := (C.edgeKappa_stageMap_OWF j _).symm
  have ha : |a| < 81 / 20 * Δ := by
    have hcl := C.edge_value_close_OWF j hqY.1 (by linarith [hqY.2.1]) (by linarith [hqY.2.2])
    rw [← hga]
    have h1 := abs_sub_abs_le_abs_sub (S.edgeRatio_BAUGD j (C.toChain.E q.val))
      (S.edgeEta_BIF j.1 q)
    obtain ⟨-, -, -, -, -, -, -, -, -, hΔ1, -⟩ := C.std
    linarith
  set δ' := C.toChain.heightRatio q.val - 4 * Δ with hδ'
  have hδ0 : 0 ≤ δ' := by linarith
  have hδ1 : δ' ≤ Δ / 10 := by linarith [hp.2]
  obtain ⟨hpc, -⟩ := C.edgeDisk_preconnected_nonempty_OWF hμ hτ hσc hb hc hC hε0 hε hγc hγc1
    hβc1 j ha hδ0 hδ1
  obtain ⟨-, ⟨q₀, hq₀⟩⟩ := C.edgeDisk_preconnected_nonempty_OWF hμ hτ hσc hb hc hC hε0 hε hγc
    hγc1 hβc1 j ha le_rfl (by positivity)
  obtain ⟨O, hO⟩ := C.exists_active_of_edgeSource_OWF j hqY
  have hconst := C.edge_native_const_OWF (by linarith) hb O hO j hpc (fun x hx => hx.1)
    (a := a) (fun x hx => by rw [C.edgeKappa_stageMap_OWF]; exact hx.2.1)
  have hqD : q ∈ {x | x ∈ S.edgeSource_OWF j ∧ S.edgeRatio_BAUGD j (C.toChain.E x.val) = a ∧
      C.toChain.heightRatio x.val - δ' ≤ 4 * Δ} := ⟨hqY, hga, by linarith⟩
  have hq₀D : q₀ ∈ {x | x ∈ S.edgeSource_OWF j ∧ S.edgeRatio_BAUGD j (C.toChain.E x.val) = a ∧
      C.toChain.heightRatio x.val - δ' ≤ 4 * Δ} := ⟨hq₀.1, hq₀.2.1, by linarith [hq₀.2.2]⟩
  have h := hconst q hqD q₀ hq₀D
  have hff : C.toChain.stageMap 1 q.val = C.toChain.stageMap 1 q₀.val := by
    rw [C.toChain.final_factor_V2_BAUGD 1 q.val, h, ← C.toChain.final_factor_V2_BAUGD 1 q₀.val]
  refine ⟨q₀.val, ⟨?_, fun _ => by linarith [hq₀.2.2]⟩, h.symm⟩
  rw [← hff]
  exact hp.1

include C in
/-- **The rim submersion on `W°`** in the `ℝ¹ × ℝ` form of the edge disk packaging: at a point
with `T = 4Δ` whose value lies in the ratio piece of chart `j`, `d(κ¹_j ∘ f₁ ∘ val, T ∘ val)` is
onto. -/
theorem edge_rim_pair_interior_OWF (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    (j : S.EdgeIdx_BAUGD) (x : W.pieceInterior ⊤)
    (hx : C.toChain.stageMap 1 x.val ∈
      ratioPiece_BBP (S.edgeKappa_BBP j) (S.edgeMarker_BAUGD j) (S.rho j.1) Δ)
    (hT : C.toChain.heightRatio x.val = 4 * Δ) :
    Surjective (mfderiv (𝓡 3) 𝓘(ℝ, ℝ¹ × ℝ) (fun z : W.pieceInterior ⊤ =>
      (S.edgeKappa1_OWF j (C.toChain.stageMap 1 z.val), C.toChain.heightRatio z.val)) x) := by
  obtain ⟨q, hq, hd, hη, ht⟩ := C.edge_final_loc_BBP j hx hT.le
  have hqx : q = x := Subtype.ext hq
  subst hqx
  have hsurj := C.rim_surjective_wdeg_BAUGD hc hC hε0 hε hγc hγc1 hβc1 j hd hη ht hT
  have hg := (C.edgeAdjusted_contMDiff_OWF j) q
  have hTc := (C.heightRatio_interior_contMDiff_OWF) q
  have hpair : Surjective (mfderiv (𝓡 3) 𝓘(ℝ, ℝ × ℝ) (fun z : W.pieceInterior ⊤ =>
      (S.edgeRatio_BAUGD j (C.toChain.E z.val), C.toChain.heightRatio z.val)) q) :=
    surjective_mfderiv_pair_EFE hg hTc fun y => by
      obtain ⟨u, hu⟩ := hsurj y
      exact ⟨u, congrArg Prod.fst hu, congrArg Prod.snd hu⟩
  let L : (ℝ × ℝ) ≃L[ℝ] (ℝ¹ × ℝ) := realToFin1_OWF.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have hpd : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ × ℝ) (fun z : W.pieceInterior ⊤ =>
      (S.edgeRatio_BAUGD j (C.toChain.E z.val), C.toChain.heightRatio z.val)) q :=
    (hg.prodMk_space hTc).mdifferentiableAt (by simp)
  have h := surjective_mfderiv_clm_comp_OWF L hpd hpair
  have hfun : (fun z : W.pieceInterior ⊤ =>
      L (S.edgeRatio_BAUGD j (C.toChain.E z.val), C.toChain.heightRatio z.val)) =
      fun z : W.pieceInterior ⊤ =>
        (S.edgeKappa1_OWF j (C.toChain.stageMap 1 z.val), C.toChain.heightRatio z.val) :=
    funext fun z => by
      rw [S.edgeKappa1_apply_OWF, C.edgeKappa_stageMap_OWF]
      rfl
  rw [hfun] at h
  exact h

include C in
/-- **The edge-stage whole-fibre disk chart at every base point** (see the module docstring). -/
theorem edge_chart_OWF (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b ≤ 1 / (1000 * Δ)) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100) (hβc1 : βc ≤ 1 / 100000)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.baseSet_BBP 1) :
    SmoothDiskChartAt_BIFc W.model 1 (C.toChain.stageMap 1) C.toChain.heightRatio (4 * Δ)
      (C.baseSource_BBP 1) (C.baseSet_BBP 1) y := by
  have : LocallyCompactSpace (W.pieceInterior ⊤) :=
    Manifold.locallyCompact_of_finiteDimensional (𝓡 3)
  obtain ⟨-, hΔ, -⟩ := C.std
  have hσ : σc ≤ 1 / 4 := by linarith
  have hy' := hy
  obtain ⟨p₀, hp₀, hfp₀⟩ := hy'
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp₀.1
  have hyj : y ∈ ratioPiece_BBP (S.edgeKappa_BBP j) (S.edgeMarker_BAUGD j) (S.rho j.1) Δ :=
    hfp₀ ▸ hj
  have hT₀ : C.toChain.heightRatio p₀ ≤ 4 * Δ := hp₀.2 rfl
  obtain ⟨q₀, hq₀, hq₀Y⟩ := C.edge_mem_Y_of_piece_OWF j hj hT₀
  have hq₀X : q₀.val ∈ C.baseSource_BBP 1 := hq₀ ▸ hp₀
  obtain ⟨O, hO⟩ := C.exists_active_of_source_OWF 1 hp₀
  obtain ⟨hd₀, hη₀, ht₀⟩ := hq₀Y
  obtain ⟨V, δ, ζ, hV, hmem, hδ, hζs, -, hl⟩ :=
    C.edge_localInverse_OWF hσ hb O hO j hd₀ (by linarith) (by linarith)
  -- the open mapping at `q₀`
  have hq₀piece : C.toChain.stageMap 1 q₀.val ∈
      ratioPiece_BBP (S.edgeKappa_BBP j) (S.edgeMarker_BAUGD j) (S.rho j.1) Δ := by
    rw [hq₀]; exact hj
  have hmap₀ := DifferentialGeometry.Topology.map_nhds_eq_of_mfderiv_surjective_at
    (((C.edge_adjusted1_contMDiff_OWF j) q₀).of_le (by simp))
    (C.edge_submersion_interior_OWF hσ hb j q₀ hq₀piece (by rw [hq₀]; exact hT₀))
  have hκf : ∀ p, S.edgeKappa1_OWF j (C.toChain.nativeStageMap_BIFc 1 p) =
      S.edgeKappa1_OWF j (C.toChain.stageMap 1 p) := fun p =>
    congrArg realToFin1_OWF (congrFun (C.edge_kappa_final_eq_BBP j) p).symm
  have hfun : (fun x : W.pieceInterior ⊤ =>
      S.edgeKappa1_OWF j (C.toChain.nativeStageMap_BIFc 1 x.val)) =
      fun x => S.edgeKappa1_OWF j (C.toChain.stageMap 1 x.val) :=
    funext fun x => hκf x.val
  have hmap : map (fun x : W.pieceInterior ⊤ =>
      S.edgeKappa1_OWF j (C.toChain.nativeStageMap_BIFc 1 x.val)) (𝓝 q₀) =
      𝓝 (S.edgeKappa1_OWF j (C.toChain.nativeStageMap_BIFc 1 q₀.val)) := by
    rw [hfun, hκf q₀.val]
    exact hmap₀
  -- the local record on the open parent
  have himgU := C.edgeParent_native_image_OWF hμ hτ hσc hb hc hC hε0 hε hγc hγc1 hβc1
  have hembU : Topology.IsEmbedding (fun x : C.toChain.nativeStageMap_BIFc 1 ''
      C.edgeParentSet_OWF => C.toChain.laterV2_BAUGD 1 x) := by
    rw [himgU]
    exact C.edge_later_isEmbedding_OWF hμ hτ hσc hb hc hC hε0 hε hγc hγc1 hβc1
  have hUo : IsOpen ((Subtype.val : W.pieceInterior ⊤ → W.Carrier) ⁻¹' C.edgeParentSet_OWF) :=
    C.isOpen_edgeParentSet_OWF.preimage continuous_subtype_val
  have hZ : ∀ p ∈ C.edgeParentSet_OWF, C.toChain.nativeStageMap_BIFc 1 p ∈ O.Z := by
    intro p hp
    obtain ⟨j', hj'⟩ := Set.mem_iUnion.mp hp.1
    obtain ⟨q, rfl, ⟨hd, hη, ht⟩, -⟩ := C.edge_loc41_OWF hc hC j' hj' hp.2
    exact C.toChain.native_scope_V2_BAUGD 1 O hO q.val
      (C.edge_plateau_cutoff_BBP j' hd (by linarith) (by linarith))
  have hq₀U : q₀.val ∈ C.edgeParentSet_OWF :=
    (C.baseSource_one_eq_edgeParent_OWF ▸ hq₀X : q₀.val ∈ C.edgeParentSet_OWF ∩ _).1
  obtain ⟨σ₀, Mk, Dset, hMk, hDo, hyMk, -, hσs, hσb, hσc'⟩ :=
    exists_localRecord_OWF (N := W.pieceInterior ⊤) continuous_subtype_val hUo
      (C.continuous_native_OWF 1) (Zs := O.Z) hZ (S.edgeKappa1_OWF j)
      (fun x => congrArg realToFin1_OWF (C.edgeKappa_laterV2_BBP j x))
      (fun p _ => C.toChain.later_contDiffAt_V2_BAUGD 1 p) hembU hq₀U hV hmem hδ hζs
      (fun w hw => (hl w hw).2) hmap
  have hB : C.baseSet_BBP 1 = C.toChain.laterV2_BAUGD 1 ''
      (C.toChain.nativeStageMap_BIFc 1 '' C.edgeParentSet_OWF) := by
    rw [himgU]
    exact C.baseSet_eq_later_native_BBP 1
  have hy0 : C.toChain.laterV2_BAUGD 1 (C.toChain.nativeStageMap_BIFc 1 q₀.val) = y := by
    rw [← C.toChain.final_factor_V2_BAUGD 1 q₀.val, hq₀, hfp₀]
  rw [hy0] at hyMk
  -- the whole fibre over `y` as a smooth disk
  have ha : |S.edgeKappa_BBP j y| < 81 / 20 * Δ := by
    have h := C.edge_kappa_lt_OWF j hj hT₀
    rwa [hfp₀] at h
  obtain ⟨φ, hφ, hr, hrim⟩ := C.edge_wholeDisk_OWF hμ hτ hσc hb hc hC hε0 hε hγc hγc1 hβc1 j ha
    le_rfl (by positivity)
  have hfib := C.edge_fibre_eq_disk_OWF hμ hτ hσc hb hc hC hε0 hε hγc hγc1 hβc1 j hy hyj
  have hψr : range φ = {x : W.pieceInterior ⊤ | x.val ∈ C.baseSource_BBP 1 ∧
      C.toChain.stageMap 1 x.val = y} := hr.trans hfib.symm
  have hψrim : ∀ w, C.toChain.heightRatio (φ w).val = 4 * Δ ↔
      ‖(w : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    intro w
    constructor
    · intro hw
      have hmemr : φ w ∈ range φ := mem_range_self w
      rw [hr] at hmemr
      have hmemb : φ w ∈ range (φ ∘ cellBoundaryInclusion 2) := by
        rw [hrim]
        exact ⟨hmemr.1, hmemr.2.1, by rw [sub_zero]; exact hw⟩
      obtain ⟨w', hw'⟩ := hmemb
      have hww : cellBoundaryInclusion 2 w' = w := hφ.isEmbedding.injective hw'
      rw [← hww]
      exact w'.2
    · intro hw
      have hmemb : φ w ∈ range (φ ∘ cellBoundaryInclusion 2) := ⟨⟨w.1, hw⟩, rfl⟩
      rw [hrim] at hmemb
      have h := hmemb.2.2
      rwa [sub_zero] at h
  have hXι : C.baseSource_BBP 1 ⊆ range (Subtype.val : W.pieceInterior ⊤ → W.Carrier) := by
    intro p hp
    obtain ⟨j', q, hq, -, -⟩ := C.edge_source_loc_BBP hp
    exact ⟨q, hq⟩
  have hprop := C.proper_of_source_eq_V2_BAUGD C.baseSource_BBP C.baseSet_BBP
    (C.baseSource_eq_preimage_BBP (by decide)) C.baseSource_one_eq_preimage_BBP
    (C.baseSource_eq_preimage_BBP (by decide)) 1
  exact smoothDiskChartAt_of_localRecord_OED (by simp) Subtype.val
    Topology.IsEmbedding.subtypeVal (isSmoothEmbedding_val_comp_diskChart_OED W)
    (C.toChain.stageMap 1) C.toChain.heightRatio (4 * Δ) C.edgeParentSet_OWF
    (C.baseSource_BBP 1) (C.baseSet_BBP 1) (S.edgeKappa1_OWF j) σ₀ (C.baseSet_BBP 1) Mk univ
    (ratioPiece_BBP (S.edgeKappa_BBP j) (S.edgeMarker_BAUGD j) (S.rho j.1) Δ)
    hDo (inter_univ _).symm isOpen_univ hMk (isOpen_ratioPiece_BBP _ _ _ _) hσs
    (fun b' hb' => hB ▸ hσb b' hb') (fun y' hy' => hσc' y' (hB ▸ hy'))
    C.baseSource_one_eq_edgeParent_OWF hXι rfl hUo
    ((C.continuous_stageMap_V2_BAUGD 1).comp continuous_subtype_val)
    (C.edge_adjusted1_contMDiff_OWF j) C.heightRatio_interior_contMDiff_OWF
    (fun x hxX _ hxP => C.edge_submersion_interior_OWF hσ hb j x hxP (hxX.2 rfl))
    (fun x _ hxT _ hxP => C.edge_rim_pair_interior_OWF hc hC hε0 hε hγc hγc1 hβc1 j x hxP hxT)
    hprop hy hyMk hyj φ hφ hψr hψrim

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
