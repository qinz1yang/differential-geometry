import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimLevelAdjusted
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleFibreLevel
import DifferentialGeometry.Topology.FundamentalGroup.Sphere

/-!
# O-WF G3e: the whole slim fibre is the adjusted level (local one-sheet at the slim stage)

On `C : BoundaryGaf02ChainE DP …`, slim stage (`Θ₂ = id`, so `f₂ = f₂⁰`), sources
`X₂ = C.baseSource_BBP 2`, bases `B₂ = C.baseSet_BBP 2`:

* `realToFin1_OWF : ℝ ≃L ℝ¹` and the `ℝ¹`-valued slim chart coordinate `slimKappa1_OWF j`
  (the base model of `SmoothProductChartAt_BIFc` is `EuclideanSpace ℝ (Fin 1)`);
* `surjective_mfderiv_clm_comp_OWF` (a submersion stays one after a linear isomorphism);
* `slim_localInverse_OWF`: the local inverse of `κ¹_j` on `Z₂` at a slim plateau point;
* `slim_mem_Y_of_piece_OWF`, `slim_norm_kappa_lt_OWF` (`|κ_j y| < 4·10⁵Δ` on the ratio piece);
* `slim_level_isPreconnected_OWF` (each whole adjusted level is the image of a standard connected
  surface), **`slim_native_const_OWF`**, **`slim_fibre_eq_level_OWF`** (the whole slim fibre over
  `y ∈ B₂` equals the whole adjusted level `{q ∈ Y_j | κ_j(f₂ q) = κ_j y}`).

Register premises: `c₂ < 1/1000`, `K ≥ 5`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic GC.GraphManifold
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- The linear isometry class identification `ℝ ≃L ℝ¹`. -/
def realToFin1_OWF : ℝ ≃L[ℝ] ℝ¹ :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).symm

/-- `ClosureSphere` is connected. -/
instance connectedSpace_closureSphere_OWF : ConnectedSpace ClosureSphere.{0} :=
  Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous

/-- **A submersion stays a submersion after a linear isomorphism of the target.** -/
theorem surjective_mfderiv_clm_comp_OWF {EM HM M F G : Type*} [NormedAddCommGroup EM]
    [NormedSpace ℝ EM] [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM} [TopologicalSpace M]
    [ChartedSpace HM M] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (L : F ≃L[ℝ] G) {f : M → F} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ, F) f x)
    (hs : Surjective (mfderiv I 𝓘(ℝ, F) f x)) :
    Surjective (mfderiv I 𝓘(ℝ, G) (fun y => L (f y)) x) := by
  intro v
  obtain ⟨w, hw⟩ := hs (L.symm v)
  refine ⟨w, (mvfderiv_clm_comp_BDFB (L : F →L[ℝ] G) hf w).trans ?_⟩
  change L (mfderiv I 𝓘(ℝ, F) f x w) = v
  rw [hw]
  exact L.apply_symm_apply (v : G)

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- The `ℝ¹`-valued slim chart coordinate `κ¹_j = e ∘ κ_j`. -/
def slimKappa1_OWF (j : S.SlimIdx_BAUGD) :
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ¹ :=
  (realToFin1_OWF : ℝ →L[ℝ] ℝ¹).comp (S.slimKappa_BBP j)

theorem slimKappa1_apply_OWF (j : S.SlimIdx_BAUGD)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.slimKappa1_OWF j y = realToFin1_OWF (S.slimKappa_BBP j y) :=
  rfl

end BoundarySupplyCore

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **Local one-sheet, slim stage** (`κ¹_j` on `Z₂` near `f₂⁰(q)`). -/
theorem slim_localInverse_OWF
    (O : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2)
      ((actualSlotsV2_BAUGD S).stageCloud 2) ((actualSlotsV2_BAUGD S).stageCloudEnlarged 2)
      (DP.stageRadius 2 (Sg 2)) (DP.stagePlane 2))
    (hO : C.toChain.slot 2 = .active O) (j : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ)) :
    ∃ (V : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) (δ : ℝ)
      (ζ : ℝ¹ → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
      IsOpen V ∧ C.toChain.nativeStageMap_BIFc 2 q.val ∈ V ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ ζ (ball (S.slimKappa1_OWF j (C.toChain.nativeStageMap_BIFc 2 q.val)) δ) ∧
      (∀ b ∈ ball (S.slimKappa1_OWF j (C.toChain.nativeStageMap_BIFc 2 q.val)) δ,
        ζ b ∈ O.Z ∩ V ∧ S.slimKappa1_OWF j (ζ b) = b) ∧
      (∀ w ∈ O.Z ∩ V,
        S.slimKappa1_OWF j w ∈ ball (S.slimKappa1_OWF j (C.toChain.nativeStageMap_BIFc 2 q.val))
          δ ∧ ζ (S.slimKappa1_OWF j w) = w) := by
  have hnd : MDifferentiableAt W.model 𝓘(ℝ, ℝ)
      (fun p => S.slimKappa_BBP j (C.toChain.nativeStageMap_BIFc 2 p)) q.val :=
    ((S.slimKappa_BBP j).comp ((actualSlotsV2_BAUGD S).stageProj 2)).differentiableAt
      |>.comp_mdifferentiableAt (((C.stage_smooth_BAUGD 3) q.val).mdifferentiableAt (by simp))
  exact C.native_localInverse_OWF 2 (S.slimKappa1_OWF j)
    (fun y => congrArg realToFin1_OWF (slimKappa_stageProj_BBP j y)) (by simp [gafStageDim])
    O hO (S.slim_plateau_mem_nhds_BBP j hq hη)
    (fun q' hq' => C.slim_plateau_cutoff_BBP j hq'.1 hq'.2)
    (surjective_mfderiv_clm_comp_OWF realToFin1_OWF hnd (C.stage_submersion_slim_BBP j hq hη))

include C in
/-- A final slim value in the ratio piece of chart `j` comes from a point of `Y_j`. -/
theorem slim_mem_Y_of_piece_OWF (j : S.SlimIdx_BAUGD) {p : W.Carrier}
    (hp : C.toChain.stageMap 2 p ∈
      ratioPiece_BBP (S.slimKappa_BBP j) (S.slimMarker_BAUGD j) (S.rho j.1) (10 ^ 5 * Δ)) :
    ∃ q : W.pieceInterior ⊤, q.val = p ∧ q ∈ S.slimY_OWF j := by
  obtain ⟨-, hΔ, -⟩ := C.std
  obtain ⟨q, hq, hd, hη⟩ := C.slim_final_loc_BBP j hp
  exact ⟨q, hq, hd, by nlinarith⟩

include C in
/-- A final slim value in the ratio piece of chart `j` has `|κ_j y| < 4·10⁵Δ`. -/
theorem slim_norm_kappa_lt_OWF (j : S.SlimIdx_BAUGD) {p : W.Carrier}
    (hp : C.toChain.stageMap 2 p ∈
      ratioPiece_BBP (S.slimKappa_BBP j) (S.slimMarker_BAUGD j) (S.rho j.1) (10 ^ 5 * Δ)) :
    |S.slimKappa_BBP j (C.toChain.stageMap 2 p)| < 4 * (10 ^ 5 * Δ) := by
  obtain ⟨-, hΔ, -⟩ := C.std
  have hm : S.slimMarker_BAUGD j ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.E p)) =
      S.slimMarker_BAUGD j (C.toChain.E p) :=
    marker_stageProj_own_BBP (Sum.inr (Sum.inl j)) (C.toChain.E p)
  have hk : S.slimKappa_BBP j ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.E p)) =
      S.slimKappa_BBP j (C.toChain.E p) := slimKappa_stageProj_BBP j _
  have hy : C.toChain.E p ∈ ratioPiece_BBP (S.slimKappa_BBP j) (S.slimMarker_BAUGD j)
      (S.rho j.1) (10 ^ 5 * Δ) := by
    obtain ⟨h1, h2⟩ := hp
    change 9 / 10 * S.rho j.1 < S.slimMarker_BAUGD j
      ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.E p)) at h1
    change S.rho j.1 * ‖S.slimKappa_BBP j ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.E p))‖ <
      39 / 10 * (10 ^ 5 * Δ) * S.slimMarker_BAUGD j
        ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.E p)) at h2
    rw [hm] at h1 h2
    rw [hk] at h2
    exact ⟨h1, h2⟩
  have hζ : 0 < S.markerCutoffW_BAUGD (Sum.inr (Sum.inl j)) p :=
    C.final_marker_pos_BBP (Sum.inr (Sum.inl j)) hy.1
  have herr := C.final_err_le_BBP (Sum.inr (Sum.inl j)) hζ
  have hv1 : ‖(S.slimMarker_BAUGD j :
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ)‖ ≤ 1 :=
    norm_blockMarkerCLM_le _
  have h := norm_kappa_lt_four_of_piece_OWF (S.rho_pos j.1) (by positivity) hv1 herr
    (S.slimBlock_boundaryOriginalMap_BAUGP2 j p).2 (S.slimCutoffW_mem_Icc_BAUGP2 j p).2 hy
  change |S.slimKappa_BBP j ((actualSlotsV2_BAUGD S).stageProj 2 (C.toChain.E p))| < _
  rw [hk, ← Real.norm_eq_abs]
  exact h

/-- **Each whole adjusted slim level is preconnected** (the image of a standard surface). -/
theorem slim_level_isPreconnected_OWF (hc : c 2 < 1 / 1000) (hK : 5 ≤ K) (j : S.SlimIdx_BAUGD)
    {a : ℝ} (ha : |a| < 4 * (10 ^ 5 * Δ)) :
    IsPreconnected {q | q ∈ S.slimY_OWF j ∧
      S.slimKappa_BBP j (C.toChain.stageMap 2 q.val) = a} := by
  rcases C.slim_level_standard_OWF hc hK j with h | h
  · obtain ⟨ψ, hψ, hr⟩ := h a ha
    rw [← hr]
    exact isPreconnected_range hψ.contMDiff.continuous
  · obtain ⟨ψ, hψ, hr⟩ := h a ha
    rw [← hr]
    exact isPreconnected_range hψ.contMDiff.continuous

/-- **The native slim map is constant on a whole adjusted level**. -/
theorem slim_native_const_OWF (hc : c 2 < 1 / 1000) (hK : 5 ≤ K)
    (O : Cfs15StageOutput (gafStageDim 2) Kj (Ξ 2) (cw 2)
      ((actualSlotsV2_BAUGD S).stageCloud 2) ((actualSlotsV2_BAUGD S).stageCloudEnlarged 2)
      (DP.stageRadius 2 (Sg 2)) (DP.stagePlane 2))
    (hO : C.toChain.slot 2 = .active O) (j : S.SlimIdx_BAUGD) {a : ℝ}
    (ha : |a| < 4 * (10 ^ 5 * Δ)) :
    ∀ x ∈ {q | q ∈ S.slimY_OWF j ∧ S.slimKappa_BBP j (C.toChain.stageMap 2 q.val) = a},
      ∀ x' ∈ {q | q ∈ S.slimY_OWF j ∧ S.slimKappa_BBP j (C.toChain.stageMap 2 q.val) = a},
        C.toChain.nativeStageMap_BIFc 2 x.val = C.toChain.nativeStageMap_BIFc 2 x'.val := by
  obtain ⟨-, hΔ, -⟩ := C.std
  have hL := C.slim_level_isPreconnected_OWF hc hK j ha
  have hh : ContinuousOn (fun q : W.pieceInterior ⊤ => C.toChain.nativeStageMap_BIFc 2 q.val)
      {q | q ∈ S.slimY_OWF j ∧ S.slimKappa_BBP j (C.toChain.stageMap 2 q.val) = a} :=
    ((C.continuous_native_OWF 2).comp continuous_subtype_val).continuousOn
  have h56 : ∀ y ∈ S.slimY_OWF j, |S.slimEta_BIF j.1 y| < 6 * (10 ^ 5 * Δ) := fun y hy => by
    have := hy.2
    nlinarith
  refine eqOn_of_isPreconnected_of_locInjOn_OWF hL hh (Zs := O.Z) ?_ (S.slimKappa1_OWF j)
    (c := realToFin1_OWF a) ?_ ?_
  · rintro q ⟨hq, -⟩
    exact C.toChain.native_scope_V2_BAUGD 2 O hO q.val
      (C.slim_plateau_cutoff_BBP j hq.1 (h56 q hq))
  · rintro q ⟨-, hqa⟩
    exact congrArg realToFin1_OWF hqa
  · rintro q ⟨hq, -⟩
    obtain ⟨V, δ, ζ, hV, hmem, -, -, -, hl⟩ := C.slim_localInverse_OWF O hO j hq.1 (h56 q hq)
    exact ⟨V, hV, hmem, fun w hw w' hw' heq =>
      (hl w hw).2.symm.trans ((congrArg ζ heq).trans (hl w' hw').2)⟩

/-- **The whole slim fibre is the whole adjusted level**. -/
theorem slim_fibre_eq_level_OWF (hc : c 2 < 1 / 1000) (hK : 5 ≤ K) (j : S.SlimIdx_BAUGD)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.baseSet_BBP 2)
    (hyj : y ∈ ratioPiece_BBP (S.slimKappa_BBP j) (S.slimMarker_BAUGD j) (S.rho j.1)
      (10 ^ 5 * Δ)) :
    {x : W.pieceInterior ⊤ | x.val ∈ C.baseSource_BBP 2 ∧ C.toChain.stageMap 2 x.val = y} =
      {x | x ∈ S.slimY_OWF j ∧
        S.slimKappa_BBP j (C.toChain.stageMap 2 x.val) = S.slimKappa_BBP j y} := by
  obtain ⟨p₀, hp₀, hfp₀⟩ := hy
  obtain ⟨O, hO⟩ := C.exists_active_of_source_OWF 2 hp₀
  have hpiece₀ : C.toChain.stageMap 2 p₀ ∈
      ratioPiece_BBP (S.slimKappa_BBP j) (S.slimMarker_BAUGD j) (S.rho j.1) (10 ^ 5 * Δ) := by
    rw [hfp₀]; exact hyj
  have ha : |S.slimKappa_BBP j y| < 4 * (10 ^ 5 * Δ) := by
    have h := C.slim_norm_kappa_lt_OWF j hpiece₀
    rwa [hfp₀] at h
  obtain ⟨q₀, hq₀, hq₀Y⟩ := C.slim_mem_Y_of_piece_OWF j hpiece₀
  have hq₀L : q₀ ∈ {x : W.pieceInterior ⊤ | x ∈ S.slimY_OWF j ∧
      S.slimKappa_BBP j (C.toChain.stageMap 2 x.val) = S.slimKappa_BBP j y} :=
    ⟨hq₀Y, by rw [hq₀, hfp₀]⟩
  ext x
  constructor
  · rintro ⟨-, hxy⟩
    have hpiece : C.toChain.stageMap 2 x.val ∈
        ratioPiece_BBP (S.slimKappa_BBP j) (S.slimMarker_BAUGD j) (S.rho j.1) (10 ^ 5 * Δ) := by
      rw [hxy]; exact hyj
    obtain ⟨q, hq, hqY⟩ := C.slim_mem_Y_of_piece_OWF j hpiece
    have hqx : q = x := Subtype.ext hq
    rw [← hqx]
    exact ⟨hqY, by rw [hq, hxy]⟩
  · intro hx
    have hconst := C.slim_native_const_OWF hc hK O hO j ha x hx q₀ hq₀L
    have hxy : C.toChain.stageMap 2 x.val = y := by
      rw [C.toChain.final_factor_V2_BAUGD 2 x.val, hconst,
        ← C.toChain.final_factor_V2_BAUGD 2 q₀.val, hq₀, hfp₀]
    refine ⟨⟨?_, fun h => absurd h (by decide)⟩, hxy⟩
    rw [hxy, ← hfp₀]
    exact hp₀.1

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
