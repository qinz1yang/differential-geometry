import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimFibreLevel
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleChart
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesEdgeParentData

/-!
# O-WF G3f: the slim-stage whole-fibre charts of the boundary chain (`S²` OR `T²`)

**`BoundaryGaf02ChainE.slim_chart_OWF`**: at every point `y` of the slim base
`B₂ = C.baseSet_BBP 2`, the final stage map `f₂ = C.toChain.stageMap 2` on `X₂ = C.baseSource_BBP 2`
has a smooth local product chart with fibre the standard `ClosureSphere` OR the standard `Torus`
(`SmoothProductChartAt_BIFc W.model (𝓡 2) (F := ClosureSphere) 1 … ∨ … (𝓡 1).prod (𝓡 1) (F :=
Circle × Circle) 1 …`), the `slim_chart` field of the whole-fibre layer. Route as for the circle
(`circle_chart_OWF`): local inverse of `κ¹_j` on `Z₂`, open mapping, local record with `Θ₂ = id`
(`later_isEmbedding_two_BBP`), the standard embedding of the whole fibre = whole adjusted level
(`slim_level_standard_OWF`, `slim_fibre_eq_level_OWF`), and
`smoothProductChartAt_of_localRecord_OWF`.

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

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- The `ℝ¹`-valued adjusted slim coordinate is smooth on `W°`. -/
theorem slim_adjusted1_contMDiff_OWF (j : S.SlimIdx_BAUGD) :
    ContMDiff (𝓡 3) (𝓡 1) ∞
      (fun q : W.pieceInterior ⊤ => S.slimKappa1_OWF j (C.toChain.stageMap 2 q.val)) :=
  ((S.slimKappa1_OWF j).comp ((actualSlotsV2_BAUGD S).stageProj 2)).contDiff.comp_contMDiff
    ((C.stage_smooth_BAUGD 3).comp (isLocalDiffeomorph_pieceInterior_val W ⊤).contMDiff)

/-- **The final slim submersion on `W°`** (`ℝ¹`-valued), at every point whose value lies in the
ratio piece of chart `j`. -/
theorem slim_submersion_interior_OWF (j : S.SlimIdx_BAUGD) (x : W.pieceInterior ⊤)
    (hx : C.toChain.stageMap 2 x.val ∈
      ratioPiece_BBP (S.slimKappa_BBP j) (S.slimMarker_BAUGD j) (S.rho j.1) (10 ^ 5 * Δ)) :
    Surjective (mfderiv (𝓡 3) (𝓡 1)
      (fun x : W.pieceInterior ⊤ => S.slimKappa1_OWF j (C.toChain.stageMap 2 x.val)) x) := by
  obtain ⟨-, hΔ, -⟩ := C.std
  obtain ⟨q, hq, hd, hη⟩ := C.slim_final_loc_BBP j hx
  have hqx : q = x := Subtype.ext hq
  subst hqx
  have hfd : MDifferentiableAt W.model 𝓘(ℝ, ℝ)
      (fun p => S.slimKappa_BBP j (C.toChain.stageMap 2 p)) q.val :=
    ((S.slimKappa_BBP j).comp ((actualSlotsV2_BAUGD S).stageProj 2)).differentiableAt
      |>.comp_mdifferentiableAt (((C.stage_smooth_BAUGD 3) q.val).mdifferentiableAt (by simp))
  have h1 := surjective_mfderiv_clm_comp_OWF realToFin1_OWF hfd
    (C.stage_submersion_slim_BBP j hd (by nlinarith))
  have hfd1 : MDifferentiableAt W.model 𝓘(ℝ, ℝ¹)
      (fun p => S.slimKappa1_OWF j (C.toChain.stageMap 2 p)) q.val :=
    ((S.slimKappa1_OWF j).comp ((actualSlotsV2_BAUGD S).stageProj 2)).differentiableAt
      |>.comp_mdifferentiableAt (((C.stage_smooth_BAUGD 3) q.val).mdifferentiableAt (by simp))
  exact surjective_mfderiv_comp_val_OWF q hfd1 h1

/-- The slim source is open in `W°` (as a preimage under `val`). -/
theorem isOpen_slim_source_interior_OWF :
    IsOpen ((Subtype.val : W.pieceInterior ⊤ → W.Carrier) ⁻¹' C.baseSource_BBP 2) := by
  have h : IsOpen (C.baseSource_BBP 2) := by
    rw [C.baseSource_two_eq_BBP]
    exact (S.isOpen_ratioSet_BBP 2).preimage (C.continuous_stageMap_V2_BAUGD 2)
  exact h.preimage continuous_subtype_val

/-- **The slim-stage chart from a standard embedding of the whole adjusted level** (generic in
the fibre model `P`; the route of the module docstring). -/
theorem slim_chart_of_embedding_OWF (hc : c 2 < 1 / 1000) (hK : 5 ≤ K)
    {EF HF : Type} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [FiniteDimensional ℝ EF]
    [TopologicalSpace HF] (IF : ModelWithCorners ℝ EF HF) [IF.Boundaryless]
    {P : Type} [TopologicalSpace P] [ChartedSpace HF P] [IsManifold IF ∞ P]
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.baseSet_BBP 2) (j : S.SlimIdx_BAUGD)
    (hyj : y ∈ ratioPiece_BBP (S.slimKappa_BBP j) (S.slimMarker_BAUGD j) (S.rho j.1)
      (10 ^ 5 * Δ))
    (ψ : P → W.pieceInterior ⊤) (hψ : IsSmoothEmbedding IF (𝓡 3) ∞ ψ)
    (hψr : range ψ = {q | q ∈ S.slimY_OWF j ∧
      S.slimKappa_BBP j (C.toChain.stageMap 2 q.val) = S.slimKappa_BBP j y}) :
    SmoothProductChartAt_BIFc W.model IF (F := P) 1 (C.toChain.stageMap 2)
      (C.baseSource_BBP 2) (C.baseSet_BBP 2) y := by
  have : LocallyCompactSpace (W.pieceInterior ⊤) :=
    Manifold.locallyCompact_of_finiteDimensional (𝓡 3)
  obtain ⟨-, hΔ, -⟩ := C.std
  have hy' := hy
  obtain ⟨p₀, hp₀, hfp₀⟩ := hy'
  have hj : C.toChain.stageMap 2 p₀ ∈
      ratioPiece_BBP (S.slimKappa_BBP j) (S.slimMarker_BAUGD j) (S.rho j.1) (10 ^ 5 * Δ) := by
    rw [hfp₀]; exact hyj
  obtain ⟨q₀, hq₀, hq₀Y⟩ := C.slim_mem_Y_of_piece_OWF j hj
  have hq₀X : q₀.val ∈ C.baseSource_BBP 2 := hq₀ ▸ hp₀
  obtain ⟨O, hO⟩ := C.exists_active_of_source_OWF 2 hp₀
  have h56 : |S.slimEta_BIF j.1 q₀| < 6 * (10 ^ 5 * Δ) := by
    have := hq₀Y.2
    nlinarith
  obtain ⟨V, δ, ζ, hV, hmem, hδ, hζs, -, hl⟩ := C.slim_localInverse_OWF O hO j hq₀Y.1 h56
  have hq₀piece : C.toChain.stageMap 2 q₀.val ∈
      ratioPiece_BBP (S.slimKappa_BBP j) (S.slimMarker_BAUGD j) (S.rho j.1) (10 ^ 5 * Δ) := by
    rw [hq₀]; exact hj
  have hmap := DifferentialGeometry.Topology.map_nhds_eq_of_mfderiv_surjective_at
    (((C.slim_adjusted1_contMDiff_OWF j) q₀).of_le (by simp))
    (C.slim_submersion_interior_OWF j q₀ hq₀piece)
  obtain ⟨σ₀, Mk, Dset, hMk, hDo, hyMk, -, hσs, hσb, hσc⟩ :=
    exists_localRecord_OWF (N := W.pieceInterior ⊤) continuous_subtype_val
      C.isOpen_slim_source_interior_OWF (C.continuous_native_OWF 2) (Zs := O.Z)
      (fun p hp => C.toChain.native_scope_V2_BAUGD 2 O hO p (C.baseSource_plateau_BBP 2 hp))
      (S.slimKappa1_OWF j) (fun _ => rfl)
      (fun p _ => C.toChain.later_contDiffAt_V2_BAUGD 2 p)
      C.later_isEmbedding_two_BBP hq₀X hV hmem hδ hζs (fun w hw => (hl w hw).2) hmap
  have hB : C.baseSet_BBP 2 = (fun x => x) ''
      (C.toChain.nativeStageMap_BIFc 2 '' C.baseSource_BBP 2) := C.baseSet_eq_later_native_BBP 2
  have hy0 : C.toChain.nativeStageMap_BIFc 2 q₀.val = y := by
    change C.toChain.stageMap 2 q₀.val = y
    rw [hq₀, hfp₀]
  have hyMk' : y ∈ Mk := hy0 ▸ hyMk
  have hfib := C.slim_fibre_eq_level_OWF hc hK j hy hyj
  have hXι : C.baseSource_BBP 2 ⊆ range (Subtype.val : W.pieceInterior ⊤ → W.Carrier) := by
    intro p hp
    obtain ⟨j', q, hq, -, -⟩ := C.slim_source_loc_BBP hp
    exact ⟨q, hq⟩
  have hprop := C.proper_of_source_eq_V2_BAUGD C.baseSource_BBP C.baseSet_BBP
    (C.baseSource_eq_preimage_BBP (by decide)) C.baseSource_one_eq_preimage_BBP
    (C.baseSource_eq_preimage_BBP (by decide)) 2
  exact smoothProductChartAt_of_localRecord_OWF (by norm_num) (by simp) IF
    Subtype.val (isSmoothEmbedding_val_interior_BAUGD W) (isInteriorPoint_val_interior_BAUGD W)
    (C.toChain.stageMap 2) (C.baseSource_BBP 2) (C.baseSet_BBP 2) (S.slimKappa1_OWF j) σ₀
    (C.baseSet_BBP 2) Mk univ
    (ratioPiece_BBP (S.slimKappa_BBP j) (S.slimMarker_BAUGD j) (S.rho j.1) (10 ^ 5 * Δ))
    hDo (inter_univ _).symm isOpen_univ hMk (isOpen_ratioPiece_BBP _ _ _ _) hσs
    (fun b hb => hB ▸ hσb b hb) (fun y' hy' => hσc y' (hB ▸ hy'))
    hXι rfl C.isOpen_slim_source_interior_OWF
    ((C.continuous_stageMap_V2_BAUGD 2).comp continuous_subtype_val)
    (C.slim_adjusted1_contMDiff_OWF j)
    (fun x _ _ hxP => C.slim_submersion_interior_OWF j x hxP) hprop hy hyMk' hyj ψ hψ
    (hψr.trans hfib.symm)

/-- **The slim-stage whole-fibre chart at every base point** (see the module docstring). -/
theorem slim_chart_OWF (hc : c 2 < 1 / 1000) (hK : 5 ≤ K)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.baseSet_BBP 2) :
    SmoothProductChartAt_BIFc W.model (𝓡 2) (F := ClosureSphere.{0}) 1 (C.toChain.stageMap 2)
        (C.baseSource_BBP 2) (C.baseSet_BBP 2) y ∨
      SmoothProductChartAt_BIFc W.model ((𝓡 1).prod (𝓡 1)) (F := Circle × Circle) 1
        (C.toChain.stageMap 2) (C.baseSource_BBP 2) (C.baseSet_BBP 2) y := by
  obtain ⟨-, hΔ, -⟩ := C.std
  have hy' := hy
  obtain ⟨p₀, hp₀, hfp₀⟩ := hy'
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp₀.1
  have hyj : y ∈ ratioPiece_BBP (S.slimKappa_BBP j) (S.slimMarker_BAUGD j) (S.rho j.1)
      (10 ^ 5 * Δ) := hfp₀ ▸ hj
  have ha : |S.slimKappa_BBP j y| < 4 * (10 ^ 5 * Δ) := by
    have h := C.slim_norm_kappa_lt_OWF j hj
    rwa [hfp₀] at h
  rcases C.slim_level_standard_OWF hc hK j with h | h
  · obtain ⟨ψ, hψ, hψr⟩ := h _ ha
    exact Or.inl (C.slim_chart_of_embedding_OWF hc hK (𝓡 2) hy j hyj ψ hψ hψr)
  · obtain ⟨ψ, hψ, hψr⟩ := h _ ha
    exact Or.inr (C.slim_chart_of_embedding_OWF hc hK torusModel hy j hyj ψ hψ hψr)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
