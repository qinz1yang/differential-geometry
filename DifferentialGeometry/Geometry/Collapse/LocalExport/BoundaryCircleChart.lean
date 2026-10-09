import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleFibreLevel
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProductChartLocal
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLocalRecord
import DifferentialGeometry.Topology.Manifold.SubmersionOpenMap

/-!
# O-WF G2f: the circle-stage whole-fibre charts of the boundary chain

**`BoundaryGaf02ChainE.circle_chart_OWF`**: at every point `y` of the circle base
`B₀ = C.baseSet_BBP 0`, the final stage map `f₀ = C.toChain.stageMap 0` on the source
`X₀ = C.baseSource_BBP 0` has a smooth local product chart with fibre `S¹`
(`SmoothProductChartAt_BIFc W.model (𝓡 1) (F := Circle) 2`), the `circle_chart` field of the
whole-fibre layer. Route (local, no global CGP07 record):

1. a chart `j` of the ratio piece of `y`, a source point `q₀` over `y` in `Y_j`, the active slot
   `O` and the local inverse `ζ` of `κ_j` on `Z₀` at `f₀⁰(q₀)` (`circle_localInverse_OWF`);
2. the open-mapping property of `κ_j ∘ f₀ ∘ val` at `q₀` (`map_nhds_eq_of_mfderiv_surjective_at`
   with the final submersion `final_submersion_circle_BBP` through `val`,
   `surjective_mfderiv_comp_val_OWF`);
3. the local record `σ₀ = Θ₀ ∘ ζ` (`exists_localRecord_OWF`, with no merging
   `circle_later_isEmbedding_OWF`);
4. the chart from the local record and the connected whole fibre
   (`smoothProductChartAt_circle_of_localRecord_OWF`, `isConnected_circle_fibre_OWF`).

Register premises: `c₂ < 1/1000`, `β₂ ≤ 10⁻⁷`, `γ ≤ 1/2`, `γ + β₂ < 1/10`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

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

omit [ConnectedSpace W.Carrier] in
/-- **A submersion of `W` at an interior point stays one on `W°`** (through `val`). -/
theorem surjective_mfderiv_comp_val_OWF {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : W.Carrier → F} (q : W.pieceInterior ⊤) (hf : MDifferentiableAt W.model 𝓘(ℝ, F) f q.val)
    (hs : Surjective (mfderiv W.model 𝓘(ℝ, F) f q.val)) :
    Surjective (mfderiv (𝓡 3) 𝓘(ℝ, F) (fun x : W.pieceInterior ⊤ => f x.val) q) := by
  intro v
  obtain ⟨w, hw⟩ := hs v
  obtain ⟨u, rfl⟩ := exists_mfderiv_val_eq_BAUGC q w
  exact ⟨u, (mvfderiv_comp_val_BCG7 W f q hf u).trans hw⟩

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The final circle submersion on `W°`** at every point whose value lies in the ratio piece of
chart `j`. -/
theorem circle_submersion_interior_OWF (hβ : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2)
    (j : S.CircleIdx_BAUGD) (x : W.pieceInterior ⊤)
    (hx : C.toChain.stageMap 0 x.val ∈
      ratioPiece_BBP (S.circleKappa_BBP j) (S.circleMarker_BAUGD j) (S.rho j.1) 1) :
    Surjective (mfderiv (𝓡 3) 𝓘(ℝ, ℝ²)
      (fun x : W.pieceInterior ⊤ => S.circleKappa_BBP j (C.toChain.stageMap 0 x.val)) x) := by
  obtain ⟨q, hq, hd, hη⟩ := C.circle_final_loc_BBP j hx
  have hqx : q = x := Subtype.ext hq
  subst hqx
  have hfd : MDifferentiableAt W.model 𝓘(ℝ, ℝ²)
      (fun p => S.circleKappa_BBP j (C.toChain.stageMap 0 p)) q.val :=
    ((S.circleKappa_BBP j).comp ((actualSlotsV2_BAUGD S).stageProj 0)).differentiableAt
      |>.comp_mdifferentiableAt (((C.stage_smooth_BAUGD 3) q.val).mdifferentiableAt (by simp))
  exact surjective_mfderiv_comp_val_OWF q hfd
    (C.final_submersion_circle_BBP hβ hγ j hd (by linarith))

/-- The circle source is open in `W°` (as a preimage under `val`). -/
theorem isOpen_circle_source_interior_OWF :
    IsOpen ((Subtype.val : W.pieceInterior ⊤ → W.Carrier) ⁻¹' C.baseSource_BBP 0) := by
  have h : IsOpen (C.baseSource_BBP 0) := by
    rw [C.baseSource_zero_eq_BBP]
    exact (S.isOpen_ratioSet_BBP 0).preimage (C.continuous_stageMap_V2_BAUGD 0)
  exact h.preimage continuous_subtype_val

/-- **The circle-stage whole-fibre chart at every base point** (see the module docstring). -/
theorem circle_chart_OWF (hc : c 2 < 1 / 1000) (hβ : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2)
    (hd : γ + β 2 < 1 / 10) {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.baseSet_BBP 0) :
    SmoothProductChartAt_BIFc W.model (𝓡 1) (F := Circle) 2 (C.toChain.stageMap 0)
      (C.baseSource_BBP 0) (C.baseSet_BBP 0) y := by
  have : LocallyCompactSpace (W.pieceInterior ⊤) :=
    Manifold.locallyCompact_of_finiteDimensional (𝓡 3)
  obtain ⟨p₀, hp₀, hfp₀⟩ := hy
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp₀.1
  have hyj : y ∈ ratioPiece_BBP (S.circleKappa_BBP j) (S.circleMarker_BAUGD j) (S.rho j.1) 1 :=
    hfp₀ ▸ hj
  obtain ⟨q₀, hq₀, hq₀Y⟩ := C.circle_mem_Y_of_piece_OWF j hj
  have hq₀X : q₀.val ∈ C.baseSource_BBP 0 := hq₀ ▸ hp₀
  obtain ⟨O, hO⟩ := C.exists_active_of_source_OWF 0 hp₀
  obtain ⟨V, δ, ζ, hV, hmem, hδ, hζs, -, hl⟩ :=
    C.circle_localInverse_OWF hβ hγ O hO j hq₀Y.1 (by linarith [hq₀Y.2])
  -- the open mapping at `q₀`
  have hfun : (fun x : W.pieceInterior ⊤ =>
      S.circleKappa_BBP j (C.toChain.nativeStageMap_BIFc 0 x.val)) =
      fun x => S.circleKappa_BBP j (C.toChain.stageMap 0 x.val) :=
    funext fun x => (congrFun (C.circle_kappa_final_eq_BBP j) x.val).symm
  have hq₀piece : C.toChain.stageMap 0 q₀.val ∈
      ratioPiece_BBP (S.circleKappa_BBP j) (S.circleMarker_BAUGD j) (S.rho j.1) 1 := by
    rw [hq₀]; exact hj
  have hmap₀ := DifferentialGeometry.Topology.map_nhds_eq_of_mfderiv_surjective_at
    (((C.circle_adjusted_contMDiff_OWF j) q₀).of_le (by simp))
    (C.circle_submersion_interior_OWF hβ hγ j q₀ hq₀piece)
  have hmap : map (fun x : W.pieceInterior ⊤ =>
      S.circleKappa_BBP j (C.toChain.nativeStageMap_BIFc 0 x.val)) (𝓝 q₀) =
      𝓝 (S.circleKappa_BBP j (C.toChain.nativeStageMap_BIFc 0 q₀.val)) := by
    rw [hfun, (congrFun (C.circle_kappa_final_eq_BBP j) q₀.val).symm]
    exact hmap₀
  -- the local record
  obtain ⟨σ₀, Mk, Dset, hMk, hDo, hyMk, -, hσs, hσb, hσc⟩ :=
    exists_localRecord_OWF (N := W.pieceInterior ⊤) continuous_subtype_val
      C.isOpen_circle_source_interior_OWF (C.continuous_native_OWF 0) (Zs := O.Z)
      (fun p hp => C.toChain.native_scope_V2_BAUGD 0 O hO p (C.baseSource_plateau_BBP 0 hp))
      (S.circleKappa_BBP j) (C.circleKappa_laterV2_BBP j)
      (fun p _ => C.toChain.later_contDiffAt_V2_BAUGD 0 p)
      (C.circle_later_isEmbedding_OWF hc hβ hγ hd) hq₀X hV hmem hδ hζs
      (fun w hw => (hl w hw).2) hmap
  have hB : C.baseSet_BBP 0 = C.toChain.laterV2_BAUGD 0 ''
      (C.toChain.nativeStageMap_BIFc 0 '' C.baseSource_BBP 0) := C.baseSet_eq_later_native_BBP 0
  have hy0 : C.toChain.laterV2_BAUGD 0 (C.toChain.nativeStageMap_BIFc 0 q₀.val) = y := by
    rw [← C.toChain.final_factor_V2_BAUGD 0 q₀.val, hq₀, hfp₀]
  rw [hy0] at hyMk
  have hy : y ∈ C.baseSet_BBP 0 := ⟨p₀, hp₀, hfp₀⟩
  refine smoothProductChartAt_circle_of_localRecord_OWF (by norm_num) (by simp)
    Subtype.val (isSmoothEmbedding_val_interior_BAUGD W) (isInteriorPoint_val_interior_BAUGD W)
    (C.toChain.stageMap 0) (C.baseSource_BBP 0) (C.baseSet_BBP 0) (S.circleKappa_BBP j) σ₀
    (C.baseSet_BBP 0) Mk univ
    (ratioPiece_BBP (S.circleKappa_BBP j) (S.circleMarker_BAUGD j) (S.rho j.1) 1) hDo
    (inter_univ _).symm isOpen_univ hMk (isOpen_ratioPiece_BBP _ _ _ _) hσs
    (fun b hb => by rw [hB]; exact hσb b hb) (fun y' hy' => hσc y' (by rw [← hB]; exact hy'))
    (fun p hp => ?_) rfl C.isOpen_circle_source_interior_OWF
    ((C.continuous_stageMap_V2_BAUGD 0).comp continuous_subtype_val)
    (C.circle_adjusted_contMDiff_OWF j)
    (fun x _ _ hxP => C.circle_submersion_interior_OWF hβ hγ j x hxP)
    (C.proper_of_source_eq_V2_BAUGD C.baseSource_BBP C.baseSet_BBP
      (C.baseSource_eq_preimage_BBP (by decide)) C.baseSource_one_eq_preimage_BBP
      (C.baseSource_eq_preimage_BBP (by decide)) 0) hy hyMk hyj
    (C.isConnected_circle_fibre_OWF hc hβ hγ hd j hy hyj)
  obtain ⟨j', q, hq, -, -⟩ := C.circle_source_loc_BBP hp
  exact ⟨q, hq⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
