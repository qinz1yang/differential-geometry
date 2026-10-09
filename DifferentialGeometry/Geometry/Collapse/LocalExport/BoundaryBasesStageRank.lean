import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesFinalSubmersion
import DifferentialGeometry.Geometry.Fibration.ActualStageChainSubmersionInputs
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedTransferNormal

/-!
# A4 / G11 (lane S-BASES-PORT), group G2 (part 2): `rank_eq` on the stage plateaus

The `rank_eq` field of `BoundaryGaf02BasesCore_BIFc` (`rank (Df_st) = k_st = (2, 1, 1)`) at every
point of the original threshold-6 plateau of every chart, for the FINAL stage maps
`f_st = π_st ∘ E` on `C : BoundaryGaf02ChainE DP …`.

* `≥ k_st`: `finrank_le_finrank_range_of_comp_surjective_BBP` (a chart coordinate `κ_j ∘ f_st`
  that is a submersion onto `F` forces `dim F ≤ rank Df_st`), `stage_rank_ge_BBP`, fed by the FINAL
  submersions of `LE/BoundaryBasesFinalSubmersion.lean`;
* `≤ k_st`: `f_st = Θ_st ∘ f_st⁰` (`mvfderiv_stageMap_BBP`), near a plateau point the native map is
  `π_st a_st (π_st g_st)` (`native_mvfderiv_full_BBP`), and `range Da_st(π g) ⊆ T` with
  `dim T = dim L_x = k_st` (`ambient_range_le_BBP` from
  `Cfs15StageOutput.ambient_tangent_coframe_BAS` with the coframe `id`; `slot_range_le_BBP`
  handles inactive slots through the empty cloud): `stage_range_le_map_BBP`, `stage_rank_le_BBP`;
* **`stage_rank_eq_circle_BBP`**, **`stage_rank_eq_edge_BBP`**, **`stage_rank_eq_slim_BBP`**
  (register premises as for the submersions).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential
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
/-- **Rank from a surjective chart coordinate**: if `κ ∘ L` is onto `E` then `dim E ≤ rank L`. -/
theorem finrank_le_finrank_range_of_comp_surjective_BBP {V H E : Type*} [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V] [AddCommGroup H] [Module ℝ H] [AddCommGroup E]
    [Module ℝ E] (L : V →ₗ[ℝ] H) (κ : H →ₗ[ℝ] E) (hs : Function.Surjective (κ ∘ₗ L)) :
    Module.finrank ℝ E ≤ Module.finrank ℝ (LinearMap.range L) := by
  have h1 : LinearMap.range (κ ∘ₗ L) = ⊤ := LinearMap.range_eq_top.mpr hs
  have h2 : Module.finrank ℝ E = Module.finrank ℝ (LinearMap.range (κ ∘ₗ L)) := by
    rw [h1, finrank_top]
  rw [h2, LinearMap.range_comp]
  exact Submodule.finrank_map_le κ (LinearMap.range L)


namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- `π_st ∘ π_st = π_st`. -/
theorem stageProj_idem_BBP (st : Fin 3)
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    (actualSlotsV2_BAUGD S).stageProj st ((actualSlotsV2_BAUGD S).stageProj st y) =
      (actualSlotsV2_BAUGD S).stageProj st y := by
  have h := fun z => DFunLike.congr_fun
    (stageQ_starProjection_BAUGD (Φ := actualSlotsV2_BAUGD S) st) z
  rw [← h ((actualSlotsV2_BAUGD S).stageProj st y), ← h y]
  exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)

/-- **The stage plane has dimension `k_st`** at every cloud point (the V3 field `dimension`). -/
theorem finrank_stagePlane_BBP (st : Fin 3) {x : BoundaryAmbient_BIF S.IntTag_BAUGA
    (Fin S.packet.cusp.count)} (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud st) :
    Module.finrank ℝ (DP.stagePlane st x) = gafStageDim st := by
  fin_cases st
  · exact (DP.circle_spec.dimension x hx).1
  · exact (DP.edge_spec.dimension x hx).1
  · exact (DP.slim_spec.dimension x hx).1

include C in
/-- **The derivative of the native map on a stage plateau**: for every tangent vector
`dι u`, `Df_st⁰(dι u) = π_st Da_st(π_st g_st)(π_st Dg_st(dι u))`. -/
theorem native_mvfderiv_full_BBP (st : Fin 3) {q : W.pieceInterior ⊤}
    {U : Set (W.pieceInterior ⊤)} (hU : U ∈ 𝓝 q)
    (hψ : ∀ q' ∈ U, (actualSlotsV2_BAUGD S).cutoff st (C.toChain.stage st.castSucc q'.val) = 1)
    (hda : DifferentiableAt ℝ (C.toChain.slot st).map
      ((actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc q.val)))
    (u : TangentSpace (𝓡 3) q) :
    mvfderiv W.model (C.toChain.nativeStageMap_BIFc st) q.val
        (mfderiv (𝓡 3) W.model Subtype.val q u) =
      (actualSlotsV2_BAUGD S).stageProj st (fderiv ℝ (C.toChain.slot st).map
          ((actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc q.val))
        ((actualSlotsV2_BAUGD S).stageProj st (mvfderiv W.model (C.toChain.stage st.castSucc)
          q.val (mfderiv (𝓡 3) W.model Subtype.val q u)))) := by
  have hfun : (fun p => (actualSlotsV2_BAUGD S).stageProj st (C.toChain.nativeStageMap_BIFc st p)) =
      C.toChain.nativeStageMap_BIFc st :=
    funext fun p => stageProj_idem_BBP st _
  have hval := C.native_mvfderiv_BBP st ((actualSlotsV2_BAUGD S).stageProj st)
    (stageProj_idem_BBP st) hU hψ hda u
  exact (congrArg (fun f => mvfderiv W.model f q.val (mfderiv (𝓡 3) W.model Subtype.val q u))
    hfun).symm.trans hval

/-- **The ambient map of an active stage has range in a `k_st`-dimensional subspace**: for a cloud
point `x` and `z ∈ B(x, r_x)`, `range Da_st(z) ⊆ T` with `dim T = k_st`
(`Cfs15StageOutput.ambient_tangent_coframe_BAS` with the coframe `id`, `m = 1`, and
`dim L_x = k_st`). -/
theorem ambient_range_le_BBP (st : Fin 3)
    (O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st)
      ((actualSlotsV2_BAUGD S).stageCloud st) ((actualSlotsV2_BAUGD S).stageCloudEnlarged st)
      (DP.stageRadius st (Sg st)) (DP.stagePlane st))
    {x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud st)
    {z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hz : z ∈ ball x (DP.stageRadius st (Sg st) x)) :
    ∃ Tm : Submodule ℝ (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
      LinearMap.range (fderiv ℝ O.ambient z :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ≤ Tm ∧
        Module.finrank ℝ Tm = gafStageDim st := by
  have hid : ‖ContinuousLinearMap.id ℝ (BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count))‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hmm : ∀ v ∈ DP.stagePlane st x, (1 : ℝ) * ‖v‖ ≤
      ‖(ContinuousLinearMap.id ℝ (BoundaryAmbient_BIF S.IntTag_BAUGA
        (Fin S.packet.cusp.count))) v‖ := fun v _ => by simp
  have hε : Ξ st / 3 < 1 := by have := O.eps_le; linarith
  obtain ⟨Tm, hTm, hdim, -⟩ := Cfs15StageOutput.ambient_tangent_coframe_BAS
    (E := BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) O ⟨x, hx⟩ hz
    (ContinuousLinearMap.id ℝ (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
    hid (m := 1) hmm hε
  exact ⟨Tm, hTm, hdim.trans (finrank_stagePlane_BBP st hx)⟩

include C in
/-- The native stage map is differentiable on `W`. -/
theorem native_mdifferentiableAt_BBP (st : Fin 3) (p : W.Carrier) :
    MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (C.toChain.nativeStageMap_BIFc st) p := by
  have hsd : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (C.toChain.stage st.succ) p :=
    ((C.stage_smooth_BAUGD st.succ) p).mdifferentiableAt (by simp)
  exact DifferentiableAt.comp_mdifferentiableAt (g := (actualSlotsV2_BAUGD S).stageProj st)
    (f := C.toChain.stage st.succ) ((actualSlotsV2_BAUGD S).stageProj st).differentiableAt hsd

include C in
/-- **The final derivative through the later embedding**: `Df_st = DΘ_st(f_st⁰ p) ∘ Df_st⁰`. -/
theorem mvfderiv_stageMap_BBP (st : Fin 3) (p : W.Carrier) (w : TangentSpace W.model p) :
    mvfderiv W.model (C.toChain.stageMap st) p w =
      fderiv ℝ (C.toChain.laterV2_BAUGD st) (C.toChain.nativeStageMap_BIFc st p)
        (mvfderiv W.model (C.toChain.nativeStageMap_BIFc st) p w) := by
  have hΘ : DifferentiableAt ℝ (C.toChain.laterV2_BAUGD st)
      (C.toChain.nativeStageMap_BIFc st p) :=
    (C.toChain.later_contDiffAt_V2_BAUGD st p).differentiableAt (by simp)
  have hfun2 : C.toChain.stageMap st =
      C.toChain.laterV2_BAUGD st ∘ C.toChain.nativeStageMap_BIFc st :=
    funext (C.toChain.final_factor_V2_BAUGD st)
  exact (congrArg (fun f => mvfderiv W.model f p w) hfun2).trans
    (mvfderiv_comp_apply_of_differentiableAt_GAF3 (C.native_mdifferentiableAt_BBP st p) hΘ w)

include C in
/-- **The slot map has range in a `k_st`-dimensional subspace** (active slots; an inactive slot
has an empty cloud): for a cloud point `x` and `z ∈ B(x, r_x)`, `range Da_st(z) ⊆ T`,
`dim T = k_st`. -/
theorem slot_range_le_BBP (st : Fin 3)
    {x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hx : x ∈ (actualSlotsV2_BAUGD S).stageCloud st)
    {z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hz : z ∈ ball x (DP.stageRadius st (Sg st) x)) :
    ∃ Tm : Submodule ℝ (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
      LinearMap.range (fderiv ℝ (C.toChain.slot st).map z :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ≤ Tm ∧
        Module.finrank ℝ Tm = gafStageDim st := by
  rcases hsl : C.toChain.slot st with O | ⟨hc, he⟩
  · exact ambient_range_le_BBP (DP := DP) st O hx hz
  · exfalso
    have h := (BoundaryStageSlot_BIF.stageCloud_eq_empty_of_inactive hc he).1
    rw [h] at hx
    exact hx

include C in
/-- **The final derivative lands in `DΘ_st(π_st T)`**: on a stage plateau every value of `Df_st`
lies in the image of the `k_st`-dimensional space `T ⊇ range Da_st(π_st g_st)` under
`DΘ_st(f_st⁰) ∘ π_st`. -/
theorem stage_range_le_map_BBP (st : Fin 3) {q : W.pieceInterior ⊤}
    {U : Set (W.pieceInterior ⊤)} (hU : U ∈ 𝓝 q)
    (hψ : ∀ q' ∈ U, (actualSlotsV2_BAUGD S).cutoff st (C.toChain.stage st.castSucc q'.val) = 1)
    (hda : DifferentiableAt ℝ (C.toChain.slot st).map ((actualSlotsV2_BAUGD S).stageProj st
      (C.toChain.stage st.castSucc q.val)))
    (Tm : Submodule ℝ (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
    (hTm : LinearMap.range (fderiv ℝ (C.toChain.slot st).map
      ((actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc q.val)) :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ≤ Tm) :
    LinearMap.range
      ((mvfderiv W.model (C.toChain.stageMap st) q.val :
          TangentSpace W.model q.val →L[ℝ]
            BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
        TangentSpace W.model q.val →ₗ[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ≤
      Tm.map ((fderiv ℝ (C.toChain.laterV2_BAUGD st)
        (C.toChain.nativeStageMap_BIFc st q.val) :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ]
            BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∘ₗ
        ((actualSlotsV2_BAUGD S).stageProj st :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ]
            BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) := by
  rintro _ ⟨w, rfl⟩
  obtain ⟨u, rfl⟩ := exists_mfderiv_val_eq_BAUGC q w
  have e1 := C.mvfderiv_stageMap_BBP st q.val (mfderiv (𝓡 3) W.model Subtype.val q u)
  have e2 := C.native_mvfderiv_full_BBP st hU hψ hda u
  refine ⟨fderiv ℝ (C.toChain.slot st).map
    ((actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc q.val))
    ((actualSlotsV2_BAUGD S).stageProj st (mvfderiv W.model (C.toChain.stage st.castSucc)
      q.val (mfderiv (𝓡 3) W.model Subtype.val q u))), hTm ⟨_, rfl⟩, ?_⟩
  exact (congrArg (fun y => fderiv ℝ (C.toChain.laterV2_BAUGD st)
    (C.toChain.nativeStageMap_BIFc st q.val) y) e2.symm).trans e1.symm

include C in
/-- **The rank of the final stage map is at most `k_st` on a stage plateau**: with the plateau
`ψ_st = 1` near `q`, the tube `π g_st q ∈ B(π F_∂ q, r)` and `q` in the stage core,
`D f_st = DΘ_st ∘ Df_st⁰`, `Df_st⁰ = π Da(π g) π Dg` and `range Da ⊆ T` with `dim T = k_st`
(`slot_range_le_BBP`, `stage_range_le_map_BBP`). -/
theorem stage_rank_le_BBP (st : Fin 3) {q : W.pieceInterior ⊤}
    (hcore : q ∈ (actualSlotsV2_BAUGD S).stageCore st)
    (hball : (actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc q.val) ∈
      ball ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val))
        (DP.stageRadius st (Sg st)
          ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val))))
    {U : Set (W.pieceInterior ⊤)} (hU : U ∈ 𝓝 q)
    (hψ : ∀ q' ∈ U, (actualSlotsV2_BAUGD S).cutoff st (C.toChain.stage st.castSucc q'.val) = 1) :
    Module.finrank ℝ (LinearMap.range
      ((mvfderiv W.model (C.toChain.stageMap st) q.val :
          TangentSpace W.model q.val →L[ℝ]
            BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
        TangentSpace W.model q.val →ₗ[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) ≤ gafStageDim st := by
  have hx : (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val) ∈
      (actualSlotsV2_BAUGD S).stageCloud st := ⟨q, hcore, rfl⟩
  obtain ⟨Tm, hTm, hdim⟩ := C.slot_range_le_BBP st hx hball
  have hda : DifferentiableAt ℝ (C.toChain.slot st).map ((actualSlotsV2_BAUGD S).stageProj st
      (C.toChain.stage st.castSucc q.val)) :=
    ((C.toChain.slot st).map_contDiffAt_BAUGD hx hball).differentiableAt (by simp)
  have hle := C.stage_range_le_map_BBP st hU hψ hda Tm hTm
  exact (Submodule.finrank_mono hle).trans ((Submodule.finrank_map_le _ Tm).trans hdim.le)

include C in
/-- **The final rank is at least `dim F`** at a point where a chart coordinate `κ ∘ f_st` is a
submersion onto `F`. -/
theorem stage_rank_ge_BBP (st : Fin 3) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (κ : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] F)
    {p : W.Carrier}
    (hs : Function.Surjective (mfderiv W.model 𝓘(ℝ, F)
      (fun x => κ (C.toChain.stageMap st x)) p)) :
    Module.finrank ℝ F ≤ Module.finrank ℝ (LinearMap.range
      ((mvfderiv W.model (C.toChain.stageMap st) p :
          TangentSpace W.model p →L[ℝ]
            BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
        TangentSpace W.model p →ₗ[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) := by
  have hmd : MDifferentiableAt W.model
      𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      (C.toChain.stageMap st) p :=
    DifferentiableAt.comp_mdifferentiableAt (g := (actualSlotsV2_BAUGD S).stageProj st)
      (f := C.toChain.stage 3) ((actualSlotsV2_BAUGD S).stageProj st).differentiableAt
      (((C.stage_smooth_BAUGD 3) p).mdifferentiableAt (by simp))
  refine finrank_le_finrank_range_of_comp_surjective_BBP _ (κ : _ →ₗ[ℝ] F) ?_
  intro y
  obtain ⟨v, hv⟩ := hs y
  exact ⟨v, (mvfderiv_clm_comp_BDFB κ hmd v).symm.trans hv⟩

/-- The stage-`0` tube at a circle plateau point (`g₀ = F_∂`, `E = 0`). -/
theorem circle_stage_tube_BBP (j : S.CircleIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 q‖ < 6) :
    (actualSlotsV2_BAUGD S).stageProj 0 (C.toChain.stage (0 : Fin 3).castSucc q.val) ∈
      ball ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val))
        (DP.stageRadius 0 (Sg 0)
          ((actualSlotsV2_BAUGD S).stageProj 0 (S.boundaryOriginalMap q.val))) := by
  have hcore := circle_plateau_mem_core_BBP j hq hη
  have hsg := (C.toChain.numbers.1 0).2.1
  have hyv : ‖C.toChain.stage (0 : Fin 3).castSucc q.val - S.boundaryOriginalMap q.val‖ ≤
      0 * S.rho q.val := by
    have e : C.toChain.stage (0 : Fin 3).castSucc q.val = S.boundaryOriginalMap q.val := rfl
    rw [e, sub_self, norm_zero, zero_mul]
  exact C.stage_tube_BBP 0 hcore le_rfl (by linarith) hyv

/-- `ψ₀ = 1` at the stage input `g₀ q' = F_∂ q'` on the circle plateau. -/
theorem circle_plateau_cutoff_BBP (j : S.CircleIdx_BAUGD) {q' : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q' j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 q'‖ < 6) :
    (actualSlotsV2_BAUGD S).cutoff 0 (C.toChain.stage (0 : Fin 3).castSucc q'.val) = 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj : j.1 ∈ S.family.circle.centres := (Set.Finite.mem_toFinset _).mp j.2
  exact C.toChain.cutoff_bindings.1.2.2.1 q' ⟨j.1, hj, hq, hη⟩

/-- **G2, circle: `rank Df₀ = 2`** at every point of the original circle plateau (final map;
`≥` from the final submersion, `≤` from `f₀ = Θ₀ ∘ f₀⁰`, `range Da₀ ⊆ T`, `dim T = 2`). -/
theorem stage_rank_eq_circle_BBP (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2)
    (j : S.CircleIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 q‖ < 6) :
    Module.finrank ℝ (LinearMap.range
      ((mvfderiv W.model (C.toChain.stageMap 0) q.val :
          TangentSpace W.model q.val →L[ℝ]
            BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
        TangentSpace W.model q.val →ₗ[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) = gafStageDim 0 := by
  refine le_antisymm (C.stage_rank_le_BBP 0 (circle_plateau_mem_core_BBP j hq hη)
    (C.circle_stage_tube_BBP j hq hη) (S.circle_plateau_mem_nhds_BBP j hq hη)
    (fun q' hq' => C.circle_plateau_cutoff_BBP j hq'.1 hq'.2)) ?_
  have h := C.stage_rank_ge_BBP 0 (S.circleKappa_BBP j)
    (C.final_submersion_circle_BBP hβ2 hγ j hq hη)
  have e : Module.finrank ℝ ℝ² = gafStageDim 0 := by
    simp [gafStageDim]
  exact e ▸ h

/-- **G2, edge: `rank Df₁ = 1`** at every point of the original edge plateau. -/
theorem stage_rank_eq_edge_BBP (hσ : σc ≤ 1 / 4) (hb' : b ≤ 1 / (1000 * Δ))
    (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 6 * Δ) (hh : S.edgeHeightRaw q < 6 * Δ) :
    Module.finrank ℝ (LinearMap.range
      ((mvfderiv W.model (C.toChain.stageMap 1) q.val :
          TangentSpace W.model q.val →L[ℝ]
            BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
        TangentSpace W.model q.val →ₗ[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) = gafStageDim 1 := by
  refine le_antisymm (C.stage_rank_le_BBP 1
    (edge_plateau_mem_core_BBP j hq hη hh C.std.2.1.le)
    (C.edge_stage_tube_BBP j hq hη hh) (S.edge_plateau_mem_nhds_BBP j hq hη hh)
    (fun q' hq' => C.edge_plateau_cutoff_BBP j hq'.1 hq'.2.1 hq'.2.2)) ?_
  have h := C.stage_rank_ge_BBP 1 (S.edgeKappa_BBP j)
    (C.final_submersion_edge_BBP hσ hb' j hq hη hh)
  have e : Module.finrank ℝ ℝ = gafStageDim 1 := by
    simp [gafStageDim]
  exact e ▸ h

/-- **G2, slim: `rank Df₂ = 1`** at every point of the original slim plateau. -/
theorem stage_rank_eq_slim_BBP (j : S.SlimIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 1000000 * Δ * S.rho j.1)
    (hη : |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ)) :
    Module.finrank ℝ (LinearMap.range
      ((mvfderiv W.model (C.toChain.stageMap 2) q.val :
          TangentSpace W.model q.val →L[ℝ]
            BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
        TangentSpace W.model q.val →ₗ[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) = gafStageDim 2 := by
  refine le_antisymm (C.stage_rank_le_BBP 2
    (slim_plateau_mem_core_BBP j hq hη C.std.2.1.le)
    (C.slim_stage_tube_BBP j hq hη) (S.slim_plateau_mem_nhds_BBP j hq hη)
    (fun q' hq' => C.slim_plateau_cutoff_BBP j hq'.1 hq'.2)) ?_
  have h := C.stage_rank_ge_BBP 2 (S.slimKappa_BBP j) (C.stage_submersion_slim_final_BBP j hq hη)
  have e : Module.finrank ℝ ℝ = gafStageDim 2 := by
    simp [gafStageDim]
  exact e ▸ h

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
