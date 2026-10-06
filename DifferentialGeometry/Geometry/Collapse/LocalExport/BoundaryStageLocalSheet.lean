import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesCore
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroSetLocalInverse

/-!
# O-WF G1b: the local one-sheet property of the native stage images on the boundary chain

On `C : BoundaryGaf02ChainE DP …` with an ACTIVE stage slot `O` (a CFS15 output) and a point `q` of
a stage plateau (`ψ_st(g_st) = 1` on a neighbourhood of `q`) at which a chart coordinate
`κ ∘ f_st⁰` is a submersion:

* `native_eq_ambient_OWF`: on the plateau `f_st⁰(p) = a_st(π_st g_st p)` (the ambient nearest map
  of `O` at the projected input; closed twin inside `native_scope_V2_BAUGD`);
* **`native_localInverse_OWF`** (generic stage, chart coordinate `κ : H^∂ →L F` with
  `κ ∘ π_st = κ` and `dim F = k_st`): `κ` has a smooth local inverse `ζ` on the native zero set
  `Z_st` near `f_st⁰(q)` (`Cfs15StageOutput.exists_localInverse_OWF` at the cloud point of the
  input, the plane dimension `finrank_stagePlane_BBP`, and
  `D(κ ∘ f_st⁰)(dι u) = κ Da(π g)(π Dg dι u)` from `native_mvfderiv_BBP`);
* **`circle_localInverse_OWF`**: the circle instance (`κ_j = circleKappa_BBP j`, the threshold-6
  plateau of chart `j`, the native submersion `stage_submersion_circle_BBP`; register premises
  `β₂ ≤ 10⁻⁷`, `γ ≤ 1/2`).
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

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **On the plateau the native value is the ambient nearest map**:
`f_st⁰(p) = a_st(π_st g_st p)` for an active slot `O` and `ψ_st(g_st p) = 1`. -/
theorem native_eq_ambient_OWF (st : Fin 3)
    (O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st)
      ((actualSlotsV2_BAUGD S).stageCloud st) ((actualSlotsV2_BAUGD S).stageCloudEnlarged st)
      (DP.stageRadius st (Sg st)) (DP.stagePlane st))
    (h : C.toChain.slot st = .active O) (p : W.Carrier)
    (hψ : (actualSlotsV2_BAUGD S).cutoff st (C.toChain.stage st.castSucc p) = 1) :
    C.toChain.nativeStageMap_BIFc st p =
      O.ambient ((actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc p)) := by
  have hz : C.toChain.stage st.castSucc p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff st) :=
    subset_tsupport _ (Function.mem_support.mpr (by rw [hψ]; exact one_ne_zero))
  have hZ := O.ambient_mem (C.toChain.input_mem_omega_V2_BAUGD st p hz)
  have hZQ : O.Z ⊆ (actualSlotsV2_BAUGD S).stageQ st :=
    O.zeroSet_subset_stageQ _ (fun x hx => by
      obtain ⟨q', -, rfl⟩ := hx
      exact stageProj_mem_stageQ_BAUGD st _) (DP.plane_le_stageQ_BAUGD st)
  have hm : (C.toChain.slot st).map = O.ambient := by rw [h]; rfl
  have e := (C.toChain.native_plateau_V2_BAUGD st p hψ).trans (congrArg (fun f =>
    ((actualSlotsV2_BAUGD S).stageQ st).starProjection
      (f (((actualSlotsV2_BAUGD S).stageQ st).starProjection (C.toChain.stage st.castSucc p))))
    hm)
  have e2 := Submodule.starProjection_eq_self_iff.mpr (hZQ hZ)
  have e3 : ((actualSlotsV2_BAUGD S).stageQ st).starProjection (C.toChain.stage st.castSucc p) =
      (actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc p) :=
    DFunLike.congr_fun (stageQ_starProjection_BAUGD (Φ := actualSlotsV2_BAUGD S) st) _
  exact (e.trans e2).trans (congrArg O.ambient e3)

/-- **Local one-sheet at a plateau point** (generic stage; see the module docstring). -/
theorem native_localInverse_OWF (st : Fin 3) {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (κc : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] F)
    (hκ : ∀ y, κc ((actualSlotsV2_BAUGD S).stageProj st y) = κc y)
    (hdimF : Module.finrank ℝ F = gafStageDim st)
    (O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st)
      ((actualSlotsV2_BAUGD S).stageCloud st) ((actualSlotsV2_BAUGD S).stageCloudEnlarged st)
      (DP.stageRadius st (Sg st)) (DP.stagePlane st))
    (hO : C.toChain.slot st = .active O) {q : W.pieceInterior ⊤}
    {U : Set (W.pieceInterior ⊤)} (hU : U ∈ 𝓝 q)
    (hψ : ∀ q' ∈ U, (actualSlotsV2_BAUGD S).cutoff st (C.toChain.stage st.castSucc q'.val) = 1)
    (hs : Surjective (mfderiv W.model 𝓘(ℝ, F)
      (fun p => κc (C.toChain.nativeStageMap_BIFc st p)) q.val)) :
    ∃ (V : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) (δ : ℝ)
      (ζ : F → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
      IsOpen V ∧ C.toChain.nativeStageMap_BIFc st q.val ∈ V ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ ζ (ball (κc (C.toChain.nativeStageMap_BIFc st q.val)) δ) ∧
      (∀ b ∈ ball (κc (C.toChain.nativeStageMap_BIFc st q.val)) δ,
        ζ b ∈ O.Z ∩ V ∧ κc (ζ b) = b) ∧
      (∀ w ∈ O.Z ∩ V, κc w ∈ ball (κc (C.toChain.nativeStageMap_BIFc st q.val)) δ ∧
        ζ (κc w) = w) := by
  have hψq := hψ q (mem_of_mem_nhds hU)
  have e := C.native_eq_ambient_OWF st O hO q.val hψq
  have hz : C.toChain.stage st.castSucc q.val ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff st) :=
    subset_tsupport _ (Function.mem_support.mpr (by rw [hψq]; exact one_ne_zero))
  have e3 : ((actualSlotsV2_BAUGD S).stageQ st).starProjection
      (C.toChain.stage st.castSucc q.val) =
      (actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc q.val) :=
    DFunLike.congr_fun (stageQ_starProjection_BAUGD (Φ := actualSlotsV2_BAUGD S) st) _
  have hzΩ := C.toChain.input_mem_omega_V2_BAUGD st q.val hz
  obtain ⟨x, hx, hzx⟩ := mem_cfs15Omega_C15.mp hzΩ
  have hzx' : (actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc q.val) ∈
      ball x (DP.stageRadius st (Sg st) x) := by
    rw [← e3]
    exact hzx
  have hzΩ' := mem_cfs15Omega_of_mem_C15 hx hzx'
  have hm : (C.toChain.slot st).map = O.ambient := by rw [hO]; rfl
  have hda : DifferentiableAt ℝ (C.toChain.slot st).map
      ((actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc q.val)) := by
    rw [hm]
    exact (O.ambient_contDiffAt hzΩ').differentiableAt (by simp)
  have hdim : Module.finrank ℝ F = Module.finrank ℝ (DP.stagePlane st x) :=
    hdimF.trans (BoundaryGaf02ChainE.finrank_stagePlane_BBP (DP := DP) st hx).symm
  have hm' : fderiv ℝ (C.toChain.slot st).map
      ((actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc q.val)) =
      fderiv ℝ O.ambient
        ((actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc q.val)) := by
    rw [hm]
  have hsurj : ∀ v : F, ∃ u, κc (fderiv ℝ O.ambient
      ((actualSlotsV2_BAUGD S).stageProj st (C.toChain.stage st.castSucc q.val)) u) = v := by
    intro v
    obtain ⟨w, hw⟩ := hs v
    obtain ⟨u, rfl⟩ := exists_mfderiv_val_eq_BAUGC q w
    have e1 := C.native_mvfderiv_BBP st κc hκ hU hψ hda u
    exact ⟨_, (congrArg (fun L : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ]
      BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) =>
        κc (L ((actualSlotsV2_BAUGD S).stageProj st (mvfderiv W.model
          (C.toChain.stage st.castSucc) q.val (mfderiv (𝓡 3) W.model Subtype.val q u)))))
            hm').symm.trans (e1.symm.trans hw)⟩
  have key : ∀ w₀, O.ambient ((actualSlotsV2_BAUGD S).stageProj st
      (C.toChain.stage st.castSucc q.val)) = w₀ →
      ∃ (V : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) (δ : ℝ)
        (ζ : F → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
        IsOpen V ∧ w₀ ∈ V ∧ 0 < δ ∧ ContDiffOn ℝ ∞ ζ (ball (κc w₀) δ) ∧
        (∀ b ∈ ball (κc w₀) δ, ζ b ∈ O.Z ∩ V ∧ κc (ζ b) = b) ∧
        (∀ w ∈ O.Z ∩ V, κc w ∈ ball (κc w₀) δ ∧ ζ (κc w) = w) := by
    rintro w₀ rfl
    exact O.exists_localInverse_OWF ⟨x, hx⟩ hzx' κc hdim hsurj
  exact key _ e.symm

/-- **Local one-sheet, circle stage**: at a point `q` of the circle chart `j`'s threshold-6 plateau
with an active first slot `O`, `κ_j` has a smooth local inverse on `Z₀` near `f₀⁰(q)`. -/
theorem circle_localInverse_OWF (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2)
    (O : Cfs15StageOutput (gafStageDim 0) Kj (Ξ 0) (cw 0)
      ((actualSlotsV2_BAUGD S).stageCloud 0) ((actualSlotsV2_BAUGD S).stageCloudEnlarged 0)
      (DP.stageRadius 0 (Sg 0)) (DP.stagePlane 0))
    (hO : C.toChain.slot 0 = .active O) (j : S.CircleIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 q‖ < 6) :
    ∃ (V : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) (δ : ℝ)
      (ζ : ℝ² → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)),
      IsOpen V ∧ C.toChain.nativeStageMap_BIFc 0 q.val ∈ V ∧ 0 < δ ∧
      ContDiffOn ℝ ∞ ζ (ball (S.circleKappa_BBP j (C.toChain.nativeStageMap_BIFc 0 q.val)) δ) ∧
      (∀ b ∈ ball (S.circleKappa_BBP j (C.toChain.nativeStageMap_BIFc 0 q.val)) δ,
        ζ b ∈ O.Z ∩ V ∧ S.circleKappa_BBP j (ζ b) = b) ∧
      (∀ w ∈ O.Z ∩ V,
        S.circleKappa_BBP j w ∈ ball (S.circleKappa_BBP j (C.toChain.nativeStageMap_BIFc 0 q.val))
          δ ∧ ζ (S.circleKappa_BBP j w) = w) :=
  C.native_localInverse_OWF 0 (S.circleKappa_BBP j)
    (fun y => congrArg (S.circleKappa_BBP j) (stageProj_zero_BBP S y)) (by simp [gafStageDim])
    O hO (S.circle_plateau_mem_nhds_BBP j hq hη)
    (fun q' hq' => C.circle_plateau_cutoff_BBP j hq'.1 hq'.2)
    (C.stage_submersion_circle_BBP hβ2 hγ j hq hη)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
