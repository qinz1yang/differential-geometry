import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainEDerivative
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceBasesV2

/-!
# A4 §A: the native / final split of the boundary chain (BAUG-Dd, G10)

Route sheet `build-logs/resume/sheet-BAUG-D-A4.md` §A / §F (lead decision 17:4x: G10 is BAUG-D's; G11 / G13 go to new lanes).
On a chain `C` over augmented data with the V3 specs on the ACTUAL v2 slot `Φ = actualSlotsV2_BAUGD S`:

* the later embeddings `C.laterV2_BAUGD st` (`Θ₀ = Ψ₂ ∘ Ψ₁`, `Θ₁ = π₁ ∘ Ψ₂`, `Θ₂ = id`; closed twin `Gaf02Chain.Θ_BAS`);
* `final_factor_V2_BAUGD` (`f_j = Θ_j ∘ f_j⁰` at EVERY point: `π₀ = id`; `π₁Ψ₂π₁ = π₁Ψ₂` from `ψ₂ ∘ π_j = ψ₂` and
  `Q₂ ⊆ Q₁`), `later_retains_V2_BAUGD` (`Θ_j` keeps the blocks of the stage's own marker charts),
  `later_contDiffAt_V2_BAUGD` (smooth at every native image point: A3h's dichotomy), `native_scope_V2_BAUGD`
  (on the plateau `ψ_st = 1` the native image lies in the native zero set `Z_st`);
* `laterSplit_V2_BAUGD` (a `BoundaryLaterSplit_BIFc` for ANY sources in the plateau with `base = Θ(f⁰(source))` and the
  no-merging embedding — the inputs G11 produces), `proper_of_source_eq_V2_BAUGD` (W compact).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- Restricting to `s ⊆ t` after `t` (or before) is restricting to `s`. -/
theorem blockRestrict_of_subset_BAUGD {κ : Type*} {V : κ → Type*} [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℝ (V i)] [DecidableEq κ] {s t : Finset κ} (hst : s ⊆ t)
    (y : BlockSpace V) :
    blockRestrict s (blockRestrict t y) = blockRestrict s y ∧
      blockRestrict t (blockRestrict s y) = blockRestrict s y := by
  constructor
  · have h := congrArg (fun L => L y) (blockRestrict_comp (V := V) t s)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h, Finset.inter_eq_right.mpr hst]
  · have h := congrArg (fun L => L y) (blockRestrict_comp (V := V) s t)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h, Finset.inter_eq_left.mpr hst]

/-- A function invariant under an idempotent linear map `P` (`f ∘ P = f`) has `P z ∉ tsupport f`
whenever `z ∉ tsupport f` (translate a zero neighbourhood of `z` by `z − P z`). -/
theorem notMem_tsupport_of_invariant_BAUGD {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : H →L[ℝ] H) (hP : ∀ y, P (P y) = P y) (f : H → ℝ) (hf : ∀ y, f (P y) = f y) {z : H}
    (hz : z ∉ tsupport f) : P z ∉ tsupport f := by
  rw [notMem_tsupport_iff_eventuallyEq] at hz ⊢
  have hcont : Continuous fun w : H => w + (z - P z) := continuous_id.add continuous_const
  have hmap : Tendsto (fun w : H => w + (z - P z)) (𝓝 (P z)) (𝓝 z) := by
    have h := hcont.tendsto (P z)
    simp only [add_sub_cancel] at h
    exact h
  filter_upwards [hmap.eventually hz] with w hw
  have hd : P (z - P z) = 0 := by rw [map_sub, hP, sub_self]
  have h1 : f w = f (w + (z - P z)) := by
    rw [← hf w, ← hf (w + (z - P z)), map_add, hd, add_zero]
  rw [h1]
  exact hw

/-- On the plateau `ψ(y) = 1` the projected adjustment is the projected smoothing map:
`π_Q Ψ(y) = π_Q a(π_Q y)`. -/
theorem starProjection_adjustmentMap_of_one_BAUGD {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] (a : H → H)
    (ψ : H → ℝ) {y : H} (hψ : ψ y = 1) :
    Q.starProjection (adjustmentMap Q (fun z => Q.starProjection (a z)) ψ y) =
      Q.starProjection (a (Q.starProjection y)) := by
  have hid : ∀ z, Q.starProjection (Q.starProjection z) = Q.starProjection z := fun z =>
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)
  rw [adjustmentMap_apply, hψ, one_smul, map_add, map_sub, hid, hid]
  abel

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

section Slot

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM)

/-- `π₀ = id` on the v2 slot (the stage-`0` tags are all interior tags). -/
theorem stageProj_zero_V2_BAUGD (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    (actualSlotsV2_BAUGD S).stageProj 0 y = y := by
  have h : (actualSlotsV2_BAUGD S).stageTagsAug 0 = Finset.univ := by
    change (S.stageTagsV2_BAUGD 0).disjSum Finset.univ = Finset.univ
    change (Finset.univ : Finset S.IntTag_BAUGA).disjSum Finset.univ = Finset.univ
    exact Finset.univ_disjSum_univ
  change blockRestrict ((actualSlotsV2_BAUGD S).stageTagsAug 0) y = y
  rw [h, blockRestrict_univ]
  rfl

/-- The augmented stage-`2` tags lie in the stage-`1` tags. -/
theorem stageTagsAug_two_subset_one_V2_BAUGD :
    (actualSlotsV2_BAUGD S).stageTagsAug 2 ⊆ (actualSlotsV2_BAUGD S).stageTagsAug 1 := by
  intro x hx
  rcases x with t | i
  · exact Finset.inl_mem_disjSum.mpr
      (S.stageTagsV2_two_subset_one_BAUGD (Finset.inl_mem_disjSum.mp hx))
  · exact Finset.inr_mem_disjSum.mpr (Finset.mem_univ i)

/-- `π₂ π₁ = π₂`, `π₁ π₂ = π₂`, `π₁ π₁ = π₁` on the v2 slot. -/
theorem stageProj_one_two_V2_BAUGD (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    (actualSlotsV2_BAUGD S).stageProj 2 ((actualSlotsV2_BAUGD S).stageProj 1 y) =
        (actualSlotsV2_BAUGD S).stageProj 2 y ∧
      (actualSlotsV2_BAUGD S).stageProj 1 ((actualSlotsV2_BAUGD S).stageProj 2 y) =
        (actualSlotsV2_BAUGD S).stageProj 2 y ∧
      (actualSlotsV2_BAUGD S).stageProj 1 ((actualSlotsV2_BAUGD S).stageProj 1 y) =
        (actualSlotsV2_BAUGD S).stageProj 1 y := by
  have h21 := blockRestrict_of_subset_BAUGD (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
    (stageTagsAug_two_subset_one_V2_BAUGD S) y
  have h11 := blockRestrict_of_subset_BAUGD (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)
    (subset_refl ((actualSlotsV2_BAUGD S).stageTagsAug 1)) y
  exact ⟨h21.1, h21.2, h11.1⟩

/-- `ψ₂ ∘ π₁ = ψ₂` and `π₁ ∘ π₁ = π₁` (the invariance used off `tsupport ψ₂`). -/
theorem cutoff_two_invariant_V2_BAUGD :
    (∀ y, (actualSlotsV2_BAUGD S).cutoff 2 ((actualSlotsV2_BAUGD S).stageProj 1 y) =
      (actualSlotsV2_BAUGD S).cutoff 2 y) ∧
    ∀ y, (actualSlotsV2_BAUGD S).stageProj 1 ((actualSlotsV2_BAUGD S).stageProj 1 y) =
      (actualSlotsV2_BAUGD S).stageProj 1 y :=
  ⟨fun y => cutoffTwo_stageProj_BAUGD S 1 y, fun y => (stageProj_one_two_V2_BAUGD S y).2.2⟩

end Slot

namespace BoundaryGaf02Chain

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  (C : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder κ)

/-- **The later embeddings** `Θ₀ = Ψ₂ ∘ Ψ₁`, `Θ₁ = π₁ ∘ Ψ₂`, `Θ₂ = id` (closed `Gaf02Chain.Θ_BAS`). -/
def laterV2_BAUGD : Fin 3 → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →
    BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) :=
  ![C.Ψ 2 ∘ C.Ψ 1, fun y => (actualSlotsV2_BAUGD S).stageProj 1 (C.Ψ 2 y), id]

/-- The third adjustment in coordinates: `Ψ₂ z = z + ψ₂(z)(π₂ a₂(π₂ z) − π₂ z)`. -/
theorem Ψ_two_apply_V2_BAUGD (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    C.Ψ 2 z = z + (actualSlotsV2_BAUGD S).cutoff 2 z •
      ((actualSlotsV2_BAUGD S).stageProj 2 ((C.slot 2).map ((actualSlotsV2_BAUGD S).stageProj 2 z)) -
        (actualSlotsV2_BAUGD S).stageProj 2 z) := by
  simp only [BoundaryGaf02Chain.Ψ, BoundaryInteriorSlots_BIF.adjust, adjustmentMap_apply,
    stageQ_starProjection_BAUGD]

/-- `π₁ Ψ₂ π₁ = π₁ Ψ₂` (`ψ₂ ∘ π₁ = ψ₂`, `Q₂ ⊆ Q₁`). -/
theorem stageProj_one_Ψ_two_V2_BAUGD
    (y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    (actualSlotsV2_BAUGD S).stageProj 1 (C.Ψ 2 ((actualSlotsV2_BAUGD S).stageProj 1 y)) =
      (actualSlotsV2_BAUGD S).stageProj 1 (C.Ψ 2 y) := by
  have h1 := stageProj_one_two_V2_BAUGD S y
  have hψ : (actualSlotsV2_BAUGD S).cutoff 2 ((actualSlotsV2_BAUGD S).stageProj 1 y) =
      (actualSlotsV2_BAUGD S).cutoff 2 y := cutoffTwo_stageProj_BAUGD S 1 y
  rw [C.Ψ_two_apply_V2_BAUGD, C.Ψ_two_apply_V2_BAUGD, map_add, map_add, map_smul, map_smul,
    map_sub, map_sub, h1.1, h1.2.2, hψ]

/-- Stage `0` of the final factorization: `π₀E = Ψ₂Ψ₁(π₀ g₁)` (`π₀ = id`). -/
theorem final_factor_zero_V2_BAUGD (p : W.Carrier) :
    (actualSlotsV2_BAUGD S).stageProj 0 (C.E p) =
      (C.Ψ 2 ∘ C.Ψ 1) ((actualSlotsV2_BAUGD S).stageProj 0 (C.g₁ p)) := by
  rw [stageProj_zero_V2_BAUGD, stageProj_zero_V2_BAUGD]
  rfl

/-- Stage `1` of the final factorization: `π₁E = π₁Ψ₂(π₁ g₂)`. -/
theorem final_factor_one_V2_BAUGD (p : W.Carrier) :
    (actualSlotsV2_BAUGD S).stageProj 1 (C.E p) =
      (actualSlotsV2_BAUGD S).stageProj 1 (C.Ψ 2 ((actualSlotsV2_BAUGD S).stageProj 1 (C.g₂ p))) := by
  rw [C.stageProj_one_Ψ_two_V2_BAUGD]
  rfl

/-- **The final factorization** `f_j = Θ_j ∘ f_j⁰` at EVERY point (D69-2). -/
theorem final_factor_V2_BAUGD (st : Fin 3) (p : W.Carrier) :
    C.stageMap st p = C.laterV2_BAUGD st (C.nativeStageMap_BIFc st p) := by
  fin_cases st
  · exact C.final_factor_zero_V2_BAUGD p
  · exact C.final_factor_one_V2_BAUGD p
  · rfl

/-- **`Θ_j` keeps the blocks of the stage's own marker charts** (chart transport; closed
`theta_retains_circle_BAS`, `theta_retains_edge_BAS`). -/
theorem later_retains_V2_BAUGD (st : Fin 3) (m : S.MarkerIdx_BAUGC) (hm : S.markerStage_BAUGC m = st)
    (x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    C.laterV2_BAUGD st x (Sum.inl (S.markerTag_BAUGC m)) = x (Sum.inl (S.markerTag_BAUGC m)) := by
  subst hm
  rcases m with j | j | j
  · have h1 := adjust_keeps_block_V2_BAUGD S 1 (C.slot 1).map x (.inl j)
      (S.circleTag_notMem_stageTagsV2_BAUGD (by decide) j)
    have h2 := adjust_keeps_block_V2_BAUGD S 2 (C.slot 2).map (C.Ψ 1 x) (.inl j)
      (S.circleTag_notMem_stageTagsV2_BAUGD (by decide) j)
    exact h2.trans h1
  · rfl
  · have hmem : (Sum.inl (S.markerTag_BAUGC (.inr (.inr j))) :
        S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count) ∈ (actualSlotsV2_BAUGD S).stageTagsAug 1 :=
      Finset.inl_mem_disjSum.mpr (S.markerTag_mem_stageTagsV2_BAUGD (.inr (.inr j)))
    have h2 := adjust_keeps_block_V2_BAUGD S 2 (C.slot 2).map x (S.markerTag_BAUGC (.inr (.inr j)))
      (S.edgeBTag_notMem_stageTagsV2_two_BAUGD j)
    change blockRestrict ((actualSlotsV2_BAUGD S).stageTagsAug 1) (C.Ψ 2 x)
      (Sum.inl (S.markerTag_BAUGC (.inr (.inr j)))) = _
    rw [blockRestrict_apply, ite_eq_left hmem]
    exact h2

/-- The first and second adjustments are smooth at the chain's own inputs `g₁ p`, `g₂ p` (the
CFS16 dichotomy: identity off `tsupport ψ`, tube otherwise). -/
theorem Ψ_contDiffAt_input_V2_BAUGD (st : Fin 3) (hst : st ≠ 0) (p : W.Carrier) :
    ContDiffAt ℝ ∞ (C.Ψ st) (C.stage st.castSucc p) := by
  have hN := C.numbers
  have hie := C.input_error_V2_BAUGD st p
  by_cases hz : C.stage st.castSucc p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff st)
  · obtain ⟨-, h⟩ := current_input_generic_BAUGD DP (C.slot st) (hN.1 st).2.1
      (C.cutoff_mem_Icc_V2_BAUGD st) (C.stage st.castSucc p) p (C.loc_V2_BAUGD st p) hie.2 hie.1
    obtain ⟨q, -, -, hx, hr1, -, htube, -, -⟩ := h hz
    have hrpos : 0 < DP.stageRadius st (Sg st)
        ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) := by
      have := mul_pos (hN.1 st).2.1 (S.rho_pos q.val)
      linarith
    have hz' : ‖(actualSlotsV2_BAUGD S).stageProj st (C.stage st.castSucc p) -
        (actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)‖ <
        DP.stageRadius st (Sg st)
          ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) := by linarith
    have hψ : ContDiffAt ℝ ∞ ((actualSlotsV2_BAUGD S).cutoff st) (C.stage st.castSucc p) := by
      have hB := C.cutoff_bindings
      fin_cases st
      · exact absurd rfl hst
      · have h1 := hB.2.1.2.2.2.2 p 1 ⟨zero_le_one, le_rfl⟩
        have e := segment_one_BAUGD (S.boundaryOriginalMap p)
          ((actualSlotsV2_BAUGD S).adjust 0 (C.slot 0).map (S.boundaryOriginalMap p))
        have hpos : 0 < S.scaleMarker_BIF
            ((actualSlotsV2_BAUGD S).adjust 0 (C.slot 0).map (S.boundaryOriginalMap p)) :=
          (congrArg (fun z => 0 < S.scaleMarker_BIF z) e).mp h1.1
        have hopen : IsOpen {z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) |
            0 < S.scaleMarker_BIF z} :=
          isOpen_lt continuous_const S.scaleMarker_BIF.continuous
        exact hB.2.1.1.contDiffAt (hopen.mem_nhds hpos)
      · exact hB.2.2.1.contDiffAt
    exact adjust_contDiffAt_BAUGD (C.slot st) hx rfl hz' hψ
  · exact adjust_contDiffAt_of_notMem_BAUGD st _ hz

/-- Stage `1`'s third adjustment is smooth at `π₁ g₂ p` (`ψ₂ ∘ π₁ = ψ₂`, `π₂π₁ = π₂`). -/
theorem Ψ_two_contDiffAt_proj_V2_BAUGD (p : W.Carrier) :
    ContDiffAt ℝ ∞ (C.Ψ 2) ((actualSlotsV2_BAUGD S).stageProj 1 (C.g₂ p)) := by
  have hN := C.numbers
  have hie := C.input_error_V2_BAUGD 2 p
  by_cases hz : C.g₂ p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 2)
  · obtain ⟨-, h⟩ := current_input_generic_BAUGD DP (C.slot 2) (hN.1 2).2.1
      (C.cutoff_mem_Icc_V2_BAUGD 2) (C.g₂ p) p (C.loc_V2_BAUGD 2 p) hie.2 hie.1
    obtain ⟨q, -, -, hx, hr1, -, htube, -, -⟩ := h hz
    have hrpos : 0 < DP.stageRadius 2 (Sg 2)
        ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val)) := by
      have := mul_pos (hN.1 2).2.1 (S.rho_pos q.val)
      linarith
    have hz' : ‖(actualSlotsV2_BAUGD S).stageProj 2 ((actualSlotsV2_BAUGD S).stageProj 1 (C.g₂ p)) -
        (actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val)‖ <
        DP.stageRadius 2 (Sg 2)
          ((actualSlotsV2_BAUGD S).stageProj 2 (S.boundaryOriginalMap q.val)) := by
      rw [(stageProj_one_two_V2_BAUGD S (C.g₂ p)).1]
      linarith
    exact adjust_contDiffAt_BAUGD (C.slot 2) hx rfl hz' C.cutoff_bindings.2.2.1.contDiffAt
  · have hinv := cutoff_two_invariant_V2_BAUGD S
    have hz2 := notMem_tsupport_of_invariant_BAUGD ((actualSlotsV2_BAUGD S).stageProj 1) hinv.2
      ((actualSlotsV2_BAUGD S).cutoff 2) hinv.1 hz
    exact adjust_contDiffAt_of_notMem_BAUGD 2 _ hz2

/-- Stage `0`: `Θ₀ = Ψ₂ ∘ Ψ₁` is smooth at `π₀ g₁ p`. -/
theorem later_contDiffAt_zero_V2_BAUGD (p : W.Carrier) :
    ContDiffAt ℝ ∞ (C.Ψ 2 ∘ C.Ψ 1) ((actualSlotsV2_BAUGD S).stageProj 0 (C.g₁ p)) := by
  rw [stageProj_zero_V2_BAUGD]
  have h1 := C.Ψ_contDiffAt_input_V2_BAUGD 1 (by decide) p
  have h2 := C.Ψ_contDiffAt_input_V2_BAUGD 2 (by decide) p
  exact h2.comp (C.g₁ p) h1

/-- Stage `1`: `Θ₁ = π₁ ∘ Ψ₂` is smooth at `π₁ g₂ p`. -/
theorem later_contDiffAt_one_V2_BAUGD (p : W.Carrier) :
    ContDiffAt ℝ ∞ (fun y => (actualSlotsV2_BAUGD S).stageProj 1 (C.Ψ 2 y))
      ((actualSlotsV2_BAUGD S).stageProj 1 (C.g₂ p)) :=
  ((actualSlotsV2_BAUGD S).stageProj 1).contDiff.contDiffAt.comp _ (C.Ψ_two_contDiffAt_proj_V2_BAUGD p)

/-- **`Θ_j` is smooth at every native image point** `f_j⁰(p)`. -/
theorem later_contDiffAt_V2_BAUGD (st : Fin 3) (p : W.Carrier) :
    ContDiffAt ℝ ∞ (C.laterV2_BAUGD st) (C.nativeStageMap_BIFc st p) := by
  fin_cases st
  · exact C.later_contDiffAt_zero_V2_BAUGD p
  · exact C.later_contDiffAt_one_V2_BAUGD p
  · exact contDiffAt_id

/-- The native map through the stage adjustment: `f_st⁰(p) = π_st Ψ_st(g_st p)`. -/
theorem native_eq_V2_BAUGD (st : Fin 3) (p : W.Carrier) :
    C.nativeStageMap_BIFc st p = ((actualSlotsV2_BAUGD S).stageQ st).starProjection
      ((actualSlotsV2_BAUGD S).adjust st (C.slot st).map (C.stage st.castSucc p)) :=
  (congrArg ((actualSlotsV2_BAUGD S).stageProj st) (C.stage_succ_eq_V2_BAUGD st p)).trans
    (DFunLike.congr_fun (stageQ_starProjection_BAUGD (Φ := actualSlotsV2_BAUGD S) st) _).symm

/-- On the plateau: `f_st⁰(p) = π_st a_st(π_st g_st p)`. -/
theorem native_plateau_V2_BAUGD (st : Fin 3) (p : W.Carrier)
    (hψ : (actualSlotsV2_BAUGD S).cutoff st (C.stage st.castSucc p) = 1) :
    C.nativeStageMap_BIFc st p = ((actualSlotsV2_BAUGD S).stageQ st).starProjection
      ((C.slot st).map (((actualSlotsV2_BAUGD S).stageQ st).starProjection
        (C.stage st.castSucc p))) :=
  (C.native_eq_V2_BAUGD st p).trans
    (starProjection_adjustmentMap_of_one_BAUGD _ (C.slot st).map _ hψ)

/-- On `tsupport ψ_st` the projected input lies in the CFS15 domain `Ω_st`. -/
theorem input_mem_omega_V2_BAUGD (st : Fin 3) (p : W.Carrier)
    (hz : C.stage st.castSucc p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff st)) :
    ((actualSlotsV2_BAUGD S).stageQ st).starProjection (C.stage st.castSucc p) ∈
      cfs15Omega_C15 ((actualSlotsV2_BAUGD S).stageCloud st) (DP.stageRadius st (Sg st)) := by
  have hN := C.numbers
  have hie := C.input_error_V2_BAUGD st p
  have hgen := (current_input_generic_BAUGD DP (C.slot st) (hN.1 st).2.1
    (C.cutoff_mem_Icc_V2_BAUGD st) (C.stage st.castSucc p) p (C.loc_V2_BAUGD st p) hie.2
      hie.1).2 hz
  obtain ⟨q, -, -, hx, hr1, -, htube, -, -⟩ := hgen
  have hrpos : 0 < DP.stageRadius st (Sg st)
      ((actualSlotsV2_BAUGD S).stageProj st (S.boundaryOriginalMap q.val)) := by
    have := mul_pos (hN.1 st).2.1 (S.rho_pos q.val)
    linarith
  have hπy : ((actualSlotsV2_BAUGD S).stageQ st).starProjection (C.stage st.castSucc p) =
      (actualSlotsV2_BAUGD S).stageProj st (C.stage st.castSucc p) :=
    DFunLike.congr_fun (stageQ_starProjection_BAUGD (Φ := actualSlotsV2_BAUGD S) st) _
  refine mem_cfs15Omega_of_mem_C15 hx ?_
  rw [hπy, mem_ball, dist_eq_norm]
  linarith

/-- **Native scope** (D69-2): on an active slot and the plateau `ψ_st(g_st p) = 1`, the native
image `f_st⁰(p) = a_st(π_st g_st p)` lies in the native zero set `Z_st`. -/
theorem native_scope_V2_BAUGD (st : Fin 3)
    (O : Cfs15StageOutput (gafStageDim st) Kj (Ξ st) (cw st)
      ((actualSlotsV2_BAUGD S).stageCloud st) ((actualSlotsV2_BAUGD S).stageCloudEnlarged st)
      (DP.stageRadius st (Sg st)) (DP.stagePlane st))
    (h : C.slot st = .active O) (p : W.Carrier)
    (hψ : (actualSlotsV2_BAUGD S).cutoff st (C.stage st.castSucc p) = 1) :
    C.nativeStageMap_BIFc st p ∈
      cfs15ZeroSet_C15 (Ξ st) (DP.stageRadius st (Sg st)) (DP.stagePlane st) O.hI := by
  have hz : C.stage st.castSucc p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff st) :=
    subset_tsupport _ (Function.mem_support.mpr (by rw [hψ]; exact one_ne_zero))
  have hZ := O.ambient_mem (C.input_mem_omega_V2_BAUGD st p hz)
  have hZQ : O.Z ⊆ (actualSlotsV2_BAUGD S).stageQ st :=
    O.zeroSet_subset_stageQ _ (fun x hx => by
      obtain ⟨q', -, rfl⟩ := hx
      exact stageProj_mem_stageQ_BAUGD st _) (DP.plane_le_stageQ_BAUGD st)
  have hm : (C.slot st).map = O.ambient := by rw [h]; rfl
  have e := (C.native_plateau_V2_BAUGD st p hψ).trans (congrArg (fun f =>
    ((actualSlotsV2_BAUGD S).stageQ st).starProjection
      (f (((actualSlotsV2_BAUGD S).stageQ st).starProjection (C.stage st.castSucc p)))) hm)
  have e2 := Submodule.starProjection_eq_self_iff.mpr (hZQ hZ)
  exact (e.trans e2).symm ▸ hZ

/-- **The native / final split** (D69-2) for ANY sources in the plateau with
`base = Θ(f⁰(source))` and the no-merging embedding (the inputs of A4's G11). -/
def laterSplit_V2_BAUGD (source : Fin 3 → Set W.Carrier)
    (base : Fin 3 → Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
    (hplateau : ∀ st, ∀ p ∈ source st,
      (actualSlotsV2_BAUGD S).cutoff st (C.stage st.castSucc p) = 1)
    (hbase : ∀ st, base st = C.laterV2_BAUGD st '' (C.nativeStageMap_BIFc st '' source st))
    (hemb : ∀ st, Topology.IsEmbedding
      (fun x : C.nativeStageMap_BIFc st '' source st => C.laterV2_BAUGD st x)) :
    BoundaryLaterSplit_BIFc C source base where
  nativeBase := fun st => C.nativeStageMap_BIFc st '' source st
  later := C.laterV2_BAUGD
  native_image_eq := fun _ => rfl
  native_scope := fun st O h => by
    rintro _ ⟨p, hp, rfl⟩
    exact C.native_scope_V2_BAUGD st O h p (hplateau st p hp)
  base_eq := hbase
  final_factor := C.final_factor_V2_BAUGD
  later_last := rfl
  later_isEmbedding := hemb
  later_contDiffAt := fun st y hy => by
    obtain ⟨p, -, rfl⟩ := hy
    exact C.later_contDiffAt_V2_BAUGD st p
  later_retains := C.later_retains_V2_BAUGD

end BoundaryGaf02Chain

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- The final stage maps `f_j = π_j ∘ E` are continuous on `W`. -/
theorem continuous_stageMap_V2_BAUGD (st : Fin 3) : Continuous (C.toChain.stageMap st) :=
  ((actualSlotsV2_BAUGD S).stageProj st).continuous.comp (C.stage_smooth_BAUGD 3).continuous

/-- **Properness for free on the compact `W`**: with the whole-preimage source equalities, every
compact `Kc ⊆ B_j` has compact `X_j ∩ f_j⁻¹(Kc)`. -/
theorem proper_of_source_eq_V2_BAUGD (source : Fin 3 → Set W.Carrier)
    (base : Fin 3 → Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
    (h0 : source 0 = C.toChain.stageMap 0 ⁻¹' base 0)
    (h1 : source 1 = C.toChain.stageMap 1 ⁻¹' base 1 ∩ {p | C.toChain.heightRatio p ≤ 4 * Δ})
    (h2 : source 2 = C.toChain.stageMap 2 ⁻¹' base 2) :
    ∀ st, ∀ Kc ⊆ base st, IsCompact Kc →
      IsCompact (source st ∩ C.toChain.stageMap st ⁻¹' Kc) := by
  have hT : IsClosed {p : W.Carrier | C.toChain.heightRatio p ≤ 4 * Δ} :=
    isClosed_le C.continuous_heightRatio_BAUGD continuous_const
  have key : ∀ (st : Fin 3) (Kc Bb : Set (BoundaryAmbient_BIF S.IntTag_BAUGA
      (Fin S.packet.cusp.count))), Kc ⊆ Bb → IsCompact Kc →
      IsClosed (C.toChain.stageMap st ⁻¹' Kc) ∧
        C.toChain.stageMap st ⁻¹' Bb ∩ C.toChain.stageMap st ⁻¹' Kc =
          C.toChain.stageMap st ⁻¹' Kc := fun st Kc Bb hB hcomp =>
    ⟨hcomp.isClosed.preimage (C.continuous_stageMap_V2_BAUGD st),
      inter_eq_right.mpr (preimage_mono hB)⟩
  intro st
  fin_cases st
  · intro Kc hKc hcomp
    obtain ⟨hcl, he⟩ := key 0 Kc (base 0) hKc hcomp
    change IsCompact (source 0 ∩ C.toChain.stageMap 0 ⁻¹' Kc)
    rw [h0, he]
    exact hcl.isCompact
  · intro Kc hKc hcomp
    obtain ⟨hcl, he⟩ := key 1 Kc (base 1) hKc hcomp
    change IsCompact (source 1 ∩ C.toChain.stageMap 1 ⁻¹' Kc)
    rw [h1, inter_right_comm, he]
    exact (hcl.inter hT).isCompact
  · intro Kc hKc hcomp
    obtain ⟨hcl, he⟩ := key 2 Kc (base 2) hKc hcomp
    change IsCompact (source 2 ∩ C.toChain.stageMap 2 ⁻¹' Kc)
    rw [h2, he]
    exact hcl.isCompact

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
