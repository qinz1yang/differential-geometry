import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainAssembly
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryOriginalDerivativeBDFB
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageNativeOutputV3

/-!
# BCG03: the ENHANCED boundary chain and its producer A2-mk v3 (BAUG-Dd)

Targets of `TargetsBoundary-A-v3.lean.txt` (review 69 D69-5 (1)–(3); closed twins `Gaf02ChainE`,
`Gaf02ChainEJA`, `gaf02_chainE_mk_GAF8`):

* **`BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj`**: the chain on `DP` over the ACTUAL v2
  slot, the uniform register block `std` (stored once), the CHOICE validity of the SAME numbers,
  and BCG01's derivative clause `‖DF_∂ v‖ ≤ bder |v|_g` on all of `W` (original metric);
* **`exists_boundaryGaf02ChainE_mk_BAUGD`** (A2-mk v3): numbers FIRST (from `Kj`, `cadj` and the
  explicit early constants `b_cut = boundaryChainCutoffConst_BAUGD`, `b_der =
  boundaryDerivBound_BDFB`, `κ = cutoffKappa_BAUGP2`), THEN every carrier / member / parameter tuple,
  every supply with the uniform register block and EVERY `DP`: one enhanced chain on `DP`, all three
  slots ACTIVE (BAUG-C's native CFS15 outputs);
* inhabitant `exists_boundaryGaf02ChainE_of_empty_BAUGD` (empty stage families; all slots active).
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

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

/-- **`BoundaryGaf02ChainE`** (closed twins `Gaf02ChainE`, `Gaf02ChainEJA`): the chain on the
augmented data `DP` over the ACTUAL v2 slot, with the uniform register block `std` (stored once),
the CHOICE validity of its numbers (`Γ Sg eg` of `DP`, `Ξ c cw` of the chain, cap `cadj`) and the
derivative bound of the ORIGINAL map by `bder` on all of `W` (original metric `g`). -/
structure BoundaryGaf02ChainE {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax
    τ γ δ εr e T V vs ζ Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
    (DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg) (Kj : ℕ)
    (Ξ c cw : Fin 3 → ℝ) (bcut bder κ cadj : ℝ) : Type where
  /-- The chain on `DP`: numbers, the three slots, the cutoff bindings; `Ψ_j`, `g_j`, `E`. -/
  toChain : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder κ
  /-- The uniform register block (closed `Gaf02Chain.std`). -/
  std : 0 ≤ Λ ∧ 0 < Δ ∧ μ ≤ 1 / 100 ∧ τ ≤ 1 / 100 ∧ 100 * Δ * Λ ≤ 1 / 100 ∧ 0 ≤ V ∧ 0 < β 1 ∧
    0 < b ∧ e ≤ 1 / 10 ∧ 1 ≤ Δ ∧ 1000000 * Δ * Λ < 1 / 100000 ∧
    4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax ∧ e < 1 / 40 ∧ 1600 * (1000000 * Δ) ≤ T ∧
    σs ∈ Icc (0 : ℝ) 1 ∧ σc ∈ Icc (0 : ℝ) 1 ∧ γc ∈ Icc (0 : ℝ) 1 ∧ εr ∈ Icc (0 : ℝ) 1
  /-- The CHOICE validity of the SAME numeric choice. -/
  validity : BoundaryChainChoiceValidity_BAUGD Ξ Γ Sg eg c cw cadj
  /-- BCG01's derivative clause: `bder` bounds the differential of the ORIGINAL map on `W`. -/
  deriv_bound : ∀ (p : W.Carrier) (v : TangentSpace W.model p),
    ‖mvfderiv W.model S.boundaryOriginalMap p v‖ ≤ bder * Real.sqrt (g.inner p v v)

theorem boundaryDerivBound_nonneg_BAUGD : 0 ≤ boundaryDerivBound_BDFB := by
  have := one_le_boundaryProfileBound_BDFB
  unfold boundaryDerivBound_BDFB
  positivity

/-- **A2-mk v3** (assembler): numbers FIRST (from `Kj`, `cadj` and the explicit early constants),
THEN every carrier, member and parameter tuple, every supply with the uniform register block and
EVERY augmented data `DP` over the ACTUAL v2 slot: ONE enhanced chain on `DP`, every slot active
(D66-4: `.active` = a native CFS15 output). [closed: `gaf02_chainE_mk_GAF8`] -/
theorem exists_boundaryGaf02ChainE_mk_BAUGD (Kj : ℕ) {cadj : ℝ} (hcadj : 0 < cadj) :
    ∃ (Ξ Γ Sg eg c cw : Fin 3 → ℝ),
      BoundaryChainChoiceValidity_BAUGD Ξ Γ Sg eg c cw cadj ∧
      (∀ j, 0 < Ξ j ∧ Ξ j < 1 / 10 ∧ 0 < Sg j ∧ 128 * (Ξ j)⁻¹ * Sg j ≤ 1 / 5 ∧ 0 < c j ∧
        c j ≤ 1 / 512) ∧ c 0 ≤ c 1 ∧ c 1 ≤ c 2 ∧
      ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
        {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
        {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
        {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
        {B : NearlyCuspidalBoundary W g K δn}
        {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
        (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
          Λz θ W g δn n B oM),
        -- BEGIN register block (uniform)
        0 ≤ Λ → 0 < Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 →
        0 < b → e ≤ 1 / 10 → 1 ≤ Δ → 1000000 * Δ * Λ < 1 / 100000 →
        4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
        σs ∈ Icc (0 : ℝ) 1 → σc ∈ Icc (0 : ℝ) 1 → γc ∈ Icc (0 : ℝ) 1 → εr ∈ Icc (0 : ℝ) 1 →
        -- END register block
        ∀ DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg,
          ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw boundaryChainCutoffConst_BAUGD
              boundaryDerivBound_BDFB cutoffKappa_BAUGP2 cadj,
            ∀ st, ∃ O, C.toChain.slot st = .active O := by
  obtain ⟨Ξf, Ξ, Γ, Sg, eg, c, hj, hc01, hc12, hcw⟩ := boundaryChain_choice_V2_BAUGD Kj hcadj
    boundaryChainCutoffConst_nonneg_BAUGD cutoffKappa_pos_BAUGP2 boundaryDerivBound_nonneg_BAUGD
  have hΓ : ∀ j, 0 < Γ j := fun j =>
    ((hcw (fun _ => 0) (fun _ => le_rfl)).1.quality j).1
  have hnat := fun st : Fin 3 =>
    boundaryStage_output_V3_BAUGC (Kj := Kj) st (hΓ st) (hj st).2.2.2.1 (hj st).2.2.2.2.1
  let cw : Fin 3 → ℝ := fun st => Classical.choose (hnat st)
  have hcw0 : ∀ st, 0 ≤ cw st := fun st => (Classical.choose_spec (hnat st)).1
  refine ⟨Ξ, Γ, Sg, eg, c, cw, (hcw cw hcw0).1, fun j => ⟨(hj j).2.1, (hj j).2.2.1,
    (hj j).2.2.2.2.2.1, (hj j).2.2.2.2.2.2.1, (hj j).2.2.2.2.2.2.2.1, (hj j).2.2.2.2.2.2.2.2⟩,
    hc01, hc12, ?_⟩
  intro K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hΔ1 hLΛ hLmax he40 hT hσs hσc hγc hεr DP
  have hO : ∀ st, Nonempty (Cfs15StageOutput (gafStageDim st) Kj (Ξf st (Γ st)) (cw st)
      ((actualSlotsV2_BAUGD S).stageCloud st) ((actualSlotsV2_BAUGD S).stageCloudEnlarged st)
      (DP.stageRadius st (Sg st)) (DP.stagePlane st)) := fun st =>
    (Classical.choose_spec (hnat st)).2 DP.toBoundaryAugmentedData hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he
      Γ Sg eg rfl (hj st).2.2.2.2.2.1 (by rw [← (hj st).1]; exact (hj st).2.2.2.2.2.2.1)
      (DP.spec st)
  let σ : ∀ st, BoundaryStageSlot_BIF DP.toBoundaryAugmentedData st Kj (Ξ st) (Sg st) (cw st) :=
    fun st => .active ((hj st).1 ▸ (hO st).some)
  obtain ⟨C, hC⟩ := exists_chain_of_slots_BAUGD DP hΛ hΔ1 hLΛ hV hβ1 hb (le_max_left _ _)
    ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))
    (hcw cw hcw0).2 σ
  refine ⟨⟨C, ⟨hΛ, hΔ, hμ, hτ, hΔΛ, hV, hβ1, hb, he, hΔ1, hLΛ, hLmax, he40, hT, hσs, hσc, hγc, hεr⟩,
    (hcw cw hcw0).1, fun p v => S.toBoundarySupplyCore.norm_mvfderiv_boundaryOriginalMap_le_BDFB
      hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hΔ1 hLΛ hLmax he40 hT hσs hσc hγc hεr
      DP.toBoundaryAugmentedData.separated p v⟩, fun st => ⟨(hj st).1 ▸ (hO st).some, ?_⟩⟩
  rw [hC]

/-- **Inhabitant of the enhanced chain** (consumer of A2-mk v3; empty stage families, all slots
active): A2-mk's numbers, and for every supply with the uniform register block, the separated
branch and empty circle / `edgeB` / slim families, augmented data with the V3 specs on the actual v2
slot (BAUG-D G5) carrying an enhanced chain. NO non-empty-stage instance exists yet (D69-11). -/
theorem exists_boundaryGaf02ChainE_of_empty_BAUGD (Kj : ℕ) {cadj : ℝ} (hcadj : 0 < cadj) :
    ∃ (Ξ Γ Sg eg c cw : Fin 3 → ℝ), BoundaryChainChoiceValidity_BAUGD Ξ Γ Sg eg c cw cadj ∧
      ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
        {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
        {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
        {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
        {B : NearlyCuspidalBoundary W g K δn}
        {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
        (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
          Λz θ W g δn n B oM),
        0 ≤ Λ → 0 < Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 100 * Δ * Λ ≤ 1 / 100 → 0 ≤ V → 0 < β 1 →
        0 < b → e ≤ 1 / 10 → 1 ≤ Δ → 1000000 * Δ * Λ < 1 / 100000 →
        4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
        σs ∈ Icc (0 : ℝ) 1 → σc ∈ Icc (0 : ℝ) 1 → γc ∈ Icc (0 : ℝ) 1 → εr ∈ Icc (0 : ℝ) 1 →
        S.SeparatedCollarZero_BIF → (∀ st, S.stageCentres_BIF st = ∅) →
        ∃ DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg,
          Nonempty (BoundaryGaf02ChainE DP Kj Ξ c cw boundaryChainCutoffConst_BAUGD
            boundaryDerivBound_BDFB cutoffKappa_BAUGP2 cadj) := by
  obtain ⟨Ξ, Γ, Sg, eg, c, cw, hval, -, -, -, h⟩ := exists_boundaryGaf02ChainE_mk_BAUGD Kj hcadj
  refine ⟨Ξ, Γ, Sg, eg, c, cw, hval, ?_⟩
  intro K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W _ g δn n B oM S
    hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hΔ1 hLΛ hLmax he40 hT hσs hσc hγc hεr hsep hempty
  obtain ⟨DP⟩ := exists_boundaryAugmentedDataPV3_of_empty_BAUGD S hsep hempty Γ Sg eg
  obtain ⟨C, -⟩ := h S hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hΔ1 hLΛ hLmax he40 hT hσs hσc hγc hεr DP
  exact ⟨DP, ⟨C⟩⟩

end DifferentialGeometry.Geometry.Collapse
