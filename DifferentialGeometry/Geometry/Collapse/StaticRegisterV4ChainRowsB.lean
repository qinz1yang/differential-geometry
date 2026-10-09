import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsEZ
import DifferentialGeometry.Geometry.Fibration.ActualStageChainBasesApplications

/-!
# `B_R`: the ONE bases object of the closed rows' source (draft 74, D74-2; D66-8; D71-13)

Lane C14-REG-CHAIN, G7b (by C14-REG-CHAINc). The frozen route of draft 74 is
`(P_Z, Ĉ_R) → B_R → actual cut choice + smooth exits on the SAME chain → FC39RowsV2`. Here
`B_R` is fixed on the C14Z source `S : ClosedChainEZRowsSource_RGC K R M δ ε_r Λ_z` (G9):

* `ClosedBases74 S := Gaf02Bases S.chain.toChain S.chain.rough` (D74-2, the D71-13 shape: the
  bases object indexed by the ACTUAL chain of the source and its OWN rough data); every later
  head of draft 74 takes `(S) (B : ClosedBases74 S)`;
* `ClosedChainEZRowsSource_RGC.bases74 S`: the deterministic bases object of the source,
  `S.chain.bases_BAS` (lane C14-BASESc's producer needs nothing besides the chain and its rough
  data, so no threshold is added to register V4's slots and no second chain or stage choice is
  made — `gaf02_bases_row_BAS`'s own existential stage constants are NOT used);
* `ClosedBases74.stageMap_ident_R74` (D66-8 identification, frozen name of G7b): for every
  bases object, `π_j ∘ E = Θ_j ∘ f_j` at EVERY point, where `π_j ∘ E` is the rows source's own
  `stageMap j` (G5 / G7a accessor through `toE_RGC`);
* `ClosedBases74.final_mapsTo_R74`, `ClosedBases74.fibre_eq_R74`: `π_jE(U_j) ⊆ W_j` on FC33's
  threshold-5 domains and (RF) on the carriers `D_j`, read off `B`;
* consumer `register_yields_bases_R74`: at the strategy of `register_yields_chainEJAZ_RGC`, every
  register has on every tail member, for every base point, a source with that base point and a
  bases object on the source's own chain (with the identification and `π_jE(U_j) ⊆ W_j`).

Deviation from the 14:1x frozen shape (recorded in the lane state): D74-2 takes precedence, so
`B` is a separate argument of type `ClosedBases74 S`, not a field of an extension structure.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **`B_R`** (D74-2): the type of bases objects of the closed rows' source `S` — lane
C14-BASES's `Gaf02Bases` on the source's own chain `S.chain.toChain` and its own rough data. -/
abbrev ClosedBases74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) : Type :=
  Gaf02Bases S.chain.toChain S.chain.rough

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-- **The bases object of the source** (deterministic; D66-8 "ONE bases object"): lane
C14-BASESc's producer applied to the source's own enhanced chain. -/
def bases74 (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) : ClosedBases74 S :=
  S.chain.bases_BAS

end ClosedChainEZRowsSource_RGC

namespace ClosedBases74

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
  {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz}

/-- **D66-8 identification** (frozen name of G7b): the rows source's final stage map `π_j ∘ E`
equals `Θ_j ∘ f_j` (BASES' later transport after the native stage map) at EVERY point. -/
theorem stageMap_ident_R74 (B : ClosedBases74 S) (j : Fin 3) (p : M.X) :
    S.toE_RGC.toRowsSource_RGC.stageMap j p =
      S.chain.toChain.Θ_BAS j (S.chain.toChain.stageMap_BAS j p) :=
  B.later.final_factor j p

/-- `π_jE(U_j) ⊆ W_j` on FC33's exact threshold-5 domain, read off the bases object. -/
theorem final_mapsTo_R74 (B : ClosedBases74 S) (j : Fin 3) :
    MapsTo (S.toE_RGC.toRowsSource_RGC.stageMap j)
      (gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets j)
      (S.chain.toChain.finalBase_BAS j) :=
  B.later.mapsTo_final j

/-- (RF) read off the bases object: on the carrier `D_j`, the final fibre over `Θ_j w₀` is the
native fibre over `w₀` (`w₀` in the marked base). -/
theorem fibre_eq_R74 (B : ClosedBases74 S) {j : Fin 3}
    {w₀ : BlockSpace (fun _ : CGPTag S.F.family.toLocalChartPacketsC14.toLocalChartFamily
      S.F.family.toLocalChartPacketsC14.zero => ℝ²)}
    (hw₀ : w₀ ∈ S.chain.toChain.markedBase_BAS j) {p : M.X}
    (hp : p ∈ S.chain.toChain.carrier_BAS j) :
    S.toE_RGC.toRowsSource_RGC.stageMap j p = S.chain.toChain.Θ_BAS j w₀ ↔
      S.chain.toChain.stageMap_BAS j p = w₀ :=
  Gaf02Bases.fibre_eq_BAS B hw₀ hp

end ClosedBases74

/-- **Consumer: the register yields `B_R` on its own source** (D74-2, D66-8): on every closed
standing sequence there is a strategy refining `closedStrategyCompleteV4C` (validity record,
PR10's binding) at which every register has, on every tail member (a nonempty model), for every
base point, a C14Z rows source with that base point and a bases object on the source's OWN chain
(`S.bases74`), with `π_j ∘ E = Θ_j ∘ f_j` everywhere and `π_jE(U_j) ⊆ W_j`. -/
theorem register_yields_bases_R74 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      T.Nb = maxNb_V4C ∧ T.cw = maxCw_V4C ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, ∀ m, R.later.tail ≤ m →
        ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧ ∀ x₀ : M.X,
          ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            ∃ B : ClosedBases74 S, B = S.bases74 ∧
              (∀ j p, S.toE_RGC.toRowsSource_RGC.stageMap j p =
                S.chain.toChain.Θ_BAS j (S.chain.toChain.stageMap_BAS j p)) ∧
              ∀ j, MapsTo (S.toE_RGC.toRowsSource_RGC.stageMap j)
                (gafStageDomain5_BAS S.F.family.toLocalChartPacketsC14.toLocalChartPackets j)
                (S.chain.toChain.finalBase_BAS j) := by
  obtain ⟨T, hTU, hv, hNb, hcw, hR⟩ := exists_closedChainEZRowsSource_RGC K hK A hA Wseq gseq hf hg
  refine ⟨T, hTU, hv, hNb, hcw, fun R => ?_⟩
  obtain ⟨εr, δ, Λz, ht⟩ := hR R
  refine ⟨εr, δ, Λz, fun m hm => ?_⟩
  obtain ⟨M, hne, hS⟩ := ht m hm
  refine ⟨M, hne, fun x₀ => ?_⟩
  obtain ⟨S, hS0⟩ := hS x₀
  exact ⟨S, hS0, S.bases74, rfl, S.bases74.stageMap_ident_R74, S.bases74.final_mapsTo_R74⟩

end DifferentialGeometry.Geometry.Collapse
