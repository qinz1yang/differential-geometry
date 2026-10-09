import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEdpE
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEZComplete

/-!
# The rows' source on the FINAL family C14Z: `R ⟶ P_Z ⟶ CE_R` (review 71 D71-3 / D71-14)

Lane C14-REG-CHAIN, G9 (re-base of G7a on `LocalChartPacketsC14Z`). The ONE source of the closed
rows at a register `R` keeps the ORIGINAL final-family packet `P_Z : LocalChartPacketsC14Z` of the
register's realization (`exists_closed_realization_C14Z_RGC`) and builds the chain on its forgetful
projection `P_Z.toLocalChartPacketsC14` (D71-3: never a `C14` packet and a `C14Z` packet from two
existence calls):

* `ClosedChainEZRowsSource_RGC K R M δ ε_r Λ_z`: the C14Z instance `F` (with `F.family = P_Z`) and
  `CE_R : Gaf02ChainEJA F.family.toLocalChartPacketsC14 K (Ξ_j(Γ_j)) Γ Σ e c (stageCwAt_V4C R.stage)
  (registerCadj_RGC K)` on `R`'s own stage data;
* `toE_RGC`: its G7a source (`F.toC14D_RGC`, the SAME chain), so every G7a / G7c accessor and fact
  (`adj = CE_R.toChain.E`, `scale`, `height = A/s`, `edge_height_RGC`, `rim_rank_RGC`, …) applies
  verbatim; `familyZ_RGC` (the kept `P_Z`), `adj_eq_RGC`, `scale_eq_RGC`;
* inhabitant `exists_closedChainEZRowsSource_RGC` at the strategy of
  `register_yields_chainEJAZ_RGC`.

The bases object `B_R = Gaf02Bases CE_R.toChain CE_R.rough` (lane C14-BASESb) is added by the
extension G7b (frozen shape in the lane's scratch), on THIS source.
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

/-- **The ONE source of the closed rows at a register, on the final family C14Z** (D71-3, D71-14):
the C14Z instance of the register's realization and the enhanced chain with (JA) on the register's
own stage data, built on the instance's forgetful projection to `LocalChartPacketsC14`. -/
structure ClosedChainEZRowsSource_RGC (K : ℕ) {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} (M : ClosedModel W g) (δ εr Λz : ℝ) where
  /-- The instance of the FINAL family `LocalChartPacketsC14Z` at `R`'s values. -/
  F : ClosedFamilyInstanceC14ZV4 K R M δ εr Λz
  /-- The chain on the enhanced planes with (JA), on `R`'s own stage data, built on `P_Z`'s
  projection to `LocalChartPacketsC14`. -/
  chain : Gaf02ChainEJA F.family.toLocalChartPacketsC14 K
    (fun j => (earlyDataSharedV4 K).Ξ j (R.stage.Γ j)) R.stage.Γ R.stage.Sig R.stage.e R.stage.c
    (stageCwAt_V4C R.stage) (registerCadj_RGC K)

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-- The G7a source of the C14Z source: the C14D projection of the SAME instance and the SAME
chain. -/
def toE_RGC (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    ClosedChainERowsSource_RGC K R M δ εr Λz where
  F := S.F.toC14D_RGC
  chain := S.chain

/-- The kept final-family packet `P_Z` (D71-3). -/
def familyZ_RGC (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    LocalChartPacketsC14Z M.X M.gX M.hmetric S.F.ρ S.F.ρ_pos R.later.scale.Λ R.β R.later.excl.Δ
      R.later.err.co.qs K R.later.err.co.qe R.later.err.bd.μ R.later.split.b R.later.err.s
      R.later.err.wk.b' R.later.err.wk.s' R.later.err.co.ε R.later.circle.γc R.later.circle.βc
      R.later.Lmax R.later.err.bd.τ R.later.circle.γ δ εr R.later.err.co.e₀ R.later.split.T₀
      R.later.split.V R.later.err.co.ve R.later.err.co.ζ Λz M.orientation_RGC :=
  S.F.family

/-- The chain is built on the kept packet's projection (no second packet). -/
theorem chain_packet_RGC (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    S.toE_RGC.F.family.toLocalChartPacketsC14 = S.familyZ_RGC.toLocalChartPacketsC14 :=
  rfl

/-- `adj = CE_R.E`. -/
theorem adj_eq_RGC (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    S.toE_RGC.toRowsSource_RGC.adj = S.chain.toChain.E :=
  rfl

/-- `s = CE_R.scale`. -/
theorem scale_eq_RGC (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    S.toE_RGC.toRowsSource_RGC.scale = S.chain.toChain.scale :=
  rfl

end ClosedChainEZRowsSource_RGC

/-- **Inhabitant of the C14Z rows' source** (consumer): on every closed standing sequence there is a
strategy refining `closedStrategyCompleteV4C`, with the validity record and PR10's binding, at which
every register has, on every member of its tail (a nonempty model), for every base point, a source
`ClosedChainEZRowsSource_RGC` whose chain has that base point. -/
theorem exists_closedChainEZRowsSource_RGC (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
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
          ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ := by
  obtain ⟨T, hv, hTU, -, hNb, hcw, hR⟩ := register_yields_chainEJAZ_RGC K hK A hA Wseq gseq hf hg
  refine ⟨T, hTU, hv, hNb, hcw, fun R => ?_⟩
  obtain ⟨-, εr, -, Λz, δc, -, -, ht⟩ := hR R
  refine ⟨εr, δc, Λz, fun m hm => ?_⟩
  obtain ⟨M, F, -, -, -, -, -, -, hchain⟩ := ht m hm
  have : ConnectedSpace (Wseq m).Carrier := (hf m).connected
  refine ⟨M, ⟨M.ψ.symm (Classical.arbitrary (Wseq m).Carrier)⟩, fun x₀ => ?_⟩
  obtain ⟨C, hC, -⟩ := hchain x₀
  exact ⟨⟨F, C⟩, hC⟩

end DifferentialGeometry.Geometry.Collapse
