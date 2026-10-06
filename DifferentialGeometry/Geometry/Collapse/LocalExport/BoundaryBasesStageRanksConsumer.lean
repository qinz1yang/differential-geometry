import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesStageRank

/-!
# A4 / G11 (lane S-BASES-PORT), group G2: consumer of the rank equalities

`BoundaryGaf02ChainE.stage_ranks_BBP` assembles the three `rank_eq` statements of the FINAL stage
maps (`rank Df_st = k_st = 2, 1, 1`) on the original plateau of every chart of every stage, with
the register premises as explicit hypotheses (`β₂ ≤ 10⁻⁷`, `γ ≤ 1/2`; `σ_c ≤ 1/4`,
`b ≤ 1/(1000Δ)`). This is the pointwise content of the `rank_eq` field of
`BoundaryGaf02BasesCore_BIFc` before the sources are defined.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic

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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
    Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

/-- The rank of the final stage map `f_st` at a point (as in the `rank_eq` field). -/
abbrev stageRankAt_BBP (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj) (st : Fin 3)
    (p : W.Carrier) : ℕ :=
  Module.finrank ℝ (LinearMap.range
    ((mvfderiv W.model (C.toChain.stageMap st) p :
        TangentSpace W.model p →L[ℝ]
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
      TangentSpace W.model p →ₗ[ℝ]
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))

/-- **Consumer of G2**: `rank Df_st = k_st` on the original plateaus of all three stages. -/
theorem BoundaryGaf02ChainE.stage_ranks_BBP
    (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
    (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2) (hσ : σc ≤ 1 / 4)
    (hb : b ≤ 1 / (1000 * Δ)) :
    (∀ (j : S.CircleIdx_BAUGD) (q : W.pieceInterior ⊤),
      (letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1) →
      ‖S.circleEta_BIF j.1 q‖ < 6 → stageRankAt_BBP C 0 q.val = 2) ∧
    (∀ (j : S.EdgeIdx_BAUGD) (q : W.pieceInterior ⊤),
      (letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1) →
      |S.edgeEta_BIF j.1 q| < 6 * Δ → S.edgeHeightRaw q < 6 * Δ →
      stageRankAt_BBP C 1 q.val = 1) ∧
    (∀ (j : S.SlimIdx_BAUGD) (q : W.pieceInterior ⊤),
      (letI := inducedMetricSpace S.completion.metric;
        dist q j.1 < 1000000 * Δ * S.rho j.1) →
      |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ) → stageRankAt_BBP C 2 q.val = 1) :=
  ⟨fun j _ hq hη => C.stage_rank_eq_circle_BBP hβ2 hγ j hq hη,
    fun j _ hq hη hh => C.stage_rank_eq_edge_BBP hσ hb j hq hη hh,
    fun j _ hq hη => C.stage_rank_eq_slim_BBP j hq hη⟩

end DifferentialGeometry.Geometry.Collapse
