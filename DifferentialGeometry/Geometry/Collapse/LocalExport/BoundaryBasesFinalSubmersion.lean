import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesStageSubmersionSlim
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesStageSubmersionEdge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainBasesSplit

/-!
# A4 / G11 (lane S-BASES-PORT), group G2 (part 1): the FINAL stage submersions

Closed twin `final_submersion_{circle,edge,slim}_BAS` (`ActualStageChainFinalSubmersion.lean`) on
`C : BoundaryGaf02ChainE DP …`. The later embeddings `Θ_st` (G10, `laterV2_BAUGD`) keep the stage's
own chart blocks (`later_retains_V2_BAUGD`), so as FUNCTIONS `κ_j ∘ f_st = κ_j ∘ f_st⁰`
(`final_factor_V2_BAUGD`); the native submersions of `LE/BoundaryBasesStageSubmersion*.lean`
therefore give the final ones with the same plateaus and premises.

* `circleKappa_laterV2_BBP`, `edgeKappa_laterV2_BBP`: `κ_j ∘ Θ_st = κ_j` (circle, edge; for the
  slim stage `Θ₂ = id`, see `stage_submersion_slim_final_BBP`);
* `circle_kappa_final_eq_BBP`, `edge_kappa_final_eq_BBP`: the function equalities;
* `surjective_mfderiv_congr_BBP`: the generic transport along a function equality;
* **`final_submersion_circle_BBP`**, **`final_submersion_edge_BBP`**: `D(κ_j ∘ f_st)(q)` is onto on
  the original plateau (register premises as for the native ones).
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
/-- A surjective manifold derivative transports along an equality of functions (stated
generically, so that the codomain tangent spaces are compared only through the function
equality). -/
theorem surjective_mfderiv_congr_BBP {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f' : W.Carrier → F} (h : f = f') {x : W.Carrier}
    (hs : Function.Surjective (mfderiv W.model 𝓘(ℝ, F) f' x)) :
    Function.Surjective (mfderiv W.model 𝓘(ℝ, F) f x) := by
  subst h
  exact hs


namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- The later embedding `Θ₀` keeps the circle chart coordinate: `κ_j ∘ Θ₀ = κ_j`. -/
theorem circleKappa_laterV2_BBP (j : S.CircleIdx_BAUGD)
    (x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.circleKappa_BBP j (C.toChain.laterV2_BAUGD 0 x) = S.circleKappa_BBP j x := by
  have h := C.toChain.later_retains_V2_BAUGD 0 (.inl j) rfl x
  unfold BoundarySupplyCore.circleKappa_BBP
  simp only [smul_apply]
  unfold BoundarySupplyCore.circleVector_BAUGD
  simp only [blockVectorCLM_apply]
  rw [show (C.toChain.laterV2_BAUGD 0 x) (Sum.inl (Sum.inl j)) = x (Sum.inl (Sum.inl j)) from h]

include C in
/-- The later embedding `Θ₁` keeps the edge chart coordinate: `κ_j ∘ Θ₁ = κ_j`. -/
theorem edgeKappa_laterV2_BBP (j : S.EdgeIdx_BAUGD)
    (x : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) :
    S.edgeKappa_BBP j (C.toChain.laterV2_BAUGD 1 x) = S.edgeKappa_BBP j x := by
  have h := C.toChain.later_retains_V2_BAUGD 1 (.inr (.inr j)) rfl x
  unfold BoundarySupplyCore.edgeKappa_BBP
  simp only [smul_apply]
  unfold BoundarySupplyCore.edgeVector_BAUGD
  simp only [blockVectorCLM_apply, ContinuousLinearMap.comp_apply]
  rw [show (C.toChain.laterV2_BAUGD 1 x) (Sum.inl (Sum.inr (Sum.inr (Sum.inl j)))) =
    x (Sum.inl (Sum.inr (Sum.inr (Sum.inl j)))) from h]

include C in
/-- `κ_j ∘ f_0 = κ_j ∘ f_0⁰` (circle chart `j`), as functions. -/
theorem circle_kappa_final_eq_BBP (j : S.CircleIdx_BAUGD) :
    (fun p => S.circleKappa_BBP j (C.toChain.stageMap 0 p)) =
      fun p => S.circleKappa_BBP j (C.toChain.nativeStageMap_BIFc 0 p) := by
  funext p
  rw [C.toChain.final_factor_V2_BAUGD 0 p]
  exact C.circleKappa_laterV2_BBP j _

include C in
/-- `κ_j ∘ f_1 = κ_j ∘ f_1⁰` (edge chart `j`), as functions. -/
theorem edge_kappa_final_eq_BBP (j : S.EdgeIdx_BAUGD) :
    (fun p => S.edgeKappa_BBP j (C.toChain.stageMap 1 p)) =
      fun p => S.edgeKappa_BBP j (C.toChain.nativeStageMap_BIFc 1 p) := by
  funext p
  rw [C.toChain.final_factor_V2_BAUGD 1 p]
  exact C.edgeKappa_laterV2_BBP j _

/-- **G2, circle: the FINAL stage submersion** (closed `final_submersion_circle_BAS`): on the
circle plateau `D(κ_j ∘ f₀)` is onto `ℝ²` (`κ_j ∘ f₀ = κ_j ∘ f₀⁰` as functions). -/
theorem final_submersion_circle_BBP (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2)
    (j : S.CircleIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 200 * S.rho j.1)
    (hη : ‖S.circleEta_BIF j.1 q‖ < 6) :
    Surjective (mfderiv W.model 𝓘(ℝ, ℝ²)
      (fun p => S.circleKappa_BBP j (C.toChain.stageMap 0 p)) q.val) := by
  exact surjective_mfderiv_congr_BBP (C.circle_kappa_final_eq_BBP j)
    (C.stage_submersion_circle_BBP hβ2 hγ j hq hη)

/-- **G2, edge: the FINAL stage submersion** (closed `final_submersion_edge_BAS`). -/
theorem final_submersion_edge_BBP (hσ : σc ≤ 1 / 4) (hb' : b ≤ 1 / (1000 * Δ))
    (j : S.EdgeIdx_BAUGD) {q : W.pieceInterior ⊤}
    (hq : letI := inducedMetricSpace S.completion.metric;
      dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| < 6 * Δ) (hh : S.edgeHeightRaw q < 6 * Δ) :
    Surjective (mfderiv W.model 𝓘(ℝ, ℝ)
      (fun p => S.edgeKappa_BBP j (C.toChain.stageMap 1 p)) q.val) := by
  exact surjective_mfderiv_congr_BBP (C.edge_kappa_final_eq_BBP j)
    (C.stage_submersion_edge_BBP hσ hb' j hq hη hh)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
