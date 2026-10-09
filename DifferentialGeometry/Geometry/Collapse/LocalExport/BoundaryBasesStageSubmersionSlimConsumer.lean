import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesStageSubmersionSlim

/-!
# A4 / G11 (lane S-BASES-PORT), group G1b: consumer of the slim stage submersion

The family form of `BoundaryGaf02ChainE.stage_submersion_slim_final_BBP` that the BASES producer
quantifies over: every slim chart `j` and every point of its ORIGINAL threshold-`6` plateau.
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

/-- **Consumer of G1b**: on every slim plateau the final stage map `f₂ = π₂E`, read in the chart
coordinate `κ_j`, is a submersion (the slim clause of BASES `submersion`, final map). -/
theorem slim_stage_submersion_forall_BBP
    (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj) :
    ∀ (j : S.SlimIdx_BAUGD) (q : W.pieceInterior ⊤),
      (letI := inducedMetricSpace S.completion.metric;
        dist q j.1 < 1000000 * Δ * S.rho j.1) →
      |S.slimEta_BIF j.1 q| < 6 * (10 ^ 5 * Δ) →
      Surjective (mfderiv W.model 𝓘(ℝ, ℝ)
        (fun p => S.slimKappa_BBP j (C.toChain.stageMap 2 p)) q.val) :=
  fun j _ hq hη => C.stage_submersion_slim_final_BBP j hq hη

end DifferentialGeometry.Geometry.Collapse
