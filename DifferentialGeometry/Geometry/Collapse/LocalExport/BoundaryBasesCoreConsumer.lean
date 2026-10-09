import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBasesCore

/-!
# A4 / G11 (lane S-BASES-PORT2), group G3a: consumer of the BASES core

`BoundaryGaf02ChainE.laterSplit_basesCore_BBP`: the core's sources and bases carry the later
split `BoundaryLaterSplit_BIFc` (G10's `laterSplit_V2_BAUGD`) as soon as `Θ_st` embeds the native
bases; the embedding is the one clause of the G11 target not proved here (CGP07 one-sheet), so it
is the explicit argument `hemb` of this consumer.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
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

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **Consumer**: the later split on the core's sources and bases, given the embedding of `Θ_st`
on the native bases. -/
theorem laterSplit_basesCore_BBP
    (hemb : ∀ st, IsEmbedding (fun x : C.toChain.nativeStageMap_BIFc st '' C.baseSource_BBP st =>
      C.toChain.laterV2_BAUGD st x)) :
    Nonempty (BoundaryLaterSplit_BIFc C.toChain C.baseSource_BBP C.baseSet_BBP) :=
  ⟨C.toChain.laterSplit_V2_BAUGD C.baseSource_BBP C.baseSet_BBP
    (fun st _ hp => C.baseSource_plateau_BBP st hp) (fun st => C.baseSet_eq_later_native_BBP st)
    hemb⟩

include C in
/-- The core's source and base are the `baseSource_BBP` / `baseSet_BBP` of the chain. -/
theorem basesCore_source_base_BBP (hβ2 : β 2 ≤ 1 / 10000000) (hγ : γ ≤ 1 / 2)
    (hσ : σc ≤ 1 / 4) (hb : b ≤ 1 / (1000 * Δ)) :
    (C.basesCore_BBP hβ2 hγ hσ hb).source = C.baseSource_BBP ∧
      (C.basesCore_BBP hβ2 hγ hσ hb).base = C.baseSet_BBP :=
  ⟨rfl, rfl⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
