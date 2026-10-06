import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleBaseFacesBCF
import DifferentialGeometry.Topology.Ehresmann.FibreTubeG6C

/-!
# The tube lemma on the actual circle base (lane O-G6C, G2 step L1)

`BoundaryGaf02ChainE.exists_open_circleFibre_subset_G6C`: on the whole-fibre layer v2b, every open
set of `W` containing the whole circle fibre of `y ∈ B₀` contains the whole circle fibres of all
base points near `y` (circle charts `WF.circle_chart`, compact fibre `Circle`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **Tube lemma on the circle base**: whole fibres over base points near `y` stay in any open
neighbourhood of the whole fibre of `y`. -/
theorem exists_open_circleFibre_subset_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Bs.base 0)
    {U : Set W.Carrier} (hU : IsOpen U) (hfib : Bs.fibre 0 y ⊆ U) :
    ∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen O ∧ y ∈ O ∧
      ∀ y' ∈ O ∩ Bs.base 0, Bs.fibre 0 y' ⊆ U := by
  obtain ⟨σ, φ, O, h0, -, hσ, -, hO, hrange, hφ, hr, hf⟩ := C.circleChart_raw_BCF WF hy
  exact exists_open_fibre_subset_of_chart_G6C h0 hσ hO hrange hφ.isEmbedding.continuous hr hf hU
    hfib

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
