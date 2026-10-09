import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCompactSlimBundleBCF

/-!
# Consumer of BCF01.a's whole-fibre restriction (lane B-BCF134)

`BoundaryActualDecomposition.slim_piece_bundle_BCF`: on the actual decomposition of a chain, the
slim piece is the union of the whole slim fibres over `K₃ ∩ D₃`, its base is exactly `K₃ ∩ D₃`, and
it is compact.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
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
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}

/-- **Consumer**: BCF01.a's slim piece on the actual decomposition. -/
theorem BoundaryActualDecomposition.slim_piece_bundle_BCF (dec : BoundaryActualDecomposition C) :
    dec.slim.piece = ⋃ y ∈ dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIF dec.zero,
        dec.bases.fibre 2 y ∧
      C.stageMap 2 '' dec.slim.piece = dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIF dec.zero ∧
      IsCompact dec.slim.piece :=
  ⟨dec.slim.piece_eq_iUnion_fibre_BCF, dec.slim.stageMap_image_piece_BCF,
    dec.slim.isCompact_piece_BCF⟩

end DifferentialGeometry.Geometry.Collapse
