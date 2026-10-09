import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceDecompositionV2
import DifferentialGeometry.Topology.Surface.Recognition.EmbeddedFacePartitionBCF

/-!
# BCF03 G7' on the v2 objects: the face counts (lane B-BCF134; text v3 §G G7')

Text v3 G7' `bcf03_counts_BCF03` ("one line from G7 and FC40"): for every component `Y` of `∂M₂` and
EVERY embedded face partition of `Y` (`EmbeddedFacePartition_BCF`, B-BCF134 G5), a sphere face has
exactly two horizontal disks and a torus face none. The counts hold for any partition of any face, so
the frozen hypotheses `WF`, `Z`, `er` are not needed (strengthening). The existence of the partition
for the actual faces (G7 proper) waits for G6 (`bcf02_pieces_BCF02`, BCF2-K / lane G).

* `BoundaryCompactSlimChoiceV2.bcf03_counts_BCF03` (G7');
* consumer `BoundaryActualDecompositionV2.bcf03_counts_dec_BCF03` (every v2 decomposition).
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
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}

/-- **G7' BCF03 (text v3), strengthened**: on every component of `∂M₂`, every embedded face partition
has two disks on a sphere face and none on a torus face. -/
theorem BoundaryCompactSlimChoiceV2.bcf03_counts_BCF03 {Bs : BoundaryGaf02BasesV2 C}
    (Kc : BoundaryCompactSlimChoiceV2 Bs) :
    ∀ x ∈ frontier Kc.M₂, ∀ P : Surface.EmbeddedFacePartition_BCF
        (connectedComponentIn (frontier Kc.M₂) x),
      (Nonempty (connectedComponentIn (frontier Kc.M₂) x ≃ₜ SphereTwo) → P.diskCount = 2) ∧
        (Nonempty (connectedComponentIn (frontier Kc.M₂) x ≃ₜ Circle × Circle) →
          P.diskCount = 0) :=
  fun _ _ P => ⟨fun ⟨φ⟩ => P.diskCount_eq_two_of_sphere φ, fun ⟨φ⟩ => P.diskCount_eq_zero_of_torus φ⟩

/-- **Consumer**: the counts on every v2 decomposition. -/
theorem BoundaryActualDecompositionV2.bcf03_counts_dec_BCF03 (dec : BoundaryActualDecompositionV2 C) :
    ∀ x ∈ frontier dec.slim.M₂, ∀ P : Surface.EmbeddedFacePartition_BCF
        (connectedComponentIn (frontier dec.slim.M₂) x),
      (Nonempty (connectedComponentIn (frontier dec.slim.M₂) x ≃ₜ SphereTwo) → P.diskCount = 2) ∧
        (Nonempty (connectedComponentIn (frontier dec.slim.M₂) x ≃ₜ Circle × Circle) →
          P.diskCount = 0) :=
  dec.slim.bcf03_counts_BCF03

end DifferentialGeometry.Geometry.Collapse
