import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersBaseOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageGeometryEmbeddedOBD

/-!
# Consumer of the base-level circle corners (lane S-BD2c, suffix `_OBD`), group G11b

For every zero / cusp exit the embedded stage geometry carries, at every frontier point of `C₁` in
the circle base, the corner model of G6c on the base manifold: one or two labelled faces with
`C₁ ∩ U = {φ_f ≤ 0}`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

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

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
/-- **The corner model of `C₁` on the circle base of the produced stages.** -/
theorem exists_stageGeometry_circleCorners_OBD (dec : BoundaryActualDecompositionV2b C.toChain)
    (geom : BoundaryGeometricExports74b C.toChain dec)
    (hint : dec.bases.edgeParent ⊆ (W.interior : Set W.Carrier))
    (zc : BoundaryZeroCuspExit74b C.toChain dec) :
    ∃ P : BoundaryStageGeometry74b zc,
      ∀ c' ∈ frontier (Subtype.val ⁻¹' P.cut.C₁ : Set P.cut.circleBaseOpen),
        ∃ U : TopologicalSpace.Opens P.cut.circleBaseOpen, c' ∈ U ∧
          ∃ (L : Finset (CircleFaceLabel74 dec.slim))
            (φ : CircleFaceLabel74 dec.slim → P.cut.circleBaseOpen → ℝ),
            1 ≤ L.card ∧ L.card ≤ 2 ∧ (Subtype.val ⁻¹' P.cut.C₁ : Set P.cut.circleBaseOpen) ∩ U =
              {b | b ∈ U ∧ ∀ f ∈ L, φ f b ≤ 0} := by
  obtain ⟨P, -, -, hιc⟩ := C.exists_stageGeometry74b_embedded_OBD dec geom hint zc
  refine ⟨P, fun c' hc' => ?_⟩
  obtain ⟨U, hU, L, φ, h1, h2, -, -, h5⟩ := C.circle_corners_base_OBD P geom
    (C.circle_cbase_compact_OBD P geom) hιc.contMDiff hc'
  exact ⟨U, hU, L, φ, h1, h2, h5⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
