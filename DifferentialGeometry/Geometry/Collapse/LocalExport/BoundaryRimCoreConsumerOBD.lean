import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRimCoreOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageGeometryEmbeddedOBD

/-!
# Consumer of the rim core (lane S-BD2c, suffix `_OBD`), group G11a

For every zero / cusp exit the embedded stage geometry carries the edge cut facts, and for ANY
circle cut facts `G` of it the rim core of `JunctionRimFacts74` (`rimBase` smooth on `C₂` with
`rim c = fibre (rimBase c)`, and `edge_region`) holds.
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
/-- **The rim core on the produced stages**: for every zero / cusp exit there are stages, edge cut
facts `F`, such that every circle cut facts `G` admits the rim core. -/
theorem exists_stageGeometry_rimCore_OBD (dec : BoundaryActualDecompositionV2b C.toChain)
    (geom : BoundaryGeometricExports74b C.toChain dec)
    (hint : dec.bases.edgeParent ⊆ (W.interior : Set W.Carrier))
    (zc : BoundaryZeroCuspExit74b C.toChain dec) :
    ∃ (P : BoundaryStageGeometry74b zc) (F : EdgeCutFacts74 P.stageGeometry P.cut),
      ∀ G : CircleCutFacts74 P.stageGeometry P.cut,
        ∃ rimBase : (edgeBundle74 P.stageGeometry P.cut F).Base →
            (circleBundle74 P.stageGeometry P.cut G).Base,
          ContMDiffOn (𝓡 1) (𝓡 2) ∞ rimBase (edgeBundle74 P.stageGeometry P.cut F).cbase ∧
          (∀ c' ∈ (edgeBundle74 P.stageGeometry P.cut F).cbase,
            (edgeBundle74 P.stageGeometry P.cut F).rim c' =
              (circleBundle74 P.stageGeometry P.cut G).fibre (rimBase c')) ∧
          P.cut.edgeSet ∩ P.cut.M₃ = (edgeBundle74 P.stageGeometry P.cut F).vertical := by
  obtain ⟨P, -, hιe, hιc⟩ := C.exists_stageGeometry74b_embedded_OBD dec geom hint zc
  exact ⟨P, C.edgeCutFacts_OBD P hιe.contMDiff geom, fun G =>
    C.exists_rimCore_OBD P geom _ G hιe.contMDiff hιc⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
