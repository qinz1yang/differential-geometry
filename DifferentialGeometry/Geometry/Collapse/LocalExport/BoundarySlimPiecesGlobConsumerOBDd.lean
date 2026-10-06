import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimPiecesGlobOBDd
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeComponentModelsEIMExits

/-!
# Consumer of the global form of the boundary slim pieces (lane S-BD2d2, `_OBDd`), group G10g

**`BoundaryGaf02ChainE.exists_slim_edgeModels_glob_OBDd`**: the `slim` and `edgeModels` fields of
`BoundaryLandingExits74b` together with the three end clauses the junction facts consume
(S-BD2e: `hnew`, `hfree`, `hend`), in exactly their shapes on the pieces `Sl.pieces`:

* `hnew`: every new end has `endFn en y = a (f₃ y)` with `a` smooth on the ambient base space;
* `hfree`: the end set of a new end misses `∂M₁ = frontier (regionM1 zero cusp)`;
* `hend`: every `x ∈ slimSet ∩ ∂M₁` lies in the end set of a SHARED end.
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
/-- **The `slim` and `edgeModels` fields with the end clauses `hnew`, `hfree`, `hend`.** -/
theorem exists_slim_edgeModels_glob_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (zc : BoundaryZeroCuspExit74b C.toChain dec) (P : BoundaryStageGeometry74b zc)
    (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (F : EdgeCutFacts74 P.stageGeometry P.cut) :
    ∃ (Sl : SlimCutPieces74 P.stageGeometry P.cut)
      (_ : EdgeComponentModels (edgeBundle74 P.stageGeometry P.cut F)),
      (∀ en : Sl.pieces.NewEnd,
        ∃ a : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ,
          ContDiff ℝ ∞ a ∧ ∀ y, Sl.pieces.endFn en y = a (C.toChain.stageMap 2 y)) ∧
      (∀ e : Sl.pieces.NewEnd, ∀ x ∈ Sl.pieces.endSet e.1,
        x ∉ frontier (regionM1 P.stageGeometry.zero P.stageGeometry.cusp)) ∧
      (∀ x ∈ P.cut.slimSet ∩ frontier (regionM1 P.stageGeometry.zero P.stageGeometry.cusp),
        ∃ (e : Sl.pieces.End) (F' : NeighbourFace P.stageGeometry.zero P.stageGeometry.cusp),
          Sl.pieces.endKind e = some F' ∧ x ∈ Sl.pieces.endSet e) := by
  obtain ⟨M⟩ := edgeBundle74_models_EIM P.stageGeometry P.cut F
  obtain ⟨N, γ', Xe, -, -, -, -, -, h1, h2, -, -, h3⟩ :=
    C.exists_slimCutPieces_glob_OBDd dec zc P hεr hrd hrd4 hrdc hprem hθ
  refine ⟨slimCutPieces_of_exit74 Xe, M, h2, fun e x hx hxf => ?_, h3⟩
  obtain ⟨i, -, hs, hk⟩ := h1 e.1
  have hx' := hs ▸ hx
  have hxf' : x ∈ frontier C.toChain.M₁_BIFc := (C.regionM1_eq_OBD zc) ▸ hxf
  exact (hk.1 e.2) (hx'.2 ▸ ⟨x, ⟨hxf', hx'.1⟩, rfl⟩)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
