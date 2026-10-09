import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimEndsRel3OBDd
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeComponentModelsEIMExits

/-!
# Consumer of the boundary slim pieces (lane S-BD2d2, `_OBDd`), group G10f

**`BoundaryGaf02ChainE.exists_slim_edgeModels_OBDd`**: the two fields `slim` and `edgeModels` of
`BoundaryLandingExits74b` at once, in their field shapes `SlimCutPieces74 P.stageGeometry P.cut` and
`EdgeComponentModels (edgeBundle74 P.stageGeometry P.cut F)` (`F : EdgeCutFacts74` of the edge
facts `edgeCutFacts_OBD`), with the `rel3` end data exposed on the slim pieces:

* every end `e` of the slim pieces is the whole slim fibre `X₃ ∩ f₃⁻¹{y}` of some base point
  `y ∈ B₃`, and `e` is a new end iff `y` is not a face point `f₃(∂M₁ ∩ X₃)`;
* every new end has its defining function `x ↦ e (f₃ x)` with `e` smooth on an open set `Ne` of the
  ambient base space containing `f₃(endNear)`.
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
/-- **The `slim` and `edgeModels` fields of `BoundaryLandingExits74b`**, with the `rel3` end data. -/
theorem exists_slim_edgeModels_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (zc : BoundaryZeroCuspExit74b C.toChain dec) (P : BoundaryStageGeometry74b zc)
    (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (F : EdgeCutFacts74 P.stageGeometry P.cut) :
    ∃ (Sl : SlimCutPieces74 P.stageGeometry P.cut)
      (_ : EdgeComponentModels (edgeBundle74 P.stageGeometry P.cut F)),
      (∀ e : Sl.pieces.End, ∃ y ∈ dec.bases.base 2, Sl.pieces.endSet e = dec.bases.fibre 2 y ∧
        (Sl.pieces.endKind e = none ↔ y ∉ C.toChain.stageMap 2 ''
          (frontier C.toChain.M₁_BIFc ∩ dec.bases.source 2))) ∧
      ∀ en : Sl.pieces.NewEnd,
        ∃ (Ne : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
          (e : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
          IsOpen Ne ∧ ContDiffOn ℝ ∞ e Ne ∧
          (∀ y ∈ (Sl.pieces.endNear en : Set W.Carrier), C.toChain.stageMap 2 y ∈ Ne) ∧
          ∀ y ∈ (Sl.pieces.endNear en : Set W.Carrier),
            Sl.pieces.endFn en y = e (C.toChain.stageMap 2 y) := by
  obtain ⟨M⟩ := edgeBundle74_models_EIM P.stageGeometry P.cut F
  obtain ⟨N, γ', Xe, -, -, -, -, h1, h2, -, -⟩ :=
    C.exists_slimCutPieces_rel3_OBDd dec zc P hεr hrd hrd4 hrdc hprem hθ
  refine ⟨slimCutPieces_of_exit74 Xe, M, fun e => ?_, h2⟩
  obtain ⟨i, -, hs, hk⟩ := h1 e
  exact ⟨(γ' i).toFun (iccEnd e.1.2), (γ' i).mapsTo (iccEnd e.1.2).2, hs, hk⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
