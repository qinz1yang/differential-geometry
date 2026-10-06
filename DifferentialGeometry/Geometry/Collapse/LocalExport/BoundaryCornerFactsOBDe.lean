import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryHprimLabelsOBDe
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCornerConstOBDe
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageRimsOfPrimOBDe

/-!
# The corner facts at the endpoints of zero-face and cusp-front labels (lane S-BD2e, `_OBDe`)

Lane O-BD1 (by S-BD2e), group G11f consumer: for rows `R` over the produced stages, face facts `F`
and rim facts `G`, every endpoint whose horizontal label is a zero face or a cusp front (not a new
slim end) has the descent (`exists_cornerDescent_nonNew_OBDe`), the rank-two sign model and the
descended face equation (`hprim_zero_OBDe` / `hprim_cusp_OBDe` fed to
`exists_cornerRankDescended_of_primitives_OBDe`): all three fields of `CornerCutFacts74` at `e`.
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

section CornerFacts

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}
  (P : BoundaryStageGeometry74b zc) (R : StageCutRows74 P.stageGeometry P.cut)

include C in
/-- **`CornerCutFacts74` at an endpoint whose label is a zero face or a cusp front.** -/
theorem exists_cornerFacts_nonNew_OBDe (geom : BoundaryGeometricExports74b C.toChain dec)
    (cov : CutCoverFacts74 P.stageGeometry P.cut)
    (hι : ContMDiff (𝓡 1) 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) ∞
      P.ιedge)
    (F : JunctionFaceFacts74 P.stageGeometry P.cut R)
    (G : JunctionRimFacts74 P.stageGeometry P.cut R) (e : R.edge.EdgeEnd)
    (hlab : ∀ en : R.slimPieces.NewEnd, F.horizontal e ≠ .inr en) :
    Nonempty (CornerDescent74 F G e) ∧
      ∃ K : CornerRank74 F G e, Nonempty (CornerDescended74 K) := by
  obtain ⟨d⟩ := C.exists_cornerDescent_nonNew_OBDe P R F G e hlab
  refine ⟨⟨d⟩, ?_⟩
  rcases hF : F.horizontal e with ⟨nbr, hnbr⟩ | en
  · rcases nbr with ⟨i, Fm⟩ | ⟨bc, Fm, hFm⟩
    · obtain ⟨b, U, heU, hb, hbreg, hCU, N', hN'o, hrim, hNeq⟩ :=
        C.hprim_zero_OBDe P R geom cov hι F e i (by rw [hF]; rfl)
      exact exists_cornerRankDescended_of_primitives_OBDe R F G cov (C.hKR_OBDe geom P) e d b U
        heU hb hbreg hCU ⟨N', hN'o, hrim, hNeq⟩
    · obtain ⟨b, U, heU, hb, hbreg, hCU, N', hN'o, hrim, hNeq⟩ :=
        C.hprim_cusp_OBDe P R geom cov hι F e bc (by rw [hF]; rfl) (by rw [hF]; rfl)
      exact exists_cornerRankDescended_of_primitives_OBDe R F G cov (C.hKR_OBDe geom P) e d b U
        heU hb hbreg hCU ⟨N', hN'o, hrim, hNeq⟩
  · exact absurd hF (hlab en)

end BoundaryGaf02ChainE

end CornerFacts

end DifferentialGeometry.Geometry.Collapse
