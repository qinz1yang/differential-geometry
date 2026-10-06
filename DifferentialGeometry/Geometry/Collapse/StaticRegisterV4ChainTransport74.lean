import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCutChoice
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransport74

/-!
# D74-6 on the closed route: pieces and sets carried by the ONE `M.ψ`

Lane C14-REG-CHAIN (by C14-REG-CHAINc), G13 (closed consumer). Draft 74 §2.2: the closed rows are
built directly on `W.Carrier`; a chain piece `j : Q → M.X` (after ZSP02's ambient `Ψ`) becomes the
row piece with map `M.ψ ∘ j`, chain sets are pushed forward by `M.ψ`, chain functions are pulled
back by `M.ψ⁻¹`:

* `PieceEmbedding.ofModel74 M Q j …` (= `PieceEmbedding.ofComp74 … M.ψ`) with
  `ofModel74_range` (`range = M.ψ(range j)`, model boundary image `M.ψ(j(∂Q))`);
* `ClosedCutChoice74.transport_R74`: for a cut choice of the closed source, the D74-5 table's set
  identities on `W` are the `M.ψ`-images of the chain's actual sets (`slimSet`, `edgeSet`, `M₂`,
  `M₃`, `edgeSource`, `circleSource`) — relative interiors (`relInt_image_R74`) and frontiers
  (`image_frontier_R74`) commute with `M.ψ`, and the pulled-back final maps
  `q_j ∘ M.ψ⁻¹` have the `M.ψ`-images of the actual fibres as fibres (`preimage_symm_R74`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **The closed-route row piece** (draft 74 §2.2): a piece `j : Q → M.X` of the model carried to
`W` by the ONE `M.ψ`. -/
def PieceEmbedding.ofModel74 {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
    (M : ClosedModel W g) (Q : Type u) [TopologicalSpace Q] [ChartedSpace (EuclideanHalfSpace 3) Q]
    [IsManifold (𝓡∂ 3) ∞ Q] [CompactSpace Q] [T2Space Q] [SecondCountableTopology Q]
    [ConnectedSpace Q] (j : Q → M.X) (hj : ContMDiff (𝓡∂ 3) 𝓘(ℝ, E3) ∞ j)
    (hjb : ∀ q, Bijective (mfderiv (𝓡∂ 3) 𝓘(ℝ, E3) j q)) (hji : Injective j) :
    PieceEmbedding W :=
  PieceEmbedding.ofComp74 Q j hj hjb hji M.ψ

/-- The closed-route row piece has range `M.ψ(range j)` and model boundary image `M.ψ(j(∂Q))`. -/
theorem PieceEmbedding.ofModel74_range {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} (M : ClosedModel W g) (Q : Type u)
    [TopologicalSpace Q] [ChartedSpace (EuclideanHalfSpace 3) Q] [IsManifold (𝓡∂ 3) ∞ Q]
    [CompactSpace Q] [T2Space Q] [SecondCountableTopology Q] [ConnectedSpace Q] (j : Q → M.X)
    (hj : ContMDiff (𝓡∂ 3) 𝓘(ℝ, E3) ∞ j) (hjb : ∀ q, Bijective (mfderiv (𝓡∂ 3) 𝓘(ℝ, E3) j q))
    (hji : Injective j) :
    range (PieceEmbedding.ofModel74 M Q j hj hjb hji).map = M.ψ '' range j ∧
      pieceBoundary (PieceEmbedding.ofModel74 M Q j hj hjb hji) =
        M.ψ '' (j '' (𝓡∂ 3).boundary Q) :=
  PieceEmbedding.ofComp74_range Q j hj hjb hji M.ψ

/-- **D74-5/D74-6 set identities through `M.ψ`** for a cut choice of the closed source: the
relative interiors defining `M₂`, `M₃` and the frontiers commute with `M.ψ`, and the
pulled-back final maps `q_j ∘ M.ψ⁻¹` have the `M.ψ`-images of the actual fibres (whole
preimages) as fibres. -/
theorem ClosedCutChoice74.transport_R74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    (D : ClosedCutChoice74 S B) :
    M.ψ '' D.M₃ = M.ψ '' D.M₂ \ relInt (M.ψ '' D.M₂) (M.ψ '' D.edgeSet) ∧
      M.ψ '' frontier D.slimSet = frontier (M.ψ '' D.slimSet) ∧
      (∀ j (T : Set (BlockSpace (fun _ : CGPTag S.F.family.toLocalChartPacketsC14.toLocalChartFamily
          S.F.family.toLocalChartPacketsC14.zero => EuclideanSpace ℝ (Fin 2)))),
        (S.chain.toGaf02ChainE.cutQ_R74 j ∘ M.ψ.symm) ⁻¹' T =
          M.ψ '' (S.chain.toGaf02ChainE.cutQ_R74 j ⁻¹' T)) ∧
      M.ψ '' D.edgeSource = (S.chain.toGaf02ChainE.cutQ_R74 1 ∘ M.ψ.symm) ⁻¹' D.edgeBaseOpen ∧
      M.ψ '' D.circleSource =
        (S.chain.toGaf02ChainE.cutQ_R74 0 ∘ M.ψ.symm) ⁻¹' D.circleBaseOpen := by
  refine ⟨?_, ?_, fun j T => preimage_symm_R74 M.ψ _ T, ?_, ?_⟩
  · rw [relInt_image_R74, ← image_sdiff (f := M.ψ) M.ψ.injective]
    rfl
  · exact image_frontier_R74 M.ψ D.slimSet
  · exact (preimage_symm_R74 M.ψ _ D.edgeBaseOpen).symm
  · exact (preimage_symm_R74 M.ψ _ D.circleBaseOpen).symm

end DifferentialGeometry.Geometry.Collapse
