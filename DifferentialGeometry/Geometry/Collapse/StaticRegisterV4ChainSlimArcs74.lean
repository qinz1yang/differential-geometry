import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimBundleEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainCutChoice
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCutChoice
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimArcPieces74

/-!
# Draft 74, D74-10 / package S0 on the chain: slim pieces over the arcs of the cut choice's `D₃`

Lane C14-REG-CHAIN (by S-REG-CHAIN2), G29 (chain binding). For a chain `C` on the final family
(`K ≥ 5`), a cut choice `D : CutChoiceOn74 C.toGaf02ChainE` (D74-3) and the carrier
identification `φ : X ≃ₘ W` (`M.ψ`): over EVERY arc `k` of the cut choice's OWN
`D.D₃` (not a second `K₃, D₃`: `slim_arc_product_EFE` is generic over arcs of `Bs`) there is a slim
piece of `W` with an interval model (`SlimModel.sphereInterval` or `.torusInterval`, the
dichotomy of the standard whole fibre), whose range is `φ(f₃⁻¹(arc k [0, 1]))` and whose two end
slices are `φ` of the WHOLE end fibres `f₃⁻¹(arc k 0)`, `f₃⁻¹(arc k 1)` (the data of
`SlimPiecesV2.endFace` / `endFn_level`).

* `Gaf02ChainEJA.slim_arc_pieces74`: the statement on a chain and any cut choice;
* `ClosedCutChoice74.slim_arc_pieces_R74`: the closed source `S`, `φ = M.ψ`.

Loops (mapping torus, S1 / D74-12) are NOT covered: only arcs (S0).
Universe: `W : CompactCarrier.{0}`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open GC.GraphManifold GC.Endpoint
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Ehresmann
open GC.GraphManifold.Assembly
open GC.GraphManifold.Assembly.FC39P0 (slimModelEnd slimModelIsInterval)

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **Slim pieces over the arcs of a cut choice** (S0): over every arc `k` of `D.D₃` a slim piece
of `W` with an interval model, range `φ(f₃⁻¹(arc k [0, 1]))`, end slices `φ` of the whole end
fibres. -/
theorem slim_arc_pieces74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hK : 5 ≤ K) {W : CompactCarrier.{0}} (φ : X ≃ₘ⟮𝓘(ℝ, E3), W.model⟯ W.Carrier)
    (D : CutChoiceOn74 C.toGaf02ChainE) (k : Fin D.D₃.m) :
    ∃ (Pc : PieceEmbedding W) (mo : SlimModel Pc), slimModelIsInterval mo ∧
      range Pc.map = φ '' (C.slimMap_ZSP35 ⁻¹' (D.D₃.arc k '' Icc 0 1)) ∧
      ∀ b : Bool, Pc.map '' slimModelEnd mo b =
        φ '' (C.slimMap_ZSP35 ⁻¹' {D.D₃.arc k (iccEnd b)}) := by
  rcases C.slim_arc_product_EFE hK (D.D₃.arc_EFE k) with ⟨F₀, ⟨Wp⟩⟩ | ⟨F₀, ⟨Wp⟩⟩
  · obtain ⟨Pc, mo, hi, -, hr, he⟩ := Wp.exists_slimPiece_sphere74 φ
    exact ⟨Pc, mo, hi, hr, he⟩
  · obtain ⟨Pc, mo, hi, -, hr, he⟩ := Wp.exists_slimPiece_torus74 φ
    exact ⟨Pc, mo, hi, hr, he⟩

end Gaf02ChainEJA

/-- **Slim pieces over the arcs of the closed cut choice** (S0 on the closed source): the chain of
`S`, the cut choice `D : ClosedCutChoice74 S B`, `φ = M.ψ`. -/
theorem ClosedCutChoice74.slim_arc_pieces_R74 {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)} {R : ClosedRegisterV4 (earlyDataSharedV4 K) T}
    {W : CompactCarrier.{0}} {g : SmoothRiemannianMetric W.model W.Carrier}
    {M : ClosedModel W g} {δ εr Λz : ℝ} {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz}
    {B : ClosedBases74 S} (D : ClosedCutChoice74 S B) (hK : 5 ≤ K) (k : Fin D.D₃.m) :
    ∃ (Pc : PieceEmbedding W) (mo : SlimModel Pc), slimModelIsInterval mo ∧
      range Pc.map = M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹' (D.D₃.arc k '' Icc 0 1)) ∧
      ∀ b : Bool, Pc.map '' slimModelEnd mo b =
        M.ψ '' (S.chain.slimMap_ZSP35 ⁻¹' {D.D₃.arc k (iccEnd b)}) :=
  S.chain.slim_arc_pieces74 hK M.ψ D.toCutChoiceOn74 k

end DifferentialGeometry.Geometry.Collapse
