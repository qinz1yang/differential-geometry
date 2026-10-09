import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsB
import DifferentialGeometry.Geometry.Fibration.ActualStageChainCutChoice

/-!
# D74-3 on the closed source: `ClosedCutChoice74 S B` and its producer

Lane C14-REG-CHAIN (by C14-REG-CHAINc), G12 (closed binding). Draft 74 §1.3: the explicit cut
choice `D` of the closed rows' source `S` with bases object `B : ClosedBases74 S` (D74-1: `S` and
`B` do not determine `K₃` nor the good open base neighbourhoods). `ClosedCutChoice74 S B` is the
kernel record `CutChoiceOn74` on the source's own chain `S.chain` (every accessor — `slimSet`,
`edgeSource`, `circleSource`, `C₂`, `C₁`, `M₂`, `M₃`, `edgeSet` — is read on the SAME chain; the
index `B` is the bases object the rows will read, not a second choice).

* **`exists_closedCutChoice74 S B`** (producer): ZSP04's actual `K₃, D₃` on `S.chain` (intervals
  and loops), `edgeBaseOpen = B₂` (empty when `C₂ = ∅`), `circleBaseOpen = W₁ ∩ R₁`, with
  `slimSet = M₁ ∩ f₃⁻¹(K₃)` compact, `M = Z ∪ slimSet ∪ M₂`, `M₃ ⊆ X₁`. Numeric premises at the
  register's values (`ε_r < 1/2`, `σ_c = q_e ≤ 1/2`, `0 ≤ γ ≤ 3/4`) are explicit row hypotheses
  (D74-18: the assembler is qualitative; numerics stay in the register layer).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **D74-3: the explicit cut choice of the closed rows' source** `S` (with its bases object `B`):
the kernel cut choice on the source's own chain. -/
structure ClosedCutChoice74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    extends CutChoiceOn74 S.chain.toGaf02ChainE

/-- **D74-3 producer on the closed source**: a cut choice from ZSP04's ACTUAL `K₃, D₃` on the
source's own chain, with the decomposition `M = Z ∪ slimSet ∪ M₂` and FDC03's `M₃ ⊆ X₁` for the
same `K₃` (numeric premises at the register's values explicit). -/
theorem exists_closedCutChoice74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S) (hεr : εr < 1 / 2)
    (hσc : R.later.err.co.qe ≤ 1 / 2) (hγ : 0 ≤ R.later.circle.γ)
    (hγ1 : R.later.circle.γ ≤ 3 / 4) :
    ∃ D : ClosedCutChoice74 S B,
      D.slimSet = (interior S.chain.zeroUnion_ZSP35)ᶜ ∩
        S.chain.slimMap_ZSP35 ⁻¹' D.K₃.carrier ∧
      IsCompact D.slimSet ∧ S.chain.zeroUnion_ZSP35 ∪ D.slimSet ∪ D.M₂ = univ ∧
      D.M₃ ⊆ {x | S.chain.toGaf02ChainE.cutQ_R74 0 x ∈ S.chain.toChain.finalBase_BAS 0 ∩
        gaf07CircleRatio_G47 S.F.family.toLocalChartPacketsC14.toLocalChartPackets} := by
  obtain ⟨D, hD⟩ := S.chain.exists_cutChoice_R74 hεr hσc hγ hγ1
  exact ⟨⟨D⟩, hD⟩

end DifferentialGeometry.Geometry.Collapse
