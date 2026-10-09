import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainLinkValues74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RowsLinkKernel74

/-!
# D74-5 on the closed source: `ClosedRowsLinkAt74 S B D Rw` and `ClosedRowsLink S B Rw`

Lane S-LANDING (`_LND74`), G1. The frozen link specification of draft 74 §2.1 for the rows of the
closed source `S : ClosedChainEZRowsSource_RGC` with bases object `B : ClosedBases74 S` and cut
choice `D : ClosedCutChoice74 S B`: the five plain-data tables of `RowsLinkKernel74`
(`ZeroLink_LND74`, `SlimLink_LND74`, `EdgeLink_LND74`, `CircleLink_LND74`, `RegionsLink_LND74`)
instantiated on the ACTUAL objects of the SAME chain, carried to `W` by the ONE `M.ψ`:

* zero: `Z_k = zspDomain_ZSP35` (index = the actual zero centres), (ZB) balls,
  `u_k(E)/v_k(E) − 2/5`;
* slim: components of `D.D₃`, whole `f₃`-preimages (`slimMap_ZSP35`), `D.slimSet`;
* edge: FINAL `q₁ = π₁ ∘ E` (`cutQ_R74 1`), height `H_S = A/s` (the rows source's `height`),
  level `4Δ` (`edgeLevel_R74`), `D.edgeBaseOpen`, `D.C₂`, `D.edgeSource`, `D.edgeSet`;
* circle: FINAL `q₀`, `D.circleBaseOpen`, `D.C₁`, `D.circleSource`, region `D.M₃`;
* regions: `M₁ = (int Z)ᶜ` (`cutM1_R74`), `D.M₂`, `D.M₃`.

`ClosedRowsLink S B Rw := ∃ D, ClosedRowsLinkAt74 S B D Rw` (D74-1: the cut choice is quantified,
not fixed). Consumer: the circle region of linked rows lies in GAF07's `X₁` on `W`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
  (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)

/-- The actual zero indices of the source's packet. -/
abbrev ZeroIdx74 : Type :=
  S.F.family.toLocalChartPacketsC14.zero.finite_centres.toFinset

/-- The actual zero domain `Z_k` (ZSP02) of the source's own chain. -/
def zeroDom74 (k : S.ZeroIdx74) : Set M.X :=
  zspDomain_ZSP35 S.F.family.toLocalChartPacketsC14.toLocalChartFamily
    S.F.family.toLocalChartPacketsC14.zero k S.chain.toChain.E

/-- The inner (ZB) ball `B̄(c_k, .38R_k)`. -/
def zeroInner74 (k : S.ZeroIdx74) : Set M.X :=
  closedBall (S.F.family.toLocalChartPacketsC14.zero.zero k.1
      ((Set.Finite.mem_toFinset _).mp k.2)).center
    (38 / 100 * (S.F.family.toLocalChartPacketsC14.zero.zero k.1
      ((Set.Finite.mem_toFinset _).mp k.2)).radius)

/-- The outer (ZB) ball `B(c_k, .42R_k)`. -/
def zeroOuter74 (k : S.ZeroIdx74) : Set M.X :=
  ball (S.F.family.toLocalChartPacketsC14.zero.zero k.1
      ((Set.Finite.mem_toFinset _).mp k.2)).center
    (42 / 100 * (S.F.family.toLocalChartPacketsC14.zero.zero k.1
      ((Set.Finite.mem_toFinset _).mp k.2)).radius)

/-- The retained ratio `u_k(E)/v_k(E) − 2/5` of the zero stage (the rows' `ratio_buffer`). -/
def zeroUV74 (k : S.ZeroIdx74) : M.X → ℝ := fun z =>
  ((S.chain.toChain.E z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
    (S.chain.toChain.E z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5

end ClosedChainEZRowsSource_RGC

/-- **`ClosedRowsLinkAt74 S B D Rw`** (D74-5, the frozen link specification): the rows `Rw` of the
closed source ARE the actual pieces of the SAME chain and the SAME cut choice `D`, through the ONE
`M.ψ`. Zero: an equivalence of indices, ranges / boundaries `M.ψ(Z_k)`, (ZB), buffer and global
ratio. Slim: components of `D₃`, whole `f₃`-preimages, union `M.ψ(slimSet)`. Edge / circle:
embeddings of the rows' bases onto `D.edgeBaseOpen` / `D.circleBaseOpen` with the FINAL
`q_j = π_j ∘ E`, height `H_S = A/s`, level `4Δ`, compact bases `C₂` / `C₁`, whole disks / rims /
fibres, pieces `M^edge` / `M₃`. Regions: `M₁ / M₂ / M₃`. -/
structure ClosedRowsLinkAt74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (D : ClosedCutChoice74 S B) (Rw : FC39RowsV2 W (BoundaryTori.empty W)) : Prop where
  zero : ZeroLink_LND74 M.ψ.toEquiv Rw.zero S.zeroDom74 S.zeroInner74 S.zeroOuter74 S.zeroUV74
  slim : SlimLink_LND74 M.ψ.toEquiv Rw.slim
    (fun c : ActualComponent D.D₃.carrier => S.chain.slimMap_ZSP35 ⁻¹' c.1) D.slimSet
  edge : EdgeLink_LND74 M.ψ.toEquiv Rw.edge (S.chain.toGaf02ChainE.cutQ_R74 1)
    S.toE_RGC.toRowsSource_RGC.height R.edgeLevel_R74 D.edgeBaseOpen D.C₂ D.edgeSource D.edgeSet
  circle : CircleLink_LND74 M.ψ.toEquiv Rw.circle (S.chain.toGaf02ChainE.cutQ_R74 0)
    D.circleBaseOpen D.C₁ D.circleSource D.M₃
  regions : RegionsLink_LND74 M.ψ.toEquiv Rw S.chain.toGaf02ChainE.cutM1_R74 D.M₂ D.M₃

/-- **`ClosedRowsLink S B Rw`** (D74-1): the link at SOME legal cut choice `D`. -/
def ClosedRowsLink {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S)
    (Rw : FC39RowsV2 W (BoundaryTori.empty W)) : Prop :=
  ∃ D : ClosedCutChoice74 S B, ClosedRowsLinkAt74 S B D Rw

namespace ClosedRowsLinkAt74

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
  {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
  {D : ClosedCutChoice74 S B} {Rw : FC39RowsV2 W (BoundaryTori.empty W)}

/-- A link at a given cut choice is a link. -/
theorem link (L : ClosedRowsLinkAt74 S B D Rw) : ClosedRowsLink S B Rw :=
  ⟨D, L⟩

/-- **Consumer**: the circle region of linked rows lies in GAF07's `X₁ = q₀⁻¹(W₁ ∩ R₁)` on `W`,
whenever the cut choice's `M₃` does (ZSP04's `M₃ ⊆ X₁`, `exists_closedCutChoice74`). -/
theorem circle_region_subset (L : ClosedRowsLinkAt74 S B D Rw)
    (hM3 : D.M₃ ⊆ {x : M.X | S.chain.toGaf02ChainE.cutQ_R74 0 x ∈ S.chain.toChain.finalBase_BAS 0 ∩
      gaf07CircleRatio_G47 S.F.family.toLocalChartPacketsC14.toLocalChartPackets}) :
    Rw.circle.region ⊆ S.stageProjW_R74 0 ⁻¹' (S.chain.toChain.finalBase_BAS 0 ∩
      gaf07CircleRatio_G47 S.F.family.toLocalChartPacketsC14.toLocalChartPackets) := by
  obtain ⟨ι, -, -, -, -, -, -, hreg⟩ := L.circle
  rw [hreg]
  rintro _ ⟨x, hx, rfl⟩
  have h := hM3 hx
  have e : M.ψ.symm (M.ψ.toEquiv x) = x := M.ψ.symm_apply_apply x
  rw [mem_preimage, ClosedChainEZRowsSource_RGC.stageProjW_R74, comp_apply, e]
  exact h

end ClosedRowsLinkAt74

end DifferentialGeometry.Geometry.Collapse
