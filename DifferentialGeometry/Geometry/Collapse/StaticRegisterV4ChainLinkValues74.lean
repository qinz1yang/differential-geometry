import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainTransport74
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeSublevel

/-!
# D74-5: the value side of the closed link table on `W` (rows that hold now)

Lane C14-REG-CHAIN (by C14-REG-CHAINc), G14. Draft 74 §2.1 (D74-5, the frozen link
specification `ClosedRowsLinkAt74`): `edge_proj / circle_proj` point at the FINAL
`q_j = π_j ∘ E` (the native `stageMap_BAS` only through the later map), `edge_height = H_S = A/s`,
`edge_level = 4Δ`, the edge disk / rim / range are actual level / sublevel sets of the SAME
`q₁, H_S`, `circle_region = M.ψ(M₃)`, everything carried to `W` by the ONE `M.ψ`. Before a rows
producer exists, this file fixes the TARGET VALUES on `W` and proves the table rows that do not
need `Rw`:

* `ClosedChainEZRowsSource_RGC.stageProjW_R74 S j = q_j ∘ M.ψ⁻¹` (smooth,
  `stageProjW_smooth_R74`; `= Θ_j ∘ f_j ∘ M.ψ⁻¹` for every bases object, `stageProjW_ident_R74`);
* `ClosedChainEZRowsSource_RGC.edgeHeightW_R74 S = H_S ∘ M.ψ⁻¹` with `H_S = A/s`
  (`edgeHeightW_eq_R74`, never `cgpHeight`; smooth, `edgeHeightW_smooth_R74`);
  `ClosedRegisterV4.edgeLevel_R74 R = 4Δ`;
* `Gaf02ChainE.edgeRegion_eq_sublevel_R74` (D74-11 through EDP's set equality, low branch kept in
  the definition): `X₂ = q₁⁻¹(B₂) ∩ {A/s ≤ 4Δ}`;
* `ClosedCutChoice74.edgeSet_W_R74`: `M.ψ(M^edge) = M.ψ(M₂) ∩ (q₁∘ψ⁻¹)⁻¹(B₂) ∩ {H_W ≤ 4Δ}`
  (the rows' `edgePiece` form `{x ∈ source | proj ∈ cbase, height ≤ level}` on the actual sets);
* consumer `closed_link_values_R74`: for every closed source and bases object (numerics explicit)
  a cut choice with the edge row on `W`, `M.ψ(M₃) ⊆ (q₀∘ψ⁻¹)⁻¹(W₁ ∩ R₁)` (circle region inside
  GAF07's `X₁` on `W`), the slim decomposition on `W` and the final-projection identity.
Not here (needs `Rw` or other packages): `zeroEquiv` (Z1 selected core), the base
identifications `edgeBaseIdent / circleBaseIdent` (the edge base needs the model
`EuclideanSpace ℝ (Fin 1)` of `EdgeBundle.Base`; G11's charts use `ℝ`), `circle_fibre` (C0).
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
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Kernel

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **D74-11 on the cut pieces**: the actual `X₂ = q₁⁻¹(B₂) ∩ V` (low branch of `V` retained in
the definition) is the height sublevel `q₁⁻¹(B₂) ∩ {A/s ≤ 4Δ}` (EDP's set equality, lane
C14-EDP-FDCd's `edgeBase_eq_heightSublevel_EFC`). -/
theorem Gaf02ChainE.edgeRegion_eq_sublevel_R74
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz} (C : Gaf02ChainE L Kj Ξ Γ S eg c cw) :
    C.edgeRegion_R74 = C.cutQ_R74 1 ⁻¹' (C.toChain.finalBase_BAS 1 ∩ edgeRatio_R74 L) ∩
      {p | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero
        (C.toChain.E p)) / C.toChain.scale p ≤ 4 * Δ} :=
  C.edgeBase_eq_heightSublevel_EFC

end Kernel

namespace ClosedChainEZRowsSource_RGC

variable {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
  {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}

/-- The rows' final stage projections on `W`: `q_j ∘ M.ψ⁻¹`. -/
def stageProjW_R74 (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (j : Fin 3) :
    W.Carrier → BlockSpace (fun _ : CGPTag S.F.family.toLocalChartPacketsC14.toLocalChartFamily
      S.F.family.toLocalChartPacketsC14.zero => ℝ²) :=
  S.chain.toGaf02ChainE.cutQ_R74 j ∘ M.ψ.symm

/-- The rows' edge height on `W`: `H_S ∘ M.ψ⁻¹` (`H_S = A/s`, the rows source's `height`). -/
def edgeHeightW_R74 (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) : W.Carrier → ℝ :=
  S.toE_RGC.toRowsSource_RGC.height ∘ M.ψ.symm

/-- `edge_height = A/s` (never `cgpHeight`). -/
theorem edgeHeightW_eq_R74 (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (x : W.Carrier) :
    S.edgeHeightW_R74 x = EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector S.F.family.toLocalChartPacketsC14.toLocalChartFamily
        S.F.family.toLocalChartPacketsC14.zero (S.chain.toChain.E (M.ψ.symm x))) /
      S.chain.toChain.scale (M.ψ.symm x) :=
  rfl

/-- The edge height on `W` is smooth. -/
theorem edgeHeightW_smooth_R74 (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) :
    ContMDiff W.model 𝓘(ℝ, ℝ) ∞ S.edgeHeightW_R74 :=
  S.toE_RGC.toRowsSource_RGC.smooth_RGC.2.2.comp M.ψ.symm.contMDiff

/-- The final stage projections on `W` are smooth. -/
theorem stageProjW_smooth_R74 (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (j : Fin 3) :
    ContMDiff W.model 𝓘(ℝ, BlockSpace (fun _ : CGPTag
      S.F.family.toLocalChartPacketsC14.toLocalChartFamily
      S.F.family.toLocalChartPacketsC14.zero => ℝ²)) ∞ (S.stageProjW_R74 j) :=
  (S.chain.toChain.final_contMDiff_BAS j).comp M.ψ.symm.contMDiff

/-- D74-5: the final projection on `W` is `Θ_j ∘ f_j ∘ M.ψ⁻¹` for every bases object (the native
stage map only through the later map). -/
theorem stageProjW_ident_R74 (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (B : ClosedBases74 S) (j : Fin 3) (x : W.Carrier) :
    S.stageProjW_R74 j x =
      S.chain.toChain.Θ_BAS j (S.chain.toChain.stageMap_BAS j (M.ψ.symm x)) :=
  B.stageMap_ident_R74 j (M.ψ.symm x)

end ClosedChainEZRowsSource_RGC

/-- `edge_level = 4Δ` at the register. -/
def ClosedRegisterV4.edgeLevel_R74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    (R : ClosedRegisterV4 (earlyDataSharedV4 K) T) : ℝ :=
  4 * R.later.excl.Δ

/-- **D74-5 edge row on `W`** for a cut choice: `M.ψ(M^edge)` is the part of `M.ψ(M₂)` over `B₂`
(through `q₁ ∘ ψ⁻¹`) with `H_W ≤ 4Δ`. -/
theorem ClosedCutChoice74.edgeSet_W_R74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    {S : ClosedChainEZRowsSource_RGC K R M δ εr Λz} {B : ClosedBases74 S}
    (D : ClosedCutChoice74 S B) :
    M.ψ '' D.edgeSet = M.ψ '' D.M₂ ∩ (S.stageProjW_R74 1 ⁻¹'
      (S.chain.toChain.finalBase_BAS 1 ∩ edgeRatio_R74 S.F.family.toLocalChartPacketsC14) ∩
      {x | S.edgeHeightW_R74 x ≤ R.edgeLevel_R74}) := by
  have hX := S.chain.toGaf02ChainE.edgeRegion_eq_sublevel_R74
  change M.ψ '' (D.M₂ ∩ S.chain.toGaf02ChainE.edgeRegion_R74) = _
  rw [hX, image_inter (f := (M.ψ : M.X → W.Carrier)) M.ψ.injective,
    image_inter (f := (M.ψ : M.X → W.Carrier)) M.ψ.injective,
    ← preimage_symm_R74 M.ψ (S.chain.toGaf02ChainE.cutQ_R74 1)]
  congr 2
  exact preimage_symm_R74 M.ψ S.toE_RGC.toRowsSource_RGC.height (Iic (4 * R.later.excl.Δ))
    |>.symm

/-- **Consumer: the D74-5 value rows on `W`** for a cut choice of the closed source built from
ZSP04's actual `K₃` (numeric premises at the register's values explicit): the edge row, the
circle region inside GAF07's `X₁` on `W`, the decomposition `W = ψ(Z) ∪ ψ(slimSet) ∪ ψ(M₂)`, and
`q_j ∘ ψ⁻¹ = Θ_j ∘ f_j ∘ ψ⁻¹`. -/
theorem closed_link_values_R74 {K : ℕ} {T : ClosedThresholdsV4 (earlyDataSharedV4 K)}
    {R : ClosedRegisterV4 (earlyDataSharedV4 K) T} {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {M : ClosedModel W g} {δ εr Λz : ℝ}
    (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz) (B : ClosedBases74 S) (hεr : εr < 1 / 2)
    (hσc : R.later.err.co.qe ≤ 1 / 2) (hγ : 0 ≤ R.later.circle.γ)
    (hγ1 : R.later.circle.γ ≤ 3 / 4) :
    ∃ D : ClosedCutChoice74 S B,
      M.ψ '' D.edgeSet = M.ψ '' D.M₂ ∩ (S.stageProjW_R74 1 ⁻¹'
        (S.chain.toChain.finalBase_BAS 1 ∩ edgeRatio_R74 S.F.family.toLocalChartPacketsC14) ∩
        {x | S.edgeHeightW_R74 x ≤ R.edgeLevel_R74}) ∧
      M.ψ '' D.M₃ ⊆ S.stageProjW_R74 0 ⁻¹' (S.chain.toChain.finalBase_BAS 0 ∩
        gaf07CircleRatio_G47 S.F.family.toLocalChartPacketsC14.toLocalChartPackets) ∧
      M.ψ '' S.chain.zeroUnion_ZSP35 ∪ M.ψ '' D.slimSet ∪ M.ψ '' D.M₂ = univ ∧
      ∀ j x, S.stageProjW_R74 j x =
        S.chain.toChain.Θ_BAS j (S.chain.toChain.stageMap_BAS j (M.ψ.symm x)) := by
  obtain ⟨D, -, -, hcov, hM3⟩ := exists_closedCutChoice74 S B hεr hσc hγ hγ1
  refine ⟨D, D.edgeSet_W_R74, ?_, ?_, S.stageProjW_ident_R74 B⟩
  · rintro _ ⟨x, hx, rfl⟩
    have h := hM3 hx
    rw [mem_preimage, ClosedChainEZRowsSource_RGC.stageProjW_R74, comp_apply,
      M.ψ.symm_apply_apply]
    exact h
  · rw [← image_union, ← image_union, hcov, image_univ]
    exact M.ψ.surjective.range_eq

end DifferentialGeometry.Geometry.Collapse
