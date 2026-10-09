import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimPiece
import DifferentialGeometry.Geometry.Fibration.ActualStageChainZeroExclusionM1

/-!
# The slim half of `q ∈ M₂`: the actual `M₂` of ZSP04/05 avoids every required slim region

Blueprint `master207B.tex`, FDC01 (B:7157–7244: `q ∈ M₂`), ZSP04 (B:6531–6595: "(SK) the slab image
lies in the relative interior of `K₃`"; "every required smaller slim region surviving in `M₁`" lies
in `M^slim`) and ZSP05 (B:6597–6640: `M₂ = M₁ ∖ int_{M₁} M^slim`). Lane C14-FDCb's FDC01–FDC04
consumers carry `q ∈ M₂` as the zero exclusion `hZ` (discharged by this lane's G1 with ZSP02's
actual `Z`) and the slim exclusion `hS : ∀ k ∈ I_s, d(q, k) < 9Δρ_k → 10Δ ≤ |η_k(q)|`; here `hS` is
DISCHARGED by lane C14-ZSP35d's actual `K₃` (`zsp04_row_ZSP35`, shared kernel of lane B-BCF134):

* `Gaf02ChainE.slim_far_of_relint_EFC` (kernel): for any base set `Kb` containing the slab image
  `f₃(⋃_i {d < 10⁶Δρ_i, |η_i| ≤ 3.5·10⁵Δ})` in its relative interior in `Bs = W₃ ∩ R₃`, and any
  `M^slim ⊇ M₁ ∩ f₃⁻¹(Kb)`, every `q ∈ M₁ ∖ int_{M₁} M^slim` satisfies `hS`: the open region
  `{d(·, k) < 9Δρ_k, |η_k| < 10Δ}` lies in the slabs, so on it `f₃` stays in `Bs`, and near `q`
  it lands in `Kb`, i.e. in `M^slim`;
* `exists_slimPiece_hS_C14Z_EFC` (final family): ZSP04's `K₃` and the actual
  `M₂ = M₁ ∖ int_{M₁} M^slim(K₃)` (`M₁ = M ∖ int Z`, `Z = ⋃_k Z_k`) satisfy `hS` at every point.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

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

namespace Gaf02ChainE

/-- **The slim exclusion from the relative interior condition (SK)** (kernel): if the slab image
lies in the relative interior of `Kb` in `Bs` and `M₁ ∩ f₃⁻¹(Kb) ⊆ M^slim`, then every point of
`M₁ ∖ int_{M₁} M^slim` is outside every required slim region
`{d(·, k) < 9Δρ_k, |η_k| < 10Δ}`. -/
theorem slim_far_of_relint_EFC
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz} (C : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    {Kb : Set (BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))}
    (hK : C.toChain.slimSlabImage_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' Kb : Set C.slimBs_ZSP35))
    {M₁ Msl : Set X} (hsl : ∀ p ∈ M₁, C.slimMap_ZSP35 p ∈ Kb → p ∈ Msl) {q : X}
    (hq : q ∈ M₁ \ Subtype.val '' interior (Subtype.val ⁻¹' Msl : Set M₁)) {k : X}
    (hk : k ∈ L.slim.centres) (hd : dist q k < 9 * Δ * ρ k) :
    10 * Δ ≤ |(L.slim.centre k hk).coord q| := by
  obtain ⟨-, hΔ1, -⟩ := C.toChain.std
  have hrk := hρ k
  by_contra hlt
  push Not at hlt
  apply hq.2
  -- the open region around `q`
  let R : Set X := ball k (9 * Δ * ρ k) ∩
    (ball k (10 ^ 6 * Δ * ρ k) ∩ (fun x => |(L.slim.centre k hk).coord x|) ⁻¹' Iio (10 * Δ))
  have hRo : IsOpen R := isOpen_ball.inter
    (((L.slim.centre k hk).contMDiffOn_coord.continuousOn.abs).isOpen_inter_preimage isOpen_ball
      isOpen_Iio)
  have hRslab : R ⊆ zsp04SlimSlabs_ZSP35 L.toLocalChartPackets := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨k, (Set.Finite.mem_toFinset _).mpr hk⟩, ?_, ?_⟩
    · exact hx.2.1
    · have h1 : |(L.slim.centre k hk).coord x| < 10 * Δ := hx.2.2
      change |(L.slim.centre k hk).coord x| ≤ 35 / 10 * 10 ^ 5 * Δ
      linarith
  have hqR : q ∈ R := by
    refine ⟨mem_ball.mpr hd, mem_ball.mpr (by nlinarith), ?_⟩
    exact hlt
  have hfq : C.slimMap_ZSP35 q ∈ C.toChain.slimSlabImage_ZSP35 := ⟨q, hRslab hqR, rfl⟩
  obtain ⟨-, O₁, hO₁, hqO₁, hO₁K⟩ :=
    DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff.mp (hK hfq)
  rw [DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff]
  refine ⟨hq.1, R ∩ C.slimMap_ZSP35 ⁻¹' O₁,
    hRo.inter (hO₁.preimage C.continuous_slimMap_ZSP35), ⟨hqR, hqO₁⟩, ?_⟩
  rintro p ⟨⟨hpR, hpO⟩, hpM⟩
  have hpB : C.slimMap_ZSP35 p ∈ C.slimBs_ZSP35 :=
    C.slimSlabImage_subset_slimBs_ZSP35 ⟨p, hRslab hpR, rfl⟩
  exact hsl p hpM (hO₁K ⟨hpO, hpB⟩)

end Gaf02ChainE

/-- **The slim half of `q ∈ M₂` on the final closed family**: ZSP04's `K₃` (lane C14-ZSP35d,
`zsp04_row_ZSP35`) with (SK), and at every point of the actual
`M₂ = M₁ ∖ int_{M₁} M^slim(K₃)` (`M₁ = M ∖ int Z`) the slim exclusion `hS` of lane C14-FDCb's
FDC01–FDC04 consumers holds. -/
theorem exists_slimPiece_hS_C14Z_EFC {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) :
    ∃ K₃ : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF Ĉ.slimBs_ZSP35,
      Ĉ.toChain.slimSlabImage_ZSP35 ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set Ĉ.slimBs_ZSP35) ∧
      Ĉ.slimPiece_ZSP35 K₃.carrier =
        (interior Ĉ.zeroUnion_ZSP35)ᶜ ∩ Ĉ.slimMap_ZSP35 ⁻¹' K₃.carrier ∧
      ∀ q ∈ (interior Ĉ.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
          (Subtype.val ⁻¹' Ĉ.slimPiece_ZSP35 K₃.carrier : Set ↥(interior Ĉ.zeroUnion_ZSP35)ᶜ),
        ∀ k (hk : k ∈ P.slim.centres), dist q k < 9 * Δ * ρ k →
          10 * Δ ≤ |(P.slim.centre k hk).coord q| := by
  obtain ⟨K₃, hKs, -, -, -, hSeq, -⟩ := Ĉ.zsp04_row_ZSP35 hεr
  refine ⟨K₃, fun w hw => hKs (Or.inl hw), hSeq, fun q hq k hk hd => ?_⟩
  exact Ĉ.toGaf02ChainE.slim_far_of_relint_EFC (fun w hw => hKs (Or.inl hw))
    (M₁ := (interior Ĉ.zeroUnion_ZSP35)ᶜ) (fun p hp hpK => by rw [hSeq]; exact ⟨hp, hpK⟩) hq hk hd

end DifferentialGeometry.Geometry.Collapse
