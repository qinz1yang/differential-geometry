import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc38SaturationGivenFCW

/-!
# Consumer of G12: FDC03's saturation on ZSP04's PRODUCED `K₃, D₃`

Lane S-FC-WRAP4, group G12 (suffix `_FCW`). `fdc03_saturation_zsp04_FCW`: on the final closed
family, for an enhanced chain with (JA), stage bases `A4` and the register numerics, ZSP04's pair
`K₃, D₃` (`zsp04_D3_ZSP35`, the five properties) satisfies `fdc03_saturation_given_FCW`: the
only hypothesis left on the pieces is (hsat), EDP06's saturation of `M₂ ∩ X₁`. Full-norm reading
of EDP02 (review 77, R13 / D77-3).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

namespace Gaf02ChainEJA

/-- **FDC03's saturation on ZSP04's produced `K₃, D₃`** (see the module docstring). -/
theorem fdc03_saturation_zsp04_FCW {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A4 : SmoothStageBasesOn74 Ĉ.toChain) (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2) (hγ : 0 ≤ γ)
    (hγ1 : γ ≤ 3 / 4) (hΔ2 : 2 ≤ Δ) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) :
    ∃ (K₃ D₃ : SmoothCompactOneDomain_BCF Ĉ.slimBs_ZSP35)
      (hD : D₃.carrier = K₃.carrier ∩ Ĉ.slimC3_ZSP35)
      (hKs : Ĉ.toChain.slimSlabImage_ZSP35 ∪ Ĉ.slimFacePoints_ZSP35 ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set Ĉ.slimBs_ZSP35))
      (hKF : Disjoint (K₃.carrier \
          Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set Ĉ.slimBs_ZSP35))
        Ĉ.slimFacePoints_ZSP35)
      (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
          (Subtype.val ⁻¹' D₃.carrier : Set Ĉ.slimBs_ZSP35)))
      (hdD : D₃.carrier \ Subtype.val '' interior
          (Subtype.val ⁻¹' D₃.carrier : Set Ĉ.slimBs_ZSP35) =
        ((K₃.carrier \ Subtype.val '' interior
              (Subtype.val ⁻¹' K₃.carrier : Set Ĉ.slimBs_ZSP35)) ∩
            Subtype.val '' interior (Subtype.val ⁻¹' Ĉ.slimC3_ZSP35 : Set Ĉ.slimBs_ZSP35)) ∪
          (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set Ĉ.slimBs_ZSP35) ∩
            Ĉ.slimFacePoints_ZSP35)),
      type_of% (Ĉ.fdc03_saturation_given_FCW A4 hεr hσc hγ hγ1 hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 K₃
        D₃ hD hKs hKF hDreg hdD) := by
  obtain ⟨K₃, D₃, hD, hKs, hKF, hDreg, hdD⟩ := Ĉ.zsp04_D3_ZSP35 hεr
  exact ⟨K₃, D₃, hD, hKs, hKF, hDreg, hdD, Ĉ.fdc03_saturation_given_FCW A4 hεr hσc hγ hγ1 hΔ2 hc
    hϑ hε0 hε hγc hγc1 hβc1 K₃ D₃ hD hKs hKF hDreg hdD⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
