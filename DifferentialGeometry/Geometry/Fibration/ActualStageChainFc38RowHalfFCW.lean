import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc38SaturationHalfFCW
import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc38RemainderFCW
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRimFibreEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07RowStrong
import DifferentialGeometry.Geometry.Fibration.ActualStageChainCircleBundleBaseApplicationsEFE

/-!
# FC38 (the remaining circle bundle): the row candidate, v3 (one half of EDP05 as the only hint)

Lane S-FC-WRAP2, group G6b (suffix `_FCW`). `Gaf02ChainEJA.fc38_row_half_FCW` is
`fc38_row_strong_FCW` of group G6 (left untouched) with conjunct 4 replaced by
`fdc03_saturation_half_FCW`: the saturation `M₃ = (π₁E)⁻¹(C₁) ∩ X₁` now needs only
(hint') `int_{M₂} A ⊆ X₂°` (EDP05's charts, the converse inclusion; the inclusion
`M₂ ∩ X₂° ⊆ int_{M₂} A` is proved from the openness of `X₂°`) and (hsat) EDP06's saturation of
`M₂ ∩ X₁`. The other six conjuncts are those of G6: `fc38_row_FCW`, AOX's circle bundle, GAF07's
strong circle part (D1, D2), compactness and (Last) at set level, EDP06 (B).
-/


set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open GC.Endpoint

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
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

namespace Gaf02ChainEJA

/-- **FC38, the row candidate on the final family** (see the module docstring). -/
theorem fc38_row_half_FCW {cadj : ℝ}
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM)
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) (hεr : εr < 1 / 2) (hσc : σc ≤ 1 / 2)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 3 / 4) :
    type_of% (C.fc38_row_FCW hβ hd hεr hσc hγ hγ1) ∧
    type_of% (Gaf02ChainEJA.gaf07_circle_bundle_C14Z_EFE P C hβ hd) ∧
    (∀ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      type_of% (C.toGaf02ChainE.gaf07_circle_piece_GAFD C.c_two_lt hβ hd i) ∧
      type_of% (C.toChain.gaf07_circle_chart_map_GAFD C.c_two_lt hβ hd i) ∧
      type_of% (C.toChain.gaf07_circle_local_trivial_GAFD C.c_two_lt hβ hd i)) ∧
    (∀ w (hW : w ∈ C.toChain.finalBase_BAS 0)
      (i : P.toLocalChartFamily.circle.finite_centres.toFinset)
      (hm : 9 / 10 * ρ i.1 < blockMarkerCLM
        (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w)
      (hr : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w‖ <
        4 * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w),
      type_of% (C.toGaf02ChainE.gaf07_circle_isotopy_GAFD C.c_two_lt hβ hd w hW i hm hr)) ∧
    type_of% (C.fdc03_saturation_half_FCW hεr hσc hγ hγ1) ∧
    type_of% (C.fdc03_remainder_compact_FCW hεr) ∧
    type_of% (C.edp06_rim_eq_whole_fibre_EFE hβ hd) :=
  ⟨C.fc38_row_FCW hβ hd hεr hσc hγ hγ1, Gaf02ChainEJA.gaf07_circle_bundle_C14Z_EFE P C hβ hd,
    fun i => ⟨C.toGaf02ChainE.gaf07_circle_piece_GAFD C.c_two_lt hβ hd i,
      C.toChain.gaf07_circle_chart_map_GAFD C.c_two_lt hβ hd i,
      C.toChain.gaf07_circle_local_trivial_GAFD C.c_two_lt hβ hd i⟩,
    fun w hW i hm hr => C.toGaf02ChainE.gaf07_circle_isotopy_GAFD C.c_two_lt hβ hd w hW i hm hr,
    C.fdc03_saturation_half_FCW hεr hσc hγ hγ1, C.fdc03_remainder_compact_FCW hεr,
    C.edp06_rim_eq_whole_fibre_EFE hβ hd⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
