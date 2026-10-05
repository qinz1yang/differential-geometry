import DifferentialGeometry.Geometry.Fibration.ActualAdjustedScaleBlend
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# Consumer: EDP01's (SD) with the blueprint constant `C_ρ`, on `LocalChartPacketsC14`

* `edp01_scale_C14`: with the actual cutoff `χ = ψ₁ ∘ 𝓔⁰` and any `z` satisfying on `tsupport χ`
  EDP01's two estimates for `z_ρ` (`|z − ρ| ≤ (80/3)Λρ`, `|dz(v)| ≤ (80N_b c_w L₀/(3Σ₁))Λ|v|_g`),
  the blend `s = (1 − χ)ρ + χz` satisfies (SD) with the blueprint's
  `C_ρ = 100(L₀ + 1)(1 + b_cut + N_b c_w/Σ₁)` (B:6737), and `s > 0` once `C_ρΛ < 1` (B:6744).
  Consumes `edp01_blend_GAFS`, `EdgeDisk.adjustedScale_constant_le`, `EdgeDisk.adjustedScale_pos`.
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

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14ASB_GAFS
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14ASB_GAFS
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14ASB_GAFS
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **EDP01 (SD) with `C_ρ = 100(L₀ + 1)(1 + b_cut + N_b c_w/Σ₁)`** (`LocalChartPacketsC14`, actual
`χ = ψ₁ ∘ 𝓔⁰`): for any `z` with EDP01's two estimates on `tsupport χ`, the blend
`s = (1 − χ)ρ + χz` has `|s − ρ| ≤ C_ρΛρ`, `|ds(v)| ≤ C_ρΛ|v|_g`, and `s > 0` if `C_ρΛ < 1`. -/
theorem edp01_scale_C14
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    {Nb cw S : ℝ} (hN : 0 ≤ Nb) (hc : 0 ≤ cw) (hS : 0 < S) {z : X → ℝ} :
    let χ : X → ℝ := fun p => markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
      (gafCircleVector P.toLocalChartPackets) (gafCircleMarker P.toLocalChartPackets)
      (cgpGlobalMap P.toLocalChartFamily P.zero p)
    let Cρ : ℝ := 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + Nb * cw / S)
    (∀ p ∈ tsupport χ, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) z p ∧
        |z p - ρ p| ≤ 80 / 3 * Λ * ρ p ∧
        ∀ v : TangentSpace 𝓘(ℝ, E3) p, |mvfderiv 𝓘(ℝ, E3) z p v| ≤
          80 * Nb * cw * gafDerivativeBound / (3 * S) * Λ * Real.sqrt (g.inner p v v)) →
      ∀ p, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => (1 - χ y) * ρ y + χ y * z y) p ∧
        |(1 - χ p) * ρ p + χ p * z p - ρ p| ≤ Cρ * Λ * ρ p ∧
        (∀ v : TangentSpace 𝓘(ℝ, E3) p,
          |mvfderiv 𝓘(ℝ, E3) (fun y => (1 - χ y) * ρ y + χ y * z y) p v| ≤
            Cρ * Λ * Real.sqrt (g.inner p v v)) ∧
        (Cρ * Λ < 1 → 0 < (1 - χ p) * ρ p + χ p * z p) := by
  intro χ Cρ hz p
  have hL0 : 0 ≤ gafDerivativeBound := le_trans zero_le_one one_le_gafDerivativeBound
  have hK₂ : 0 ≤ 80 * Nb * cw * gafDerivativeBound / (3 * S) := by positivity
  obtain ⟨hC1, hC2⟩ := EdgeDisk.adjustedScale_constant_le hL0 gafCutoffConstant_nonneg hN hc hS
  obtain ⟨hd, hv, hD⟩ := edp01_blend_GAFS P.toLocalChartPackets hΛ hΔ hμ hτ hLΛ hLmax he hT hσs
    hσs1 hσc hγc hεr (by norm_num : (0 : ℝ) ≤ 80 / 3) hK₂ hz p
  have hρp := hρ p
  have hval : |(1 - χ p) * ρ p + χ p * z p - ρ p| ≤ Cρ * Λ * ρ p := by
    refine hv.trans ?_
    have hΛρ : 0 ≤ Λ * ρ p := mul_nonneg hΛ hρp.le
    have h := mul_le_mul_of_nonneg_right hC1 hΛρ
    calc 80 / 3 * Λ * ρ p = 80 / 3 * (Λ * ρ p) := by ring
      _ ≤ Cρ * (Λ * ρ p) := h
      _ = Cρ * Λ * ρ p := by ring
  refine ⟨hd, hval, fun v => ?_, fun hCΛ => EdgeDisk.adjustedScale_pos hρp ?_ hCΛ⟩
  · refine (hD v).trans ?_
    have hn : 0 ≤ Λ * Real.sqrt (g.inner p v v) := mul_nonneg hΛ (Real.sqrt_nonneg _)
    have h := mul_le_mul_of_nonneg_right hC2 hn
    calc (1 + 80 * Nb * cw * gafDerivativeBound / (3 * S) +
          80 / 3 * (gafCutoffConstant * gafDerivativeBound)) * Λ * Real.sqrt (g.inner p v v)
        = (1 + 80 * Nb * cw * gafDerivativeBound / (3 * S) +
          80 / 3 * (gafCutoffConstant * gafDerivativeBound)) *
            (Λ * Real.sqrt (g.inner p v v)) := by ring
      _ ≤ Cρ * (Λ * Real.sqrt (g.inner p v v)) := h
      _ = Cρ * Λ * Real.sqrt (g.inner p v v) := by ring
  · exact hval

end DifferentialGeometry.Geometry.Collapse
