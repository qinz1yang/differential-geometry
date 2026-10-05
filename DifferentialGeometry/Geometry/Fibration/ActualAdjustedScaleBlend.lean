import DifferentialGeometry.Geometry.Fibration.ActualAdjustedScaleInputs
import DifferentialGeometry.Geometry.Collapse.EdgeDisk.AdjustedScaleManifold
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.VerticalDerivativeBridge

/-!
# EDP01's blend on the original map: `s = (1 − χ)ρ + χz` with the actual `χ = ψ₁ ∘ 𝓔⁰`

Blueprint `master207B.tex`, EDP01 (`lem:fibration-actual-adjusted-scale-derivative`, B:6726–6745):
"The actual blend is `s = (1−χ)ρ + χz_ρ`. CFS31 gives `‖Dχ‖ ≤ b_cut L₀/ρ`. The product rule bounds
its derivative by `(1 + K₂ + K₁K₃)Λ` … Outside the closed support `s = ρ`."

* `abs_mvfderiv_scale_le_GAFS`: LC02's scale has `|dρ(v)| ≤ Λ|v|_g` (Lipschitz scale + T0's
  distance convention).
* `edp01_blend_GAFS`: with the ACTUAL cutoff `χ = ψ₁ ∘ 𝓔⁰` (`edp01_cutoff_GAFS`,
  `K₃ = b_cut L₀`) and any `z` satisfying on `tsupport χ` the two estimates EDP01 proves for
  `z_ρ = (P₁𝓔⁰)_ρ` (`|z − ρ| ≤ K₁Λρ`, `|dz(v)| ≤ K₂Λ|v|_g`), the blend is differentiable with
  `|s − ρ| ≤ K₁Λρ` and `|ds(v)| ≤ (1 + K₂ + K₁ b_cut L₀)Λ|v|_g` (kernel
  `adjustedScale_slow_mfd_GAFS`). The estimates for `z_ρ` need GAF02's stage-one map `P₁` and
  are not part of this module.
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
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNASB_GAFS
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNASB_GAFS
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCASB_GAFS
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- LC02's scale varies slowly in the derivative form: `|dρ(v)| ≤ Λ|v|_g`. -/
theorem abs_mvfderiv_scale_le_GAFS
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (x : X) (v : TangentSpace 𝓘(ℝ, E3) x) :
    |mvfderiv 𝓘(ℝ, E3) ρ x v| ≤ Λ * Real.sqrt (g.inner x v v) :=
  Geodesic.abs_mvfderiv_le_of_lipschitzWith_riemannianEDistOf g hmetric hΛ P.lipschitz_scale
    ((P.contMDiff_scale x).mdifferentiableAt (by simp)) v

/-- **EDP01's blend with the actual cutoff** `χ = ψ₁ ∘ 𝓔⁰`: for any `z` with `|z − ρ| ≤ K₁Λρ` and
`|dz(v)| ≤ K₂Λ|v|_g` (differentiable) on `tsupport χ`, the blend `s = (1 − χ)ρ + χz` is
differentiable everywhere, `|s − ρ| ≤ K₁Λρ` and `|ds(v)| ≤ (1 + K₂ + K₁ b_cut L₀)Λ|v|_g`
(`b_cut = gafCutoffConstant`, `L₀ = gafDerivativeBound`). -/
theorem edp01_blend_GAFS
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    {z : X → ℝ} {K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) :
    let χ : X → ℝ := fun p => markerLocalitySourceCutoff lc87EdgeTransition (fun j => ρ j.1)
      (gafCircleVector P) (gafCircleMarker P) (cgpGlobalMap P.toLocalChartFamily P.zero p)
    (∀ p ∈ tsupport χ, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) z p ∧ |z p - ρ p| ≤ K₁ * Λ * ρ p ∧
        ∀ v : TangentSpace 𝓘(ℝ, E3) p,
          |mvfderiv 𝓘(ℝ, E3) z p v| ≤ K₂ * Λ * Real.sqrt (g.inner p v v)) →
      ∀ p, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => (1 - χ y) * ρ y + χ y * z y) p ∧
        |(1 - χ p) * ρ p + χ p * z p - ρ p| ≤ K₁ * Λ * ρ p ∧
        ∀ v : TangentSpace 𝓘(ℝ, E3) p,
          |mvfderiv 𝓘(ℝ, E3) (fun y => (1 - χ y) * ρ y + χ y * z y) p v| ≤
            (1 + K₂ + K₁ * (gafCutoffConstant * gafDerivativeBound)) * Λ *
              Real.sqrt (g.inner p v v) := by
  intro χ hz
  obtain ⟨hχs, hχ01, -, -, hχd⟩ := edp01_cutoff_GAFS P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1 hσc
    hγc hεr
  have hK₃ : 0 ≤ gafCutoffConstant * gafDerivativeBound :=
    mul_nonneg gafCutoffConstant_nonneg (le_trans zero_le_one one_le_gafDerivativeBound)
  refine EdgeDisk.adjustedScale_slow_mfd_GAFS (fun x v => Real.sqrt (g.inner x v v)) hΛ hK₁
    (add_nonneg hK₂ (mul_nonneg hK₁ hK₃))
    (fun x => (P.contMDiff_scale x).mdifferentiableAt (by simp)) hρ
    (abs_mvfderiv_scale_le_GAFS P hΛ) (fun x => hχ01 x) fun x hx => ?_
  obtain ⟨hzd, hzv, hz'⟩ := hz x hx
  exact ⟨hzd, (hχs x).mdifferentiableAt (by simp), hzv, hz', hχd x⟩

end DifferentialGeometry.Geometry.Collapse
