import DifferentialGeometry.Geometry.Fibration.ActualCfs20RowCFSB

/-!
# Consumer of CFS20: the first stage (`E = H₀ = 0`)

* `cfs20_first_stage_CFSB`: at the first stage the input is `F = 𝓔⁰` itself (no preceding error),
  so CFS20's budget gives value error `≤ (3c/16)ρ` and derivative error `≤ (3c/8)|w|_g` for
  `Ψ ∘ 𝓔⁰`, both below `c`.
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

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- CFS20 at the first stage: `f = 𝓔⁰`, `E = H₀ = 0`. -/
theorem cfs20_first_stage_CFSB
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : σs ∈ Icc (0 : ℝ) 1)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    (st : Fin 3) (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st)
        (sel x) = x)
    {Kj : ℕ} {εa cw sg : ℝ} (hsg : 0 < sg)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (O : Cfs15StageOutput (gafStageDim st) Kj εa cw (gafCloud P.toLocalChartFamily P.zero st)
      (gafCloudEnlarged P.toLocalChartFamily P.zero st) (fun x => sg * ρ (sel x)) plane)
    (ψ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ)
    (hψI : ∀ y, ψ y ∈ Icc (0 : ℝ) 1)
    {c μr bc ν : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hμr : 0 < μr) (hbc : 0 ≤ bc) (hν : 0 ≤ ν)
    (hνc : ν ≤ c / 16)
    (hεα : εa ≤ min (c / (16 * (1 + bc) * (1 + gafDerivativeBound)))
      (μr / (8 * (1 + gafDerivativeBound))))
    (hsg2 : sg ≤ 1 / 2) (p : X)
    (hloc : cgpGlobalMap P.toLocalChartFamily P.zero p ∈ tsupport ψ →
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection
        (cgpGlobalMap P.toLocalChartFamily P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero st)
    (hψd : cgpGlobalMap P.toLocalChartFamily P.zero p ∈ tsupport ψ →
      DifferentiableAt ℝ ψ (cgpGlobalMap P.toLocalChartFamily P.zero p) ∧
        ‖fderiv ℝ ψ (cgpGlobalMap P.toLocalChartFamily P.zero p)‖ ≤ bc / ρ p)
    (hnormal : (gafStageQ P.toLocalChartFamily P.zero st).starProjection
        (cgpGlobalMap P.toLocalChartFamily P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero st →
      ∀ w, ‖(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero =>
          ℝ²)) - (plane ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero p))).starProjection)
        ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
          (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w))‖ ≤
        ν * Real.sqrt (g.inner p w w)) :
    ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero st) O.ambient ψ
        (cgpGlobalMap P.toLocalChartFamily P.zero p) -
        cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ 3 * c / 16 * ρ p ∧
      ∀ w, ‖mvfderiv 𝓘(ℝ, E3) (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero st)
          O.ambient ψ ∘ cgpGlobalMap P.toLocalChartFamily P.zero) p w -
          mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        3 * c / 8 * Real.sqrt (g.inner p w w) := by
  have hder := gaf01_derivative_bound P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσc hγc hεr
  have ht0 : (0 : ℝ) ≤ min (3 * sg / 10) (min (min (c / (16 * (1 + bc) *
      (1 + gafDerivativeBound))) (μr / (8 * (1 + gafDerivativeBound)))) 1) := by
    have hL := zero_le_one.trans one_le_gafDerivativeBound
    refine le_min (by positivity) (le_min (le_min (by positivity) (by positivity)) zero_le_one)
  have h := cfs20_row_CFSB P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσc hγc hεr st sel hsel hsg plane O ψ
    hψI (cgpGlobalMap P.toLocalChartFamily P.zero) hc hc1 hμr hbc hν hνc hεα hsg2 le_rfl le_rfl
    ht0 ht0 p hloc (by simp) ((hder.1 p).mdifferentiableAt (by simp)) hψd hnormal (fun w => by simp)
  exact ⟨h.1, h.2.1⟩

end DifferentialGeometry.Geometry.Collapse
