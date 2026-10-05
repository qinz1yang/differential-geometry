import DifferentialGeometry.Geometry.Fibration.ActualStagePerturbedRows
import DifferentialGeometry.Geometry.Fibration.ActualAdjustmentChoiceApplications
import DifferentialGeometry.Analysis.ParameterSelection.ThreeStageAdjustmentChoice

/-!
# CFS20 on the actual data: explicit three-stage tolerance budgets

Blueprint `master207B.tex`, CFS20 (`prop:fibration-adjustment-budget-order`, B:3117–3190). On the
actual packets (`F = 𝓔⁰`, `‖D𝓔⁰‖ ≤ L₀ = gafDerivativeBound`, GAF01 / CGP02), at an actual stage
`st` with CFS15's native output `O` (accuracy `ε = ε_st ≤ 1/10`, radius `Σ_st ρ ∘ sel`, plane slot)
and a cutoff `ψ ∈ [0,1]` with derivative constant `b` (CFS17–CFS18 inputs), the row's choice

* `α = min{c/(16(1+b)(1+L₀)), μ/(8(1+L₀))}`, `ν ≤ Γ ≤ c/16`, `ε ≤ min{1/10, α}`, `Σ ≤ 1/2`, and
  preceding errors `E, H₀ ≤ t = min{3Σ/10, α, 1}`

gives, for the adjusted map `g = Ψ ∘ f` (`Ψ = adjustmentMap Q_st P ψ`, `P = O.ambient`, CFS17 of
lane C14-CFS-A): cumulative value error `≤ 3c/16`, derivative error `≤ 3c/8` (both `< c`), the rank
perturbation `ε(L₀ + H₀) + H₀ < μ`, hence a submersion to `W_st⁰` at every plateau point
(`cfs20_row_CFSB`). The three stages can be chosen in the order
`c₃; Γ₃, ε₃, Σ₃; c₂; …; c₁; Γ₁, ε₁, Σ₁` with `c₂ ≤ t₃`, `c₁ ≤ t₂` and the actual constants
`b = C = gafCutoffConstant`, `L₀ = gafDerivativeBound`, `μ = 1/2`, and CFS25's `4κ/5` added
(`cfs20_order_CFSB`).
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

/-- **CFS20** (`prop:fibration-adjustment-budget-order`) at an actual stage. With CFS20's choice
(`α`, `ν ≤ c/16`, `ε ≤ α`, `Σ ≤ 1/2`, `E, H₀ ≤ t`), the CFS17 inputs at `p` (localization on the
closed support, prior value / derivative errors `E`, `H₀`, cutoff derivative `≤ b/ρ`, normal error
`ν`), the adjusted map has value error `≤ (3c/16)ρ(p)` and derivative error `≤ (3c/8)|w|_g`, both
strictly below `c`, the rank perturbation is `< μ`, and at a plateau point `ψ(f p) = 1` with rank
margin `μ` on a `k_st`-dimensional `V`, `d(P ∘ π_st ∘ f)_p` is onto `T W_st⁰`. -/
theorem cfs20_row_CFSB
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
    (f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    {c μr bc ν E H₀ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hμr : 0 < μr) (hbc : 0 ≤ bc) (hν : 0 ≤ ν)
    (hνc : ν ≤ c / 16)
    (hεα : εa ≤ min (c / (16 * (1 + bc) * (1 + gafDerivativeBound)))
      (μr / (8 * (1 + gafDerivativeBound))))
    (hsg2 : sg ≤ 1 / 2) (hE0 : 0 ≤ E) (hH₀ : 0 ≤ H₀)
    (hEt : E ≤ min (3 * sg / 10) (min (min (c / (16 * (1 + bc) * (1 + gafDerivativeBound)))
      (μr / (8 * (1 + gafDerivativeBound)))) 1))
    (hHt : H₀ ≤ min (3 * sg / 10) (min (min (c / (16 * (1 + bc) * (1 + gafDerivativeBound)))
      (μr / (8 * (1 + gafDerivativeBound)))) 1))
    (p : X)
    (hloc : f p ∈ tsupport ψ →
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection
        (cgpGlobalMap P.toLocalChartFamily P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero st)
    (hprior : ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ E * ρ p)
    (hf : MDifferentiableAt 𝓘(ℝ, E3)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) f p)
    (hψd : f p ∈ tsupport ψ → DifferentiableAt ℝ ψ (f p) ∧ ‖fderiv ℝ ψ (f p)‖ ≤ bc / ρ p)
    (hnormal : (gafStageQ P.toLocalChartFamily P.zero st).starProjection
        (cgpGlobalMap P.toLocalChartFamily P.zero p) ∈ gafCloud P.toLocalChartFamily P.zero st →
      ∀ w, ‖(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero =>
          ℝ²)) - (plane ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero p))).starProjection)
        ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
          (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w))‖ ≤
        ν * Real.sqrt (g.inner p w w))
    (hpriorD : ∀ w, ‖mvfderiv 𝓘(ℝ, E3) f p w -
      mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        H₀ * Real.sqrt (g.inner p w w)) :
    ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero st) O.ambient ψ (f p) -
        cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ 3 * c / 16 * ρ p ∧
      (∀ w, ‖mvfderiv 𝓘(ℝ, E3) (adjustmentMap (gafStageQ P.toLocalChartFamily P.zero st)
          O.ambient ψ ∘ f) p w - mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p w‖ ≤
        3 * c / 8 * Real.sqrt (g.inner p w w)) ∧
      3 * c / 16 < c ∧ 3 * c / 8 < c ∧
      εa * (gafDerivativeBound + H₀) + H₀ < μr ∧
      (ψ (f p) = 1 → ∀ V : Submodule ℝ (TangentSpace 𝓘(ℝ, E3) p),
        Module.finrank ℝ V = gafStageDim st → (∀ v ∈ V, v ≠ 0 → 0 < Real.sqrt (g.inner p v v)) →
        (∀ v ∈ V, μr * Real.sqrt (g.inner p v v) ≤
          ‖(plane ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
            (cgpGlobalMap P.toLocalChartFamily P.zero p))).starProjection
            ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
              (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap P.toLocalChartFamily P.zero) p v))‖) →
        ∃ hy : (gafStageQ P.toLocalChartFamily P.zero st).starProjection (f p) ∈
            cfs15Omega_C15 (gafCloud P.toLocalChartFamily P.zero st) (fun x => sg * ρ (sel x)),
          let _ := O.cs
          LinearMap.range (mvfderiv 𝓘(ℝ, E3)
              (fun q => O.ambient ((gafStageQ P.toLocalChartFamily P.zero st).starProjection
                (f q))) p).toLinearMap =
            actualZeroSetTangentSpace (gafStageDim st) O.Z
              (O.p ⟨(gafStageQ P.toLocalChartFamily P.zero st).starProjection (f p), hy⟩) ∧
          Module.finrank ℝ (actualZeroSetTangentSpace (gafStageDim st) O.Z
            (O.p ⟨(gafStageQ P.toLocalChartFamily P.zero st).starProjection (f p), hy⟩)) =
            gafStageDim st) := by
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hL := zero_le_one.trans one_le_gafDerivativeBound
  have hder := gaf01_derivative_bound P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσc hγc hεr
  have hεa := O.eps_pos
  have hEα : E ≤ min (c / (16 * (1 + bc) * (1 + gafDerivativeBound)))
      (μr / (8 * (1 + gafDerivativeBound))) :=
    hEt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hHα : H₀ ≤ min (c / (16 * (1 + bc) * (1 + gafDerivativeBound)))
      (μr / (8 * (1 + gafDerivativeBound))) :=
    hHt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hE : E ≤ 3 * sg / 10 := hEt.trans (min_le_left _ _)
  obtain ⟨hαpos, hval, hrank⟩ := adjustment_threshold_pos_and_bounds hc hμr hbc hL
  have hbud := adjustment_errors_le_of_budget hc hc1 hμr hαpos.le hbc hL hεa.le hE0 hH₀
    (O.eps_le) hεα hsg2 hEα hHα hνc hval hrank
  dsimp only at hbud
  obtain ⟨hb1, hb2, hb3⟩ := hbud
  have h17 := cfs17_row_CFSA P.toLocalChartFamily P.zero hΔ hΛ hsmall st sel hsel hsg plane O ψ hψI
    f hE0 hE hbc hL hH₀ hν p hloc hprior hf hψd (fun w => Real.sqrt (g.inner p w w))
    (fun w => Real.sqrt_nonneg _) (fun w => hder.2 p w) hnormal hpriorD
  obtain ⟨h1, h2, h3⟩ := h17
  have hρp := hρ p
  refine ⟨h1.trans (mul_le_mul_of_nonneg_right hb1 hρp.le), fun w => (h2 w).trans
    (mul_le_mul_of_nonneg_right hb2 (Real.sqrt_nonneg _)), by linarith, by linarith, hb3,
    fun hpl V hV hVpos hVlow => h3 hpl μr V hV hVpos hVlow hb3⟩

/-- **CFS20's order** on the actual constants (`b = C = gafCutoffConstant`,
`L₀ = gafDerivativeBound`, rank margin `μ = 1/2`, CFS25's `4κ/5` added): for CFS15's modulus
`Ξ_j` (positive, `→ 0`), the numbers can be chosen in the order
`c₃; Γ₃, ε₃, Σ₃; c₂; …; c₁; Γ₁, ε₁, Σ₁` with `c₂ ≤ t₃`, `c₁ ≤ t₂`, and at every stage
`0 < c ≤ 1`, `Γ ≤ c/16`, `ε = Ξ(Γ) ≤ min{1/10, α}`, `0 < Σ ≤ min{1/2, ε/640}`.
(Index `0, 1, 2` of `Fin 3` is stage `1, 2, 3`.) -/
theorem cfs20_order_CFSB (Ξ : Fin 3 → ℝ → ℝ) (hΞpos : ∀ j Γ, 0 < Γ → 0 < Ξ j Γ)
    (hΞ : ∀ j, Tendsto (Ξ j) (𝓝[>] 0) (𝓝 0)) :
    ∃ c Γ S : Fin 3 → ℝ,
      (c 1 ≤ min (3 * S 2 / 10) (min (min (c 2 / (16 * (1 + gafCutoffConstant) *
          (1 + gafDerivativeBound))) ((1 / 2) / (8 * (1 + gafDerivativeBound)))) 1) ∧
        c 1 ≤ 4 * gafKappa / 5) ∧
      (c 0 ≤ min (3 * S 1 / 10) (min (min (c 1 / (16 * (1 + gafCutoffConstant) *
          (1 + gafDerivativeBound))) ((1 / 2) / (8 * (1 + gafDerivativeBound)))) 1) ∧
        c 0 ≤ 4 * gafKappa / 5) ∧
      ∀ j, 0 < c j ∧ c j ≤ 1 ∧ 0 < Γ j ∧ Γ j ≤ c j / 16 ∧ Ξ j (Γ j) ≤ 1 / 10 ∧
        Ξ j (Γ j) ≤ min (c j / (16 * (1 + gafCutoffConstant) * (1 + gafDerivativeBound)))
          ((1 / 2) / (8 * (1 + gafDerivativeBound))) ∧
        0 < S j ∧ S j ≤ 1 / 2 ∧ S j ≤ Ξ j (Γ j) / 640 := by
  obtain ⟨c, Γ, S, e, h⟩ := exists_three_stage_adjustment_choice Ξ hΞpos hΞ (fun _ => 1)
    one_pos gafCutoffConstant_nonneg gafKappa_pos (zero_le_one.trans one_le_gafDerivativeBound)
    le_rfl (fun _ => one_pos)
  obtain ⟨-, ⟨-, hc1t, hc1k, -, -⟩, ⟨-, hc0t, hc0k, -, -⟩, hstage⟩ := h
  refine ⟨c, Γ, S, ⟨hc1t, hc1k⟩, ⟨hc0t, hc0k⟩, fun j => ?_⟩
  obtain ⟨⟨hcj, hcj1, hΓj, hΓc, hΞ1, hΞα, -, hSj, hSj2, hSΞ, -⟩, -⟩ := hstage j
  have hΞj := hΞpos j (Γ j) hΓj
  exact ⟨hcj, hcj1, hΓj, hΓc, hΞ1.le, hΞα.le, hSj, hSj2.le, by linarith⟩

end DifferentialGeometry.Geometry.Collapse
