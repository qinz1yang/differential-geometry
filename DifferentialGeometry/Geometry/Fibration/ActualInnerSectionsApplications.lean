import DifferentialGeometry.Geometry.Fibration.ActualInnerSections

/-!
# CGP03 on the actual LC87 family (G10 with edge disk packets and EGP05 sections)

Blueprint `master207B.tex`, CGP03 (`lem:fibration-actual-inner-sections`, B:4004–4016).

`cgp03_row`: the G10 producer (`eventually_nonempty_localChartPacketsD`, binders verbatim through
`egp05_row`) whose family `L` has, at EVERY circle, slim and edge centre `j`, a continuous
section of the block coordinate `η_j` over `B(0, 23ℓ_j/4)` (`ℓ_j = 1, 10⁵Δ, Δ`) into CGP01's
domain `U_j`, along
which the original cutoff is one (a FULL `j` marker of `𝓔⁰ = cgpGlobalMap`) and the scale lies in
`[3ρ(j)/4, 5ρ(j)/4]`; on the edge kind also `t = F/ρ < Δ/100`. Circle and slim sections come from
the family's own charts (`cgp03_circle_section`, `cgp03_slim_section`), the edge section is EGP05's
restricted to `B(0, 23Δ/4)` (`cgp03_edge_point`). Concrete consumer of `egp05_row`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The three scale budgets of CGP03 from the producer's `ΔΛ · 2·10⁶ ≤ 1/100`. -/
theorem cgp03_budgets_KC {Δ Λ : ℝ} (hΔ : 1 ≤ Δ) (hΛ : 0 < Λ) (h : Δ * Λ * 2000000 ≤ 1 / 100) :
    Λ * 102 ≤ 1 / 4 ∧ Λ * (10 ^ 6 * Δ) ≤ 1 / 4 ∧ Λ * (10 * Δ) ≤ 1 / 4 := by
  have h1 : Λ ≤ Δ * Λ := by nlinarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- **CGP03** on the actual LC87 family: see the module docstring. -/
theorem cgp03_row
    {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 → ε ≤ 1 / 10 ^ 8 → μ ≤ 1 / 10 ^ 8 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) → 100 * Δ * Λ ≤ 1 / 10 ^ 8 →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 → ∃ bd₀ : ℝ, 0 < bd₀ ∧
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → b < bd₀ →
      ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ Lmax : ℝ, 0 < Lmax →
      ∀ (X : ℕ → Type) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
        [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (X i))
        (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
        (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
        (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
          ∀ C, 0 < C → C < α i → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
            curvatureDerivativeNorm (g i) k y ≤
              A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
        (∀ i, ManifoldOrientation (𝓡 3) (X i) 3) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ i in atTop,
        ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        ∃ L : LocalChartPacketsD (X i) (g i) (hmetric i) ρ hρpos Λ β Δ σs K
            σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V,
          (∀ j (hj : j ∈ L.circle.centres), ∃ sec : ball (0 : ℝ²) (23 / 4) → X i, Continuous sec ∧
            ∀ a, (let c := L.circle.chart j hj;
              letI := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j)); c.coord (sec a)) = a ∧
              sec a ∈ ball j (200 * ρ j) ∧ L.circle.cutoff j (sec a) = 1 ∧
              3 / 4 * ρ j ≤ ρ (sec a) ∧ ρ (sec a) ≤ 5 / 4 * ρ j) ∧
          (∀ j (hj : j ∈ L.slim.centres), ∃ sec : ball (0 : ℝ) (23 / 4 * (10 ^ 5 * Δ)) → X i,
            Continuous sec ∧ ∀ a, (L.slim.centre j hj).coord (sec a) = a ∧
              sec a ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ L.slim.cutoff j (sec a) = 1 ∧
              3 / 4 * ρ j ≤ ρ (sec a) ∧ ρ (sec a) ≤ 5 / 4 * ρ j) ∧
          ∀ j ∈ L.edge.centres, ∃ sec : ball (0 : ℝ) (23 / 4 * Δ) → X i, Continuous sec ∧
            ∀ a, L.edge.coord j (sec a) = a ∧ sec a ∈ ball j (100 * Δ * ρ j) ∧
              L.edge.smoothing (sec a) / ρ (sec a) < Δ / 100 ∧ L.edge.cutoff j (sec a) = 1 ∧
              3 / 4 * ρ j ≤ ρ (sec a) ∧ ρ (sec a) ≤ 5 / 4 * ρ j := by
  obtain ⟨a₂, ha₂, h⟩ := egp05_row hσs hσs1 K hK A hA
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔ1 : 1 ≤ Δ := by
    have h100 : 100 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b' s'
    hs hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b'
    s' hs hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8 => ?_⟩
  obtain ⟨hb102, hbslim, hbedge⟩ := cgp03_budgets_KC hΔ1 hΛ hΛΔ
  obtain ⟨w₀, hw₀, h⟩ := h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8
  refine ⟨w₀, hw₀, fun w hw hww hwc => ?_⟩
  obtain ⟨bd₀, hbd₀, h⟩ := h w hw hww hwc
  refine ⟨bd₀, hbd₀, fun b hb hbs hbc hbb₁ hsource hbd => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h b hb hbs hbc hbb₁ hsource hbd
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone => ?_⟩
  obtain ⟨εr, δ', Λ5, hεr, hεr4, hδ', hΛ5, h⟩ := h β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone
  refine ⟨εr, δ', Λ5, hεr, hεr4, hδ', hΛ5,
    fun T hT hTΛ e he he1 Lmax hLmax X _ _ _ _ g hmetric α hα hstand hder hor => ?_⟩
  obtain ⟨V, hTV, δ, hδ0, hδδ', h⟩ := h T hT hTΛ e he he1 Lmax hLmax X g hmetric α hα hstand hder
    hor
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  filter_upwards [h] with i hi
  obtain ⟨ρ, hρpos, hρb, L, hL⟩ := hi
  have hΔ0 : 0 < Δ := by linarith
  refine ⟨ρ, hρpos, hρb, L, fun j hj => cgp03_circle_section L.toLocalChartFamily hΛ.le hb102 hj,
    fun j hj => cgp03_slim_section L.toLocalChartFamily hΔ0 hΛ.le hbslim hj, fun j hj => ?_⟩
  obtain ⟨sec, hsc, hsec⟩ := hL j hj
  let ι : ball (0 : ℝ) (23 / 4 * Δ) → Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ) := fun a =>
    ⟨a, by
      have := mem_ball_zero_iff.mp a.2
      rw [Real.norm_eq_abs] at this
      constructor <;> linarith [abs_lt.mp this]⟩
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  refine ⟨sec ∘ ι, hsc.comp hι, fun a => ?_⟩
  obtain ⟨hco, -, ht, hd⟩ := hsec (ι a)
  have ha : |(a : ℝ)| < 23 / 4 * Δ := by
    have := mem_ball_zero_iff.mp a.2
    rwa [Real.norm_eq_abs] at this
  have hco' : L.edge.coord j (sec (ι a)) = a := hco
  obtain ⟨hU, hcut, hsc1, hsc2⟩ := cgp03_edge_point L.toLocalChartFamily hΔ0 hΛ.le hbedge hj
    (x := sec (ι a)) (by rw [hco']; linarith) (by linarith) hd
  exact ⟨hco', hU, ht, hcut, hsc1, hsc2⟩

end DifferentialGeometry.Geometry.Collapse
