import DifferentialGeometry.Geometry.Fibration.ActualStageClouds
import DifferentialGeometry.Geometry.Fibration.ActualAdjustmentChoice
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14

/-!
# CFS14 on the actual stage clouds with GAF01's smoothing moduli (final family)

Consumer of `cfs14_stage_inputs_GAF2` and of GAF01's CFS15 moduli (`gaf01_row`, first conjunct):
for every stage `st`, every quality `0 < Γ < θ_st` and every `0 < Σ ≤ Ξ_st(Γ)/640` (CFS15's (MO)),
on the final family `LocalChartPacketsC14` with FC07's parameter range, any selection of preimages
and any planes of the stage dimension satisfying the actual (CS) tests at quality `Γ` (FC27's
conclusion, from TCP06 / EGP07 / SGP06), the smoothing `W` of CFS14 exists with CFS14's
conclusion (1): `W ⊆ N_{Ξr}(S̃)` (radius at the witness) and, at every core centre, the
`r_x⁻¹`-rescaled enlarged cloud and `W` have truncated Hausdorff error `≤ 7Ξ/16` on the closed
radius-`Ξ⁻¹` ball.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14S_GAF2 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14S_GAF2 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14S_GAF2 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **CFS14 (1) on the actual stage clouds** with GAF01's moduli: for every stage, quality
`0 < Γ < θ_st`, `0 < Σ ≤ Ξ_st(Γ)/640`, packets of the final family in FC07's range, selection of
preimages, and planes of the stage dimension with the actual (CS) tests at quality `Γ`: a smoothing
`W ⊆ N_{Ξr}(S̃)` whose rescaled truncation at every core centre is `7Ξ/16`-close to the enlarged
cloud's (closed radius-`Ξ⁻¹` ball). -/
theorem cfs14_actual_stage_GAF2 (Kj : ℕ) :
    ∃ (θ : Fin 3 → ℝ) (Ξ : Fin 3 → ℝ → ℝ), ∀ st : Fin 3, 0 < θ st ∧
      Tendsto (Ξ st) (𝓝[>] 0) (𝓝 0) ∧
      ∀ Γ, 0 < Γ → Γ < θ st → 0 < Ξ st Γ ∧
        ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
          [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
          (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
          (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
          (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
          (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
            εr e T V vs ζ Λz),
          0 ≤ Λ → 1 ≤ Δ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → e ≤ 1 / 8 →
          1000000 * Δ * Λ < 1 / 100000 →
          ∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
          (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
            cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st)
              (sel x) = x) →
          ∀ sg : ℝ, 0 < sg → sg ≤ Ξ st Γ / 640 →
          ∀ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
            Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
          (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
            Module.finrank ℝ (plane x) = gafStageDim st) →
          (∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
            hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero st ∩
                ball x (sg * ρ (sel x) / Γ))
              ((AffineSubspace.mk' x (plane x) :
                  Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
                ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) →
          ∃ W : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
            W ⊆ ⋃ q ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
              ball q (Ξ st Γ * (sg * ρ (sel q))) ∧
            ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st,
              hausdorffEDist (((fun y => (sg * ρ (sel x))⁻¹ • (y - x)) ''
                  gafCloudEnlarged P.toLocalChartFamily P.zero st) ∩ closedBall 0 (Ξ st Γ)⁻¹)
                (((fun y => (sg * ρ (sel x))⁻¹ • (y - x)) '' W) ∩ closedBall 0 (Ξ st Γ)⁻¹) ≤
                ENNReal.ofReal (7 * Ξ st Γ / 16) := by
  obtain ⟨θ, Ξ, hcfs, -⟩ := gaf01_row Kj
  refine ⟨θ, Ξ, fun st => ⟨(hcfs st).1, (hcfs st).2.1, fun Γ hΓ hθΓ => ?_⟩⟩
  have hst := (hcfs st).2.2 Γ hΓ hθΓ
  obtain ⟨⟨m, hm⟩, hmain⟩ := hst
  have hΞ : 0 < Ξ st Γ := by
    rw [hm]
    positivity
  refine ⟨hΞ, ?_⟩
  obtain ⟨F, -, Cc, -, δ₀, -, -, hΓδ, hmain'⟩ := hmain
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ he hLΛ sel hsel sg hsg hsgΞ plane hdim hcloud
  have hmo : 128 * (Ξ st Γ)⁻¹ * sg ≤ 1 / 5 := by
    have h1 : 128 * (Ξ st Γ)⁻¹ * sg ≤ 128 * (Ξ st Γ)⁻¹ * (Ξ st Γ / 640) :=
      mul_le_mul_of_nonneg_left hsgΞ (by positivity)
    have h2 : 128 * (Ξ st Γ)⁻¹ * (Ξ st Γ / 640) = 1 / 5 := by
      field_simp
      norm_num
    linarith
  obtain ⟨hST, htb, ⟨rmin, R, hrmin, hlo, hhi⟩, hmcb⟩ :=
    cfs14_stage_inputs_GAF2 P.toLocalChartPackets hΛ hΔ hμ hτ he hLΛ st sel hsel hΞ hsg hmo
  have happ := hmain' (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (gafCloud P.toLocalChartFamily P.zero st) (gafCloudEnlarged P.toLocalChartFamily P.zero st)
    hST htb (fun x => sg * ρ (sel x)) plane hdim rmin R Γ hrmin hlo hhi hΓ hΓδ hmcb hcloud
  obtain ⟨I, hI, -, -, -, -, hrest⟩ := happ
  obtain ⟨-, -, hZ, hH, -⟩ := hrest
  exact ⟨_, hZ, fun x hx => (hH x hx).1⟩

end DifferentialGeometry.Geometry.Collapse
