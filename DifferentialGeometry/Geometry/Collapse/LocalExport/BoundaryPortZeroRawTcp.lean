import DifferentialGeometry.Geometry.Fibration.ActualZeroRawAlignmentApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyBindings
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortChartFamilyEdgeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortQuantitativeApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortPacketsResidualApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortActiveSupportPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeComparisonList
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeSupportLink
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortRawAlignment
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortSupportRows
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeeting
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortZeroMeetingTcp
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeight
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortBlockBudgets

/-!
# Boundary port (lane B-PORT-A): ActualZeroRawAlignmentApplications (circle-stage closure)

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualZeroRawAlignmentApplications.lean` by
`build-logs/scratch/B-PORT-A/gen_circle.py` (engine `portlib2.py`), then hand-patched by
lane O-PORT-A (`(Λz' := 0)`; the closed consumer example dropped). Closed family → boundary family
(`LocalPacketsOnB` /
`LocalPacketsOnBF`, complete σ-compact carrier, regional `…On` families, ACTIVE edge `edgeB`); every
ported declaration `x` ↦ `x_BAUGP` (namespaced `T.m` ↦ `TOn.m_BAUGP`). Substitution table and
failure points: `build-logs/resume/state-B-PORT-A.md`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E1" => EuclideanSpace ℝ (Fin 1)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricNZ''_ZERO_BAUGP {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric
        𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ} {vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsZ`, as a named local instance. -/
local instance instChartedNZ''_ZERO_BAUGP {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric
        𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ} {vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricCZ''_ZERO_BAUGP {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric
        𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ} {vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **TCP02 (TR0) on the actual packets (supplier).** For a target error `E₀` and the exclusion
quality `ν` (`3ν ≤ β₃ < 1`) there are an early `σ` and a zero quality bound `η₁` (independent of
`Δ`) such that, with `3β₂ ≤ σ`, `β₁ ≤ η₁`, `σ⁻¹ ≤ Lmax` and the zero ranges (`T ≥ 1600L`,
`e < 1/40`, `LΛ < 10⁻⁵`): at every circle centre `i` whose `D_i = B(i, 10ρ(i))` meets the support
of the zero ball at `p₀ = k`, there is a unit row `A₀ : ℝ² → ℝ¹` with
`‖ρ(i)⁻¹ (d(p₀, x) − d(p₀, i)) − A₀ u_i(x)‖ < E₀` on `B(i, 1000ρ(i))`
(`u_i = circleRaw_KA3_BAUGP`). -/
theorem tcp02_zero_supplier_ZERO_BAUGP {E₀ ν : ℝ} (hE : 0 < E₀) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ} {vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
      (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
          vs ζ Λz U₁ U₂ Ue₁ Ue₂),
      0 ≤ Λ → 1 ≤ Δ → 1000000 * Δ * Λ < 1 / 100000 → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 1 ≤ η₁ → σ⁻¹ ≤ Lmax →
      ∀ i ∈ P.circle.centres, ∀ k (hk : k ∈ P.zero.centres),
        (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
          ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
        ∃ A₀ : ℝ² →L[ℝ] E1, A₀.comp (ContinuousLinearMap.adjoint A₀) = ContinuousLinearMap.id ℝ _ ∧
          ∀ x, dist x i < 1000 * ρ i →
            ‖EuclideanSpace.single 0 ((ρ i)⁻¹ * (dist k x - dist k i)) -
              A₀ (circleRaw_KA3_BAUGP P.toLocalPacketsOnB i
                x)‖ < E₀ := by
  obtain ⟨σ, hσ, hσ1, h1⟩ := tcp02_pair_complete_BCG1 hE hν hν1 (j := 1) le_rfl one_le_two
  obtain ⟨η, hη, hk1⟩ := h1 0 le_rfl
  refine ⟨σ, hσ, hσ1, η, hη, ?_⟩
  intro X mX _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz vs
      U₁ U₂ Ue₁ Ue₂ P
    hΛ hΔ hLΛ he hT hν3 hβ3 hβ2σ hβ1 hσL i hi k hk hmeet
  have hri := hρ i
  let P' := P.toLocalPacketsOnB
  have hsec := tcp02_sectional_KA3_BAUGP P' hσ (by linarith) hσL i (P'.circle.centres_subset hi).1
  have hno := circle_no_three_KA3_BAUGP P.circle hi hν3 hβ3
  have hii : i ∈ ball i (10 * ρ i) := mem_ball_self (by positivity)
  obtain ⟨h1, h2, -⟩ := tcp01_zero_lc73_inputs_ZERO_BAUGP P hΛ hΔ hLΛ he hT
    (Λz' := 0) (by linarith) i hk hmeet i hii
  obtain ⟨Zf, mZ, z, F, hF⟩ := P.zero_shell_split k hk i h1 h2
  let Ai := P'.circleAdapted i hi
  have hc12 : (1 / 2 : ℝ) ≤ ρ i / ρ i := by rw [div_self hri.ne']; norm_num
  have hc2 : ρ i / ρ i ≤ 2 := by rw [div_self hri.ne']; norm_num
  have hd : dist i i ≤ 0 * ρ i := by rw [dist_self, zero_mul]
  obtain ⟨A₀, hA₀, hal⟩ := @hk1 X mX _ _ _ _ g hmetric i i (ρ i) (ρ i) hri hri hc12 hc2 hd hsec
    hno Zf Ai.Y mZ Ai.instY z Ai.a (β 1) (β 2) hβ1 hβ2σ F Ai.split
  refine ⟨A₀, hA₀, fun x hx => ?_⟩
  have hmain := hal x hx
  rw [hF x, hF i, sub_self, mul_zero, div_self hri.ne', one_smul, one_smul] at hmain
  have hz : WithLp.toLp 2 (Function.const (Fin 1) (0 : ℝ)) = (0 : E1) := rfl
  rw [hz, sub_zero] at hmain
  rw [circleRaw_KA3_eq_BAUGP P' hi, single_zero_eq_toLp_const_ZERO]
  exact hmain


end DifferentialGeometry.Geometry.Collapse
