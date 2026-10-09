import DifferentialGeometry.Geometry.Fibration.ActualRawAlignmentZero
import DifferentialGeometry.Geometry.Fibration.ActualRawAlignmentApplications

/-!
# Consumer of TCP02's complete row: the difference form of (TR0) used by TCP03's zero block

* `tcp02_zero_difference`: on `P : LocalChartPacketsZ`, at every circle centre `i` and every zero
  ball meeting `D_i`, `‖ρ(i)⁻¹ (d(p₀, x) − d(p₀, y)) e₀ − A₀ (u_i x − u_i y)‖ < 2E₀` on
  `B(i, 1000ρ(i))` (the translation `d(p₀, i)` cancels).
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
local instance instMetricNZ_TCP02A_KA5 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsZ`, as a named local instance. -/
local instance instChartedNZ_TCP02A_KA5 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricCZ_TCP02A_KA5 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- `e₀ a − e₀ b = e₀ (a − b)` in `ℝ¹`. -/
theorem single_zero_sub_KA5 (a b : ℝ) :
    EuclideanSpace.single (0 : Fin 1) a - EuclideanSpace.single 0 b =
      EuclideanSpace.single 0 (a - b) := by
  ext m
  fin_cases m
  simp

/-- **TCP02 (TR0), difference form** on `LocalChartPacketsZ`, under the threshold choice of the
complete row `tcp02_rowZ`. -/
theorem tcp02_zero_difference {E₀ ν : ℝ} (hE : 0 < E₀) (hν : 0 < ν) (hν1 : ν < 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ ≤ 1 / 1000 ∧ ∃ η₂ : ℝ, 0 < η₂ ∧ ∀ Δ : ℝ, 1 ≤ Δ → ∃ η₁ : ℝ, 0 < η₁ ∧
    ∀ {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
      [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
      {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
      {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}
      (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
        T V ζ Λz),
      0 ≤ Λ → μ ≤ 1 / 100 → τ ≤ 1 / 100 → 1000000 * Δ * Λ < 1 / 100000 →
      4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax → e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T →
      3 * ν ≤ β 3 → β 3 < 1 → 3 * β 2 ≤ σ → β 2 ≤ η₂ → β 1 ≤ η₁ → b ≤ η₁ → σ⁻¹ ≤ Lmax →
      ∀ i ∈ P.circle.centres, ∀ k (hk : k ∈ P.zero.centres),
        (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
          ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty →
        ∃ A₀ : ℝ² →L[ℝ] E1,
          A₀.comp (ContinuousLinearMap.adjoint A₀) = ContinuousLinearMap.id ℝ _ ∧
          ∀ x y, dist x i < 1000 * ρ i → dist y i < 1000 * ρ i →
            ‖EuclideanSpace.single 0 ((ρ i)⁻¹ * (dist k x - dist k y)) -
              A₀ (circleRaw_KA3 P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets
                  i x -
                circleRaw_KA3 P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets
                  i y)‖ < 2 * E₀ := by
  obtain ⟨σ, hσ, hσ1, η₂, hη₂, hrow⟩ := tcp02_rowZ hE hν hν1
  refine ⟨σ, hσ, hσ1, η₂, hη₂, fun Δ hΔ => ?_⟩
  obtain ⟨η₁, hη₁, hrow'⟩ := hrow Δ hΔ
  refine ⟨η₁, hη₁, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz P hΛ hμ
    hτ hLΛ hLmax he hT hν3 hβ3 hβ2σ hβ2 hβ1 hb hσL i hi k hk hmeet
  obtain ⟨A₀, hA₀, hal⟩ := (hrow' P hΛ hμ hτ hLΛ hLmax he hT hν3 hβ3 hβ2σ hβ2 hβ1 hb hσL i
    hi).2.2.2 k hk hmeet
  refine ⟨A₀, hA₀, fun x y hx hy => ?_⟩
  have h := norm_sub_sub_lt_of_affine_KA3 A₀ (s := 1) (c := EuclideanSpace.single 0
    ((ρ i)⁻¹ * dist k i))
    (a := EuclideanSpace.single 0 ((ρ i)⁻¹ * dist k x))
    (a' := EuclideanSpace.single 0 ((ρ i)⁻¹ * dist k y))
    (by rw [one_smul, sub_right_comm, single_zero_sub_KA5, ← mul_sub]; exact hal x hx)
    (by rw [one_smul, sub_right_comm, single_zero_sub_KA5, ← mul_sub]; exact hal y hy)
  rw [one_smul, single_zero_sub_KA5, ← mul_sub] at h
  exact h

end DifferentialGeometry.Geometry.Collapse
