import DifferentialGeometry.Geometry.Fibration.ActualStagePlaneZeroBlock

/-!
# ZSP01's contributor input from (ZB\*) on the enhanced stage planes

Blueprint `master207B.tex`, ZSP01 (B:6323–6395) through GAF03 (`large_cloud_affine_marker_locality`,
B:5871) with `K = (ker J_k)ᗮ`, `c = 0`; draft 59 §1.5. For a zero tag `k` and a preimage `p` of
`x ∈ S_st` with `ρ(p) > 200R_k/T`: every window contributor `y` of the radius `Σρ ∘ A.rsel x₀` has
`K.starProjection y = 0` and `A.plane y ≤ Kᗮ`.

* `FirstStagePlanes_PLN.zsp01_input`, `EdgeStagePlanes_PLN.zsp01_input`,
  `SlimStagePlanes_PLN.zsp01_input`.
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

/-- The model metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricNC14_PLNy {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_PLNy {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_PLNy {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

section C14

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- **ZSP01's contributor input, first stage**: for a zero tag `k` and a preimage `p` of `x ∈ S`
with
`ρ(p) > 200R_k/T`, every window contributor `y ∈ S` has `K.starProjection y = 0` and
`A.plane y ≤ Kᗮ` for the whole-block line `K = (ker J_k)ᗮ` (GAF03's hypothesis with `c = 0`). -/
theorem FirstStagePlanes_PLN.zsp01_input
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : FirstStagePlanes_PLN P Γ sg eg) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hT : 0 < T) (he : e < 1 / 10) (hεr : 0 ≤ 1 + εr)
    {εc σ : ℝ} (hε : 0 < εc) (hσε : σ ≤ εc / 10000) (x₀ : X)
    (k : P.zero.finite_centres.toFinset) {p : X} {x :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hpx : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 0) p =
      x) (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 0)
    (hρp : 200 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / T < ρ p) :
    ∀ y ∈ gafCloud P.toLocalChartFamily P.zero 0,
      (closedBall y (80 * εc⁻¹ * A.radius x₀ σ ρ y) ∩
        ball x (8 * εc⁻¹ * A.radius x₀ σ ρ x)).Nonempty →
      (LinearMap.ker ((blockProjCLM_PLN (V
          := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inr (.inl k)))) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] WithLp 2
              (ℝ² × ℝ)) :
                  BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2
                      (ℝ² × ℝ)))ᗮ.starProjection y = 0 ∧
      A.plane y ≤ (LinearMap.ker ((blockProjCLM_PLN (V
          := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inr (.inl k)))) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] WithLp 2
              (ℝ² × ℝ)) :
                  BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2
                      (ℝ² × ℝ)))ᗮᗮ := by
  intro y hy hmeet
  obtain ⟨h1, h2⟩ := A.zero_block hΔ hΛ hLΛ hT he hεr hε hσε x₀ k hpx hx hρp hy hmeet
  exact zeroBlock_input_PLN _ _ h1 h2

/-- **ZSP01's contributor input, edge stage**: for a zero tag `k` and a preimage `p` of `x ∈ S` with
`ρ(p) > 200R_k/T`, every window contributor `y ∈ S` has `K.starProjection y = 0` and
`A.plane y ≤ Kᗮ` for the whole-block line `K = (ker J_k)ᗮ` (GAF03's hypothesis with `c = 0`). -/
theorem EdgeStagePlanes_PLN.zsp01_input
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : EdgeStagePlanes_PLN P Γ sg eg) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hT : 0 < T) (he : e < 1 / 10) (hεr : 0 ≤ 1 + εr)
    {εc σ : ℝ} (hε : 0 < εc) (hσε : σ ≤ εc / 10000) (x₀ : X)
    (k : P.zero.finite_centres.toFinset) {p : X} {x :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hpx : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 1) p =
      x) (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 1)
    (hρp : 200 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / T < ρ p) :
    ∀ y ∈ gafCloud P.toLocalChartFamily P.zero 1,
      (closedBall y (80 * εc⁻¹ * A.radius x₀ σ ρ y) ∩
        ball x (8 * εc⁻¹ * A.radius x₀ σ ρ x)).Nonempty →
      (LinearMap.ker ((blockProjCLM_PLN (V
          := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inr (.inl k)))) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] WithLp 2
              (ℝ² × ℝ)) :
                  BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2
                      (ℝ² × ℝ)))ᗮ.starProjection y = 0 ∧
      A.plane y ≤ (LinearMap.ker ((blockProjCLM_PLN (V
          := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inr (.inl k)))) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] WithLp 2
              (ℝ² × ℝ)) :
                  BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2
                      (ℝ² × ℝ)))ᗮᗮ := by
  intro y hy hmeet
  obtain ⟨h1, h2⟩ := A.zero_block hΔ hΛ hLΛ hT he hεr hε hσε x₀ k hpx hx hρp hy hmeet
  exact zeroBlock_input_PLN _ _ h1 h2

/-- **ZSP01's contributor input, slim stage**: for a zero tag `k` and a preimage `p` of `x ∈ S` with
`ρ(p) > 200R_k/T`, every window contributor `y ∈ S` has `K.starProjection y = 0` and
`A.plane y ≤ Kᗮ` for the whole-block line `K = (ker J_k)ᗮ` (GAF03's hypothesis with `c = 0`). -/
theorem SlimStagePlanes_PLN.zsp01_input
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Γ sg eg : ℝ} (A : SlimStagePlanes_PLN P Γ sg eg) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hT : 0 < T) (he : e < 1 / 10) (hεr : 0 ≤ 1 + εr)
    {εc σ : ℝ} (hε : 0 < εc) (hσε : σ ≤ εc / 10000) (x₀ : X)
    (k : P.zero.finite_centres.toFinset) {p : X} {x :
        BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hpx : cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) p =
      x) (hx : x ∈ gafCloud P.toLocalChartFamily P.zero 2)
    (hρp : 200 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius / T < ρ p) :
    ∀ y ∈ gafCloud P.toLocalChartFamily P.zero 2,
      (closedBall y (80 * εc⁻¹ * A.radius x₀ σ ρ y) ∩
        ball x (8 * εc⁻¹ * A.radius x₀ σ ρ x)).Nonempty →
      (LinearMap.ker ((blockProjCLM_PLN (V
          := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inr (.inl k)))) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] WithLp 2
              (ℝ² × ℝ)) :
                  BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2
                      (ℝ² × ℝ)))ᗮ.starProjection y = 0 ∧
      A.plane y ≤ (LinearMap.ker ((blockProjCLM_PLN (V
          := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inr (.inr (.inl k)))) :
          BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] WithLp 2
              (ℝ² × ℝ)) :
                  BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] WithLp 2
                      (ℝ² × ℝ)))ᗮᗮ := by
  intro y hy hmeet
  obtain ⟨h1, h2⟩ := A.zero_block hΔ hΛ hLΛ hT he hεr hε hσε x₀ k hpx hx hρp hy hmeet
  exact zeroBlock_input_PLN _ _ h1 h2

end C14

end DifferentialGeometry.Geometry.Collapse
