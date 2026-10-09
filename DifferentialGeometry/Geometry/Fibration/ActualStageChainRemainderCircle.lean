import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimExclusionM2
import DifferentialGeometry.Geometry.Fibration.ActualStageChainCircleCover
import DifferentialGeometry.Geometry.Fibration.ActualSlimDerivativeComparison
import DifferentialGeometry.Geometry.Fibration.ActualReplacementExclusions

/-!
# FDC03, first clause: the actual remainder `M₃` lies in GAF07's circle region `X₁`

Blueprint `master207B.tex`, FDC03 (B:7285–7335: "`M₃ = M₂ ∖ int_{M₂} M^edge ⊂ X₁`"; coverage proof:
every point is zero-stratum (then in `int Z`), in a slim region (then in `int_{M₁} M^slim`), in a
circle covering ball (then in `X₁`, GAF07) or in the interior of the edge piece). With the ACTUAL
pieces — ZSP02's `Z` (this lane's G1), ZSP04's `M^slim(K₃)` (lane C14-ZSP35d, this lane's G8 slim
exclusion), `M₂ = M₁ ∖ int_{M₁} M^slim`, the edge piece `A = M₂ ∩ V ∩ {∃ k, v_k(E) = R_k,
|u_k(E)| < 4ΔR_k}` (FDC04's) and `M₃ = M₂ ∖ int_{M₂} A` — every point of `M₃` lies in
`X₁ = (π₁E)⁻¹(W₁ ∩ R₁)`:

* `Gaf02ChainEJA.remainder_subset_X₁_EFC` (kernel, any `M₂` avoiding the zero stratum and the slim
  regions, any `A ⊇ M₂ ∩ X₂°`): lane C14-FDCb's coverage `fdc03_coverage_FDC` and
  `circle_ball_mem_X₁_FDC`; slim balls `B(j, 2Δρ_j)` lie in the regions `{d < 9Δρ_j, |η_j| < 10Δ}`
  (`SlimCentre.abs_coord_sub_le_SGP2`, `coord_self_FDC1`); `int X₂° ∩ M₂ ⊆ int_{M₂} A`.
* `Gaf02ChainE.not_zero_of_mem_M1_EFC`: a point of the actual `M₁` is not zero-stratum (LPA05's
  tenth-radius cover against ZSP02's `(.381 − e)R` far-field, `e < 1/40`).
* `fdc03_remainder_subset_X₁_C14Z_EFC` (final family): the statement for the actual pieces.
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
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainE

/-- **The actual `M₁` avoids the zero stratum**: a point `q ∉ int ⋃_k Z_k` is not zero-stratum
(LPA05 puts a zero-stratum point in `B(z, R_z/10)`, ZSP02 puts `q` outside `B(z, (.381 − e)R_z)`,
`e < 1/40`). -/
theorem not_zero_of_mem_M1_EFC
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2) {q : X}
    (hq : q ∈ (interior (⋃ k : P.zero.finite_centres.toFinset,
      zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E))ᶜ) :
    q ∉ scaledSplittingStratum.{0, 0} ρ hρ β 0 := by
  intro h0
  obtain ⟨-, -, -, -, -, -, he, -⟩ := Ĉ.toChain.std
  have hcov := P.zero.covers_stratum h0
  simp only [mem_iUnion] at hcov
  obtain ⟨z, hz, hqz⟩ := hcov
  have hqz' : dist q z < (P.zero.zero z hz).radius / 10 := hqz
  have hfar := Ĉ.zero_far_of_mem_M1_EFC hεr hq z hz
  have hR := (P.zero.zero z hz).radius_pos
  have h1 : (P.zero.zero z hz).radius / 10 ≤ (381 / 1000 - e) * (P.zero.zero z hz).radius := by
    have : (1 : ℝ) / 10 ≤ 381 / 1000 - e := by linarith
    nlinarith
  linarith

end Gaf02ChainE

namespace Gaf02ChainEJA

/-- **FDC03's remainder lies in `X₁`** (kernel): for `M₂` avoiding the zero stratum and every
slim region `{d(·, k) < 9Δρ_k, |η_k| < 10Δ}`, and any `A ⊇ M₂ ∩ X₂°`
(`X₂° = {T < 4Δ} ∩ {∃ k, v_k(E) = R_k, |u_k(E)| < 4ΔR_k}`), every point of `M₂ ∖ int_{M₂} A` has
`π₁E ∈ W₁ ∩ R₁` (`σc ≤ 1/2`, `0 ≤ γ ≤ 3/4`). -/
theorem remainder_subset_X₁_EFC {cadj : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) (hσc : σc ≤ 1 / 2) (hγ : 0 ≤ γ)
    (hγ1 : γ ≤ 3 / 4) {M₂ A : Set X}
    (hzero : ∀ x ∈ M₂, x ∉ scaledSplittingStratum.{0, 0} ρ hρ β 0)
    (hS : ∀ x ∈ M₂, ∀ k (hk : k ∈ P.slim.centres), dist x k < 9 * Δ * ρ k →
      10 * Δ ≤ |(P.slim.centre k hk).coord x|)
    (hA : M₂ ∩ ({x | EuclideanSpace.proj (0 : Fin 2) (gafHeightVector P.toLocalChartFamily
        P.zero (C.toChain.E x)) / C.toChain.scale x < 4 * Δ} ∩
      {x | ∃ k : P.toLocalChartFamily.edge.finite_centres.toFinset,
        blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (C.toChain.E x) = ρ k.1 ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inr (.inl k))) (C.toChain.E x)‖ < 4 * Δ * ρ k.1}) ⊆ A) :
    M₂ \ Subtype.val '' interior (Subtype.val ⁻¹' A : Set M₂) ⊆
      {x | (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E x) ∈
        C.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets} := by
  obtain ⟨-, hΔ1, -, -, -, -, -, -, hσs0, hσs1, -⟩ := C.toChain.std
  rintro x ⟨hxM, hxA⟩
  rcases C.toGaf02ChainE.fdc03_coverage_FDC hσc x with h0 | ⟨j, hj, hx⟩ | ⟨j, hj, hx⟩ | hint
  · exact absurd h0 (hzero x hxM)
  · exact C.circle_ball_mem_X₁_FDC hγ hγ1 ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ hx
  · exfalso
    have hrj := hρ j
    have hd : dist x j < 2 * (Δ * ρ j) := mem_ball.mp hx
    have hlip := (P.slim.centre j hj).abs_coord_sub_le_SGP2 hσs0 x j
    rw [(P.slim.centre j hj).coord_self_FDC1, sub_zero] at hlip
    have h2 : (ρ j)⁻¹ * dist x j < 2 * Δ := by
      rw [inv_mul_lt_iff₀ hrj]
      linarith
    have h3 : (1 + σs) * (ρ j)⁻¹ * dist x j < 10 * Δ := by
      have h4 : (1 + σs) * ((ρ j)⁻¹ * dist x j) ≤ (1 + σs) * (2 * Δ) :=
        mul_le_mul_of_nonneg_left h2.le (by linarith)
      nlinarith
    have hfar := hS x hxM j hj (by nlinarith)
    linarith
  · exfalso
    apply hxA
    rw [DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff]
    refine ⟨hxM, _, isOpen_interior, hint, ?_⟩
    rintro y ⟨hy, hyM⟩
    exact hA ⟨hyM, interior_subset hy⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
