import DifferentialGeometry.Geometry.Fibration.ActualStageMean

/-!
# GAF02's stage nearest maps with EDP01's weighted mean on the actual stage clouds

Consumer of `gaf01_row_nearest_mean_abstract_GAFS2`, bound like `gaf01_row_nearest_GAF3`:

* `gaf01_row_nearest_mean_GAFS2`: GAF01's moduli `θ, Ξ` such that for every stage `st`, quality
  `0 < Γ < θ_st` there is `c_w ≥ 0` (CFS12's weight constant of the stage smoothing) with: on
  every `LocalChartPacketsC14` in FC07's range, for every selection `sel` of preimages over
  `S̃_st`, radius factor `0 < Σ ≤ Ξ_st(Γ)/640` and planes of the stage dimension with the (CS) tests
  at quality `Γ`, a map `a` (CFS15's nearest-point map extended to `H`) with every conclusion of
  `gaf01_row_nearest_GAF3` (smoothness on `Ω`, value, derivative, GAF03's locality) and (SMV): for
  every functional `ℓ` whose contributing planes lie in `ker ℓ` and every `R₀, β` with
  `|ℓ(i) − R₀| ≤ β` on the contributing centres `i ∈ S_st`, `|ℓ(a z) − R₀| ≤ β` and
  `‖ℓ ∘ Da(z)‖ ≤ 2c_wβ / r_x`; and GAF01's choice clause verbatim. GAF02's stage one must use THIS
  map for EDP01's blend to be the scale coordinate of the stage-one adjustment.
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
local instance instMetricNC14SM_GAFS2 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14SM_GAFS2 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14SM_GAFS2 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **GAF01 with the actual stage nearest maps and EDP01's weighted mean.** The moduli `θ, Ξ` such
that for every stage `st` and quality `0 < Γ < θ_st` (`0 < Ξ_st(Γ) ≤ 1`) there is `c_w ≥ 0` with:
for packets of the final family in FC07's range, any selection `sel` of preimages over `S̃_st`,
`0 < Σ ≤ Ξ_st(Γ)/640` and planes of the stage dimension with the (CS) tests at quality `Γ`, a map
`a` smooth on `Ω = ⋃_{x ∈ S_st} B(x, r_x)` (`r = Σρ ∘ sel`) with, on every `B(x, r_x)`, the value
and derivative bounds, GAF03's locality and (SMV); and GAF01's choice clause verbatim. -/
theorem gaf01_row_nearest_mean_GAFS2 :
    ∃ (θ : Fin 3 → ℝ) (Ξ : Fin 3 → ℝ → ℝ),
      (∀ st : Fin 3, 0 < θ st ∧ Tendsto (Ξ st) (𝓝[>] 0) (𝓝 0) ∧
        ∀ Γ, 0 < Γ → Γ < θ st → 0 < Ξ st Γ ∧ Ξ st Γ ≤ 1 ∧ ∃ cw : ℝ, 0 ≤ cw ∧
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
            ∃ a : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
                BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
              ContDiffOn ℝ ∞ a (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero st,
                ball x (sg * ρ (sel x))) ∧
              ∀ x ∈ gafCloud P.toLocalChartFamily P.zero st, ∀ z ∈ ball x (sg * ρ (sel x)),
                ‖a z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ st Γ * (sg * ρ (sel x)) ∧
                DifferentiableAt ℝ a z ∧
                ‖fderiv ℝ a z - (plane x).starProjection‖ ≤ Ξ st Γ ∧
                (∀ (Kk : Submodule ℝ
                    (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
                  (c : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
                  (∀ i ∈ gafCloud P.toLocalChartFamily P.zero st,
                    (closedBall i (80 * (Ξ st Γ)⁻¹ * (sg * ρ (sel i))) ∩
                      ball x (8 * (Ξ st Γ)⁻¹ * (sg * ρ (sel x)))).Nonempty →
                    Kk.starProjection i = c ∧ plane i ≤ Kkᗮ) →
                  Kk.starProjection (a z) = c) ∧
                ∀ ℓ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ,
                  (∀ i ∈ gafCloud P.toLocalChartFamily P.zero st,
                    (closedBall i (80 * (Ξ st Γ)⁻¹ * (sg * ρ (sel i))) ∩
                      ball x (8 * (Ξ st Γ)⁻¹ * (sg * ρ (sel x)))).Nonempty →
                    plane i ≤ LinearMap.ker (ℓ : BlockSpace
                      (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ)) →
                  ∀ R₀ β : ℝ,
                  (∀ i ∈ gafCloud P.toLocalChartFamily P.zero st,
                    (closedBall i (80 * (Ξ st Γ)⁻¹ * (sg * ρ (sel i))) ∩
                      ball x (8 * (Ξ st Γ)⁻¹ * (sg * ρ (sel x)))).Nonempty →
                    |ℓ i - R₀| ≤ β) →
                  |ℓ (a z) - R₀| ≤ β ∧
                    ‖ℓ.comp (fderiv ℝ a z)‖ ≤ 2 * cw * β / (sg * ρ (sel x))) ∧
      ∀ (C : Fin 3 → ℝ), (∀ j, 0 < C j) → ∀ cadj : ℝ, 0 < cadj →
      ∃ c Γ S e : Fin 3 → ℝ,
        let Ω : ℝ := max 1 (max (C 0) (max (C 1) (C 2)))
        let α : Fin 3 → ℝ := fun j =>
          min (c j / (16 * (1 + gafCutoffConstant) * (1 + gafDerivativeBound)))
            ((1 / 2) / (8 * (1 + gafDerivativeBound)))
        let t : Fin 3 → ℝ := fun j => min (3 * S j / 10) (min (α j) 1)
        (c 2 < cadj ∧ c 2 < 1 / 1000 ∧ c 2 < 1 / 512) ∧
        (c 1 ≤ c 2 ∧ c 1 ≤ t 2 ∧ c 1 ≤ 4 * gafKappa / 5 ∧ c 1 ≤ 1 / 1000 ∧ c 1 ≤ 1 / 512) ∧
        (c 0 ≤ c 1 ∧ c 0 ≤ t 1 ∧ c 0 ≤ 4 * gafKappa / 5 ∧ c 0 ≤ 1 / 1000 ∧ c 0 ≤ 1 / 512) ∧
        ∀ j, (Γ j < θ j ∧ 0 < c j ∧ c j ≤ 1 ∧ 0 < Γ j ∧ Γ j ≤ c j / 16 ∧ Ξ j (Γ j) < 1 / 10 ∧
            Ξ j (Γ j) < α j ∧ Ξ j (Γ j) < 1 / (1000 * (Ω + 1)) ∧
            0 < S j ∧ S j < 1 / 2 ∧ S j < Ξ j (Γ j) / 10000 ∧ S j < Γ j / 200 ∧
            S j < Γ j ^ 3 / (100 * C j) ∧
            0 < e j ∧ e j < 1 / 100 ∧ e j < Γ j * S j / 100 ∧ e j < S j / 1000 ∧
            2 * e j < 1 / (48 * Ω)) ∧
          (∀ E H ν σ : ℝ, 0 ≤ E → E ≤ t j → 0 ≤ H → H ≤ t j → ν ≤ Γ j → σ ≤ 1 / 2 →
            let a := (5 / 3 : ℝ) * Ξ j (Γ j) * σ + (1 + Ξ j (Γ j)) * E
            E + a < c j ∧ a * gafCutoffConstant * (gafDerivativeBound + H) +
                Ξ j (Γ j) * (gafDerivativeBound + H) + ν + 2 * H < c j ∧
              Ξ j (Γ j) * (gafDerivativeBound + H) + H < 1 / 2) ∧
          (∀ ν : ℝ, ν ≤ e j → ν + e j ≤ 1 / (48 * Ω)) ∧
          (∀ R rx : ℝ, 0 < R → 9 / 20 * S j * R ≤ rx →
            (2 * e j + 25 / 12 * (1 + Ω) * Ξ j (Γ j) * S j) * R < S j * R / 100 ∧
              S j * R / 100 < rx / 4 ∧ Ξ j (Γ j) < 1 / (2 * Ω)) := by
  obtain ⟨θ, Ξ, hnear, hchoice⟩ := gaf01_row_nearest_mean_abstract_GAFS2
  refine ⟨θ, Ξ, fun st => ⟨(hnear st).1, (hnear st).2.1, fun Γ hΓ hθΓ => ?_⟩, hchoice⟩
  have hst := (hnear st).2.2 Γ hΓ hθΓ
  obtain ⟨hΞ, hΞ1, cw, hcw, habs⟩ := hst
  refine ⟨hΞ, hΞ1, cw, hcw, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hΛ hΔ hμ hτ he hLΛ sel hsel sg hsg hsgΞ plane hdim hcloud
  have hmo : 128 * (Ξ st Γ)⁻¹ * sg ≤ 1 / 5 := by
    have h1 : 128 * (Ξ st Γ)⁻¹ * sg ≤ 128 * (Ξ st Γ)⁻¹ * (Ξ st Γ / 640) :=
      mul_le_mul_of_nonneg_left hsgΞ (by positivity)
    have h2 : 128 * (Ξ st Γ)⁻¹ * (Ξ st Γ / 640) = 1 / 5 := by
      field_simp
      norm_num
    linarith
  have hin := cfs14_stage_inputs_GAF2 P.toLocalChartPackets hΛ hΔ hμ hτ he hLΛ st sel hsel hΞ hsg
    hmo
  have hR := Classical.choose_spec (Classical.choose_spec hin.2.2.1)
  exact habs (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (gafCloud P.toLocalChartFamily P.zero st) (gafCloudEnlarged P.toLocalChartFamily P.zero st)
    hin.1 hin.2.1 (fun x => sg * ρ (sel x)) plane hdim _ _ hR.1 hR.2.1 hR.2.2 hin.2.2.2 hcloud

end DifferentialGeometry.Geometry.Collapse
