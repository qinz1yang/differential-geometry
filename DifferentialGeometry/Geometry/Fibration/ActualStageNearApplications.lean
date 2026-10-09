import DifferentialGeometry.Geometry.Fibration.ActualStageNearMarkers
import DifferentialGeometry.Geometry.Fibration.ActualStageSlimTestPP
import DifferentialGeometry.Geometry.Fibration.ActualStageEdgeTestPP
import DifferentialGeometry.Geometry.Fibration.ActualStageNearestApplications

/-!
# CFS31's `hnear` on the actual slim stage (consumer of the (PP) tests)

* `fc27_slim_test_pp_C14_GAF4`: the slim test with (PP) on `LocalChartPacketsC14`.
* `gaf02_slim_stage_hnear_GAF4`: GAF01's stage nearest maps (`gaf01_row_nearest_GAF3`) with the slim
  planes of `fc27_slim_test_pp_C14_GAF4` give the slim stage projection `P₃ = π_{Q₃} ∘ a` with all
  of `gaf02_slim_stage_projection_GAF3`'s properties AND CFS31's `hnear` at stage three
  (`gafStage_hnear_GAF4`).
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
local instance instMetricNC14_GAF4h {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAF4h {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAF4h {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **FC27's slim test with (PP) on `LocalChartPacketsC14`** (`fc27_slim_test_pp_GAF4` at the
underlying RVZ family). -/
theorem fc27_slim_test_pp_C14_GAF4 {Δ β₂ Γ sg eg : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hΓ : 0 < Γ) (hΓ1 : Γ < 1) (hsg : 0 < sg) (hsgΓ : sg < Γ / 200)
    (hsgC : sg < Γ ^ 3 / (100 * sgpGraphBound)) (heg : 0 < eg) (heg1 : eg < 1 / 100)
    (hegΓ : eg < Γ * sg / 100) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < θ ^ 2 / 10 ^ 6 → vs < θ / 100 →
        0 < ζ → ζ < θ ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θ / (100 * (1000000 * Δ)) →
        ∃ plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
            Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
          (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
            Module.finrank ℝ (plane x) = gafStageDim 2 ∧
              plane x ≤ gafStageQ P.toLocalChartFamily P.zero 2) ∧
          (∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
            (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
              cgpProjMap P.toLocalChartFamily P.zero
                (gafStageTags P.toLocalChartFamily P.zero 2) (sel x) = x) →
            ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
              hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero 2 ∩
                  ball x (sg * ρ (sel x) / Γ))
                ((AffineSubspace.mk' x (plane x) :
                    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
                  ball x (sg * ρ (sel x) / Γ)) ≤ ENNReal.ofReal (Γ * (sg * ρ (sel x)))) ∧
          (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
            ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
            ∀ q, cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero) q =
              x →
            let Pq := (plane x).orthogonalProjectionOnto.comp ((ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3)
              (cgpProjMap P.toLocalChartFamily P.zero (cgpQ3Tags P.toLocalChartFamily P.zero)) q)
            Function.Surjective Pq ∧
            (∀ v, ‖(ρ i.1)⁻¹ • mvfderiv 𝓘(ℝ, E3) (cgpProjMap P.toLocalChartFamily P.zero
                (cgpQ3Tags P.toLocalChartFamily P.zero)) q v - (Pq v : BlockSpace _)‖ ≤
              eg * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
            (∀ v, (∀ k, Pq k = 0 → g.inner q v k = 0) →
              1 / 2 * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v) ≤ ‖Pq v‖) ∧
            ∀ v, ‖Pq v‖ ≤ 3 * sgpGraphBound * Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner q v v)) ∧
          ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ q,
            cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero 2) q =
              x →
            ∀ a : CGPMarkerIndex P.toLocalChartFamily,
              ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 5 →
              plane x ≤ LinearMap.ker ((blockMarkerCLM
                (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
                (cgpMarkerTag P.toLocalChartFamily P.zero a) :
                  BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ) :
                BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →ₗ[ℝ] ℝ) := by
  obtain ⟨θ, hθ, hθ1, Lc, η₀, hLc, hη₀, h⟩ :=
    fc27_slim_test_pp_GAF4 hΔ hβ₂ hβ₂1 hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ
  refine ⟨θ, hθ, hθ1, Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
  exact h X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    P.toLocalChartPacketsRVZ

/-- **Consumer: GAF02's slim stage projection with CFS31's `hnear`.** As
`gaf02_slim_stage_projection_GAF3`, with the planes of the slim test with (PP)
(`fc27_slim_test_pp_C14_GAF4`), and in addition: for every `x ∈ S₃`, `z ∈ B(x, r_x)`, preimage
`q` of `x` and retained marker with `ρ(c_a) < ρ(q)/16`, the marker `v_a(P₃ z)` vanishes (CFS31's
`hnear` at stage three). With GAF01's moduli `θ, Ξ` (with nearest maps): for
every `0 < Γ < min(1, θ₂)` and (CP) with `Σ ≤ Ξ₂(Γ)/640`, on the final family with the slim test's
hypotheses and `μ, τ ≤ 1/100`, for every selection of preimages over `S̃₃` there are planes (FC27's
slim test, inside `Q₃`) and a stage projection `P₃` with values in `Q₃`, smooth on
`Ω = ⋃_{x ∈ S₃} B(x, r_x)`, with `‖P₃ z − (x + Π_x(z − x))‖ ≤ Ξr_x`, `‖DP₃(z) − Π_x‖ ≤ Ξ` on every
`B(x, r_x)`, and the slim adjustment's value step `‖Ψ₃(y) − y‖ ≤ Ξr_x + ‖z − x‖` for every cutoff
value in `[0, 1]` at every `y` with `π_{Q₃}y = z ∈ B(x, r_x)`. -/
theorem gaf02_slim_stage_hnear_GAF4 (Kj : ℕ) {Δ β₂ : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂)
    (hβ₂1 : β₂ < 1) :
    ∃ (θ : Fin 3 → ℝ) (Ξ : Fin 3 → ℝ → ℝ), 0 < θ 2 ∧
      ∀ Γ sg eg : ℝ, 0 < Γ → Γ < 1 → Γ < θ 2 → 0 < sg → sg < Γ / 200 →
        sg < Γ ^ 3 / (100 * sgpGraphBound) → sg ≤ Ξ 2 Γ / 640 → 0 < eg → eg < 1 / 100 →
        eg < Γ * sg / 100 →
        ∃ θs : ℝ, 0 < θs ∧ θs < 1 ∧ ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
          ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
            [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
            (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
            (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
            (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
            (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ
              δ εr e T V vs ζ Λz),
            β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
            e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
            0 < σs → σs < θs ^ 2 / 10 ^ 6 → vs < θs / 100 →
            0 < ζ → ζ < θs ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
            εr < θs / (100 * (1000000 * Δ)) → μ ≤ 1 / 100 → τ ≤ 1 / 100 →
            ∀ sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
            (∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero 2,
              cgpProjMap P.toLocalChartFamily P.zero
                (gafStageTags P.toLocalChartFamily P.zero 2) (sel x) = x) →
            ∃ (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
                Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
              (Pst : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
                BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
              (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
                Module.finrank ℝ (plane x) = gafStageDim 2 ∧
                  plane x ≤ gafStageQ P.toLocalChartFamily P.zero 2) ∧
              (∀ z, Pst z ∈ gafStageQ P.toLocalChartFamily P.zero 2) ∧
              ContDiffOn ℝ ∞ Pst (⋃ x ∈ gafCloud P.toLocalChartFamily P.zero 2,
                ball x (sg * ρ (sel x))) ∧
              (∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ z ∈ ball x (sg * ρ (sel x)),
                ‖Pst z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ 2 Γ * (sg * ρ (sel x)) ∧
                DifferentiableAt ℝ Pst z ∧
                ‖fderiv ℝ Pst z - (plane x).starProjection‖ ≤ Ξ 2 Γ ∧
                ∀ (ψ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ)
                  (y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
                  ψ y ∈ Icc (0 : ℝ) 1 →
                  (gafStageQ P.toLocalChartFamily P.zero 2).starProjection y = z →
                  ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2) Pst ψ y - y‖ ≤
                    Ξ 2 Γ * (sg * ρ (sel x)) + ‖z - x‖) ∧
              ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ z ∈ ball x (sg * ρ (sel x)), ∀ q,
                (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
                    (cgpGlobalMap P.toLocalChartFamily P.zero q) = x →
                ∀ a : CGPMarkerIndex P.toLocalChartFamily,
                  ρ (cgpMarkerCentre P.toLocalChartFamily a) < ρ q / 16 →
                  blockMarkerCLM (cgpMarkerTag P.toLocalChartFamily P.zero a) (Pst z) = 0 := by
  obtain ⟨θ, Ξ, hnear, -⟩ := gaf01_row_nearest_GAF3 Kj
  refine ⟨θ, Ξ, (hnear 2).1, fun Γ sg eg hΓ hΓ1 hθΓ hsg hsgΓ hsgC hsgΞ heg heg1 hegΓ => ?_⟩
  have hst := (hnear 2).2.2 Γ hΓ hθΓ
  obtain ⟨hΞ, -, hmain⟩ := hst
  have hmo : 128 * (Ξ 2 Γ)⁻¹ * sg ≤ 1 / 5 := by
    have h1 : 128 * (Ξ 2 Γ)⁻¹ * sg ≤ 128 * (Ξ 2 Γ)⁻¹ * (Ξ 2 Γ / 640) :=
      mul_le_mul_of_nonneg_left hsgΞ (by positivity)
    have h2 : 128 * (Ξ 2 Γ)⁻¹ * (Ξ 2 Γ / 640) = 1 / 5 := by
      field_simp
      norm_num
    linarith
  have hslim := fc27_slim_test_pp_C14_GAF4 hΔ hβ₂ hβ₂1 hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ
  obtain ⟨θs, hθs, hθs1, Lc, η₀, hLc, hη₀, hrow⟩ := hslim
  refine ⟨θs, hθs, hθs1, Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr hμ hτ sel hsel
  have hP := hrow X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr
  obtain ⟨plane, hdimQ, hcloud, -, hpp⟩ := hP
  have ha := hmain X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    P hΛ hΔ hμ hτ (by linarith) hLΛ sel hsel sg hsg hsgΞ plane (fun x hx => (hdimQ x hx).1)
    (hcloud sel hsel)
  obtain ⟨a, hsm, hpt⟩ := ha
  have hproj := stage_projection_of_nearest_GAF3 (gafStageQ P.toLocalChartFamily P.zero 2)
    (gafCloud P.toLocalChartFamily P.zero 2) (fun x => sg * ρ (sel x)) plane a
    (fun x hx => gafCloud_subset_gafStageQ P.toLocalChartFamily P.zero 2 hx)
    (fun x hx => (hdimQ x hx).2) hsm
    (fun x hx z hz => ⟨(hpt x hx z hz).1, (hpt x hx z hz).2.1, (hpt x hx z hz).2.2.1⟩)
  have hnr := gafStage_hnear_GAF4 P.toLocalChartPackets hΔ hΛ hLΛ 2 sel hsel hsg hΞ hmo plane hpp
    a (fun x hx z hz => (hpt x hx z hz).2.2.2)
  exact ⟨plane, _, hdimQ, hproj.1, hproj.2.1, hproj.2.2, hnr⟩

end DifferentialGeometry.Geometry.Collapse
