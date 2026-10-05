import DifferentialGeometry.Geometry.Fibration.ActualStageNearest
import DifferentialGeometry.Geometry.Fibration.ActualStageSlimTestApplications

/-!
# GAF02's slim stage projection on the actual slim cloud (consumer of the stage nearest maps)

* Generic: `norm_sub_self_le_of_affine_GAF3` (`‖P z − z‖ ≤ B + ‖z − x‖` from the affine value bound
  `‖P z − (x + Π(z − x))‖ ≤ B`), `norm_id_sub_starProjection_le_GAF3` (`‖id − Π‖ ≤ 1`, the
  comparison hypothesis of `adjustmentMap_step_deriv_GAF3`).
* `gaf02_slim_stage_projection_GAF3`: with GAF01's moduli (`gaf01_row_nearest_GAF3`) and FC27's
  slim test (`fc27_slim_test_C14_GAF3`): for every quality and (CS) budget, on the final family,
  for every selection there are planes and a stage projection `P₃ = π_{Q₃} ∘ a` with values in
  `Q₃`, smooth on `Ω`, with CFS14 (3)'s value and derivative bounds on every `B(x, r_x)` and the
  value step of the slim adjustment: `‖Ψ₃(y) − y‖ ≤ Ξr_x + ‖π_{Q₃}y − x‖` whenever
  `π_{Q₃}y ∈ B(x, r_x)` (`adjustmentMap_step_value_GAF3`).
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
local instance instMetricNC14_GAF3m {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsC14`, as a named local instance. -/
local instance instChartedNC14_GAF3m {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14`, as a named local instance. -/
local instance instMetricCC14_GAF3m {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

section Generic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The affine value bound gives the displacement bound `‖P z − z‖ ≤ B + ‖z − x‖`. -/
theorem norm_sub_self_le_of_affine_GAF3 (W : Submodule ℝ H) {Pz x z : H} {B : ℝ}
    (h : ‖Pz - (x + W.starProjection (z - x))‖ ≤ B) : ‖Pz - z‖ ≤ B + ‖z - x‖ := by
  have hperp : ‖(x + W.starProjection (z - x)) - z‖ ≤ ‖z - x‖ := by
    have heq : (x + W.starProjection (z - x)) - z = -(Wᗮ.starProjection (z - x)) := by
      rw [Submodule.starProjection_orthogonal_val]
      abel
    rw [heq, norm_neg]
    exact Wᗮ.norm_starProjection_apply_le _
  calc ‖Pz - z‖ = ‖(Pz - (x + W.starProjection (z - x))) +
        ((x + W.starProjection (z - x)) - z)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖Pz - (x + W.starProjection (z - x))‖ + ‖(x + W.starProjection (z - x)) - z‖ :=
        norm_add_le _ _
    _ ≤ B + ‖z - x‖ := add_le_add h hperp

/-- `‖id − Π_W‖ ≤ 1` (it is the orthogonal projection onto `Wᗮ`). -/
theorem norm_id_sub_starProjection_le_GAF3 (W : Submodule ℝ H) :
    ‖ContinuousLinearMap.id ℝ H - W.starProjection‖ ≤ 1 := by
  rw [← Submodule.starProjection_orthogonal]
  exact Wᗮ.starProjection_norm_le

/-- **A stage projection from a nearest map** (abstract): for `Pst = π_Q ∘ a` with the cloud and its
planes inside `Q`, CFS14 (3)'s value and derivative bounds for `a` give the same bounds for `Pst`,
values in `Q`, smoothness on `Ω = ⋃_{x ∈ S} B(x, r_x)` and the adjustment's value step
`‖Ψ(y) − y‖ ≤ Ξr_x + ‖π_Q y − x‖`. -/
theorem stage_projection_of_nearest_GAF3 (Q : Submodule ℝ H) (S : Set H) (r : H → ℝ)
    (plane : H → Submodule ℝ H) (a : H → H) {Ξ : ℝ} (hSQ : ∀ x ∈ S, x ∈ Q)
    (hplane : ∀ x ∈ S, plane x ≤ Q) (hsm : ContDiffOn ℝ ∞ a (⋃ x ∈ S, ball x (r x)))
    (hpt : ∀ x ∈ S, ∀ z ∈ ball x (r x),
      ‖a z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ * r x ∧ DifferentiableAt ℝ a z ∧
        ‖fderiv ℝ a z - (plane x).starProjection‖ ≤ Ξ) :
    (∀ z, Q.starProjection (a z) ∈ Q) ∧
      ContDiffOn ℝ ∞ (fun z => Q.starProjection (a z)) (⋃ x ∈ S, ball x (r x)) ∧
      ∀ x ∈ S, ∀ z ∈ ball x (r x),
        ‖Q.starProjection (a z) - (x + (plane x).starProjection (z - x))‖ ≤ Ξ * r x ∧
        DifferentiableAt ℝ (fun z => Q.starProjection (a z)) z ∧
        ‖fderiv ℝ (fun z => Q.starProjection (a z)) z - (plane x).starProjection‖ ≤ Ξ ∧
        ∀ (ψ : H → ℝ) (y : H), ψ y ∈ Icc (0 : ℝ) 1 → Q.starProjection y = z →
          ‖adjustmentMap Q (fun z => Q.starProjection (a z)) ψ y - y‖ ≤ Ξ * r x + ‖z - x‖ := by
  refine ⟨fun z => starProjection_comp_mem_GAF3 Q a z,
    Q.starProjection.contDiff.comp_contDiffOn hsm, fun x hx z hz => ?_⟩
  obtain ⟨hv, hd, hD⟩ := hpt x hx z hz
  have hval :=
    norm_starProjection_comp_sub_affine_le_GAF3 Q (plane x) a (hSQ x hx) (hplane x hx) hv
  obtain ⟨hdiff, hder⟩ :=
    norm_fderiv_starProjection_comp_sub_le_GAF3 Q (plane x) hd (hplane x hx) hD
  refine ⟨hval, hdiff, hder, fun ψ y hψ hy => ?_⟩
  have h1 := norm_sub_self_le_of_affine_GAF3 (plane x) hval
  have h1' : ‖Q.starProjection (a (Q.starProjection y)) - Q.starProjection y‖ ≤
      (Ξ * r x + ‖z - x‖) * 1 := by
    rw [hy, mul_one]
    exact h1
  have h0 : ‖y - y‖ ≤ 0 * 1 := by simp
  have h2 := adjustmentMap_step_value_GAF3 Q (P := fun z => Q.starProjection (a z)) hψ h1' h0
  rw [zero_add, mul_one] at h2
  exact h2

end Generic

/-- **Consumer: GAF02's slim stage projection.** With GAF01's moduli `θ, Ξ` (with nearest maps): for
every `0 < Γ < min(1, θ₂)` and (CP) with `Σ ≤ Ξ₂(Γ)/640`, on the final family with the slim test's
hypotheses and `μ, τ ≤ 1/100`, for every selection of preimages over `S̃₃` there are planes (FC27's
slim test, inside `Q₃`) and a stage projection `P₃` with values in `Q₃`, smooth on
`Ω = ⋃_{x ∈ S₃} B(x, r_x)`, with `‖P₃ z − (x + Π_x(z − x))‖ ≤ Ξr_x`, `‖DP₃(z) − Π_x‖ ≤ Ξ` on every
`B(x, r_x)`, and the slim adjustment's value step `‖Ψ₃(y) − y‖ ≤ Ξr_x + ‖z − x‖` for every cutoff
value in `[0, 1]` at every `y` with `π_{Q₃}y = z ∈ B(x, r_x)`. -/
theorem gaf02_slim_stage_projection_GAF3 (Kj : ℕ) {Δ β₂ : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂)
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
              ∀ x ∈ gafCloud P.toLocalChartFamily P.zero 2, ∀ z ∈ ball x (sg * ρ (sel x)),
                ‖Pst z - (x + (plane x).starProjection (z - x))‖ ≤ Ξ 2 Γ * (sg * ρ (sel x)) ∧
                DifferentiableAt ℝ Pst z ∧
                ‖fderiv ℝ Pst z - (plane x).starProjection‖ ≤ Ξ 2 Γ ∧
                ∀ (ψ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ)
                  (y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
                  ψ y ∈ Icc (0 : ℝ) 1 →
                  (gafStageQ P.toLocalChartFamily P.zero 2).starProjection y = z →
                  ‖adjustmentMap (gafStageQ P.toLocalChartFamily P.zero 2) Pst ψ y - y‖ ≤
                    Ξ 2 Γ * (sg * ρ (sel x)) + ‖z - x‖ := by
  obtain ⟨θ, Ξ, hnear, -⟩ := gaf01_row_nearest_GAF3 Kj
  refine ⟨θ, Ξ, (hnear 2).1, fun Γ sg eg hΓ hΓ1 hθΓ hsg hsgΓ hsgC hsgΞ heg heg1 hegΓ => ?_⟩
  have hst := (hnear 2).2.2 Γ hΓ hθΓ
  obtain ⟨-, -, hmain⟩ := hst
  have hslim := fc27_slim_test_C14_GAF3 hΔ hβ₂ hβ₂1 hΓ hΓ1 hsg hsgΓ hsgC heg heg1 hegΓ
  obtain ⟨θs, hθs, hθs1, Lc, η₀, hLc, hη₀, hrow⟩ := hslim
  refine ⟨θs, hθs, hθs1, Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr hμ hτ sel hsel
  have hP := hrow X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hΛzT hσs hσθ hvθ hζ hζθ hζL hεr
  obtain ⟨plane, hdimQ, hcloud, -⟩ := hP
  have ha := hmain X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    P hΛ hΔ hμ hτ (by linarith) hLΛ sel hsel sg hsg hsgΞ plane (fun x hx => (hdimQ x hx).1)
    (hcloud sel hsel)
  obtain ⟨a, hsm, hpt⟩ := ha
  have hproj := stage_projection_of_nearest_GAF3 (gafStageQ P.toLocalChartFamily P.zero 2)
    (gafCloud P.toLocalChartFamily P.zero 2) (fun x => sg * ρ (sel x)) plane a
    (fun x hx => gafCloud_subset_gafStageQ P.toLocalChartFamily P.zero 2 hx)
    (fun x hx => (hdimQ x hx).2) hsm
    (fun x hx z hz => ⟨(hpt x hx z hz).1, (hpt x hx z hz).2.1, (hpt x hx z hz).2.2.1⟩)
  exact ⟨plane, _, hdimQ, hproj⟩

end DifferentialGeometry.Geometry.Collapse
