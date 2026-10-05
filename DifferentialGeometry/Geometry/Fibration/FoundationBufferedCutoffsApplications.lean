import DifferentialGeometry.Geometry.Fibration.FoundationBufferedCutoffs

/-!
# Consumer of FC30: the cutoff value moves by a fixed amount between `𝓔⁰` and the stage input

`fc30_stage_shift_FCF`: on the final closed family, for stage inputs `f₁` (edge stage) and `f₂`
(slim stage) quantitatively close to `𝓔⁰` (CFS31's contract), the cutoffs `ψ₂`, `ψ₃` change by at
most `b_cut · (4κ/5)` between `𝓔⁰ p` and `f_j p` — the mean value inequality along the segment
`[𝓔⁰ p, f_j p]`, fed by FC30's open smoothness domain and its derivative bound `b_cut/ρ(p)` on the
whole segment (`fc30_row_FCF`).
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

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- A mean value bound along a segment from a pointwise derivative bound on the segment. -/
theorem norm_sub_le_of_segment_fderiv_le_FCF {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ψ : F → ℝ} {a z : F} {C : ℝ}
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ ψ ((1 - t) • a + t • z))
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ ψ ((1 - t) • a + t • z)‖ ≤ C) :
    ‖ψ z - ψ a‖ ≤ C * ‖z - a‖ := by
  refine (convex_segment a z).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) ?_ ?_
    (left_mem_segment ℝ a z) (right_mem_segment ℝ a z)
  · intro x hx
    rw [segment_eq_image] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    exact hd t ht
  · intro x hx
    rw [segment_eq_image] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    exact hb t ht

/-- **Consumer of FC30**: for stage inputs `f₁`, `f₂` with CFS31's contract (edge resp. slim), the
cutoff values satisfy `|ψ₂(f₁ p) − ψ₂(𝓔⁰ p)| ≤ b_cut · 4κ/5` and `|ψ₃(f₂ p) − ψ₃(𝓔⁰ p)| ≤
b_cut · 4κ/5` at every point (mean value inequality along `[𝓔⁰ p, f_j p]`). -/
theorem fc30_stage_shift_FCF
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (f₁ f₂ : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hpert₁ : ∀ p, ‖f₁ p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ 4 * gafKappa / 5 * ρ p)
    (hZM₁ : ∀ (j : P.edge.finite_centres.toFinset) p, P.edge.cutoff j.1 p = 0 →
      |gafEdgeMarker P.toLocalChartFamily P.zero j (f₁ p)| ≤ ρ j.1 / 32)
    (hpert₂ : ∀ p, ‖f₂ p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ 4 * gafKappa / 5 * ρ p)
    (hZM₂ : ∀ (j : P.slim.finite_centres.toFinset) p, P.slim.cutoff j.1 p = 0 →
      |gafSlimMarker P.toLocalChartFamily P.zero j (f₂ p)| ≤ ρ j.1 / 32) (p : X) :
    |gafStageTwoCutoff P.toLocalChartFamily P.zero (f₁ p) -
        gafStageTwoCutoff P.toLocalChartFamily P.zero (cgpGlobalMap P.toLocalChartFamily P.zero p)|
        ≤ gafCutoffConstant * (4 * gafKappa / 5) ∧
      |gafStageThreeCutoff P.toLocalChartFamily P.zero (f₂ p) -
        gafStageThreeCutoff P.toLocalChartFamily P.zero
          (cgpGlobalMap P.toLocalChartFamily P.zero p)| ≤ gafCutoffConstant * (4 * gafKappa / 5) := by
  obtain ⟨-, h2, h3⟩ := fc30_row_FCF P hΛ hΔ hμ hτ hLΛ hLmax he hT hσs hσs1
  obtain ⟨hU, k1, -, -, -, -, k5⟩ := h2 f₁ hpert₁ hZM₁
  obtain ⟨l1, -, -, -, l5⟩ := h3 f₂ hpert₂ hZM₂
  have hC : 0 ≤ gafCutoffConstant := by unfold gafCutoffConstant; positivity
  have hρp := hρ p
  have key : ∀ (ψ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ)
      (z : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
      (∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ ψ
        ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • z)) →
      (∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ ψ
        ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • z)‖ ≤ gafCutoffConstant / ρ p) →
      ‖z - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤ 4 * gafKappa / 5 * ρ p →
      |ψ z - ψ (cgpGlobalMap P.toLocalChartFamily P.zero p)| ≤
        gafCutoffConstant * (4 * gafKappa / 5) := by
    intro ψ z hd hb hz
    have h := norm_sub_le_of_segment_fderiv_le_FCF hd hb
    rw [Real.norm_eq_abs] at h
    calc |ψ z - ψ (cgpGlobalMap P.toLocalChartFamily P.zero p)|
        ≤ gafCutoffConstant / ρ p * ‖z - cgpGlobalMap P.toLocalChartFamily P.zero p‖ := h
      _ ≤ gafCutoffConstant / ρ p * (4 * gafKappa / 5 * ρ p) :=
          mul_le_mul_of_nonneg_left hz (div_nonneg hC hρp.le)
      _ = gafCutoffConstant * (4 * gafKappa / 5) := by field_simp
  refine ⟨key _ _ (fun t ht => ?_) (fun t ht => (k5 p t ht).2) (hpert₁ p),
    key _ _ (fun t _ => (l1.differentiable (by simp)) _) (fun t ht => l5 p t ht) (hpert₂ p)⟩
  exact (k1.contDiffAt (hU.mem_nhds (k5 p t ht).1)).differentiableAt (by simp)

end DifferentialGeometry.Geometry.Collapse
