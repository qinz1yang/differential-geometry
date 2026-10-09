import DifferentialGeometry.Geometry.Fibration.ActualBlockBudgetsApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBlockBudgetsBDFB

/-!
# Boundary port (lane B-DFB, G1): CGP02 (b) tag budgets of `cgpGlobalMap_BAUGP`

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualBlockBudgetsApplications.lean` by `build-logs/scratch/B-DFB/gen_g1.py` (engine: lane B-PORT-A's
`build-logs/scratch/B-PORT-A/portlib2.py`); do not edit by hand, re-run the script. Closed family →
boundary family (`LocalPacketsOnB`, complete σ-compact carrier, regional `…On` families, ACTIVE edge
`edgeB` with BAUG-A's actual cutoff `cutoff_BAUGA` = the closed formula `f(η/Δ) g(F/(ρΔ))`); every
ported declaration `x` ↦ `x_BDFB` (namespaced `T.m` ↦ `TOn.m_BDFB`); B-PORT-A's ports keep `_BAUGP`.
Closed generic lemmas (profiles `cgpProfileBound`, Leibniz / chain rules, the arithmetic budgets,
`zeroModelBall_radial_facts_KA2`) are reused from the closed import.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Arithmetic

end Arithmetic

section Tags

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  {τ γ vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **The scale block of `𝓔⁰`**: `‖d(0, ρ)(v)‖ ≤ Λ ν`. -/
theorem cgp02_scale_tag_budget_BDFB
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (hΛ : 0 ≤ Λ) (x : X)
    (v : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap_BAUGP L Z y (cgpScaleTag_BAUGP L Z)) x v‖ ≤
      Λ * Real.sqrt (g.inner x v v) := by
  have : CompleteSpace X := ‹CompleteSpace X›
  exact norm_mvfderiv_scaleBlock_le_riemannian (W := ℝ²) g hmetric hΛ L.lipschitz_scale
    ((L.contMDiff_scale x).mdifferentiableAt (by simp)) (hρ x).le v

/-- **The constant-radius blocks of `𝓔⁰`** (circle, slim, edge, zero): at a point of the block's
closed support, `‖d(block)(v)‖ ≤ (2 + 80 P₀) ν`. -/
theorem cgp02_constant_radius_tag_budget_BDFB
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (hΔ : 1 ≤ Δ)
    (hσs : σs ∈ Icc (0 : ℝ) 1) (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1)
    (hεr : εr ∈ Icc (0 : ℝ) 1) (he : e ≤ 1 / 20)
    (hmargin : ∀ j ∈ L.edgeB.centres, tsupport (L.edgeB.cutoff_BAUGA j) ⊆ ball j (100 * Δ * ρ j))
    (i : CGPTag_BAUGP L Z) (hiρ : i ≠ cgpScaleTag_BAUGP L Z)
    (hiE : i ≠ cgpEdgeTag_BAUGP L Z) {x : X}
    (hx : x ∈ tsupport (cgpCutoff_BAUGP L Z i)) (v : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap_BAUGP L Z y i) x v‖ ≤
      (2 + 80 * cgpProfileBound) * Real.sqrt (g.inner x v v) := by
  have hP1 := cgpProfileBound_spec.1
  have hν : 0 ≤ Real.sqrt (g.inner x v v) := Real.sqrt_nonneg _
  have hΔ0 : 0 < Δ := by linarith
  rcases i with j | j | j | i | bb
  · have h := circle_block_budget_KA2_BDFB L ((Set.Finite.mem_toFinset _).mp j.2) hx v
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hν)
    linarith
  · have h := slim_block_budget_KA2_BDFB L hΔ0 hσs.1 ((Set.Finite.mem_toFinset _).mp j.2) hx v
    exact h.trans (mul_le_mul_of_nonneg_right
      (slim_budget_le_KA2 hP1 hΔ hσs.1 hσs.2) hν)
  · have hj := (Set.Finite.mem_toFinset _).mp j.2
    have h := edge_block_budget_KA2_BDFB L.edgeB hΔ0 hσc.1 hγc.1 L.contMDiff_scale.continuous hj
      (hmargin j.1 hj) hx v
    exact h.trans (mul_le_mul_of_nonneg_right
      (edge_budget_le_KA2 hP1 hΔ hσc.1 hσc.2 hγc.1 hγc.2) hν)
  · have h := zero_block_budget_KA2_BDFB (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)) hmetric
      hεr.1 (by linarith) hx v
    exact h.trans (mul_le_mul_of_nonneg_right
      (zero_budget_le_KA2 hP1 hεr.1 hεr.2 he) hν)
  · cases bb
    · exact absurd rfl hiρ
    · exact absurd rfl hiE

open Classical in
/-- **The `E'` block of `𝓔⁰`**: on its closed support, `‖d(block)(v)‖ ≤ 500 (n + 1) P₀² ν`,
`n` the number of edge cutoffs whose closed support contains `x`. -/
theorem cgp02_edgeMarker_tag_budget_BDFB
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1)
    (hmargin : ∀ j ∈ L.edgeB.centres, tsupport (L.edgeB.cutoff_BAUGA j) ⊆ ball j (100 * Δ * ρ j))
    {x : X} (hx : x ∈ tsupport (cgpCutoff_BAUGP L Z (cgpEdgeTag_BAUGP L Z)))
    (v : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap_BAUGP L Z y (cgpEdgeTag_BAUGP L Z)) x v‖ ≤
      500 * (((Finset.univ.filter fun i : L.edgeB.finite_centres.toFinset =>
        x ∈ tsupport (L.edgeB.cutoff_BAUGA i)).card : ℝ) + 1) * cgpProfileBound ^ 2 *
        Real.sqrt (g.inner x v v) := by
  have hP1 := cgpProfileBound_spec.1
  have hν : 0 ≤ Real.sqrt (g.inner x v v) := Real.sqrt_nonneg _
  have h := edgeMarker_block_budget_KA2_BDFB L (by linarith) hΛ hσc.1 hγc.1 hmargin hx v
  exact h.trans (mul_le_mul_of_nonneg_right (edgeMarker_budget_le_KA2 hP1 hΔ hσc.1 hσc.2 hγc.1
    hγc.2 hΛ hΔΛ (Nat.cast_nonneg _)) hν)

end Tags


end DifferentialGeometry.Geometry.Collapse
