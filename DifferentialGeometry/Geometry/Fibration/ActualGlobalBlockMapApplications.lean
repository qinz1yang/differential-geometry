import DifferentialGeometry.Geometry.Fibration.ActualGlobalBlockMap

/-!
# Consumers of CGP01

* `cgp01_edge_cutoff_eq_one`: on the joint inner region `|η_j| < 8Δ`, `t < 8Δ` of the original
  chart ball, the actual edge cutoff of `𝓔⁰` is one (CFS23's full marker).
* `cgp01_edge_marker_block`: the `E'` block of `𝓔⁰` has marker `ρ z₀ ∈ [0, ρ]`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- On the joint inner region the actual edge cutoff is one. -/
theorem cgp01_edge_cutoff_eq_one
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΔ : 0 < Δ)
    {j : X} (hj : j ∈ L.edge.centres) {p : X} (hp : p ∈ ball j (100 * Δ * ρ j))
    (hη : |L.edge.coord j p| < 8 * Δ) (ht : cgpHeight L p < 8 * Δ) : L.edge.cutoff j p = 1 := by
  rw [cgp01_edge_identity L hj hp hη hΔ, cfsRamp_eq_zero
    (fun y hy => lc87EdgeTransition_eq_zero hy) (by norm_num), sub_zero]
  rw [div_le_iff₀ hΔ]
  linarith

/-- The `E'` block of `𝓔⁰` has marker `ρ z₀ ∈ [0, ρ]`. -/
theorem cgp01_edge_marker_block
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (p : X) :
    (cgpGlobalMap L Z p (cgpEdgeTag L Z)).snd ∈ Icc 0 (ρ p) := by
  rw [cgpGlobalMap_edgeMarker]
  have h := cgpEdgeMarker_mem_Icc L p
  have hr := (hρ p).le
  exact ⟨mul_nonneg hr h.1, by nlinarith [h.1, h.2]⟩

end DifferentialGeometry.Geometry.Collapse
