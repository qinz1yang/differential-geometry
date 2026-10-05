import DifferentialGeometry.Geometry.Fibration.ActualBlockBudgets

/-!
# Consumers of CGP02 (b): the budget of every block of the actual `𝓔⁰`

On CGP01's actual map `cgpGlobalMap L.toLocalChartFamily Z` (`L : LocalChartFamilyQ`, `Z` the zero
family), with the edge zero-extension margin, in the Riemannian norm `ν = √(g_x(v, v))`:

* `cgp02_scale_tag_budget`: the scale block contributes at most `Λ ν`;
* `cgp02_constant_radius_tag_budget`: every circle, slim, edge and zero block whose cutoff's closed
  support contains `x` contributes at most `B ν`, `B = 2 + 80 P₀` (CGP02's constant-radius budget),
  for `Δ ≥ 1`, `σ_s, σ_c, γ_c, ε_r ∈ [0, 1]`, `e ≤ 1/20`;
* `cgp02_edgeMarker_tag_budget`: the `E'` block contributes at most `500 (n + 1) P₀² ν` on its closed
  support, `n` the number of edge cutoffs whose closed support contains `x`
  (CGP02's variable-block constant), for `100ΔΛ ≤ 1/100`.
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

/-- The slim budget is at most `2 + 80 P₀`. -/
theorem slim_budget_le_KA2 {P Δ σ : ℝ} (hP : 1 ≤ P) (hΔ : 1 ≤ Δ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    (1 + σ) + (89 * 10 ^ 4 * Δ + 1) * (P * (1 + σ) / (10 ^ 5 * Δ)) ≤ 2 + 80 * P := by
  have hc : (0 : ℝ) < 10 ^ 5 * Δ := by positivity
  have h1 : (89 * 10 ^ 4 * Δ + 1) * (P * (1 + σ) / (10 ^ 5 * Δ)) ≤ 18 * P := by
    rw [mul_div_assoc', div_le_iff₀ hc]
    have hA : P * (1 + σ) ≤ 2 * P := by nlinarith
    have hB : 89 * 10 ^ 4 * Δ + 1 ≤ 9 * 10 ^ 5 * Δ := by nlinarith
    have hA0 : 0 ≤ P * (1 + σ) := by nlinarith
    calc (89 * 10 ^ 4 * Δ + 1) * (P * (1 + σ)) ≤ 9 * 10 ^ 5 * Δ * (2 * P) :=
          mul_le_mul hB hA hA0 (by positivity)
      _ = 18 * P * (10 ^ 5 * Δ) := by ring
  linarith

/-- The edge budget is at most `2 + 80 P₀`. -/
theorem edge_budget_le_KA2 {P Δ σ γ : ℝ} (hP : 1 ≤ P) (hΔ : 1 ≤ Δ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (1 + σ) + (9 * Δ + 1) * (P * ((1 + σ) + 100 / 99 * (1 + γ)) / Δ) ≤ 2 + 80 * P := by
  have hΔ0 : 0 < Δ := by linarith
  have h1 : (9 * Δ + 1) * (P * ((1 + σ) + 100 / 99 * (1 + γ)) / Δ) ≤ 50 * P := by
    rw [mul_div_assoc', div_le_iff₀ hΔ0]
    have hA : P * ((1 + σ) + 100 / 99 * (1 + γ)) ≤ 5 * P := by nlinarith
    have hA0 : 0 ≤ P * ((1 + σ) + 100 / 99 * (1 + γ)) := by positivity
    calc (9 * Δ + 1) * (P * ((1 + σ) + 100 / 99 * (1 + γ))) ≤ 10 * Δ * (5 * P) :=
          mul_le_mul (by linarith) hA hA0 (by positivity)
      _ = 50 * P * Δ := by ring
  linarith

/-- The zero budget is at most `2 + 80 P₀`. -/
theorem zero_budget_le_KA2 {P ε e : ℝ} (hP : 1 ≤ P) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (he : e ≤ 1 / 20) :
    (1 + ε) + (9 / 10 + 2 * e + 1) * (P * (1 + ε)) ≤ 2 + 80 * P := by
  have hA : P * (1 + ε) ≤ 2 * P := by nlinarith
  have hA0 : 0 ≤ P * (1 + ε) := by positivity
  have h1 : (9 / 10 + 2 * e + 1) * (P * (1 + ε)) ≤ 2 * (2 * P) :=
    mul_le_mul (by linarith) hA hA0 (by norm_num)
  linarith

/-- The `E'` budget is at most `500 (n + 1) P₀²`. -/
theorem edgeMarker_budget_le_KA2 {P Δ σ γ Λ n : ℝ} (hP : 1 ≤ P) (hΔ : 1 ≤ Δ) (hσ0 : 0 ≤ σ)
    (hσ1 : σ ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hΛ : 0 ≤ Λ) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100)
    (hn : 0 ≤ n) :
    (1 + γ) + (10 * Δ + 1) * (P * (1 + γ) / Δ +
      P * n * ((1 + 100 * Δ * Λ) * (P * ((1 + σ) + 100 / 99 * (1 + γ)) / Δ)) + Λ) ≤
      500 * (n + 1) * P ^ 2 := by
  have hΔ0 : 0 < Δ := by linarith
  have hK : P * ((1 + σ) + 100 / 99 * (1 + γ)) ≤ 5 * P := by nlinarith
  have hK0 : 0 ≤ P * ((1 + σ) + 100 / 99 * (1 + γ)) := by positivity
  set Kn := P * ((1 + σ) + 100 / 99 * (1 + γ)) with hKn
  have hinner : P * (1 + γ) / Δ + P * n * ((1 + 100 * Δ * Λ) * (Kn / Δ)) + Λ =
      (P * (1 + γ) + P * n * ((1 + 100 * Δ * Λ) * Kn)) / Δ + Λ := by
    field_simp
  rw [hinner, mul_add]
  have hY : P * (1 + γ) + P * n * ((1 + 100 * Δ * Λ) * Kn) ≤ 2 * P + 6 * n * P ^ 2 := by
    have h1 : P * (1 + γ) ≤ 2 * P := by nlinarith
    have h2 : (1 + 100 * Δ * Λ) * Kn ≤ 6 * P := by nlinarith
    have hPn : 0 ≤ P * n := by positivity
    have h3 : P * n * ((1 + 100 * Δ * Λ) * Kn) ≤ P * n * (6 * P) :=
      mul_le_mul_of_nonneg_left h2 hPn
    nlinarith
  have hY0 : 0 ≤ P * (1 + γ) + P * n * ((1 + 100 * Δ * Λ) * Kn) := by positivity
  have hA : (10 * Δ + 1) * ((P * (1 + γ) + P * n * ((1 + 100 * Δ * Λ) * Kn)) / Δ) ≤
      11 * (2 * P + 6 * n * P ^ 2) := by
    rw [mul_div_assoc', div_le_iff₀ hΔ0]
    calc (10 * Δ + 1) * (P * (1 + γ) + P * n * ((1 + 100 * Δ * Λ) * Kn)) ≤
          11 * Δ * (2 * P + 6 * n * P ^ 2) := mul_le_mul (by linarith) hY hY0 (by positivity)
      _ = 11 * (2 * P + 6 * n * P ^ 2) * Δ := by ring
  have hB : (10 * Δ + 1) * Λ ≤ 1 := by nlinarith
  have hP2 : P ≤ P ^ 2 := by nlinarith
  nlinarith

end Arithmetic

section Tags

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- **The scale block of `𝓔⁰`**: `‖d(0, ρ)(v)‖ ≤ Λ ν`. -/
theorem cgp02_scale_tag_budget
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΛ : 0 ≤ Λ) (x : X)
    (v : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap L Z y (cgpScaleTag L Z)) x v‖ ≤
      Λ * Real.sqrt (g.inner x v v) := by
  have : CompleteSpace X := complete_of_compact
  exact norm_mvfderiv_scaleBlock_le_riemannian (W := ℝ²) g hmetric hΛ L.lipschitz_scale
    ((L.contMDiff_scale x).mdifferentiableAt (by simp)) (hρ x).le v

/-- **The constant-radius blocks of `𝓔⁰`** (circle, slim, edge, zero): at a point of the block's
closed support, `‖d(block)(v)‖ ≤ (2 + 80 P₀) ν`. -/
theorem cgp02_constant_radius_tag_budget
    (L : LocalChartFamilyQ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 1 ≤ Δ)
    (hσs : σs ∈ Icc (0 : ℝ) 1) (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1)
    (hεr : εr ∈ Icc (0 : ℝ) 1) (he : e ≤ 1 / 20)
    (hmargin : ∀ j ∈ L.edge.centres, tsupport (L.edge.cutoff j) ⊆ ball j (100 * Δ * ρ j))
    (i : CGPTag L.toLocalChartFamily Z) (hiρ : i ≠ cgpScaleTag L.toLocalChartFamily Z)
    (hiE : i ≠ cgpEdgeTag L.toLocalChartFamily Z) {x : X}
    (hx : x ∈ tsupport (cgpCutoff L.toLocalChartFamily Z i)) (v : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap L.toLocalChartFamily Z y i) x v‖ ≤
      (2 + 80 * cgpProfileBound) * Real.sqrt (g.inner x v v) := by
  have hP1 := cgpProfileBound_spec.1
  have hν : 0 ≤ Real.sqrt (g.inner x v v) := Real.sqrt_nonneg _
  have hΔ0 : 0 < Δ := by linarith
  rcases i with j | j | j | i | bb
  · have h := circle_block_budget_KA2 L ((Set.Finite.mem_toFinset _).mp j.2) hx v
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hν)
    linarith
  · have h := slim_block_budget_KA2 L hΔ0 hσs.1 ((Set.Finite.mem_toFinset _).mp j.2) hx v
    exact h.trans (mul_le_mul_of_nonneg_right
      (slim_budget_le_KA2 hP1 hΔ hσs.1 hσs.2) hν)
  · have hj := (Set.Finite.mem_toFinset _).mp j.2
    have h := edge_block_budget_KA2 L.edge hΔ0 hσc.1 hγc.1 L.contMDiff_scale.continuous hj
      (hmargin j.1 hj) hx v
    exact h.trans (mul_le_mul_of_nonneg_right
      (edge_budget_le_KA2 hP1 hΔ hσc.1 hσc.2 hγc.1 hγc.2) hν)
  · have h := zero_block_budget_KA2 (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)) hmetric
      hεr.1 (by linarith) hx v
    exact h.trans (mul_le_mul_of_nonneg_right
      (zero_budget_le_KA2 hP1 hεr.1 hεr.2 he) hν)
  · cases bb
    · exact absurd rfl hiρ
    · exact absurd rfl hiE

open Classical in
/-- **The `E'` block of `𝓔⁰`**: on its closed support, `‖d(block)(v)‖ ≤ 500 (n + 1) P₀² ν`,
`n` the number of edge cutoffs whose closed support contains `x`. -/
theorem cgp02_edgeMarker_tag_budget
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1)
    (hmargin : ∀ j ∈ L.edge.centres, tsupport (L.edge.cutoff j) ⊆ ball j (100 * Δ * ρ j))
    {x : X} (hx : x ∈ tsupport (cgpCutoff L Z (cgpEdgeTag L Z)))
    (v : TangentSpace 𝓘(ℝ, E3) x) :
    ‖mvfderiv 𝓘(ℝ, E3) (fun y => cgpGlobalMap L Z y (cgpEdgeTag L Z)) x v‖ ≤
      500 * (((Finset.univ.filter fun i : L.edge.finite_centres.toFinset =>
        x ∈ tsupport (L.edge.cutoff i)).card : ℝ) + 1) * cgpProfileBound ^ 2 *
        Real.sqrt (g.inner x v v) := by
  have hP1 := cgpProfileBound_spec.1
  have hν : 0 ≤ Real.sqrt (g.inner x v v) := Real.sqrt_nonneg _
  have h := edgeMarker_block_budget_KA2 L (by linarith) hΛ hσc.1 hγc.1 hmargin hx v
  exact h.trans (mul_le_mul_of_nonneg_right (edgeMarker_budget_le_KA2 hP1 hΔ hσc.1 hσc.2 hγc.1
    hγc.2 hΛ hΔΛ (Nat.cast_nonneg _)) hν)

end Tags

end DifferentialGeometry.Geometry.Collapse
