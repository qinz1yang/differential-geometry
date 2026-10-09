import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14Producer
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartFamilyBindings

/-!
# Consumers of the final chapter-13 family (`LocalChartPacketsC14`)

Lane C14-FAM (design `build-logs/resume/design-C14-FAM.md` (b), (c)).

* `LocalChartPacketsZ.zero_shell_rank_FAM` (R5): LPA05's raw shell clause, dropped by every
  producer, is DERIVABLE from the field `zero_shell_split`: at every point `q` of a closed zero
  shell, `HasEuclideanSplitting q 1 β₁` in `ρ(q)⁻¹ d` and `splittingRank β 3 ≠ 0`.
* `LocalChartPackets.zero_curvature_of_buffer_FAM` (R6, the quantifier route): once `400V ≤ Lmax`
  (requestable in `eventually_nonempty_localChartPacketsC14`, where `Lmax` is bound after `V`), the
  family's own `sectional_buffer` gives LPA05's enlarged zero-ball curvature
  `sec ≥ -(1/60)² r_c⁻²` on `B(c, 400 r_c)` (the field `zero_curvature` holds for every `Lmax`).
* `LocalChartPacketsC14.edge_section_FAM` (R9): EGP05's section in physical form: a continuous
  `s : (-8.5Δ, 8.5Δ) → X` with `η_j ∘ s = id` (`EdgeFamily.coord`), `0 ≤ t ∘ s < Δ/100` (`t = F/ρ`)
  and image in `B(p_j, 10Δρ(j))` (blueprint 207B, B:5042–5053).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_FAM
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_FAM
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_FAM
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **LPA05's raw shell clause from the zero shell field** (R5): at every point `q` of the closed
shell `r/10 ≤ d(c, q) ≤ 10r` of a selected zero ball, `(X, ρ(q)⁻¹ d, q)` has a `(1, β₁)`-splitting
and its splitting rank (up to `3`) is not zero. -/
theorem LocalChartPacketsZ.zero_shell_rank_FAM
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) {c : X} (hc : c ∈ P.zero.centres) {q : X}
    (hq1 : (P.zero.zero c hc).radius / 10 ≤ dist c q)
    (hq2 : dist c q ≤ 10 * (P.zero.zero c hc).radius) :
    @HasEuclideanSplitting.{0, 0} X (mX.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q 1 (β 1) ∧
      @splittingRank.{0, 0} X (mX.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q β 3 ≠ 0 := by
  obtain ⟨Zf, mZ, z, F, -⟩ := P.zero_shell_split c hc q hq1 hq2
  have h : @HasEuclideanSplitting.{0, 0} X (mX.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q 1 (β 1) :=
    ⟨Zf, mZ, z, ⟨F⟩⟩
  refine ⟨h, ?_⟩
  have h1 := @le_splittingRank.{0, 0} X (mX.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q β 3 1
    (by norm_num) h
  omega

/-- **LPA05's enlarged zero-ball curvature from the sectional buffer** (R6, quantifier route):
if `400V ≤ Lmax`, then at every selected zero centre `c`, `sec ≥ -(1/60)² r_c⁻²` on
`B(c, 400 r_c)`. -/
theorem LocalChartPackets.zero_curvature_of_buffer_FAM
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hL : 400 * V ≤ Lmax) {c : X} (hc : c ∈ P.zero.centres) :
    ∀ y ∈ ball c (400 * (P.zero.zero c hc).radius),
      SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * ((P.zero.zero c hc).radius)⁻¹ ^ 2)) := by
  intro y hy
  have hr := (P.zero.zero c hc).radius_pos
  have hrV := (P.zero.radius_mem c hc).2
  have hρc := hρ c
  have hV : 0 < V := by
    by_contra hV
    have : V * ρ c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hV) hρc.le
    linarith
  have hsub : 400 * (P.zero.zero c hc).radius ≤ 400 * V * ρ c := by nlinarith
  have hbuf := P.sectional_buffer (400 * V) (by positivity) hL c y (ball_subset_ball hsub hy)
  refine hbuf.mono ?_
  have he : (1 / 60 : ℝ) ^ 2 * ((P.zero.zero c hc).radius)⁻¹ ^ 2 =
      ((60 * (P.zero.zero c hc).radius) ^ 2)⁻¹ := by
    field_simp
  rw [he, neg_le_neg_iff]
  apply inv_anti₀ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  nlinarith

/-- **EGP05's section on the final family, physical form** (R9): at every edge centre `j`, a
continuous `s : (-8.5Δ, 8.5Δ) → X` with `η_j(s(a)) = a`, `0 ≤ F(s(a))/ρ(s(a)) < Δ/100` and
`d(s(a), j) < 10Δρ(j)`. -/
theorem LocalChartPacketsC14.edge_section_FAM
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      vs ζ Λz) {j : X} (hj : j ∈ P.edge.centres) :
    ∃ sec : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ) → X, Continuous sec ∧
      ∀ a : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ), P.edge.coord j (sec a) = a ∧
        0 ≤ P.edge.smoothing (sec a) / ρ (sec a) ∧
        P.edge.smoothing (sec a) / ρ (sec a) < Δ / 100 ∧ dist (sec a) j < 10 * Δ * ρ j := by
  have hnn := P.edge.smoothing_nonneg
  obtain ⟨sec, hsc, hsec⟩ := P.edge_section j hj
  refine ⟨sec, hsc, fun a => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hsec a
  have hrj := hρ j
  have hrs := hρ (sec a)
  refine ⟨?_, div_nonneg (hnn _) hrs.le, ?_, ?_⟩
  · simp only [EdgeFamily.coord, dite_eq_left hj]
    exact h1
  · have hq : P.edge.smoothing (sec a) / ρ j / (ρ (sec a) / ρ j) =
        P.edge.smoothing (sec a) / ρ (sec a) := by
      field_simp
    rw [← hq]
    exact h2
  · have h3' : (ρ j)⁻¹ * dist (sec a) j < 10 * Δ := h3
    rw [inv_mul_lt_iff₀ hrj] at h3'
    linarith

end DifferentialGeometry.Geometry.Collapse
