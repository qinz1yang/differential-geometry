import DifferentialGeometry.Geometry.Fibration.ActualInnerSectionsApplications
import DifferentialGeometry.Geometry.Fibration.ActualGlobalBlockMap
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14Applications
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes

/-!
# CGP03 on the GIVEN final family (`LocalChartPacketsC14Z`), with the marker reading of preimages

External review 60 (§三 CGP03, §六.2, §七.2) and dispositions-task60: the registered `cgp03_row`
returns its sections on an EXISTENTIAL ancestor family `∃ L : LocalChartPacketsD`, which does not
say that a later fixed family `P` has them. Blueprint `master207B.tex`, CGP03 (B:4004–4016): for
`ℓ_i = 1, Δ, 10⁵Δ` (`i ∈ I_2, I_e, I_s`) a continuous section `s_i : B(0, 23ℓ_i/4) → U_i`,
`η_i s_i = id`, with image in the original threshold-6 plateau, `t < Δ/100` on edges, full `i`
marker and scale in `[3R_i/4, 5R_i/4]`.

* `blockMap_marker_one_PKG`: FC01's marker reading — a point whose FULL block `i` equals the block
  of a point with cutoff one (constant nonzero radius) has cutoff one and the SAME coordinate.
* `cgp03_row_C14Z_PKG`: for the given `P : LocalChartPacketsC14Z` (no new family is produced), from
  the pointwise section lemmas `cgp03_circle_section`, `cgp03_slim_section` (on `P`'s own charts)
  and C14's `LocalChartPacketsC14.edge_section_FAM` restricted to `B(0, 23Δ/4)` with
  `cgp03_edge_point`:
  at every circle / slim / edge centre `j`, a continuous section with `η_j ∘ s = id`, position in
  `U_j`, cutoff `= 1`, scale ratio in `[3/4, 5/4]`, `|η_j| < 6ℓ_j` (threshold-6 plateau: parameter
  ball `23/4 < 6`), on edges also `0 ≤ F/ρ < Δ/100` (the ACTUAL height `F(s(a))/ρ(s(a))`) and
  `d(s(a), j) < 10Δρ(j)`; and the marker reading: every `x` whose `j` block of
  `𝓔⁰ = cgpGlobalMap P P.zero` equals that of `s(a)` has cutoff one and `η_j(x) = a`.
  The scale budget is the producer's `ΔΛ·2·10⁶ ≤ 1/100` (as in `cgp03_row`).
* consumer `cgp03_edge_height_PKG`: the edge sections of the final family stay in the region
  `{t < Δ/100}` with full edge marker, at every edge centre.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

section Marker

variable {κ : Type*} {V : κ → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℝ (V i)]

/-- **FC01's marker reading of a preimage**: if the block `i` of `x` equals the block `i` of `y`,
the radius is the same nonzero number at both and `ζ_i(y) = 1`, then `ζ_i(x) = 1` and
`η_i(x) = η_i(y)`. -/
theorem blockMap_marker_one_PKG {M : Type*} (R ζ : κ → M → ℝ) (η : ∀ i, M → V i) {i : κ}
    {x y : M} (hR : R i x = R i y) (hR0 : R i y ≠ 0) (hy : ζ i y = 1)
    (h : blockMap R ζ η x i = blockMap R ζ η y i) : ζ i x = 1 ∧ η i x = η i y := by
  have h2 : (blockMap R ζ η x i).snd = (blockMap R ζ η y i).snd := by rw [h]
  have h1 : (blockMap R ζ η x i).fst = (blockMap R ζ η y i).fst := by rw [h]
  rw [blockMap_apply_snd, blockMap_apply_snd, hR, hy, mul_one] at h2
  have hx : ζ i x = 1 := by
    have := mul_left_cancel₀ hR0 (h2.trans (mul_one _).symm)
    exact this
  refine ⟨hx, ?_⟩
  rw [blockMap_apply_fst, blockMap_apply_fst, hR, hy, hx] at h1
  exact smul_right_injective _ (by rwa [mul_one]) h1

end Marker

/-- `planeAxis` is injective. -/
theorem planeAxis_injective_PKG : Injective planeAxis := by
  intro t t' h
  have h0 : ‖planeAxis (t - t')‖ = 0 := by rw [map_sub, h, sub_self, norm_zero]
  rw [norm_planeAxis, abs_eq_zero, sub_eq_zero] at h0
  exact h0

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- The three CGP03 scale budgets from `ΔΛ·2·10⁶ ≤ 1/100` (`Δ ≥ 1`, `Λ ≥ 0`). -/
theorem cgp03_budgets_PKG {Δ Λ : ℝ} (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (h : Δ * Λ * 2000000 ≤ 1 / 100) :
    Λ * 102 ≤ 1 / 4 ∧ Λ * (10 ^ 6 * Δ) ≤ 1 / 4 ∧ Λ * (10 * Δ) ≤ 1 / 4 := by
  have h1 : Λ ≤ Δ * Λ := by nlinarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- **CGP03 on the GIVEN final closed family** (see the module docstring). -/
theorem cgp03_row_C14Z_PKG
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hΛΔ : Δ * Λ * 2000000 ≤ 1 / 100) :
    (∀ j (hj : j ∈ P.circle.centres), ∃ sec : ball (0 : ℝ²) (23 / 4) → X, Continuous sec ∧
      ∀ a, (let c := P.circle.chart j hj;
        letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord (sec a)) = a ∧
        ‖(a : ℝ²)‖ < 6 ∧ sec a ∈ ball j (200 * ρ j) ∧ P.circle.cutoff j (sec a) = 1 ∧
        3 / 4 * ρ j ≤ ρ (sec a) ∧ ρ (sec a) ≤ 5 / 4 * ρ j ∧
        ∀ x, cgpGlobalMap P.toLocalChartFamily P.zero x
            (.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩) =
          cgpGlobalMap P.toLocalChartFamily P.zero (sec a)
            (.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩) →
          P.circle.cutoff j x = 1 ∧ (let c := P.circle.chart j hj;
            letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j)); c.coord x) = a) ∧
    (∀ j (hj : j ∈ P.slim.centres), ∃ sec : ball (0 : ℝ) (23 / 4 * (10 ^ 5 * Δ)) → X,
      Continuous sec ∧ ∀ a, (P.slim.centre j hj).coord (sec a) = a ∧
        |(a : ℝ)| < 6 * (10 ^ 5 * Δ) ∧ sec a ∈ ball j (10 ^ 6 * Δ * ρ j) ∧
        P.slim.cutoff j (sec a) = 1 ∧ 3 / 4 * ρ j ≤ ρ (sec a) ∧ ρ (sec a) ≤ 5 / 4 * ρ j ∧
        ∀ x, cgpGlobalMap P.toLocalChartFamily P.zero x
            (.inr (.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩)) =
          cgpGlobalMap P.toLocalChartFamily P.zero (sec a)
            (.inr (.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩)) →
          P.slim.cutoff j x = 1 ∧ (P.slim.centre j hj).coord x = a) ∧
    ∀ j (hj : j ∈ P.edge.centres), ∃ sec : ball (0 : ℝ) (23 / 4 * Δ) → X, Continuous sec ∧
      ∀ a, P.edge.coord j (sec a) = a ∧ |(a : ℝ)| < 6 * Δ ∧ sec a ∈ ball j (100 * Δ * ρ j) ∧
        dist (sec a) j < 10 * Δ * ρ j ∧ 0 ≤ P.edge.smoothing (sec a) / ρ (sec a) ∧
        P.edge.smoothing (sec a) / ρ (sec a) < Δ / 100 ∧ P.edge.cutoff j (sec a) = 1 ∧
        3 / 4 * ρ j ≤ ρ (sec a) ∧ ρ (sec a) ≤ 5 / 4 * ρ j ∧
        ∀ x, cgpGlobalMap P.toLocalChartFamily P.zero x
            (.inr (.inr (.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩))) =
          cgpGlobalMap P.toLocalChartFamily P.zero (sec a)
            (.inr (.inr (.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩))) →
          P.edge.cutoff j x = 1 ∧ P.edge.coord j x = a := by
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨hb102, hbslim, hbedge⟩ := cgp03_budgets_PKG hΔ hΛ hΛΔ
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · obtain ⟨sec, hsc, hsec⟩ := cgp03_circle_section P.toLocalChartFamily hΛ hb102 hj
    refine ⟨sec, hsc, fun a => ?_⟩
    obtain ⟨hco, hU, hcut, hs1, hs2⟩ := hsec a
    have ha : ‖(a : ℝ²)‖ < 23 / 4 := mem_ball_zero_iff.mp a.2
    refine ⟨hco, by linarith, hU, hcut, hs1, hs2, fun x hx => ?_⟩
    obtain ⟨h1, h2⟩ := blockMap_marker_one_PKG (cgpRadius P.toLocalChartFamily P.zero)
      (cgpCutoff P.toLocalChartFamily P.zero) (cgpCoord P.toLocalChartFamily P.zero)
      (i := .inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩) (x := x) (y := sec _) rfl
      (hρ j).ne' hcut hx
    exact ⟨h1, h2.trans hco⟩
  · obtain ⟨sec, hsc, hsec⟩ := cgp03_slim_section P.toLocalChartFamily hΔ0 hΛ hbslim hj
    refine ⟨sec, hsc, fun a => ?_⟩
    obtain ⟨hco, hU, hcut, hs1, hs2⟩ := hsec a
    have ha : |(a : ℝ)| < 23 / 4 * (10 ^ 5 * Δ) := by
      have := mem_ball_zero_iff.mp a.2
      rwa [Real.norm_eq_abs] at this
    refine ⟨hco, by linarith, hU, hcut, hs1, hs2, fun x hx => ?_⟩
    obtain ⟨h1, h2⟩ := blockMap_marker_one_PKG (cgpRadius P.toLocalChartFamily P.zero)
      (cgpCutoff P.toLocalChartFamily P.zero) (cgpCoord P.toLocalChartFamily P.zero)
      (i := .inr (.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩)) (x := x) (y := sec _) rfl
      (hρ j).ne' hcut hx
    exact ⟨h1, (planeAxis_injective_PKG h2).trans hco⟩
  · obtain ⟨sec, hsc, hsec⟩ := P.toLocalChartPacketsC14D.toLocalChartPacketsC14.edge_section_FAM hj
    let ι : ball (0 : ℝ) (23 / 4 * Δ) → Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ) := fun a =>
      ⟨a, by
        have := mem_ball_zero_iff.mp a.2
        rw [Real.norm_eq_abs] at this
        constructor <;> linarith [abs_lt.mp this]⟩
    have hι : Continuous ι := continuous_subtype_val.subtype_mk _
    refine ⟨sec ∘ ι, hsc.comp hι, fun a => ?_⟩
    obtain ⟨hco, ht0, ht, hd⟩ := hsec (ι a)
    have ha : |(a : ℝ)| < 23 / 4 * Δ := by
      have := mem_ball_zero_iff.mp a.2
      rwa [Real.norm_eq_abs] at this
    have hco' : P.edge.coord j (sec (ι a)) = a := hco
    obtain ⟨hU, hcut, hs1, hs2⟩ := cgp03_edge_point P.toLocalChartFamily hΔ0 hΛ hbedge hj
      (x := sec (ι a)) (by rw [hco']; linarith) (by linarith) hd
    refine ⟨hco', by linarith, hU, hd, ht0, ht, hcut, hs1, hs2, fun x hx => ?_⟩
    obtain ⟨h1, h2⟩ := blockMap_marker_one_PKG (cgpRadius P.toLocalChartFamily P.zero)
      (cgpCutoff P.toLocalChartFamily P.zero) (cgpCoord P.toLocalChartFamily P.zero)
      (i := .inr (.inr (.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩))) (x := x) (y := sec _) rfl
      (hρ j).ne' hcut hx
    exact ⟨h1, (planeAxis_injective_PKG h2).trans hco'⟩

/-- **Consumer: the edge sections of the final family lie in `{t < Δ/100}` with full edge marker**:
at every edge centre `j` of `P`, every point `s(a)`, `|a| < 23Δ/4`, of CGP03's edge section has
`0 ≤ t(s(a)) < Δ/100` (`t = F/ρ` of the shared smoothing, `cgpHeight`) and edge block marker
`R_jζ_j(s(a)) = ρ(j)` in `𝓔⁰`. -/
theorem cgp03_edge_height_PKG
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hΛΔ : Δ * Λ * 2000000 ≤ 1 / 100)
    {j : X} (hj : j ∈ P.edge.centres) :
    ∃ sec : ball (0 : ℝ) (23 / 4 * Δ) → X, Continuous sec ∧ ∀ a,
      cgpHeight P.toLocalChartFamily (sec a) ∈ Ico 0 (Δ / 100) ∧
      (cgpGlobalMap P.toLocalChartFamily P.zero (sec a)
        (.inr (.inr (.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩)))).snd = ρ j := by
  obtain ⟨sec, hsc, hsec⟩ := (cgp03_row_C14Z_PKG P hΔ hΛ hΛΔ).2.2 j hj
  refine ⟨sec, hsc, fun a => ?_⟩
  obtain ⟨-, -, -, -, ht0, ht, hcut, -⟩ := hsec a
  refine ⟨⟨ht0, ht⟩, ?_⟩
  change ρ j * P.edge.cutoff j (sec a) = ρ j
  rw [hcut, mul_one]

end DifferentialGeometry.Geometry.Collapse
