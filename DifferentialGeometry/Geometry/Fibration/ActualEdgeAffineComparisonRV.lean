import DifferentialGeometry.Geometry.Fibration.ActualEdgeSlimComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsValueApplications

/-!
# EGP04 (EC) for `J_e ∪ J_s` on the final family with LFR19's slim value tolerance

Blueprint `master207B.tex`, EGP04 (`lem:fibration-edge-actual-comparison`, B:4943–5040): "Use LFR19
with separate value errors less than `θ/100`"; "the value assertion in both cases follows
independently from (ER) and the two original value errors, at cost `E + (1 + s_j)θ/100 < θ`".
The edge value error is the edge chart's `μΔ` (`EdgeFamily.value_KC2`); the slim value error is
the field `slim_value` of `LocalChartPacketsRV … vs` (`|η_j − u_j| < v_s` on `B(j, 10⁶Δρ(j))`).

* `slim_meeting_ball_KC3`: a slim centre whose cutoff support meets `D_i` has `s_j < 1.01` and
  `D_i ⊆ B(j, 10⁶Δρ(j))`.
* `egp04_slim_value_arith_KC3`, `egp04_slim_value_pair_KC3`: the `J_s` value clause at one pair.
* `egp04_row`: EGP04's (EC), value and derivative clauses, for every `j ∈ J_e` and every slim
  `j` meeting `D_i` (one sign per `j` for both clauses), on every actual `LocalChartPacketsRV`.

Not here: the zero block (LC67 / LC73 on the zero packets).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- EGP04's slim value budget: `|s_j η_j − (a η_i + s_j c)| < s_j v_s + E + μΔ < θ` for
`s_j < 1.01`, `v_s, μΔ < θ/100` and `E ≤ θ²/10⁸`. -/
theorem egp04_slim_value_arith_KC3 {sj a ηj ηi uj ui c E vs m θ : ℝ} (hsj : 0 < sj)
    (hs2 : sj < 101 / 100) (ha : a = 1 ∨ a = -1) (hj : |ηj - uj| < vs) (hi : |ηi - ui| < m)
    (hRA : |sj * uj - a * ui - sj * c| < E) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hE : E ≤ θ ^ 2 / 10 ^ 8) (hm : m < θ / 100) (hvs : vs < θ / 100) :
    |sj * ηj - (a * ηi + sj * c)| < θ := by
  have hsplit : sj * ηj - (a * ηi + sj * c) =
      sj * (ηj - uj) + (sj * uj - a * ui - sj * c) - a * (ηi - ui) := by ring
  have haabs : |a| = 1 := by rcases ha with rfl | rfl <;> norm_num
  have hvs0 : 0 < vs := lt_of_le_of_lt (abs_nonneg _) hj
  have h1 : sj * |ηj - uj| < sj * vs := mul_lt_mul_of_pos_left hj hsj
  have h2 : sj * vs ≤ 101 / 100 * vs := mul_le_mul_of_nonneg_right hs2.le hvs0.le
  have hθ2 : θ ^ 2 ≤ θ := by nlinarith
  rw [hsplit]
  calc _ ≤ |sj * (ηj - uj) + (sj * uj - a * ui - sj * c)| + |a * (ηi - ui)| := abs_sub _ _
    _ ≤ |sj * (ηj - uj)| + |sj * uj - a * ui - sj * c| + |a * (ηi - ui)| := by
        gcongr; exact abs_add_le _ _
    _ = sj * |ηj - uj| + |sj * uj - a * ui - sj * c| + |ηi - ui| := by
        rw [abs_mul, abs_mul, abs_of_pos hsj, haabs, one_mul]
    _ < θ := by linarith

section Pair

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ}

/-- A slim centre `j` whose cutoff support meets `D_i = B(i, 20Δρ(i))` has `ρ(j)/ρ(i) < 1.01` and
`D_i ⊆ B(j, 10⁶Δρ(j))`. -/
theorem slim_meeting_ball_KC3
    (L : LocalChartFamilyE X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) {i j : X}
    (hjc : j ∈ L.slim.centres)
    (hj : (tsupport (L.slim.cutoff j) ∩ ball i (20 * Δ * ρ i)).Nonempty) :
    ρ j / ρ i < 101 / 100 ∧ ball i (20 * Δ * ρ i) ⊆ ball j (10 ^ 6 * Δ * ρ j) := by
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  have hrj := hρ j
  have hρL : LipschitzWith (Real.toNNReal Λ) ρ := L.lipschitz_scale
  have hc : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ
  obtain ⟨y₀, hy1, hy2⟩ := hj
  have hsl := fc18_slim_row L.toLocalChartFamily hΔ0 hjc
  have hm : (closedBall j ((910000 * Δ) * ρ j) ∩ ball i ((20 * Δ) * ρ i)).Nonempty :=
    ⟨y₀, hsl.1 hy1, hy2⟩
  have hΛ1 : 250 * (Λ * (20 * Δ)) ≤ 1 := by
    have e : Λ * (20 * Δ) = 1 / 50000 * (1000000 * Δ * Λ) := by ring
    linarith
  have hΛ2 : 250 * (Λ * (910000 * Δ)) ≤ 1 := by
    have e : Λ * (910000 * Δ) = 91 / 100 * (1000000 * Δ * Λ) := by ring
    linarith
  obtain ⟨-, hs2, -, h4⟩ := support_meeting_sharp_bounds hρL hri hrj (a := 20 * Δ)
    (c := 910000 * Δ) (by positivity) (by positivity) (by rw [hc]; exact hΛ1)
    (by rw [hc]; exact hΛ2) hm
  refine ⟨hs2, (h4 (20 * Δ) (by positivity)).trans (ball_subset_ball ?_)⟩
  exact mul_le_mul_of_nonneg_right (by linarith) hrj.le

/-- **EGP04's value clause for one slim chart** (`j ∈ J_s`), given EGP03's (ER) with the sign
`a`: on `D_i`, `|s_j η_j − (a η_i + s_j u_j(p_i))| < θ`, from (ER), LFR19's slim value tolerance
`v_s < θ/100` (field `slim_value`) and the edge value error `μΔ < θ/100`. -/
theorem egp04_slim_value_pair_KC3
    (P : LocalChartPacketsRV X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs)
    {θ E a : ℝ} (hΔ : 1 ≤ Δ) (hθ : 0 < θ) (hθ1 : θ < 1) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hE : E ≤ θ ^ 2 / 10 ^ 8) (hμ : μ * Δ < θ / 100)
    (hvs : vs < θ / 100) {i j : X} (hi : i ∈ P.edge.centres) (hjc : j ∈ P.slim.centres)
    (hj : (tsupport (P.slim.cutoff j) ∩ ball i (20 * Δ * ρ i)).Nonempty)
    (ha : a = 1 ∨ a = -1)
    (hER : ∀ x ∈ ball i (600 * Δ * ρ i), |ρ j / ρ i * sgpRaw P.slim j x - a * egpRaw P.edge i x -
      ρ j / ρ i * sgpRaw P.slim j i| < E) :
    ∀ x ∈ ball i (20 * Δ * ρ i),
      |ρ j / ρ i * (P.slim.centre j hjc).coord x -
        (a * P.edge.coord i x + ρ j / ρ i * sgpRaw P.slim j i)| < θ := by
  intro x hx
  obtain ⟨hs2, hsub⟩ := slim_meeting_ball_KC3 P.toLocalChartFamilyE hΔ hΛ hLΛ hjc hj
  have hri := hρ i
  have hΔ0 : 0 < Δ := by linarith
  have hxi : dist x i < 20 * Δ * ρ i := hx
  have hΔρi : 0 < Δ * ρ i := mul_pos hΔ0 hri
  have hx100i : x ∈ ball i (100 * Δ * ρ i) := mem_ball.mpr (by linarith)
  have hx600 : x ∈ ball i (600 * Δ * ρ i) := mem_ball.mpr (by linarith)
  exact egp04_slim_value_arith_KC3 (div_pos (hρ j) hri) hs2 ha
    (P.slim_value_sgpRaw hjc (hsub hx)) (P.edge.value_KC2 hi hx100i) (hER x hx600) hθ hθ1 hE hμ
    hvs

end Pair

section Row

/-- **EGP04 (EC) for `J_e ∪ J_s` on the actual final family with LFR19's slim value tolerance.**
For `0 < θ < 1` there are a curvature radius `Lc` and a raw quality `η₀` (EGP03 at
`E = θ²/10⁸`, and `η₀ ≤ θ²/10⁸, 1/(1000L)`) such that for every actual
`P : LocalChartPacketsRV … vs` with EGP03's hypotheses, `σc, σs ≤ θ²/10⁸` (`σs > 0`) and the
separate value errors `μΔ, v_s < θ/100`, at every edge centre `i`: every `j ∈ J_e` and every slim
centre `j` whose cutoff support meets `D_i` have ONE sign `a` with, on `D_i = B(i, 20Δρ(i))`,
`|s_j η_j − (a η_i + s_j u_j(p_i))| < θ` and `|s_j dη_j(w) − a dη_i(w)| < θ` for every unit
vector `w` of `ρ(i)⁻² g`. -/
theorem egp04_row {Δ β₂ θ : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 1000000)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ)
        (P : LocalChartPacketsRV X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
          e T V vs),
        b ≤ η₀ → s < 1 / 1000000 → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ →
        1000000 * Δ * Λ < 1 / 100000 → μ ≤ 1 / 100 → τ ≤ 1 / 100 → σc ≤ θ ^ 2 / 10 ^ 8 →
        μ * Δ < θ / 100 → 0 < σs → σs ≤ θ ^ 2 / 10 ^ 8 → vs < θ / 100 → ∀ i ∈ P.edge.centres,
          (∀ j ∈ egpEdgeList P.toLocalChartFamily i, ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            ∀ x ∈ ball i (20 * Δ * ρ i),
              |ρ j / ρ i * P.edge.coord j x -
                  (a * P.edge.coord i x + ρ j / ρ i * egpRaw P.edge j i)| < θ ∧
                ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
                  |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (P.edge.coord j) x w -
                    a * mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w| < θ) ∧
          ∀ j (hj : j ∈ P.slim.centres),
            (tsupport (P.slim.cutoff j) ∩ ball i (20 * Δ * ρ i)).Nonempty →
            ∃ a : ℝ, (a = 1 ∨ a = -1) ∧ ∀ x ∈ ball i (20 * Δ * ρ i),
              |ρ j / ρ i * (P.slim.centre j hj).coord x -
                  (a * P.edge.coord i x + ρ j / ρ i * sgpRaw P.slim j i)| < θ ∧
                ∀ w : TangentSpace 𝓘(ℝ, E3) x, (ρ i)⁻¹ ^ 2 * g.inner x w w = 1 →
                  |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj).coord x w -
                    a * mvfderiv 𝓘(ℝ, E3) (P.edge.coord i) x w| < θ := by
  have hE : (0 : ℝ) < θ ^ 2 / 10 ^ 8 := by positivity
  obtain ⟨Lc, η₃, hLc, hη₃, h3⟩ := egp03_row hΔ hβ₂ hβ₂1 hE
  have hΔ0 : 0 < Δ := by linarith
  refine ⟨Lc, min η₃ (min (θ ^ 2 / 10 ^ 8) (1 / (1000 * (1000000 * Δ)))), hLc,
    lt_min hη₃ (lt_min hE (by positivity)), ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs P hb hs
    hβ1 hLmax hΛ hLΛ hμ hτ hσc hμΔ hσs0 hσs hvs i hi
  obtain ⟨he, hsl⟩ := h3 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ
    P.toLocalChartFamilyE (hb.trans (min_le_left _ _)) hs (hβ1.trans (min_le_left _ _)) hLmax hΛ
    hLΛ hμ hτ i hi
  refine ⟨fun j hj => ?_, fun j hj hmeet => ?_⟩
  · obtain ⟨a, ha, hER⟩ := he j hj
    exact ⟨a, ha, egp04_edge_pair_KC2 P.toLocalChartFamilyE hΔ hθ hθ1 hΛ hLΛ hμ hτ
      (hb.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (hb.trans ((min_le_right _ _).trans (min_le_right _ _))) le_rfl hσc hμΔ hi hj ha hER⟩
  · obtain ⟨a, ha, hER⟩ := hsl j ⟨hj, hmeet⟩
    have hval := egp04_slim_value_pair_KC3 P hΔ hθ hθ1 hΛ hLΛ le_rfl hμΔ hvs hi hj hmeet ha hER
    have hder := egp04_slim_derivative_pair_KC3 P.toLocalChartFamilyE hΔ hθ hθ1 hΛ hLΛ
      (hβ1.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (hβ1.trans ((min_le_right _ _).trans (min_le_right _ _))) le_rfl hσc hσs0 hσs hi hj hmeet
      ha hER
    exact ⟨a, ha, fun x hx => ⟨hval x hx, hder x hx⟩⟩

end Row

end DifferentialGeometry.Geometry.Collapse
