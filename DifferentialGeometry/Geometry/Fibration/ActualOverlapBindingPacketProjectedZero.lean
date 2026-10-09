import DifferentialGeometry.Geometry.Fibration.ActualOverlapBindingPacketProjected
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsZeroApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes

/-!
# FC23 item 2, zero block, at the projected bases without the scale-ratio hypothesis

Lane C14-ROWS-S. Blueprint `master207B.tex`, FC23 (B:1505–1541), zero radial line of the binding
matrix ("FC13's original shell and LC73; original radial directional estimate, `R₀/r` retained").
Lane C14-ROWS-FC's zero-block configurations at the projected bases
(`fc23_edgebase_zero_tests_RFC`, `fc23_slimbase_zero_tests_RFC`) take `.99ρ(i) < ρ(x) < 1.01ρ(i)`
as hypotheses. Here the ratio is DERIVED on the actual family from the field
`lipschitz_scale` (`ρ` is `Λ`-Lipschitz) and the register clause `10⁶ΔΛ < 10⁻⁵`
(`fc23_scale_ratio_RWS`; both bases have `D_i ⊆ B(i, .95·10⁶Δρ(i))`), and the zero rows are
stated on the complete closed family with its own LC73 parameters `ζ`, `Λz`:

* `fc23_scale_ratio_RWS`: `x ∈ B(i, .95·10⁶Δρ(i))` ⟹ `.99ρ(i) < ρ(x) < 1.01ρ(i)`.
* ROW `fc23_edgebase_zero_row_RWS` (edge base `D_i = B(i, 20Δρ(i))`, EGP04) and ROW
  `fc23_slimbase_zero_row_RWS` (slim base `D_i = B(i, .95·10⁶Δρ(i))`, SGP03): at every `x ∈ D_i`
  the scale ratio, LC73's inputs for every zero support meeting `D_i` (closed shell
  `R₀/10 ≤ d(k, x) ≤ 10R₀`, `Λz ≤ R₀/ρ(x)`), and for each sign `a₀` the reference lift in LC73's
  test domain `ρ(x) < d(x, y) < ζ⁻¹ρ(x)`.
* `fc23_zero_premises_RWS`: the numerical premises of both rows hold simultaneously.

Consumer: `fc23_edgebase_zero_far_RWS` (the zero test length is at least `ρ(i)/2`).
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

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **The scale ratio on the projected bases** (slow variation of `ρ`): on the actual family,
`x ∈ B(i, .95·10⁶Δρ(i))` and `10⁶ΔΛ < 10⁻⁵` give `.99ρ(i) < ρ(x) < 1.01ρ(i)`. -/
theorem fc23_scale_ratio_RWS
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc) (hΛ : 0 ≤ Λ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) {i x : X}
    (hx : x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i)) :
    99 / 100 * ρ i < ρ x ∧ ρ x < 101 / 100 * ρ i := by
  have hlip : |ρ x - ρ i| ≤ Λ * dist x i := by
    have h := L.lipschitz_scale.dist_le_mul x i
    rwa [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h
  exact sgp03_rho_ratio_SGP3 (hρ i) hΛ hlip (mem_ball.mp hx) hLΛ

omit [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] in
/-- `D_i = B(i, 20Δρ(i))` lies in `B(i, .95·10⁶Δρ(i))`. -/
theorem fc23_edgebase_subset_RWS (hΔ : 1 ≤ Δ) {i : X} (hri : 0 < ρ i) :
    ball i (20 * Δ * ρ i) ⊆ ball i (95 / 100 * (1000000 * Δ) * ρ i) :=
  ball_subset_ball (by nlinarith)

/-- **FC23 item 2, zero block, at the edge base** (EGP04, `D_i = B(i, 20Δρ(i))`), on the complete
closed family with its LC73 parameters `ζ`, `Λz` (`20Λz ≤ T`, `0 < ζ ≤ 1/(1000·10⁶Δ)`): for every
`x ∈ D_i`, (a) `.99ρ(i) < ρ(x) < 1.01ρ(i)`; (b) every zero support meeting `D_i` has `x` in LC73's
closed shell and `Λz ≤ R₀/ρ(x)`; (c) for each sign `a₀` the reference lift `y` of length `400Δρ(i)`
(EGP04's raw-offset lift, a `g`-unit direction reaching it, the edge test domains of `i`, the
(ER) ball) lies in LC73's test domain `ρ(x) < d(x, y) < ζ⁻¹ρ(x)`. -/
theorem fc23_edgebase_zero_row_RWS
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (hΛz : 20 * Λz ≤ T)
    (hbL : b ≤ 1 / (1000 * (1000000 * Δ))) (hζ0 : 0 < ζ)
    (hζL : ζ ≤ 1 / (1000 * (1000000 * Δ))) {i : X} (hi : i ∈ P.edge.centres) :
    ∀ x ∈ ball i (20 * Δ * ρ i),
      (99 / 100 * ρ i < ρ x ∧ ρ x < 101 / 100 * ρ i) ∧
      (∀ k (hk : k ∈ P.zero.centres),
        (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
          ((P.zero.zero k hk).radial y)) ∩ ball i (20 * Δ * ρ i)).Nonempty →
        (P.zero.zero k hk).radius / 10 ≤ dist k x ∧ dist k x ≤ 10 * (P.zero.zero k hk).radius ∧
          Λz ≤ (P.zero.zero k hk).radius / ρ x) ∧
      ∀ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) →
      ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
        ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
        |egpRaw P.edge i y - egpRaw P.edge i x - 400 * Δ * a₀| < 2 * b ∧
        (400 * Δ - 3 * b) * ρ i < dist x y ∧ dist x y < (400 * Δ + 3 * b) * ρ i ∧
        x ∈ ball i (100 * Δ * ρ i) ∧ y ∈ ball i (1000 * Δ * ρ i) ∧ 100 * Δ * ρ i < dist x y ∧
        x ∈ ball i (600 * Δ * ρ i) ∧ y ∈ ball i (600 * Δ * ρ i) ∧
        ρ x < dist x y ∧ dist x y < ζ⁻¹ * ρ x := by
  intro x hx
  have hΔ0 : 0 < Δ := by linarith
  have hT0 : 0 < T := by
    have : (0 : ℝ) < 1600 * (1000000 * Δ) := by positivity
    linarith
  have hsmall : 2 * (20 * Δ / T) + 2 * (20 * Δ * Λ) ≤ 1 / 40 := by
    have h1 : 20 * Δ / T ≤ 1 / 80000 := by
      rw [div_le_iff₀ hT0]
      linarith
    have h2 : 20 * Δ * Λ ≤ 1 / 5000000 := by nlinarith
    linarith
  obtain ⟨hρ1, hρ2⟩ := fc23_scale_ratio_RWS P.toLocalChartFamily hΛ hLΛ
    (fc23_edgebase_subset_RWS hΔ (hρ i) hx)
  refine ⟨⟨hρ1, hρ2⟩, fun k hk hmeet => ?_, fun a₀ ha₀ => ?_⟩
  · obtain ⟨h1, h2, -, h4⟩ := zero_adapted_ratio_ZERO P.toLocalChartPacketsZ hΛ he hT0 hΛz i
      (by positivity : (0 : ℝ) < 20 * Δ) hsmall hk hmeet x hx
    exact ⟨h1, h2, h4⟩
  · exact fc23_edgebase_zero_tests_RFC P.edge hΔ hbL hζ0 hζL hi hx hρ1 hρ2 ha₀

/-- **FC23 item 2, zero block, at the slim base** (SGP03, `D_i = B(i, .95Lρ(i))`, `L = 10⁶Δ`), on
the complete closed family with its LC73 parameters (`20Λz ≤ T`, `0 < ζ < 1/(100L)`): for every
`x ∈ D_i`, (a) `.99ρ(i) < ρ(x) < 1.01ρ(i)`; (b) every zero support meeting `D_i` has `x` in LC73's
closed shell and `Λz ≤ R₀/ρ(x)`; (c) for each sign `a₀` SGP03's reference lift `y` (length
`≈ 10Lρ(i)`, the slim test domains of `i`, the (RA) ball) lies in LC73's test domain
`ρ(x) < d(x, y) < ζ⁻¹ρ(x)`. -/
theorem fc23_slimbase_zero_row_RWS
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (hΛz : 20 * Λz ≤ T) {δr : ℝ} (hδ1 : δr < 1)
    (hβ : β 1 ≤ min (1 / (1000 * (1000000 * Δ))) (δr / 100)) (hσs : 0 < σs)
    (hσs24 : σs * 24 ≤ 1) (hζ : 0 < ζ) (hζL : ζ < 1 / (100 * (1000000 * Δ))) {i : X}
    (hi : i ∈ P.slim.centres) :
    ∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i),
      (99 / 100 * ρ i < ρ x ∧ ρ x < 101 / 100 * ρ i) ∧
      (∀ k (hk : k ∈ P.zero.centres),
        (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
          ((P.zero.zero k hk).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty →
        (P.zero.zero k hk).radius / 10 ≤ dist k x ∧ dist k x ≤ 10 * (P.zero.zero k hk).radius ∧
          Λz ≤ (P.zero.zero k hk).radius / ρ x) ∧
      ∀ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) →
      ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
        ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
        |(ρ i)⁻¹ * dist x y - 10 * (1000000 * Δ)| < 2 * δr ∧
        10 * (1000000 * Δ) - δr < a₀ * (sgpRaw P.slim i y - sgpRaw P.slim i x) ∧
        x ∈ ball i (10 ^ 6 * Δ * ρ i) ∧ y ∈ ball i (10 ^ 6 * Δ / σs * ρ i) ∧
        10 ^ 6 * Δ * ρ i < dist x y ∧
        x ∈ ball i (30 * (1000000 * Δ) * ρ i) ∧ y ∈ ball i (30 * (1000000 * Δ) * ρ i) ∧
        ρ x < dist x y ∧ dist x y < ζ⁻¹ * ρ x := by
  intro x hx
  obtain ⟨hT0, hℓ, hsmall⟩ := sgp01_zero_smallness_ZERO hΔ hLΛ hT
  obtain ⟨hρ1, hρ2⟩ := fc23_scale_ratio_RWS P.toLocalChartFamily hΛ hLΛ hx
  refine ⟨⟨hρ1, hρ2⟩, fun k hk hmeet => ?_, fun a₀ ha₀ => ?_⟩
  · obtain ⟨h1, h2, -, h4⟩ := zero_adapted_ratio_ZERO P.toLocalChartPacketsZ hΛ he hT0 hΛz i hℓ
      hsmall hk hmeet x hx
    exact ⟨h1, h2, h4⟩
  · exact fc23_slimbase_zero_tests_RFC P.slim hΔ hδ1 hβ hσs hσs24 hζ hζL hi hx hρ1 hρ2 ha₀

/-- **The numerical premises of both zero rows hold simultaneously** (e.g. `Δ = 1`, `Λ = 0`,
`e = 1/80`, `T = 1600·10⁶`, `Λz = 0`, `b = 1/10⁹`, `ζ = 1/10¹⁰`, `δr = 1/2`, `β₁ = 1/10¹⁰`,
`σs = 1/100`). -/
theorem fc23_zero_premises_RWS :
    ∃ Λ Δ e T Λz b ζ δr β₁ σs : ℝ, 0 ≤ Λ ∧ 1 ≤ Δ ∧ 1000000 * Δ * Λ < 1 / 100000 ∧ e < 1 / 40 ∧
      1600 * (1000000 * Δ) ≤ T ∧ 20 * Λz ≤ T ∧ b ≤ 1 / (1000 * (1000000 * Δ)) ∧ 0 < ζ ∧
      ζ ≤ 1 / (1000 * (1000000 * Δ)) ∧ ζ < 1 / (100 * (1000000 * Δ)) ∧ δr < 1 ∧
      β₁ ≤ min (1 / (1000 * (1000000 * Δ))) (δr / 100) ∧ 0 < σs ∧ σs * 24 ≤ 1 :=
  ⟨0, 1, 1 / 80, 1600 * 1000000, 0, 1 / 1000000000, 1 / 10000000000, 1 / 2, 1 / 10000000000,
    1 / 100, le_rfl, le_rfl, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num,
    le_min (by norm_num) (by norm_num), by norm_num, by norm_num⟩

/-- **Consumer: the zero test length at the edge base is at least `ρ(i)/2`** (the lower end of
LC73's domain with the derived ratio): for every `x ∈ D_i` and sign `a₀` the reference lift has
`ρ(i)/2 < d(x, y)`. -/
theorem fc23_edgebase_zero_far_RWS
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (hΛz : 20 * Λz ≤ T)
    (hbL : b ≤ 1 / (1000 * (1000000 * Δ))) (hζ0 : 0 < ζ)
    (hζL : ζ ≤ 1 / (1000 * (1000000 * Δ))) {i : X} (hi : i ∈ P.edge.centres) {x : X}
    (hx : x ∈ ball i (20 * Δ * ρ i)) {a₀ : ℝ} (ha₀ : a₀ = 1 ∨ a₀ = -1) :
    ∃ y : X, ρ i / 2 < dist x y := by
  obtain ⟨⟨hρ1, -⟩, -, htest⟩ :=
    fc23_edgebase_zero_row_RWS P hΛ hΔ hLΛ he hT hΛz hbL hζ0 hζL hi x hx
  obtain ⟨y, -, -, -, -, -, -, -, -, -, -, -, hfar, -⟩ := htest a₀ ha₀
  have := hρ i
  exact ⟨y, by linarith⟩

end DifferentialGeometry.Geometry.Collapse
