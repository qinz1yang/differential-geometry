import DifferentialGeometry.Geometry.Fibration.ActualOverlapBindingPacket
import DifferentialGeometry.Geometry.Fibration.ActualZeroMeetingClausesApplications
import DifferentialGeometry.Geometry.Fibration.ZeroAdaptedPhysicalTest

/-!
# FC23 items 1–2 at the two-stratum base: the zero radial block

Blueprint `master207B.tex`, FC23 (B:1505–1538), binding matrix row "Zero radial: FC13's original
shell and LC73 | original radial directional estimate, `R₀/r` retained; no bounded translation
assumption". On `LocalChartPacketsZ`, at a circle centre `i` and a zero ball (centre `k`, radius
`R₀`) whose cutoff support meets `D_i = B(i, 10ρ(i))`:

* item 1: every `x ∈ D_i` lies in FC13's original shell `R₀/10 ≤ d(k, x) ≤ 10R₀`, and the scale
  ratio `Λ_z ≤ R₀/ρ(i)` of LC73's adapted test holds (`R₀/r` retained, no bound on it);
* item 2: for every unit `ξ`, a long endpoint `y` (the reference lift of length `400ρ(i)` in
  direction `ξ`) and a `g`-unit `w₀` reaching it, with the reference circle's original tests
  (near ball, far ball, separation `201ρ(i)`, (TR0) ball `B(i, 1000ρ(i))`) and LC73's original
  radial test domain at scale `r = ρ(i)`: separation `ρ(i) < d(x, y)` and far ball
  `ζ d(x, y) < ρ(i)`.

* ROW `fc23_items12_zero_RFC`; consumer `fc23_zero_far_ball_RFC` (the radial test applies along
  `w₀`: `|R₀ dη₀(w₀) − (d(k, y) − d(k, x))/d(x, y)| < ζ`, LC73's own conclusion via
  `zero_adapted_test_phys_KA5`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V ζ Λz : ℝ}

/-- The model metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricNZ_RFC23
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPacketsZ`, as a named local instance. -/
local instance instChartedNZ_RFC23
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPacketsZ`, as a named local instance. -/
local instance instMetricCZ_RFC23
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **FC23 items 1–2 for the zero radial block** (B:1505–1538, zero row of the binding matrix) on
`LocalChartPacketsZ`, with `0 ≤ Λ`, `Δ ≥ 1`, `10⁶ΔΛ < 10⁻⁵`, `e < 1/40`, `1600·10⁶Δ ≤ T`,
`20Λ_z ≤ T`, `0 < ζ ≤ 1/1000`, `β₂ ≤ 1/1000`: at a circle centre `i` and a zero ball meeting
`D_i`, FC13's shell and LC73's scale ratio at every `x ∈ D_i`, and for every unit `ξ` the long
endpoint `y` with the reference circle's original tests and LC73's original radial test domain
at scale `ρ(i)`. -/
theorem fc23_items12_zero_RFC
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (hΛz : 20 * Λz ≤ T) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 1000)
    (hβ2 : β 2 ≤ 1 / 1000) {i : X} (hi : i ∈ P.circle.centres) {k : X} (hk : k ∈ P.zero.centres)
    (hmeet : (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
      ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty) :
    Λz ≤ (P.zero.zero k hk).radius / ρ i ∧
    ∀ x ∈ ball i (10 * ρ i),
      (P.zero.zero k hk).radius / 10 ≤ dist k x ∧ dist k x ≤ 10 * (P.zero.zero k hk).radius ∧
      ∀ ξ : ℝ², ‖ξ‖ = 1 →
      ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
        ScaledGeodesicReaches_RFC g hmetric x w₀ y ∧
        397 * ρ i ≤ dist x y ∧ dist x y ≤ (400 + 3 * β 2) * ρ i ∧
        ‖circleRaw_KA3 P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets i y -
          circleRaw_KA3 P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets i x -
          (400 : ℝ) • ξ‖ < 2 * β 2 ∧
        x ∈ ball i (200 * ρ i) ∧ y ∈ ball i (201 * 10000 * ρ i) ∧ 201 * ρ i < dist x y ∧
        y ∈ ball i (1000 * ρ i) ∧ ρ i < dist x y ∧ ζ * dist x y < ρ i := by
  let P' := P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets
  have hri := hρ i
  have hin := tcp01_zero_lc73_inputs_ZERO P.toLocalChartPacketsR hΛ hΔ hLΛ he hT hΛz i hk hmeet
  obtain ⟨-, -, hΛi⟩ := hin i (mem_ball_self (by positivity))
  refine ⟨hΛi, fun x hx => ?_⟩
  obtain ⟨h1, h2, -⟩ := hin x hx
  refine ⟨h1, h2, fun ξ hξ => ?_⟩
  have hs : ρ i / ρ i ∈ Ioo (99 / 100 : ℝ) (101 / 100) := by
    rw [div_self hri.ne']
    norm_num
  obtain ⟨y, w₀, hw₀, hgy, hD1, hD2, hlift, hxi, hyi, -, hsep, -, hTR⟩ :=
    fc23_circle_tests_RFC P' hi hs (by rw [dist_self]; positivity) hx hβ2 ξ hξ
  have hβ0 : 0 ≤ β 2 := by
    let Ai := P'.circleAdapted i hi
    let _ := Ai.instY
    exact (@KleinerLottApprox.error_pos X _ (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ _ _ _
      Ai.split).le
  have hfar : ζ * dist x y < ρ i := by
    have hD : dist x y ≤ 401 * ρ i := by nlinarith
    have hζD : ζ * dist x y ≤ 1 / 1000 * (401 * ρ i) :=
      mul_le_mul hζ1 hD dist_nonneg (by norm_num)
    linarith
  exact ⟨y, w₀, hw₀, hgy, hD1, hD2, hlift, hxi, hyi, hsep, hTR, by linarith, hfar⟩

/-- **Consumer: LC73's original radial test applies on FC23's configuration**: under the
hypotheses of `fc23_items12_zero_RFC`, at every `x ∈ D_i` and unit `ξ` the long endpoint `y` and
direction `w₀` of item 2 satisfy LC73's test at scale `ρ(i)`:
`|R₀ dη₀(w₀) − (d(k, y) − d(k, x))/d(x, y)| < ζ`. -/
theorem fc23_zero_far_ball_RFC
    (P : LocalChartPacketsZ X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      ζ Λz)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (hΛz : 20 * Λz ≤ T) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 1000)
    (hβ2 : β 2 ≤ 1 / 1000) {i : X} (hi : i ∈ P.circle.centres) {k : X} (hk : k ∈ P.zero.centres)
    (hmeet : (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
      ((P.zero.zero k hk).radial y)) ∩ ball i (10 * ρ i)).Nonempty)
    {x : X} (hx : x ∈ ball i (10 * ρ i)) (ξ : ℝ²) (hξ : ‖ξ‖ = 1) :
    ∃ (y : X) (w₀ : TangentSpace 𝓘(ℝ, E3) x), g.inner x w₀ w₀ = 1 ∧
      |(P.zero.zero k hk).radius * mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w₀ -
        (dist k y - dist k x) / dist x y| < ζ := by
  obtain ⟨hΛi, hrow⟩ := fc23_items12_zero_RFC P hΛ hΔ hLΛ he hT hΛz hζ hζ1 hβ2 hi hk hmeet
  obtain ⟨h1, h2, hξrow⟩ := hrow x hx
  obtain ⟨y, w₀, hw₀, hgy, -, -, -, -, -, -, -, hsep, hfar⟩ := hξrow ξ hξ
  exact ⟨y, w₀, hw₀, zero_adapted_test_phys_KA5 P hk h1 h2 (hρ i) hΛi hζ hsep hfar w₀ hw₀ hgy⟩

end DifferentialGeometry.Geometry.Collapse
