import DifferentialGeometry.Geometry.Fibration.ActualSlimZeroComparison
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes

/-!
# SGP03 with the strict error wording, slim and zero blocks on one final family

External review 60 (§三 SGP03, §四.3, §七.2) and dispositions-task60 ("SGP03: unify strict vs
non-strict error wording by an inner tolerance `θ' < θ`, `E' < min(E, θ'²/10⁶)`"). Blueprint
`master207B.tex`, SGP03 (B:4483–4512): `|U_j − λ_j(η_i)| < θ`, `‖DU_j − a_jDη_i‖ < θ` (SC) on
`D_i ∩ B(p_j, LR_j)` (norms of `R_i⁻²g`), the model-support enclosure, and the analogous two bounds
on ALL of `D_i` for a meeting zero support. The registered parts (`sgp03_row`, `sgp03_zero_row`)
give the derivative bound in the NON-strict form `≤ θ|w|` and need `E < θ²/10⁶`.

* `sgp03_strict_row_PKG`: the inner tolerances are fixed as `θ' = θ/2` and
  `E' = min(E/2, θ'²/(2·10⁶))`, so `θ' < θ`, `0 < E' < min(E, θ'²/10⁶)` (the raw tolerance is
  decreased TOGETHER with `θ`, review 60 §4.3); both parts are called at `(θ', E')` on the SAME
  `P : LocalChartPacketsC14Z` (ONE `Lc` = max, ONE `η₀` = min). Output at every slim reference `i`:
  for every `j ∈ J_i` ONE sign `a` with (RA) `< E` on `B(i, 30Lρ(i))`, derivative `≤ (θ/2)|w|`
  (so `‖DU_j − aDη_i‖ ≤ θ/2 < θ`) and `< θ|w|` for every `w ≠ 0`, the model-support enclosure, and
  value `< θ/2 < θ`, on `D_i ∩ B(j, Lρ(j))`; for every zero support meeting `D_i` ONE sign `a₀` with
  (R0) `< E` and the same derivative / value bounds on ALL of `D_i`. The (SB) budgets are those of
  the parts at `θ' = θ/2`.
* consumer `sgp03_strict_value_PKG`: the public strict form `|U_j − λ_j(η_i)| < θ` and
  `|DU_j(w) − a Dη_i(w)| < θ|w|` (`w ≠ 0`) for the slim block.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
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

/-- The inner tolerances of the strict wrapper: `θ' = θ/2`, `E' = min(E/2, θ'²/(2·10⁶))`. -/
theorem sgp03_inner_tolerances_PKG {θ E : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hE : 0 < E) :
    0 < θ / 2 ∧ θ / 2 < 1 ∧ θ / 2 < θ ∧ 0 < min (E / 2) ((θ / 2) ^ 2 / (2 * 10 ^ 6)) ∧
      min (E / 2) ((θ / 2) ^ 2 / (2 * 10 ^ 6)) < E ∧
      min (E / 2) ((θ / 2) ^ 2 / (2 * 10 ^ 6)) < (θ / 2) ^ 2 / 10 ^ 6 := by
  have h2 : 0 < (θ / 2) ^ 2 := by positivity
  refine ⟨by positivity, by linarith, by linarith, lt_min (by positivity) (by positivity),
    (min_le_left _ _).trans_lt (by linarith), (min_le_right _ _).trans_lt ?_⟩
  apply div_lt_div_of_pos_left h2 (by positivity) (by norm_num)

/-- A non-strict bound `≤ (θ/2)√q` is strict `< θ√q` when `q > 0`. -/
theorem lt_of_le_half_mul_sqrt_PKG {d θ q : ℝ} (hθ : 0 < θ) (hq : 0 < q)
    (h : d ≤ θ / 2 * Real.sqrt q) : d < θ * Real.sqrt q := by
  have hs := Real.sqrt_pos.mpr hq
  nlinarith

/-- **SGP03 with the strict error wording, slim and zero blocks on the final closed family**
(see the module docstring). -/
theorem sgp03_strict_row_PKG {Δ β₂ θ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (oM : ManifoldOrientation 𝓘(ℝ, E3) X 3)
        (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz oM),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < (θ / 2) ^ 2 / 10 ^ 6 → vs < θ / 2 / 100 →
        0 < ζ → ζ < (θ / 2) ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θ / 2 / (100 * (1000000 * Δ)) →
        ∀ i (hi : i ∈ P.slim.centres),
          (∀ j (hj : j ∈ sgpSlimList P.slim i), ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
            (∀ x ∈ ball i (30 * (1000000 * Δ) * ρ i),
              |ρ j / ρ i * sgpRaw P.slim j x - a * sgpRaw P.slim i x -
                ρ j / ρ i * sgpRaw P.slim j i| < E) ∧
            (∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i), x ∈ ball j (1000000 * Δ * ρ j) →
              ∀ w : TangentSpace 𝓘(ℝ, E3) x,
                |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj.1).coord x w -
                  a * mvfderiv 𝓘(ℝ, E3) (P.slim.centre i hi).coord x w| ≤
                  θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) ∧
                (w ≠ 0 → |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj.1).coord x w -
                  a * mvfderiv 𝓘(ℝ, E3) (P.slim.centre i hi).coord x w| <
                  θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))) ∧
            (∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i),
              slimCutoffProfile_LC87 ((a * (P.slim.centre i hi).coord x +
                ρ j / ρ i * sgpRaw P.slim j i) / (ρ j / ρ i * (100000 * Δ))) ≠ 0 →
              x ∈ ball j (91 / 100 * (1000000 * Δ) * ρ j)) ∧
            ∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i), x ∈ ball j (1000000 * Δ * ρ j) →
              |ρ j / ρ i * (P.slim.centre j hj.1).coord x -
                (a * (P.slim.centre i hi).coord x + ρ j / ρ i * sgpRaw P.slim j i)| < θ / 2) ∧
          ∀ k (hk : k ∈ P.zero.centres),
            (tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
              ((P.zero.zero k hk).radial y)) ∩ ball i (95 / 100 * (1000000 * Δ) * ρ i)).Nonempty →
            ∃ a₀ : ℝ, (a₀ = 1 ∨ a₀ = -1) ∧
              (∀ x ∈ ball i (30 * (1000000 * Δ) * ρ i),
                |(ρ i)⁻¹ * (dist k x - dist k i) - a₀ * sgpRaw P.slim i x| < E) ∧
              (∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i), ∀ w : TangentSpace 𝓘(ℝ, E3) x,
                |(P.zero.zero k hk).radius / ρ i *
                    mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w -
                  a₀ * mvfderiv 𝓘(ℝ, E3) (P.slim.centre i hi).coord x w| ≤
                  θ / 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) ∧
                (w ≠ 0 → |(P.zero.zero k hk).radius / ρ i *
                    mvfderiv 𝓘(ℝ, E3) (P.zero.zero k hk).radial x w -
                  a₀ * mvfderiv 𝓘(ℝ, E3) (P.slim.centre i hi).coord x w| <
                  θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w))) ∧
              ∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i),
                |(P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial x -
                  (a₀ * (P.slim.centre i hi).coord x +
                    (P.zero.zero k hk).radius / ρ i * (P.zero.zero k hk).radial i)| < θ / 2 := by
  obtain ⟨hθ'0, hθ'1, -, hE'0, hE'E, hE'θ⟩ := sgp03_inner_tolerances_PKG hθ hθ1 hE
  set E' := min (E / 2) ((θ / 2) ^ 2 / (2 * 10 ^ 6)) with hE'def
  obtain ⟨L₁, η₁, hL₁, hη₁, h1⟩ := sgp03_row hΔ hβ₂ hβ₂1 hθ'0 hθ'1 hE'0 hE'θ
  obtain ⟨L₂, η₂, hL₂, hη₂, h2⟩ := sgp03_zero_row hΔ hβ₂ hβ₂1 hθ'0 hθ'1 hE'0 hE'θ
  refine ⟨max L₁ L₂, min η₁ η₂, lt_max_of_lt_left hL₁, lt_min hη₁ hη₂, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hTz hσs hσθ hvθ hζ0 hζθ hζL hεr i hi
  have hq : ∀ x (w : TangentSpace 𝓘(ℝ, E3) x), w ≠ 0 → 0 < (ρ i)⁻¹ ^ 2 * g.inner x w w :=
    fun x w hw => mul_pos (by have := hρ i; positivity) (g.pos x w hw)
  refine ⟨fun j hj => ?_, fun k hk hmeet => ?_⟩
  · obtain ⟨a, ha, hRA, hD, hM, hV⟩ := h1 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ
      γ δ εr e T V vs P.toLocalChartPacketsRVZ.toLocalChartPacketsRV hβ2
      (hβ1.trans (min_le_left _ _)) ((le_max_left _ _).trans hLmax) hΛ hLΛ hσs hσθ hvθ i hi j hj
    refine ⟨a, ha, fun x hx => (hRA x hx).trans hE'E, fun x hxi hxj w =>
      ⟨hD x hxi hxj w, fun hw => lt_of_le_half_mul_sqrt_PKG hθ (hq x w hw) (hD x hxi hxj w)⟩,
      hM, hV⟩
  · obtain ⟨a₀, ha₀, hR0, hD, hV⟩ := h2 X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ
      δ εr e T V vs ζ Λz P.toLocalChartPacketsRVZ hβ2 (hβ1.trans (min_le_right _ _))
      ((le_max_right _ _).trans hLmax) hΛ hLΛ he hT hTz hσs hσθ hvθ hζ0 hζθ hζL hεr i hi k hk
      hmeet
    refine ⟨a₀, ha₀, fun x hx => (hR0 x hx).trans hE'E, fun x hx w =>
      ⟨hD x hx w, fun hw => lt_of_le_half_mul_sqrt_PKG hθ (hq x w hw) (hD x hx w)⟩, hV⟩

/-- **Consumer: the public strict (SC) for the slim block.** Under the thresholds of
`sgp03_strict_row_PKG`, at every slim reference `i` and listed `j ∈ J_i`, ONE sign `a` has, on
`D_i ∩ B(j, Lρ(j))`, `|U_j − λ_j(η_i)| < θ` and `|DU_j(w) − a Dη_i(w)| < θ|w|` for every `w ≠ 0`
(`U_j = s_jη_j`, `λ_j(t) = at + s_ju_j(i)`, `|w|` of `ρ(i)⁻²g`). -/
theorem sgp03_strict_value_PKG {Δ β₂ θ E : ℝ} (hΔ : 1 ≤ Δ) (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1)
    (hθ : 0 < θ) (hθ1 : θ < 1) (hE : 0 < E) :
    ∃ Lc η₀ : ℝ, 0 < Lc ∧ 0 < η₀ ∧
      ∀ (X : Type) [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
        (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (σs : ℝ) (K : ℕ)
        (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ)
        (oM : ManifoldOrientation 𝓘(ℝ, E3) X 3)
        (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
          εr e T V vs ζ Λz oM),
        β 2 = β₂ → β 1 ≤ η₀ → Lc ≤ Lmax → 0 ≤ Λ → 1000000 * Δ * Λ < 1 / 100000 →
        e < 1 / 40 → 1600 * (1000000 * Δ) ≤ T → 20 * Λz ≤ T →
        0 < σs → σs < (θ / 2) ^ 2 / 10 ^ 6 → vs < θ / 2 / 100 →
        0 < ζ → ζ < (θ / 2) ^ 2 / 10 ^ 6 → ζ < 1 / (100 * (1000000 * Δ)) →
        εr < θ / 2 / (100 * (1000000 * Δ)) →
        ∀ i (hi : i ∈ P.slim.centres), ∀ j (hj : j ∈ sgpSlimList P.slim i), ∃ a : ℝ,
          (a = 1 ∨ a = -1) ∧
          ∀ x ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i), x ∈ ball j (1000000 * Δ * ρ j) →
            |ρ j / ρ i * (P.slim.centre j hj.1).coord x -
              (a * (P.slim.centre i hi).coord x + ρ j / ρ i * sgpRaw P.slim j i)| < θ ∧
            ∀ w : TangentSpace 𝓘(ℝ, E3) x, w ≠ 0 →
              |ρ j / ρ i * mvfderiv 𝓘(ℝ, E3) (P.slim.centre j hj.1).coord x w -
                a * mvfderiv 𝓘(ℝ, E3) (P.slim.centre i hi).coord x w| <
                θ * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner x w w) := by
  obtain ⟨Lc, η₀, hLc, hη₀, hrow⟩ := sgp03_strict_row_PKG hΔ hβ₂ hβ₂1 hθ hθ1 hE
  refine ⟨Lc, η₀, hLc, hη₀, ?_⟩
  intro X _ _ _ _ g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz oM P
    hβ2 hβ1 hLmax hΛ hLΛ he hT hTz hσs hσθ hvθ hζ0 hζθ hζL hεr i hi j hj
  obtain ⟨a, ha, -, hD, -, hV⟩ := (hrow X g hmetric ρ hρ Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz oM P hβ2 hβ1 hLmax hΛ hLΛ he hT hTz hσs hσθ hvθ hζ0 hζθ hζL hεr i hi).1 j hj
  exact ⟨a, ha, fun x hxi hxj => ⟨(hV x hxi hxj).trans (by linarith),
    fun w hw => (hD x hxi hxj w).2 hw⟩⟩

end DifferentialGeometry.Geometry.Collapse
