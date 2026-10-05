import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementWitnessBCF2KApplications

/-!
# BCF02, strict replacement, step four: the replacement index and its strict marker (Repl_∂)

External draft 61 §6.2, step four, and the contract (Repl_∂); review 68 (dispositions D68-3, D68-5,
D68-7); blueprint `master207B.tex`, BCF02 (B:9799–9803), FDC01 (B:7217–7244), GAF05 (B:5971).
Kernel mode: the boundary chain `E : W → H^∂` does not exist yet, so its clauses enter as EXPLICIT
premises about an arbitrary map `E : X → Y`, a stage projection `π₂ : Y → Y` and base coordinates
`u v : X → Y → ℝ` (the `j`-edge block of the target), of exactly the shapes the closed chain proves:
* (ERR) the strict stage error on the edge block (`stage_error_lt` with the block formula
  `(R_jη_jζ_j, R_jζ_j)`): `|u_j(π₂E x) − ρ_j η_j(x)ζ_j(x)| < c₃ρ(x)`;
* (FM) GAF05's exact full marker on the original threshold-6 plateau:
  `d(x, j) < 100Δρ_j`, `|η_j(x)| < 6Δ`, `t(x) < 6Δ` ⟹ `v_j(π₂E x) = ρ_j`.
EGP04's value clause (EC) for a pair of revised edge charts on `D_i` is carried as DATA inside the
conclusion: this file is the EC-CONDITIONAL exit of D68-5 (`…_of_comparison_…`); the exit with EC
instantiated (lane B-EGP04-EC's `egp04_edgeB_value_BFRZ`) is
`LocalPacketsOnBFRZ.bcf02_strict_replacement_BCF2K` in `BoundaryReplacementStrictECBCF2K`.

Review 68, A2 (D68-3): the witness chain `d(q', j) ≤ d(q', a) + d(a, j) < ρ(a) + Δρ_j` is kept with
`ρ(a) ≤ 1.01ρ_j` (slow variation, the register's `100ΔΛ ≤ 10⁻⁸`), i.e. `R = Δ + 1.01`, so that
`1.001R + .031Δ < 2Δ` for `Δ ≥ 2` (`bcf02_replacement_constants_BCF2K`); the register supplies
`Δ ≥ 2` through `100/β₂ < Δ`, `β₂ < 1/100` (`bcf02_register_delta_BCF2K`).

Family-free scalar kernels (D68-7, "state once, wrap twice"):
* `bcf02_replacement_core_BCF2K`: the replacement-of-comparison computation for arbitrary functions
  `η_i, η_j, ζ_j, t` with `η_j(j) = 0`, the `max(1 + σc, 0)/ρ_j`-Lipschitz bound and the plateau;
* `bcf02_strict_marker_core_BCF2K`: (ERR) at a plateau point with `|η| < 2Δ` ⟹ `|u|/R < 3Δ`.
Wrappers on the revised edge charts `edgeB`:
* `EdgeFamilyOn.cutoff_eq_one_of_le_BCF2K`: FC27's plateau for the actual `edgeB` cutoff (with the
  chart-ball membership, A1);
* `LocalPacketsOnB.bcf02_replacement_of_comparison_BCF2K`,
  `LocalPacketsOnB.bcf02_strict_marker_BCF2K`;
* `LocalPacketsOnBFRZ.bcf02_strict_replacement_of_comparison_BCF2K`: (Repl_∂) on the final family,
  EC-conditional.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal NNReal
open DifferentialGeometry GC.Endpoint GC.MetricGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-! ## Constants (review 68, A2) -/

/-- **A2's constants**: with `R = Δ + 1.01` and `Δ ≥ 2`, `R ≤ 2Δ` and `1.001R + .031Δ < 2Δ`. -/
theorem bcf02_replacement_constants_BCF2K {Δ : ℝ} (hΔ : 2 ≤ Δ) :
    Δ + 101 / 100 ≤ 2 * Δ ∧ 1001 / 1000 * (Δ + 101 / 100) + 31 / 1000 * Δ < 2 * Δ :=
  ⟨by linarith, by linarith⟩

/-- **The register supplies `Δ ≥ 2`**: the T3B register's clauses `0 < β₂`, `β₂ < 1/100`,
`100/β₂ < Δ` give `Δ > 10⁴`. -/
theorem bcf02_register_delta_BCF2K {β₂ Δ : ℝ} (hβ₂ : 0 < β₂) (hβ₂1 : β₂ < 1 / 100)
    (hΔ : 100 / β₂ < Δ) : 2 ≤ Δ := by
  have h : 10000 < 100 / β₂ := by
    rw [lt_div_iff₀ hβ₂]
    linarith
  linarith

/-! ## Family-free scalar kernels (D68-7) -/

/-- **The replacement-of-comparison computation** (family-free kernel of FDC01 step four): for
functions `η_i, η_j, ζ_j, t` on a pseudo-metric space with a positive `Λ`-Lipschitz scale `ρ`, where
`η_j(j) = 0`, `η_j` is `max(1 + σc, 0)/ρ_j`-Lipschitz and `ζ_j = 1` on the plateau
`{x ∈ B(j, 100Δρ_j) | |η_j| ≤ 8Δ, t/ρ ≤ 8Δ}`: for the (WB) data `q, q'` and `d(q', j) < Rρ_j`
(`R ≤ 2Δ`), `ζ_j(q') = 1`, `q' ∈ D_i = B(i, 20Δρ_i)`, and an affine comparison
`|s_j η_j − (aη_i + c)| < θ` on `D_i` (`a = ±1`, `θ ≤ 1/100`, EGP04's (EC)) gives
`d(q, j) < 7Δρ_j`, `|η_j(q)| < 1.001R + .031Δ` and `ζ_j(q) = 1`. -/
theorem bcf02_replacement_core_BCF2K {X : Type} [PseudoMetricSpace X] {ρ : X → ℝ}
    (hρ : ∀ p, 0 < ρ p) {Λ Δ σc : ℝ} (hlip : LipschitzWith (Real.toNNReal Λ) ρ) (hΔ : 1 ≤ Δ)
    (hΛ : 0 ≤ Λ) (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    {ηi ηj ζj t : X → ℝ} {i j : X} (hself : ηj j = 0)
    (hηlip : ∀ y z, |ηj y - ηj z| ≤ max (1 + σc) 0 / ρ j * dist y z)
    (hplat : ∀ x ∈ ball j (100 * Δ * ρ j), |ηj x| ≤ 8 * Δ → t x / ρ x ≤ 8 * Δ → ζj x = 1)
    {q q' : X} (hq'i : dist q' i < 41 / 10 * Δ * ρ i) (hqq' : dist q q' < 42 / 10 * Δ * ρ i)
    (hη' : |ηi q' - ηi q| < Δ / 100) (ht' : t q' / ρ q' < Δ / 100)
    (htq : t q / ρ q ≤ 401 / 100 * Δ) {R : ℝ} (hR : R ≤ 2 * Δ) (hq'j : dist q' j < R * ρ j) :
    ζj q' = 1 ∧ q' ∈ ball i (20 * Δ * ρ i) ∧
      ∀ a θ c : ℝ, (a = 1 ∨ a = -1) → θ ≤ 1 / 100 →
        (∀ x ∈ ball i (20 * Δ * ρ i), |ρ j / ρ i * ηj x - (a * ηi x + c)| < θ) →
        dist q j < 7 * Δ * ρ j ∧ |ηj q| < 1001 / 1000 * R + 31 / 1000 * Δ ∧ ζj q = 1 := by
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  have hrj := hρ j
  have hκ : Δ * Λ ≤ 1 / 10 ^ 10 := by linarith
  -- the scale ratio `s_j = ρ(j)/ρ(i)`
  have hq'j2 : dist q' j < 2 * Δ * ρ j := by
    have := mul_le_mul_of_nonneg_right hR hrj.le
    linarith
  have hij : dist i j < 41 / 10 * Δ * ρ i + 2 * Δ * ρ j := by
    have h := dist_triangle i q' j
    rw [dist_comm i q'] at h
    linarith
  have hρij : |ρ j - ρ i| ≤ 41 / 10 * (Δ * Λ) * ρ i + 2 * (Δ * Λ) * ρ j := by
    have h1 := hlip.dist_le_mul j i
    rw [Real.coe_toNNReal _ hΛ, Real.dist_eq, dist_comm] at h1
    have h2 : Λ * dist i j ≤ Λ * (41 / 10 * Δ * ρ i + 2 * Δ * ρ j) :=
      mul_le_mul_of_nonneg_left hij.le hΛ
    linarith
  have hκi : (Δ * Λ) * ρ i ≤ 1 / 10 ^ 10 * ρ i := mul_le_mul_of_nonneg_right hκ hri.le
  have hκj : (Δ * Λ) * ρ j ≤ 1 / 10 ^ 10 * ρ j := mul_le_mul_of_nonneg_right hκ hrj.le
  have hr1 : 99 / 100 * ρ i ≤ ρ j := by linarith [(abs_le.mp hρij).1]
  -- the coordinate and the cutoff of `j` at `q'`
  have hlip' := hηlip q' j
  rw [hself, sub_zero] at hlip'
  have hmax : max (1 + σc) 0 ≤ 1001 / 1000 := max_le (by linarith) (by norm_num)
  have hcq' : |ηj q'| < 1001 / 1000 * R := by
    have h1 : max (1 + σc) 0 / ρ j * dist q' j ≤ 1001 / 1000 / ρ j * dist q' j :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hmax hrj.le) dist_nonneg
    have h2 : 1001 / 1000 / ρ j * dist q' j < 1001 / 1000 / ρ j * (R * ρ j) :=
      mul_lt_mul_of_pos_left hq'j (by positivity)
    have h3 : 1001 / 1000 / ρ j * (R * ρ j) = 1001 / 1000 * R := by
      field_simp
    linarith
  have hDj : 0 < Δ * ρ j := mul_pos hΔ0 hrj
  have hDi : 0 < Δ * ρ i := mul_pos hΔ0 hri
  have hq'jB : q' ∈ ball j (100 * Δ * ρ j) := by
    rw [mem_ball]
    linarith
  have hζq' : ζj q' = 1 := hplat q' hq'jB (by linarith) (by linarith)
  have hq'D : q' ∈ ball i (20 * Δ * ρ i) := by
    rw [mem_ball]
    linarith
  refine ⟨hζq', hq'D, fun a θ c ha hθ hEC => ?_⟩
  -- (EC) at `q` and `q'`
  have hqD : q ∈ ball i (20 * Δ * ρ i) := by
    rw [mem_ball]
    have h := dist_triangle q q' i
    linarith
  have h1 := hEC q hqD
  have h2 := hEC q' hq'D
  set sj := ρ j / ρ i with hsj
  have hsj99 : 99 / 100 ≤ sj := by
    rw [hsj, le_div_iff₀ hri]
    exact hr1
  have hdiff : sj * |ηj q - ηj q'| < 3 / 100 * Δ := by
    have hai : |a * ηi q - a * ηi q'| < Δ / 100 := by
      rcases ha with rfl | rfl
      · rw [one_mul, one_mul, abs_sub_comm]
        exact hη'
      · have he : -1 * ηi q - -1 * ηi q' = ηi q' - ηi q := by ring
        rw [he]
        exact hη'
    have hs0 : 0 ≤ sj := by linarith
    rw [← abs_of_nonneg hs0, ← abs_mul, mul_sub]
    have h3 := abs_sub_le (sj * ηj q) (a * ηi q + c) (sj * ηj q')
    have h4 := abs_sub_le (a * ηi q + c) (a * ηi q' + c) (sj * ηj q')
    have h5 : (a * ηi q + c) - (a * ηi q' + c) = a * ηi q - a * ηi q' := by ring
    rw [h5] at h4
    rw [abs_sub_comm (a * ηi q' + c)] at h4
    linarith
  have hdiff' : |ηj q - ηj q'| < 31 / 1000 * Δ := by
    have h3 : 99 / 100 * |ηj q - ηj q'| ≤ sj * |ηj q - ηj q'| :=
      mul_le_mul_of_nonneg_right hsj99 (abs_nonneg _)
    linarith
  have hcq : |ηj q| < 1001 / 1000 * R + 31 / 1000 * Δ := by
    have h3 := abs_sub_abs_le_abs_sub (ηj q) (ηj q')
    linarith
  -- the distance from `q` to `j` and the cutoff of `j` at `q`
  have hqj : dist q j < 7 * Δ * ρ j := by
    have h3 := dist_triangle q q' j
    have h4 : 99 / 100 * (Δ * ρ i) ≤ Δ * ρ j := by
      have := mul_le_mul_of_nonneg_left hr1 hΔ0.le
      linarith
    linarith
  have hqjB : q ∈ ball j (100 * Δ * ρ j) := by
    rw [mem_ball]
    linarith
  exact ⟨hqj, hcq, hplat q hqjB (by linarith) (by linarith)⟩

/-- **The strict base coordinate** (family-free kernel of FDC01's marker step): a block value `w`
with `|w − R η ζ| < c₃ρ_q`, at a plateau point `ζ = 1` with `|η| < 2Δ`, `ρ_q ≤ 2R`, `c₃ ≤ Δ/2`,
has `|w|/R < 3Δ`. -/
theorem bcf02_strict_marker_core_BCF2K {Δ c₃ R ρq η ζ w : ℝ} (hR : 0 < R) (hρq : 0 < ρq)
    (hρ : ρq ≤ 2 * R) (hc₃ : c₃ ≤ Δ / 2) (hη : |η| < 2 * Δ) (hζ : ζ = 1)
    (herr : |w - R * (η * ζ)| < c₃ * ρq) : |w| / R < 3 * Δ := by
  rw [hζ, mul_one] at herr
  have hc0 : 0 < c₃ := by
    have h0 := (abs_nonneg _).trans_lt herr
    by_contra hc
    push Not at hc
    nlinarith
  have hw : |w| < R * |η| + c₃ * ρq := by
    have h1 := abs_sub_abs_le_abs_sub w (R * η)
    rw [abs_mul, abs_of_pos hR] at h1
    linarith
  have h2 : R * |η| < R * (2 * Δ) := mul_lt_mul_of_pos_left hη hR
  have h3 : c₃ * ρq ≤ Δ / 2 * (2 * R) := mul_le_mul hc₃ hρ hρq.le (by linarith)
  rw [div_lt_iff₀ hR]
  linarith

section Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **FC27's plateau for the actual revised edge cutoff**: `ζ_j = 1` on
`{x ∈ B(j, 100Δρ(j)) | |η_j| ≤ 8Δ, F/ρ ≤ 8Δ}` (the chart-ball membership is a premise: the cutoff
is the zero extension off the normalized chart ball). -/
theorem EdgeFamilyOn.cutoff_eq_one_of_le_BCF2K
    (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) (hΔ : 0 < Δ) {j : X}
    (hj : j ∈ F.centres) {x : X} (hx : x ∈ ball j (100 * Δ * ρ j))
    (hη : |F.coord_BAUGA j x| ≤ 8 * Δ) (hF : F.smoothing x / ρ x ≤ 8 * Δ) :
    F.cutoff_BAUGA j x = 1 := by
  rw [F.cutoff_eq_formula_BAUGA hj hx]
  have hh : edgeHeightProfile (F.smoothing x / ρ x / Δ) = 1 := by
    refine descendingIntervalProfile_one (by norm_num) ?_
    rw [div_le_iff₀ hΔ]
    linarith
  have hcp : edgeCoordinateProfile (F.coord_BAUGA j x / Δ) = 1 := by
    refine (edgeProfiles_plateaus (x := F.coord_BAUGA j x / Δ)).1 ⟨?_, ?_⟩
    · rw [le_div_iff₀ hΔ]
      linarith [(abs_le.mp hη).1]
    · rw [div_le_iff₀ hΔ]
      linarith [(abs_le.mp hη).2]
  rw [hh, hcp, mul_one]

/-- **(Repl_∂), step four, the replacement index on the revised edge charts** (wrapper of
`bcf02_replacement_core_BCF2K` on `edgeB`). For points `q, q'` with `d(q', i) < 4.1Δρ(i)`,
`d(q, q') < 4.2Δρ(i)`, `|η_i(q') − η_i(q)| < Δ/100`, `t(q') < Δ/100`, `t(q) ≤ 4.01Δ` (the (WB) data
of step two) and a revised centre `j` with `d(q', j) < Rρ(j)` (`R ≤ 2Δ`): `ζ_j(q') = 1` and
`q' ∈ D_i = B(i, 20Δρ_i)` (so `j ∈ J_e(i)`), and if `η_j` satisfies an affine comparison
`|s_j η_j − (aη_i + c)| < θ` on `D_i` (`a = ±1`, `θ ≤ 1/100`, EGP04's (EC)), then
`d(q, j) < 7Δρ(j)`, `|η_j(q)| < 1.001R + .031Δ` and `ζ_j(q) = 1`. -/
theorem LocalPacketsOnB.bcf02_replacement_of_comparison_BCF2K
    (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂)
    (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    {i : X} {q q' : X} (hq'i : dist q' i < 41 / 10 * Δ * ρ i)
    (hqq' : dist q q' < 42 / 10 * Δ * ρ i)
    (hη' : |F.edgeB.coord_BAUGA i q' - F.edgeB.coord_BAUGA i q| < Δ / 100)
    (ht' : F.edgeB.smoothing q' / ρ q' < Δ / 100)
    (htq : F.edgeB.smoothing q / ρ q ≤ 401 / 100 * Δ)
    {R : ℝ} (hR : R ≤ 2 * Δ) {j : X} (hj : j ∈ F.edgeB.centres) (hq'j : dist q' j < R * ρ j) :
    F.edgeB.cutoff_BAUGA j q' = 1 ∧ q' ∈ ball i (20 * Δ * ρ i) ∧
      ∀ a θ c : ℝ, (a = 1 ∨ a = -1) → θ ≤ 1 / 100 →
        (∀ x ∈ ball i (20 * Δ * ρ i),
          |ρ j / ρ i * F.edgeB.coord_BAUGA j x - (a * F.edgeB.coord_BAUGA i x + c)| < θ) →
        dist q j < 7 * Δ * ρ j ∧ |F.edgeB.coord_BAUGA j q| < 1001 / 1000 * R + 31 / 1000 * Δ ∧
          F.edgeB.cutoff_BAUGA j q = 1 :=
  bcf02_replacement_core_BCF2K hρ F.lipschitz_scale hΔ hΛ hlam hσc
    (F.edgeB.coord_self_BCF2K hj) (F.edgeB.coord_lipschitz_BCF2K hj)
    (fun x hx hη ht => F.edgeB.cutoff_eq_one_of_le_BCF2K (by linarith) hj hx hη ht)
    hq'i hqq' hη' ht' htq hR hq'j

/-- **(Repl_∂), step four, the strict marker and the strict base coordinate** (kernel; the chain's
clauses as explicit premises): with the strict stage error (ERR) on the `j`-edge block and GAF05's
exact full marker (FM) on the threshold-6 plateau, a revised centre `j` with `d(q, j) < 7Δρ_j`,
`|η_j(q)| < 2Δ`, `ζ_j(q) = 1`, `t(q) ≤ 4.01Δ` has `v_j(π₂E q) = ρ_j` EXACTLY and
`|u_j(π₂E q)|/ρ_j < 3Δ` (`c₃ ≤ Δ/2`, `100ΔΛ ≤ 10⁻⁸`). -/
theorem LocalPacketsOnB.bcf02_strict_marker_BCF2K
    (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂) {Y : Type} (E : X → Y) (π₂ : Y → Y) (u v : X → Y → ℝ) {c₃ : ℝ}
    (hΔ : 0 < Δ) (hΛ : 0 ≤ Λ) (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (hc₃ : c₃ ≤ Δ / 2)
    (hERR : ∀ j ∈ F.edgeB.centres, ∀ x, |u j (π₂ (E x)) -
      ρ j * (F.edgeB.coord_BAUGA j x * F.edgeB.cutoff_BAUGA j x)| < c₃ * ρ x)
    (hFM : ∀ j ∈ F.edgeB.centres, ∀ x, dist x j < 100 * Δ * ρ j →
      |F.edgeB.coord_BAUGA j x| < 6 * Δ → F.edgeB.smoothing x / ρ x < 6 * Δ →
        v j (π₂ (E x)) = ρ j)
    {j q : X} (hj : j ∈ F.edgeB.centres) (hqj : dist q j < 7 * Δ * ρ j)
    (hηq : |F.edgeB.coord_BAUGA j q| < 2 * Δ) (hζq : F.edgeB.cutoff_BAUGA j q = 1)
    (htq : F.edgeB.smoothing q / ρ q ≤ 401 / 100 * Δ) :
    v j (π₂ (E q)) = ρ j ∧ |u j (π₂ (E q))| / ρ j < 3 * Δ := by
  have hrj := hρ j
  refine ⟨hFM j hj q (by nlinarith) (by linarith) (by linarith), ?_⟩
  -- `ρ(q) ≤ 2ρ_j`
  have hρq : ρ q ≤ 2 * ρ j := by
    have h1 := F.lipschitz_scale.dist_le_mul q j
    rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h1
    have h2 : Λ * dist q j ≤ Λ * (7 * Δ * ρ j) := mul_le_mul_of_nonneg_left hqj.le hΛ
    have h3 : Δ * Λ * ρ j ≤ 1 / 10 ^ 10 * ρ j :=
      mul_le_mul_of_nonneg_right (by nlinarith) hrj.le
    have h4 : Λ * (7 * Δ * ρ j) = 7 * (Δ * Λ * ρ j) := by ring
    linarith [(abs_le.mp h1).2]
  exact bcf02_strict_marker_core_BCF2K hrj (hρ q) hρq hc₃ hηq hζq (hERR j hj q)

end Generic

/-! ## (Repl_∂) on the final boundary family over `(W°, d_ĝ)`, EC-conditional -/

section Carrier

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **The strict replacement contract (Repl_∂), EC-conditional exit** on the final boundary family
over the completion `(W°, d_ĝ)` (regions `{D > 10}`, `{D ≥ 20}`, `{D > 20}`, `{D ≥ 35}`), BCP04.a at
the index `n`. The premises on the point are exactly those of the contract: `q ∈ M₂` through
`D(q) ≥ 35` and its two original-coordinate consequences (outside every selected zero ball
`B(z, .38R_z)`, outside every selected slim region), a revised edge centre `i`, `q ∈ U_i`,
`|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ`; NO `q ∈ X₂` and NO `π₂E(q) ∈ B₂`. The chain enters through
(ERR) and (FM) for an arbitrary map `E`, stage projection `π₂` and edge-block coordinates `u, v`.
Conclusion: a revised centre `j` (from the strong witness `a`, `d(a, j) < Δρ_j`, with
`d(q', j) < ρ(a) + Δρ_j ≤ (Δ + 1.01)ρ_j`, review 68 A2) and the border witness `q'` with
`ζ_j(q') = 1`, `q' ∈ D_i` (so `j ∈ J_e(i)`), such that EGP04's value clause (EC) for `(i, j)` on
`D_i` — carried as data — gives `|η_j(q)| < 2Δ`, `ζ_j(q) = 1`, `v_j(π₂E q) = ρ_j` and
`|u_j(π₂E q)|/ρ_j < 3Δ`. -/
theorem LocalPacketsOnBFRZ.bcf02_strict_replacement_of_comparison_BCF2K (W : CompactCarrier.{0})
    [ConnectedSpace W.Carrier] (g : SmoothRiemannianMetric W.model W.Carrier)
    (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))
    (hle : ∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
      (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v)
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n : ℝ}
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz c₃ : ℝ}
    (hΔ : 2 ≤ Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000) (hn : 1140 * Δ ≤ 35 * n)
    (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100) (hb : b < 1 / 1000000)
    (hs : s < 1 / 1000000) (hβ2 : β 2 < 1 / 1000000) (hc₃ : c₃ ≤ Δ / 2)
    (oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3) :
    letI := inducedMetricSpace ĝ
    ∀ [CompleteSpace (W.pieceInterior ⊤)]
      (F : LocalPacketsOnBFRZ (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
        (fun x => ρ x) (fun x => hρ x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
        {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x}
        {x | ENNReal.ofReal 20 < distanceToBoundary W g x}
        {x | ENNReal.ofReal 35 ≤ distanceToBoundary W g x} oM)
      {Y : Type} (E : W.pieceInterior ⊤ → Y) (π₂ : Y → Y) (u v : W.pieceInterior ⊤ → Y → ℝ),
      (∀ j ∈ F.edgeB.centres, ∀ x, |u j (π₂ (E x)) -
        ρ j * (F.edgeB.coord_BAUGA j x * F.edgeB.cutoff_BAUGA j x)| < c₃ * ρ x) →
      (∀ j ∈ F.edgeB.centres, ∀ x, dist x j < 100 * Δ * ρ j →
        |F.edgeB.coord_BAUGA j x| < 6 * Δ → F.edgeB.smoothing x / ρ x < 6 * Δ →
          v j (π₂ (E x)) = ρ j) →
      ∀ i : W.pieceInterior ⊤, i ∈ F.edgeB.centres →
      ∀ q : W.pieceInterior ⊤, dist q i < 100 * Δ * ρ i →
        |F.edgeB.coord_BAUGA i q| ≤ 401 / 100 * Δ →
        F.edgeB.smoothing q / ρ q ≤ 401 / 100 * Δ →
        ENNReal.ofReal 35 ≤ distanceToBoundary W g q →
        (letI := F.instMetricN; letI := F.instChartedN; letI := F.instMetricC
          ∀ z (hz : z ∈ F.zero.centres), 38 / 100 * (F.zero.zero z hz).radius ≤ dist q z) →
        (∀ k (hk : k ∈ F.slim.centres), dist q k < 9 * Δ * ρ k →
          10 * Δ ≤ |(F.slim.centre k hk).coord_BCG2 q|) →
        ∃ j ∈ F.edgeB.centres, ∃ q' : W.pieceInterior ⊤, F.edgeB.cutoff_BAUGA j q' = 1 ∧
          q' ∈ ball i (20 * Δ * ρ i) ∧
          ∀ a θ c : ℝ, (a = 1 ∨ a = -1) → θ ≤ 1 / 100 →
            (∀ x ∈ ball i (20 * Δ * ρ i),
              |ρ j / ρ i * F.edgeB.coord_BAUGA j x - (a * F.edgeB.coord_BAUGA i x + c)| < θ) →
            |F.edgeB.coord_BAUGA j q| < 2 * Δ ∧ F.edgeB.cutoff_BAUGA j q = 1 ∧
              v j (π₂ (E q)) = ρ j ∧ |u j (π₂ (E q))| / ρ j < 3 * Δ := by
  let _ : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  intro _ F Y E π₂ u v hERR hFM i hi q hq hηq htq hq35 hZ hS
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨-, -, q', a, -, hq'i, hqq', hcoord, htq', -, hq'a, -, j, hj, haj⟩ :=
    F.bcf02_steps_one_three_BCF2K W g ĝ hle ρ hρ hbcp hΔ hΛ hμ hτ hlam hn hT hσs
      hσs1 hb hs hβ2 oM i hi q hq hηq htq hq35 hZ hS
  have hrj := hρ j
  -- A2: `ρ(a) ≤ 1.01ρ_j` (slow variation, `d(a, j) < Δρ_j`)
  have hρa : ρ a ≤ 101 / 100 * ρ j := by
    have h1 := F.lipschitz_scale.dist_le_mul a j
    rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h1
    have h2 : Λ * dist a j ≤ Λ * (Δ * ρ j) := mul_le_mul_of_nonneg_left haj.le hΛ
    have h3 : Δ * Λ * ρ j ≤ 1 / 10 ^ 10 * ρ j :=
      mul_le_mul_of_nonneg_right (by nlinarith) hrj.le
    have h4 : Λ * (Δ * ρ j) = Δ * Λ * ρ j := by ring
    linarith [(abs_le.mp h1).2]
  -- A2: `d(q', j) ≤ d(q', a) + d(a, j) < ρ(a) + Δρ_j ≤ (Δ + 1.01)ρ_j`
  have hq'j : dist q' j < (Δ + 101 / 100) * ρ j := by
    have h := dist_triangle q' a j
    have he : (Δ + 101 / 100) * ρ j = Δ * ρ j + 101 / 100 * ρ j := by ring
    rw [he]
    linarith
  obtain ⟨hR, hR2⟩ := bcf02_replacement_constants_BCF2K hΔ
  obtain ⟨hζq', hq'D, hrep⟩ := F.toLocalPacketsOnB.bcf02_replacement_of_comparison_BCF2K
    (by linarith) hΛ hlam hσc hq'i hqq' hcoord htq' htq hR hj hq'j
  refine ⟨j, hj, q', hζq', hq'D, fun a' θ c ha' hθ hEC => ?_⟩
  obtain ⟨hqj, hηj, hζj⟩ := hrep a' θ c ha' hθ hEC
  have hη2 : |F.edgeB.coord_BAUGA j q| < 2 * Δ := by linarith
  obtain ⟨hv, hu⟩ := F.toLocalPacketsOnB.bcf02_strict_marker_BCF2K E π₂ u v hΔ0 hΛ hlam hc₃
    hERR hFM hj hqj hη2 hζj htq
  exact ⟨hη2, hζj, hv, hu⟩

end Carrier

end DifferentialGeometry.Geometry.Collapse
