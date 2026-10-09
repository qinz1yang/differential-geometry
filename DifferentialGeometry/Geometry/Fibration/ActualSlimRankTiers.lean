import DifferentialGeometry.Geometry.Fibration.ActualFullMarkerContributors
import DifferentialGeometry.Geometry.Fibration.ActualSlimDerivativeComparison
import DifferentialGeometry.Analysis.Calculus.GraphCoverageAdapters

/-!
# SGP05 and SGP06: the tiers that do not use the model graph (actual LC87 packets)

Blueprint `master207B.tex`, SGP05 (`lem:fibration-slim-all-preimage-rank`, B:4667–4709) and SGP06
(`thm:fibration-actual-third-cloud`, B:4711–4786), bound to CGP01's actual map
`𝓔⁰ = cgpGlobalMap L Z` and its `Q₃` projection `π₃𝓔⁰ = cgpProjMap L Z (cgpQ3Tags L Z)`.
Units: `L = 10⁶Δ`, `ℓ = 10⁵Δ`, `D_i = B(i, .95Lρ(i))`, `η_i` the ORIGINAL slim coordinate.

* `sgp05_full_marker`: every preimage `q` of `x = π₃𝓔⁰(p)` (with `p ∈ B(i, Lρ(i))`,
  `|η_i(p)| ≤ 8ℓ`) has slim cutoff `ζ_i(q) = 1` and `η_i(q) = η_i(p)` ("the full marker of `i` at
  `x` forces `ζ_i(q) = 1` … its vector block then gives `η_i(q) = η_i(p)`").
* `sgp05_reference_bounds`: on `D_i`, the original reference-axis test with positive sign gives
  a `ρ(i)⁻²g`-unit `w` with `dη_i(w) > 9/10`, and `|dη_i(w)| ≤ 2√(ρ(i)⁻²g(w, w))` for all `w`
  (`9/10 < ‖ρ(i) dη_i(q)‖ ≤ 2` in the original metric).
* `sgp06_coordinate_coverage`: every `|u| ≤ 8ℓ` is `η_i(q_u)` for a point `q_u` of the original
  enlargement `Ã₃` with full marker (LFR20's surjectivity: exact coordinate coverage).
* `sgp06_localization`: FC03 on `π₃𝓔⁰`: if `|π₃𝓔⁰(q) − π₃𝓔⁰(p)| ≤ Rρ(i)`, `R < 1/100`, and `p` has
  `|η_i(p)| ≤ 7ℓ`, then `q` has full `i` marker and `|η_i(q) − η_i(p)| < ℓ/10`.
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
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

section Marker

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- `planeAxis` is injective. -/
theorem planeAxis_injective_SGP3 : Function.Injective planeAxis := by
  intro a b h
  have h' : ‖planeAxis (a - b)‖ = 0 := by rw [map_sub, h, sub_self, norm_zero]
  rw [norm_planeAxis, abs_eq_zero, sub_eq_zero] at h'
  exact h'

/-- **SGP05, the full marker at every preimage.** If `p ∈ B(i, Lρ(i))` has `|η_i(p)| ≤ 8ℓ`, every
`q` with `π₃𝓔⁰(q) = π₃𝓔⁰(p)` has slim cutoff `ζ_i(q) = 1` and `η_i(q) = η_i(p)`. -/
theorem sgp05_full_marker (i : L.slim.finite_centres.toFinset) {p q : X}
    (hp : p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1))
    (hη : |(L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤ 8 * 10 ^ 5 * Δ)
    (hpq : cgpProjMap L Z (cgpQ3Tags L Z) q = cgpProjMap L Z (cgpQ3Tags L Z) p) :
    L.slim.cutoff i.1 q = 1 ∧
      (L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord q =
        (L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p := by
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hri := hρ i.1
  have hcutp : L.slim.cutoff i.1 p = 1 := by
    rw [slimFamily_cutoff_eq_KA2 L hi]
    exact SlimCentre.cutoff_eq_one_of_abs_coord_le _ hp hη
  have hblk : cgpGlobalMap L Z q (.inr (.inl i)) = cgpGlobalMap L Z p (.inr (.inl i)) := by
    have h1 := cgpProjMap_apply_of_mem L Z (slim_mem_cgpQ3Tags L Z i) q
    have h2 := cgpProjMap_apply_of_mem L Z (slim_mem_cgpQ3Tags L Z i) p
    rw [hpq] at h1
    exact h1.symm.trans h2
  have hsnd : ρ i.1 * L.slim.cutoff i.1 q = ρ i.1 * L.slim.cutoff i.1 p :=
    congrArg (fun y : WithLp 2 (ℝ² × ℝ) => y.snd) hblk
  have hfst : (ρ i.1 * L.slim.cutoff i.1 q) • planeAxis ((L.slim.centre i.1 hi).coord q) =
      (ρ i.1 * L.slim.cutoff i.1 p) • planeAxis ((L.slim.centre i.1 hi).coord p) :=
    congrArg (fun y : WithLp 2 (ℝ² × ℝ) => y.fst) hblk
  rw [hcutp, mul_one] at hsnd
  have hcutq : L.slim.cutoff i.1 q = 1 := by
    have := mul_left_cancel₀ hri.ne' (hsnd.trans (mul_one _).symm)
    exact this
  rw [hcutq, hcutp, mul_one] at hfst
  exact ⟨hcutq, planeAxis_injective_SGP3 (smul_right_injective _ hri.ne' hfst)⟩

/-- SGP05's full marker with the blueprint's core threshold `|η_i(p)| ≤ 7ℓ` verbatim. -/
example (i : L.slim.finite_centres.toFinset) {p q : X} (hΔ : 0 ≤ Δ)
    (hp : p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1))
    (hη : |(L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤
      7 * (10 ^ 5 * Δ))
    (hpq : cgpProjMap L Z (cgpQ3Tags L Z) q = cgpProjMap L Z (cgpQ3Tags L Z) p) :
    L.slim.cutoff i.1 q = 1 ∧
      (L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord q =
        (L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p :=
  sgp05_full_marker L Z i hp (by nlinarith) hpq

/-- **SGP06, exact coordinate coverage.** Every `|u| ≤ 8ℓ` is `η_i(q)` for a point `q` of the
original enlargement `Ã₃ = fc27SlimSet L 8` in `B(i, Lρ(i))` with full marker `ζ_i(q) = 1`. -/
theorem sgp06_coordinate_coverage (hΔ : 0 ≤ Δ) (i : L.slim.finite_centres.toFinset) {u : ℝ}
    (hu : |u| ≤ 8 * 10 ^ 5 * Δ) :
    ∃ q ∈ fc27SlimSet L 8, q ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) ∧
      (L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord q = u ∧
      L.slim.cutoff i.1 q = 1 := by
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hmem : u ∈ Icc (-(905 * 10 ^ 3 * Δ)) (905 * 10 ^ 3 * Δ) := by
    rw [abs_le] at hu
    constructor <;> nlinarith
  obtain ⟨q, hq, hqu⟩ := (L.slim.centre i.1 hi).Icc_subset_image_coord hmem
  have hqη : |(L.slim.centre i.1 hi).coord q| ≤ 8 * 10 ^ 5 * Δ := by rw [hqu]; exact hu
  refine ⟨q, ⟨i, hq, by linarith⟩, hq, hqu, ?_⟩
  rw [slimFamily_cutoff_eq_KA2 L hi]
  exact SlimCentre.cutoff_eq_one_of_abs_coord_le _ hq hqη

/-- **SGP06, localization (FC03 on `π₃𝓔⁰`).** If `p ∈ B(i, Lρ(i))` has `|η_i(p)| ≤ 7ℓ` and
`|π₃𝓔⁰(q) − π₃𝓔⁰(p)| ≤ Rρ(i)` with `0 ≤ R < 1/100`, then `q ∈ B(i, Lρ(i))`, `ζ_i(q) = 1` (full
marker), `|η_i(q) − η_i(p)| < ℓ/10` and `|η_i(q)| < 8ℓ`. -/
theorem sgp06_localization (hΔ : 1 ≤ Δ) (i : L.slim.finite_centres.toFinset) {p q : X}
    (hp : p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1))
    (hη : |(L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤
      7 * (10 ^ 5 * Δ))
    {R : ℝ} (hR0 : 0 ≤ R) (hR : R < 1 / 100)
    (hpq : dist (cgpProjMap L Z (cgpQ3Tags L Z) q) (cgpProjMap L Z (cgpQ3Tags L Z) p) ≤
      R * ρ i.1) :
    q ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) ∧ L.slim.cutoff i.1 q = 1 ∧
      |(L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord q -
        (L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| < 10 ^ 5 * Δ / 10 ∧
      |(L.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord q| < 8 * 10 ^ 5 * Δ := by
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hri := hρ i.1
  have hΔ0 : 0 < Δ := by linarith
  have hcutp : L.slim.cutoff i.1 p = 1 := by
    rw [slimFamily_cutoff_eq_KA2 L hi]
    exact SlimCentre.cutoff_eq_one_of_abs_coord_le _ hp (by nlinarith)
  obtain ⟨e', he'def⟩ : ∃ e', e' = (R + 1 / 100) / 2 := ⟨_, rfl⟩
  have he'0 : 0 < e' := by rw [he'def]; linarith
  have he'R : R < e' := by rw [he'def]; linarith
  have he'1 : e' < 1 / 100 := by rw [he'def]; linarith
  have hblk := dist_block_le_projMap_GAF L Z (slim_mem_cgpQ3Tags L Z i) q p
  have hblk' : dist (WithLp.toLp 2 ((ρ i.1 * L.slim.cutoff i.1 q) •
      planeAxis ((L.slim.centre i.1 hi).coord q), ρ i.1 * L.slim.cutoff i.1 q))
      (WithLp.toLp 2 ((ρ i.1 * 1) • planeAxis ((L.slim.centre i.1 hi).coord p), ρ i.1 * 1)) <
        ρ i.1 * e' := by
    rw [← hcutp]
    exact lt_of_le_of_lt (hblk.trans hpq)
      ((mul_lt_mul_of_pos_right he'R hri).trans_eq (mul_comm _ _))
  rw [dist_block_scale_GAF hri, one_smul] at hblk'
  have hd : dist (WithLp.toLp 2 (L.slim.cutoff i.1 q • planeAxis ((L.slim.centre i.1 hi).coord q),
      L.slim.cutoff i.1 q)) (WithLp.toLp 2 (planeAxis ((L.slim.centre i.1 hi).coord p), (1 : ℝ))) <
        e' := lt_of_mul_lt_mul_left hblk' hri.le
  have hA : ‖planeAxis ((L.slim.centre i.1 hi).coord p)‖ ≤ 7 * (10 ^ 5 * Δ) := by
    rw [norm_planeAxis]; exact hη
  obtain ⟨hζ, hv⟩ := norm_coordinate_sub_lt_of_block_dist he'0 (by linarith) hA hd
  rw [← map_sub, norm_planeAxis] at hv
  have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
  have hloc := marker_localization_lt he'0.le he'1 hℓ le_rfl
  have hv' : |(L.slim.centre i.1 hi).coord q - (L.slim.centre i.1 hi).coord p| <
      10 ^ 5 * Δ / 10 := hv.trans hloc
  have hcutq_ne : L.slim.cutoff i.1 q ≠ 0 := by
    intro h
    rw [h] at hζ
    linarith
  have hdom := cgpMarkerCutoff_ne_zero L hΔ0 (.inr (.inl i)) q hcutq_ne
  have hdom' : q ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) := by
    change q ∈ ball i.1 (1000000 * Δ * ρ i.1) at hdom
    rw [mem_ball] at hdom ⊢
    norm_num at hdom ⊢
    exact hdom
  have hqη : |(L.slim.centre i.1 hi).coord q| < 8 * 10 ^ 5 * Δ := by
    have := abs_sub_abs_le_abs_sub ((L.slim.centre i.1 hi).coord q)
      ((L.slim.centre i.1 hi).coord p)
    nlinarith
  refine ⟨hdom', ?_, hv', hqη⟩
  rw [slimFamily_cutoff_eq_KA2 L hi]
  exact SlimCentre.cutoff_eq_one_of_abs_coord_le _ hdom' hqη.le

end Marker

section Reference

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}

/-- SGP05's reference budget: `1 − (σ + 3δ/(10L − 2δ)) > 9/10` for `σ < 1/100`, `δ = 1/2`,
`L ≥ 10⁶`. -/
theorem sgp05_reference_budget_SGP3 {σ L : ℝ} (hσ : σ < 1 / 100) (hL : 1000000 ≤ L) :
    9 / 10 < 1 - (σ + (3 * (1 / 2) + 2 * 0) / (10 * L - 2 * (1 / 2))) := by
  have hden : 1 ≤ 10 * L - 2 * (1 / 2) := by linarith
  have hq : (3 * (1 / 2) + 2 * 0) / (10 * L - 2 * (1 / 2)) ≤ 3 / 2 / (10 * L - 2 * (1 / 2)) := by
    norm_num
  have hq2 : 3 / 2 / (10 * L - 2 * (1 / 2)) ≤ 3 / 2 / 9999999 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have : (3 : ℝ) / 2 / 9999999 < 1 / 100 := by norm_num
  linarith

/-- **SGP05, the reference bounds.** On `D_i`: the original reference-axis test with POSITIVE sign
gives a `ρ(i)⁻²g`-unit vector `w` with `dη_i(w) > 9/10` (the SGP03 lift toward
`(u_i(q) + 10L, v_i(q))`), and `|dη_i(w)| ≤ 2√(ρ(i)⁻² g(w, w))` for every `w` (the
`(1 + σs)`-Lipschitz bound): `9/10 < ‖ρ(i) dη_i(q)‖ ≤ 2` in the original metric. -/
theorem sgp05_reference_bounds (S : SlimFamily X g hmetric ρ hρ β Δ σs K) (hΔ : 1 ≤ Δ)
    (hσs : 0 < σs) (hσs1 : σs < 1 / 100)
    (hβ : β 1 ≤ min (1 / (1000 * (1000000 * Δ))) (1 / 2 / 100)) {i : X} (hi : i ∈ S.centres)
    {q : X} (hq : q ∈ ball i (95 / 100 * (1000000 * Δ) * ρ i)) :
    (∃ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 ∧
      9 / 10 < mvfderiv 𝓘(ℝ, E3) (S.centre i hi).coord q w) ∧
    ∀ w : TangentSpace 𝓘(ℝ, E3) q,
      |mvfderiv 𝓘(ℝ, E3) (S.centre i hi).coord q w| ≤
        2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner q w w) := by
  have hri := hρ i
  have hΔ0 : 0 < Δ := by linarith
  have h106 : (10 : ℝ) ^ 6 * Δ = 1000000 * Δ := by norm_num
  have hLpos : 0 < 1000000 * Δ := by positivity
  have hL6 : (1000000 : ℝ) ≤ 1000000 * Δ := by linarith
  have hqL : q ∈ ball i (10 ^ 6 * Δ * ρ i) := by
    rw [h106]
    refine ball_subset_ball ?_ hq
    have := mul_mul_le_mul_mul_SGP2 (k := 95 / 100) (k' := 1) (by norm_num) hLpos.le hri.le
    linarith
  have hsq : ∀ w : TangentSpace 𝓘(ℝ, E3) q, Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner q w w) =
      (ρ i)⁻¹ * Real.sqrt (g.inner q w w) := by
    intro w
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  refine ⟨?_, fun w => ?_⟩
  · obtain ⟨y, hy21, hdxy, hay⟩ := sgp03_reference_lift_SGP2 S hΔ (by norm_num) hβ hi hq
      (Or.inl rfl)
    obtain ⟨v, hvv, hgeo⟩ := exists_rescaled_minimizing_SGP2 g hmetric q y
    obtain ⟨d, hd⟩ : ∃ d, d = dist q y := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, r = (ρ i)⁻¹ * d := ⟨_, rfl⟩
    have hr1 : 10 * (1000000 * Δ) - 2 * (1 / 2) < r := by
      rw [hr, hd]; linarith [(abs_lt.mp hdxy).1]
    have hr2 : r < 10 * (1000000 * Δ) - 2 * (1 / 2) + 4 * (1 / 2) := by
      rw [hr, hd]; linarith [(abs_lt.mp hdxy).2]
    have hD : 0 < 10 * (1000000 * Δ) - 2 * (1 / 2) := by linarith
    have hrpos : 0 < r := hD.trans hr1
    have hdeq : d = ρ i * r := by rw [hr]; field_simp
    have hσ24 : σs * 24 ≤ 1 := by linarith
    have hyLi : y ∈ ball i (10 ^ 6 * Δ / σs * ρ i) := by
      rw [h106]
      refine ball_subset_ball ?_ hy21
      exact mul_le_mul_of_nonneg_right
        (sgp03_num_outer_SGP2 hLpos.le hσs (by linarith)) hri.le
    have hxyi : 10 ^ 6 * Δ * ρ i < dist q y := by
      rw [h106, ← hd, hdeq]
      exact sgp03_num_far_SGP2 hL6 (by norm_num) hri (by linarith) hr1
    have Ti := (S.centre i hi).test_phys_SGP2 hqL hyLi hxyi hvv (hgeo (ρ i) hri)
    rw [← hd, ← hr] at Ti
    simp only [sgpRaw_of_mem S hi] at hay
    have hV : 10 * (1000000 * Δ) - 2 * (1 / 2) + 1 / 2 <
        1 * ((sgpSplitMap (S.centre i hi) y).fst - (sgpSplitMap (S.centre i hi) q).fst) := by
      linarith
    have hl := sgp03_lower_i_SGP2 (E := 0) (Or.inl rfl) hD hr1 hr2 le_rfl Ti hV
    have hcr : ρ i / d = r⁻¹ := by rw [hr]; field_simp
    refine ⟨(ρ i / d) • v, ?_, ?_⟩
    · rw [gInner_smul_self, hvv, ← hd, hdeq]
      field_simp
    · rw [map_smul, smul_eq_mul, hcr]
      have hb := sgp05_reference_budget_SGP3 hσs1 hL6
      linarith
  · have hb := (S.centre i hi).abs_mvfderiv_le_SGP2 hσs.le hqL w
    rw [hsq]
    have hg0 := Real.sqrt_nonneg (g.inner q w w)
    have hk : 0 ≤ (ρ i)⁻¹ * Real.sqrt (g.inner q w w) := by positivity
    calc |mvfderiv 𝓘(ℝ, E3) (S.centre i hi).coord q w|
        ≤ (1 + σs) * (ρ i)⁻¹ * Real.sqrt (g.inner q w w) := hb
      _ = (1 + σs) * ((ρ i)⁻¹ * Real.sqrt (g.inner q w w)) := by ring
      _ ≤ 2 * ((ρ i)⁻¹ * Real.sqrt (g.inner q w w)) := by gcongr; linarith

end Reference

end DifferentialGeometry.Geometry.Collapse
