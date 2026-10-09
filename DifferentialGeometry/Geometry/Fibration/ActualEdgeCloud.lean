import DifferentialGeometry.Geometry.Fibration.ActualEdgeGraph
import DifferentialGeometry.Geometry.Fibration.ActualSlimRankTiers

/-!
# EGP07: the full marker, the reference bounds and the rank-one projection (edge cloud)

Blueprint `master207B.tex`, EGP07 (`thm:fibration-actual-second-cloud`, B:5141–5225), the tiers
that do not need the model graph, on the actual CGP01 map `𝓔⁰ = cgpGlobalMap L Z` and its `Q₂`
projection `π₂F = cgpProjMap L Z (cgpQ2Tags L Z)`.

* `egp07_full_marker`: "At ANY of its preimages that marker gives `f(η_j/Δ)g(t/Δ) = 1`. Each
  factor is in `[0, 1]`, and the fixed profile is strictly between zero and one on `(8, 9)`.
  Hence both factors equal one, and in particular `t ≤ 8Δ` at EVERY preimage": a full edge
  marker `ρ(j)` at `π₂F(q)` forces `ζ_j(q) = 1`, `q ∈ B(j, 100Δρ(j))`, `|η_j(q)| ≤ 8Δ` and
  `t(q) ≤ 8Δ`. The strictness of the profile is `descendingIntervalProfile_lt_one_KC5`.
* `egp07_exact_coordinate`: "its vector block gives `η_i(q) = a` at every preimage".
* `egp07_reference_bounds`: "The reference positive-axis test in EGP04 gives
  `‖R_i dη_i‖ > 9/10` in the original metric, while its upper bound is two" — a `ρ(i)⁻²g`-unit
  `w` with `dη_i(w) > 9/10` and `|dη_i(w)| ≤ 2√(ρ(i)⁻²g(w, w))` for all `w`; the wide form
  `egp07_reference_bounds_wide_KC5` holds on the whole chart ball `B(i, 100Δρ(i))`.
* `rank_one_projection_KC5`: FC06 in dimension one for a rank-one reference `T : ℝ →L H` with
  `|z| ≤ ‖Tz‖ ≤ C|z|`: if `‖d − T a‖ < e`, the orthogonal projection `P` onto `range T` has normal
  error `‖d − Pd‖ < e`, `‖Pd − Ta‖ < e` and `|a| − e < ‖Pd‖ < C|a| + e`;
  `rank_one_onto_KC5` (the projected map is onto `range T` once one projected value is nonzero) and
  `finrank_range_KC5` (`range T` is a line).
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

section Profile

/-- The cutoff profile is below one past its plateau: `value s < 1` for `s > 1`. -/
theorem cutoffProfile_value_lt_one_KC5 {s : ℝ} (hs : 1 < s) : CutoffProfile.value s < 1 := by
  have h0 : 0 < Real.smoothTransition (s - 1) := Real.smoothTransition.pos_of_pos (by linarith)
  have h1 := Real.smoothTransition.le_one (s - 1)
  unfold CutoffProfile.value CutoffProfile.stem
  nlinarith

/-- A descending interval profile is strictly below one past its left end. -/
theorem descendingIntervalProfile_lt_one_KC5 {a b x : ℝ} (hab : a < b) (hx : a < x) :
    descendingIntervalProfile a b x < 1 := by
  apply cutoffProfile_value_lt_one_KC5
  have : 0 < (x - a) / (b - a) := div_pos (by linarith) (by linarith)
  linarith

/-- Where a descending interval profile equals one, its argument is at most the left end. -/
theorem le_of_descendingIntervalProfile_eq_one_KC5 {a b x : ℝ} (hab : a < b)
    (h : descendingIntervalProfile a b x = 1) : x ≤ a := by
  by_contra hx
  exact (descendingIntervalProfile_lt_one_KC5 hab (lt_of_not_ge hx)).ne h

/-- Two factors in `[0, 1]` with product one are both one. -/
theorem eq_one_of_mul_eq_one_KC5 {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1)
    (h : u * v = 1) : u = 1 ∧ v = 1 := by
  constructor <;> nlinarith [hu.1, hu.2, hv.1, hv.2]

/-- The edge coordinate profile equals one only on `[-8, 8]`. -/
theorem abs_le_of_edgeCoordinateProfile_eq_one_KC5 {y : ℝ} (h : edgeCoordinateProfile y = 1) :
    |y| ≤ 8 := by
  have h1 := descendingIntervalProfile_mem_Icc (-(-8)) (-(-9)) (-y)
  have h2 := descendingIntervalProfile_mem_Icc 8 9 y
  obtain ⟨hl, hr⟩ := eq_one_of_mul_eq_one_KC5 h1 h2 h
  have hl' := le_of_descendingIntervalProfile_eq_one_KC5 (by norm_num) hl
  have hr' := le_of_descendingIntervalProfile_eq_one_KC5 (by norm_num) hr
  rw [abs_le]
  constructor <;> linarith

end Profile

section Marker

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- Where an actual edge cutoff equals one, `x ∈ B(j, 100Δρ(j))`, `|η_j(x)| ≤ 8Δ` and
`F(x)/ρ(x) ≤ 8Δ` (both factors of `f(η_j/Δ)g(F/(ρΔ))` equal one). -/
theorem EdgeFamily.le_of_cutoff_eq_one_KC5
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (hΔ : 0 < Δ) {j x : X}
    (h : F.cutoff j x = 1) :
    j ∈ F.centres ∧ x ∈ ball j (100 * Δ * ρ j) ∧ |F.coord j x| ≤ 8 * Δ ∧
      F.smoothing x / ρ x ≤ 8 * Δ := by
  obtain ⟨hj, hball, -, -⟩ := F.mem_of_cutoff_ne_zero hΔ (by rw [h]; exact one_ne_zero)
  have hx : x ∈ ball j (100 * Δ * ρ j) := by
    have hh := (inv_mul_lt_iff₀ (hρ j)).mp hball
    rw [mem_ball]
    linarith
  rw [F.cutoff_eq_formula hj hx] at h
  have h1 := intervalPlateauProfile_mem_Icc (-9) (-8) 8 9 (F.coord j x / Δ)
  have h2 := descendingIntervalProfile_mem_Icc 8 9 (F.smoothing x / ρ x / Δ)
  obtain ⟨hf, hg⟩ := eq_one_of_mul_eq_one_KC5 h1 h2 h
  have hη := abs_le_of_edgeCoordinateProfile_eq_one_KC5 hf
  have ht := le_of_descendingIntervalProfile_eq_one_KC5 (by norm_num) hg
  refine ⟨hj, hx, ?_, ?_⟩
  · rw [abs_div, abs_of_pos hΔ, div_le_iff₀ hΔ] at hη
    linarith
  · rw [div_le_iff₀ hΔ] at ht
    linarith

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- **EGP07, the full marker at every preimage.** If the edge marker of `j` at `π₂F(q)` is full
(`= ρ(j)`), then `ζ_j(q) = 1`, `q ∈ B(j, 100Δρ(j))`, `|η_j(q)| ≤ 8Δ` and `t(q) ≤ 8Δ`. -/
theorem egp07_full_marker (hΔ : 0 < Δ) (j : L.edge.finite_centres.toFinset) {q : X}
    (hq : cgpMarker L Z (.inr (.inr j)) (cgpProjMap L Z (cgpQ2Tags L Z) q) = ρ j.1) :
    L.edge.cutoff j.1 q = 1 ∧ q ∈ ball j.1 (100 * Δ * ρ j.1) ∧
      |L.edge.coord j.1 q| ≤ 8 * Δ ∧ cgpHeight L q ≤ 8 * Δ := by
  rw [cgpMarker_projMap L Z (edge_mem_cgpQ2Tags L Z j)] at hq
  have hblk : cgpMarker L Z (.inr (.inr j)) (cgpGlobalMap L Z q) =
      ρ j.1 * L.edge.cutoff j.1 q := (cgpGlobalMap_edgeBlock L Z j q).2
  rw [hblk] at hq
  have hcut : L.edge.cutoff j.1 q = 1 :=
    mul_left_cancel₀ (hρ j.1).ne' (hq.trans (mul_one _).symm)
  obtain ⟨-, hball, hη, ht⟩ := L.edge.le_of_cutoff_eq_one_KC5 hΔ hcut
  exact ⟨hcut, hball, hη, ht⟩

/-- **EGP07, the exact coordinate at every preimage.** If `ζ_j(p) = 1` and `π₂F(q) = π₂F(p)`, then
`ζ_j(q) = 1` and `η_j(q) = η_j(p)` (the vector block of `j`). -/
theorem egp07_exact_coordinate (j : L.edge.finite_centres.toFinset) {p q : X}
    (hcut : L.edge.cutoff j.1 p = 1)
    (hpq : cgpProjMap L Z (cgpQ2Tags L Z) q = cgpProjMap L Z (cgpQ2Tags L Z) p) :
    L.edge.cutoff j.1 q = 1 ∧ L.edge.coord j.1 q = L.edge.coord j.1 p := by
  have hrj := hρ j.1
  have hblk : cgpGlobalMap L Z q (cgpEdgeBlockTag L Z j) =
      cgpGlobalMap L Z p (cgpEdgeBlockTag L Z j) := by
    have h1 := cgpProjMap_apply_of_mem L Z (edge_mem_cgpQ2Tags L Z j) q
    have h2 := cgpProjMap_apply_of_mem L Z (edge_mem_cgpQ2Tags L Z j) p
    rw [hpq] at h1
    exact h1.symm.trans h2
  obtain ⟨hfq, hsq⟩ := cgpGlobalMap_edgeBlock L Z j q
  obtain ⟨hfp, hsp⟩ := cgpGlobalMap_edgeBlock L Z j p
  have hsnd : ρ j.1 * L.edge.cutoff j.1 q = ρ j.1 * L.edge.cutoff j.1 p := by
    rw [← hsq, ← hsp, hblk]
  have hfst : (ρ j.1 * L.edge.cutoff j.1 q) • planeAxis (L.edge.coord j.1 q) =
      (ρ j.1 * L.edge.cutoff j.1 p) • planeAxis (L.edge.coord j.1 p) := by
    rw [← hfq, ← hfp, hblk]
  rw [hcut, mul_one] at hsnd
  have hcutq : L.edge.cutoff j.1 q = 1 :=
    mul_left_cancel₀ hrj.ne' (hsnd.trans (mul_one _).symm)
  rw [hcutq, hcut, mul_one] at hfst
  exact ⟨hcutq, planeAxis_injective_SGP3 (smul_right_injective _ hrj.ne' hfst)⟩

end Marker

section Reference

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ}

/-- EGP07's reference budget: `(21b/4)/(400Δ − 4b) < 1/20` for `b ≤ 1/(1000·10⁶Δ)`, `Δ ≥ 1`. -/
theorem egp07_reference_budget_KC5 {b Δ : ℝ} (hΔ : 1 ≤ Δ) (hb0 : 0 < b)
    (hbΔ : b * (1000 * (1000000 * Δ)) ≤ 1) :
    (3 * (7 * b / 4) + 2 * 0) / (400 * Δ - 4 * b) < 1 / 20 := by
  have hbb : b ≤ b * Δ := le_mul_of_one_le_right hb0.le hΔ
  have hb9 : b * 1000000000 ≤ 1 := by nlinarith
  have hD : 1 ≤ 400 * Δ - 4 * b := by linarith
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-- **EGP07, the reference bounds on the whole chart ball.** For `q ∈ B(i, 100Δρ(i))`: the
reference positive-axis lift of length `400Δ` (EGP04) gives a `ρ(i)⁻²g`-unit `w` with
`dη_i(w) > 9/10`, and `|dη_i(w)| ≤ 2√(ρ(i)⁻²g(w, w))` for every `w`. -/
theorem egp07_reference_bounds_wide_KC5
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (hΔ : 1 ≤ Δ)
    (hσ : σc < 1 / 20) (hbL : b ≤ 1 / (1000 * (1000000 * Δ))) {i : X} (hi : i ∈ F.centres)
    {q : X} (hq : q ∈ ball i (100 * Δ * ρ i)) :
    (∃ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 ∧
      9 / 10 < mvfderiv 𝓘(ℝ, E3) (F.coord i) q w) ∧
    ∀ w : TangentSpace 𝓘(ℝ, E3) q,
      |mvfderiv 𝓘(ℝ, E3) (F.coord i) q w| ≤ 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner q w w) := by
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  refine ⟨?_, fun w => ?_⟩
  · obtain ⟨Bi, mBi, qi, ψ, hψx⟩ := exists_edge_split_KC2 F hi
    have hb0 : 0 < b := @KleinerLottApprox.error_pos X (WithLp 2 (ℝ × Bi))
      (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) _ i _ b ψ
    have hbinv : 1000 * (1000000 * Δ) ≤ b⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hb0]
      simpa only [one_div] using hbL
    have hbΔ : b * (1000 * (1000000 * Δ)) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hbL
      linarith
    have hbb : b ≤ b * Δ := le_mul_of_one_le_right hb0.le hΔ
    have hb1 : 5 * b ≤ Δ := by linarith
    have hqiR : (ρ i)⁻¹ * dist q i < 100 * Δ := inv_mul_dist_lt_of_mem_ball_LC87 hri hq
    have h400 : |400 * Δ * 1| = 400 * Δ := by
      rw [mul_one, abs_of_pos (by positivity)]
    obtain ⟨y, hyR, hyu, hyd⟩ := @exists_raw_offset_lift_KC2 X Bi
      (mX.rescale (ρ i)⁻¹ (inv_pos.mpr hri)) mBi i qi b ψ q (400 * Δ * 1) (by
        change |400 * Δ * 1| + 2 * ((ρ i)⁻¹ * dist q i) + 5 * b < b⁻¹
        rw [h400]
        linarith)
    change (ρ i)⁻¹ * dist y i < |400 * Δ * 1| + 2 * ((ρ i)⁻¹ * dist q i) + 5 * b at hyR
    change abs ((ρ i)⁻¹ * dist q y - |400 * Δ * 1|) < 3 * b at hyd
    rw [hψx, hψx] at hyu
    rw [h400] at hyR hyd
    obtain ⟨d, hd⟩ : ∃ d, d = dist q y := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, r = (ρ i)⁻¹ * d := ⟨_, rfl⟩
    have hr1 : 400 * Δ - 3 * b < r := by rw [hr, hd]; linarith [(abs_lt.mp hyd).1]
    have hr2 : r < 400 * Δ + 3 * b := by rw [hr, hd]; linarith [(abs_lt.mp hyd).2]
    have hdeq : d = ρ i * r := by rw [hr]; field_simp
    have hA : 400 * Δ - 2 * b < 1 * (egpRaw F i y - egpRaw F i q) := by
      have h := abs_lt.mp hyu
      linarith [h.1]
    obtain ⟨hD, hD1, hD2, hV⟩ := egp04_zero_lift_arith_KC3 hb0 hb1 hr1 hr2 hA
    have hyiR : (ρ i)⁻¹ * dist y i < 601 * Δ := by linarith
    have hyi : dist y i < 601 * Δ * ρ i := by
      rw [inv_mul_lt_iff₀ hri] at hyiR
      linarith
    have hΔρi : 0 < Δ * ρ i := mul_pos hΔ0 hri
    have hy1000 : y ∈ ball i (1000 * Δ * ρ i) := mem_ball.mpr (by linarith)
    have hrd : 399 * Δ < r := by linarith
    have hρΔ : ρ i ≤ Δ * ρ i := le_mul_of_one_le_left hri.le hΔ
    have hd399 : 399 * Δ * ρ i < d := by
      rw [hdeq]
      have h := mul_lt_mul_of_pos_left hrd hri
      linarith only [h]
    have hsep : 100 * Δ * ρ i < dist q y := by rw [← hd]; linarith
    obtain ⟨v, hvv, hgeo⟩ := exists_rescaled_minimizing_SGP2 g hmetric q y
    have Ti := F.test_phys_KC3 hi hq hy1000 hsep hvv (hgeo (ρ i) hri)
    rw [← hd, ← hr] at Ti
    have hli := sgp03_lower_i_SGP2 (E := 0) (Or.inl rfl) hD hD1 hD2 le_rfl Ti hV
    have hbud := egp07_reference_budget_KC5 hΔ hb0 hbΔ
    have hd0 : 0 < d := by linarith only [hd399, hΔρi]
    refine ⟨(ρ i / d) • v, ?_, ?_⟩
    · rw [gInner_smul_self, hvv, ← hd]
      field_simp
    · rw [map_smul, smul_eq_mul]
      have hcr : ρ i / d = r⁻¹ := by rw [hr]; field_simp
      rw [hcr]
      linarith
  · have hud : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (F.coord i) q :=
      ((F.contMDiffOn_coord hi).contMDiffAt (isOpen_ball.mem_nhds hq)).mdifferentiableAt
        (by simp)
    have h := abs_mvfderiv_le_of_lipschitzOn_riem g hmetric isOpen_univ (mem_univ q) hud
      (fun y _ z _ => F.coord_lipschitz_max_KC4 hi y z) w
    rw [sqrt_inv_sq_mul_KC2 hri]
    have hmax : max (1 + σc) 0 ≤ 2 := max_le (by linarith) (by norm_num)
    have hs := Real.sqrt_nonneg (g.inner q w w)
    have hk : 0 ≤ (ρ i)⁻¹ * Real.sqrt (g.inner q w w) := by positivity
    calc |mvfderiv 𝓘(ℝ, E3) (F.coord i) q w|
        ≤ max (1 + σc) 0 / ρ i * Real.sqrt (g.inner q w w) := h
      _ = max (1 + σc) 0 * ((ρ i)⁻¹ * Real.sqrt (g.inner q w w)) := by ring
      _ ≤ 2 * ((ρ i)⁻¹ * Real.sqrt (g.inner q w w)) := by gcongr

/-- **EGP07, the reference bounds** (frozen form, on `D_i = B(i, 20Δρ(i))`): a `ρ(i)⁻²g`-unit `w`
with `dη_i(w) > 9/10`, and `|dη_i(w)| ≤ 2√(ρ(i)⁻²g(w, w))` for every `w`
(`9/10 < ‖ρ(i) dη_i(q)‖ ≤ 2` in the original metric). -/
theorem egp07_reference_bounds
    (F : EdgeFamily X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc) (hΔ : 1 ≤ Δ)
    (hσ : σc < 1 / 20) (hbL : b ≤ 1 / (1000 * (1000000 * Δ))) {i : X} (hi : i ∈ F.centres)
    {q : X} (hq : q ∈ ball i (20 * Δ * ρ i)) :
    (∃ w : TangentSpace 𝓘(ℝ, E3) q, (ρ i)⁻¹ ^ 2 * g.inner q w w = 1 ∧
      9 / 10 < mvfderiv 𝓘(ℝ, E3) (F.coord i) q w) ∧
    ∀ w : TangentSpace 𝓘(ℝ, E3) q,
      |mvfderiv 𝓘(ℝ, E3) (F.coord i) q w| ≤ 2 * Real.sqrt ((ρ i)⁻¹ ^ 2 * g.inner q w w) := by
  have hΔρi : 0 < Δ * ρ i := mul_pos (by linarith) (hρ i)
  refine egp07_reference_bounds_wide_KC5 F hΔ hσ hbL hi (mem_ball.mpr ?_)
  have := mem_ball.mp hq
  linarith

end Reference

section RankOne

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **FC06 in dimension one, concrete form.** For `T : ℝ →L H` with `|z| ≤ ‖Tz‖` and `‖T‖ ≤ C`,
`P` the orthogonal projection onto `K = range T` and `‖d − T a‖ < e`: the normal error is
`‖d − Pd‖ < e`, `‖Pd − Ta‖ < e`, and `|a| − e < ‖Pd‖ < C|a| + e`. -/
theorem rank_one_projection_KC5 (T : ℝ →L[ℝ] H) {C : ℝ} (hT : ∀ z : ℝ, |z| ≤ ‖T z‖)
    (hTC : ‖T‖ ≤ C) [(LinearMap.range (T : ℝ →ₗ[ℝ] H)).HasOrthogonalProjection]
    {d : H} {a e : ℝ} (hd : ‖d - T a‖ < e) :
    ‖d - (LinearMap.range (T : ℝ →ₗ[ℝ] H)).starProjection d‖ < e ∧
      ‖(LinearMap.range (T : ℝ →ₗ[ℝ] H)).starProjection d - T a‖ < e ∧
      |a| - e < ‖(LinearMap.range (T : ℝ →ₗ[ℝ] H)).starProjection d‖ ∧
      ‖(LinearMap.range (T : ℝ →ₗ[ℝ] H)).starProjection d‖ < C * |a| + e := by
  set K := LinearMap.range (T : ℝ →ₗ[ℝ] H) with hK
  have hTa : T a ∈ K := LinearMap.mem_range_self (T : ℝ →ₗ[ℝ] H) a
  have hPTa : K.starProjection (T a) = T a := (K.starProjection_eq_self_iff).mpr hTa
  have hP : K.starProjection d - T a = K.starProjection (d - T a) := by
    rw [map_sub, hPTa]
  have h2 : ‖K.starProjection d - T a‖ < e := by
    rw [hP]
    exact (K.norm_starProjection_apply_le _).trans_lt hd
  have h1 : ‖d - K.starProjection d‖ < e := by
    have hdist := K.dist_starProjection_eq_infDist d
    have hinf : Metric.infDist d (K : Set H) ≤ dist d (T a) :=
      Metric.infDist_le_dist_of_mem hTa
    rw [← dist_eq_norm, hdist]
    exact hinf.trans_lt (by rw [dist_eq_norm]; exact hd)
  have hTa_le : ‖T a‖ ≤ C * |a| := by
    have := T.le_opNorm a
    rw [Real.norm_eq_abs] at this
    exact this.trans (mul_le_mul_of_nonneg_right hTC (abs_nonneg a))
  have hlow := hT a
  have htri1 : ‖T a‖ ≤ ‖K.starProjection d‖ + ‖K.starProjection d - T a‖ := by
    have := norm_sub_norm_le (T a) (K.starProjection d)
    rw [norm_sub_rev (T a)] at this
    linarith
  have htri2 : ‖K.starProjection d‖ ≤ ‖T a‖ + ‖K.starProjection d - T a‖ := by
    have := norm_sub_norm_le (K.starProjection d) (T a)
    linarith
  exact ⟨h1, h2, by linarith, by linarith⟩

/-- **Ontoness of the projected map.** If `D` is homogeneous and the projection of `D w₀` onto
`K = range T` is nonzero, every `k ∈ K` is the projection of some `D w`. -/
theorem rank_one_onto_KC5 (T : ℝ →L[ℝ] H)
    [(LinearMap.range (T : ℝ →ₗ[ℝ] H)).HasOrthogonalProjection] {V : Type*} [SMul ℝ V]
    (D : V → H) (hD : ∀ (c : ℝ) (w : V), D (c • w) = c • D w) {w₀ : V}
    (hw₀ : (LinearMap.range (T : ℝ →ₗ[ℝ] H)).starProjection (D w₀) ≠ 0) :
    ∀ k ∈ LinearMap.range (T : ℝ →ₗ[ℝ] H),
      ∃ w, (LinearMap.range (T : ℝ →ₗ[ℝ] H)).starProjection (D w) = k := by
  set K := LinearMap.range (T : ℝ →ₗ[ℝ] H) with hK
  obtain ⟨z₀, hz₀⟩ := K.starProjection_apply_mem (D w₀)
  have hz₀0 : z₀ ≠ 0 := by
    rintro rfl
    apply hw₀
    rw [← hz₀]
    exact map_zero _
  rintro k ⟨z, rfl⟩
  refine ⟨(z / z₀) • w₀, ?_⟩
  rw [hD, map_smul]
  change (z / z₀) • K.starProjection (D w₀) = T z
  rw [← hz₀]
  change (z / z₀) • T z₀ = T z
  rw [← map_smul, smul_eq_mul, div_mul_cancel₀ z hz₀0]

/-- The image of a rank-one reference with `|z| ≤ ‖Tz‖` is a line: `finrank (range T) = 1`. -/
theorem finrank_range_KC5 (T : ℝ →L[ℝ] H) (hT : ∀ z : ℝ, |z| ≤ ‖T z‖) :
    Module.finrank ℝ (LinearMap.range (T : ℝ →ₗ[ℝ] H)) = 1 := by
  have hinj : Function.Injective (T : ℝ →ₗ[ℝ] H) := by
    intro z z' h
    have h0 : T (z - z') = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr h
    have := hT (z - z')
    rw [h0, norm_zero] at this
    exact sub_eq_zero.mp (abs_nonpos_iff.mp this)
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_self]

end RankOne

end DifferentialGeometry.Geometry.Collapse
