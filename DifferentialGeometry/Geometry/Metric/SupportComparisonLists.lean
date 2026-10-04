import DifferentialGeometry.Geometry.Metric.SupportScalePacking
import DifferentialGeometry.Analysis.Integration.Measure.FinitePacking
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Whole comparison lists of the graph packets (EGP02, TCP01; FC08 in its meeting-ball form)

Blueprint `master207B.tex`: FC08 (`lem:fibration-ball-packing`, lines 448–490), EGP02
(`lem:fibration-edge-comparison-list`, 4845–4895), TCP01 (`lem:fibration-first-comparison-list`,
5250–5309), and the same calculus in SGP01 (4353–4408).

* `support_meeting_sharp_bounds`: a closed support `closedBall z (c ρ z)` meeting the reference ball
  `ball p (a ρ p)`, with `ρ` `Λ`-Lipschitz and `250 Λ a ≤ 1`, `250 Λ c ≤ 1`, gives the ratio
  `.99 < ρ z / ρ p < 1.01`, the center bound and the inclusion of every concentric reference ball in
  an explicit ball about `z` (the slow-scale calculation of EGP02).
* `edge_comparison_list_edge_bounds`, `edge_comparison_list_slim_bounds`: EGP02's list (EL) with
  `D = ball p (20 Δ ρ p)`, edge support radius `15 Δ`, slim support radius `901002 Δ`,
  `L = 10⁶ Δ`, `L Λ < 10⁻⁵`.
* `two_stratum_list_circle_bounds`, `…_edge_bounds`, `…_slim_bounds`: TCP01 with `D = ball p (10 ρ p)`
  and circle support radius `10`.
* `card_supports_meeting_ball_le`: FC08 as stated in the blueprint — the number of supports of a
  family with pairwise disjoint cores `ball (c j) (a ρ (c j))` that MEET the ball `ball p (R ρ p)` is
  at most any common volume ratio `b` of `ball (c j) (4 (R + 2C + a) ρ (c j))` to the core, required
  only for the meeting indices. (The tree's `card_le_of_lipschitz_scale_ball_overlap` counts balls
  through ONE point; the blueprint stresses that this does not bound supports meeting a ball.)
-/

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped ENNReal

namespace GC.MetricGeometry

variable {X : Type*} [PseudoMetricSpace X]

/-- Sharp slow-scale calculus for a support meeting a reference ball (EGP02/TCP01/SGP01). -/
theorem support_meeting_sharp_bounds {ρ : X → ℝ} {Λ : NNReal} (hρ : LipschitzWith Λ ρ)
    {p z : X} (hp : 0 < ρ p) (hz : 0 < ρ z) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (haΛ : 250 * (Λ * a) ≤ 1) (hcΛ : 250 * (Λ * c) ≤ 1)
    (hmeet : (closedBall z (c * ρ z) ∩ ball p (a * ρ p)).Nonempty) :
    99 / 100 < ρ z / ρ p ∧ ρ z / ρ p < 101 / 100 ∧ dist p z < (a + 101 / 100 * c) * ρ p ∧
      ∀ b : ℝ, 0 ≤ b → ball p (b * ρ p) ⊆ ball z ((100 / 99 * (a + b) + c) * ρ z) := by
  obtain ⟨q, hqz, hqp⟩ := hmeet
  change dist q z ≤ c * ρ z at hqz
  change dist q p < a * ρ p at hqp
  have hd : dist p z < a * ρ p + c * ρ z := by
    have ht := dist_triangle p q z
    rw [dist_comm p q] at ht
    linarith
  have hlip := hρ.dist_le_mul p z
  rw [Real.dist_eq] at hlip
  have hΛd : (Λ : ℝ) * dist p z ≤ (Λ * a) * ρ p + (Λ * c) * ρ z := by
    have h := mul_le_mul_of_nonneg_left hd.le (NNReal.coe_nonneg Λ)
    linarith
  have hx : (Λ * a) * ρ p ≤ ρ p / 250 := by nlinarith
  have hy : (Λ * c) * ρ z ≤ ρ z / 250 := by nlinarith
  have hup : ρ z * 249 < ρ p * 251 + ρ p / 100 := by
    nlinarith [(abs_le.mp (hlip.trans hΛd)).1]
  have hlo : ρ p * 249 ≤ ρ z * 251 := by
    nlinarith [(abs_le.mp (hlip.trans hΛd)).2]
  have hr1 : 99 / 100 < ρ z / ρ p := by
    rw [lt_div_iff₀ hp]; nlinarith
  have hr2 : ρ z / ρ p < 101 / 100 := by
    rw [div_lt_iff₀ hp]; nlinarith
  have hzp : ρ z < 101 / 100 * ρ p := by
    have h := (div_lt_iff₀ hp).mp hr2; linarith
  have hpz : ρ p < 100 / 99 * ρ z := by
    have h := (lt_div_iff₀ hp).mp hr1; linarith
  refine ⟨hr1, hr2, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hzp.le hc]
  · intro b hb x hx
    change dist x p < b * ρ p at hx
    change dist x z < (100 / 99 * (a + b) + c) * ρ z
    have ht := dist_triangle x p z
    have hab : 0 ≤ a + b := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hpz.le hab]

/-- EGP02 (EL), edge line: `D = ball p (20 Δ ρ p)` and edge support radius `15 Δ`. -/
theorem edge_comparison_list_edge_bounds {ρ : X → ℝ} {Λ : NNReal} (hρ : LipschitzWith Λ ρ)
    {p z : X} (hp : 0 < ρ p) (hz : 0 < ρ z) {Δ : ℝ} (hΔ : 1 ≤ Δ)
    (hΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hmeet : (closedBall z (15 * Δ * ρ z) ∩ ball p (20 * Δ * ρ p)).Nonempty) :
    99 / 100 < ρ z / ρ p ∧ ρ z / ρ p < 101 / 100 ∧ dist p z < 36 * Δ * ρ p ∧
      ball p (20 * Δ * ρ p) ⊆ ball z (57 * Δ * ρ z) := by
  have hΛ0 := NNReal.coe_nonneg Λ
  obtain ⟨h1, h2, h3, h4⟩ := support_meeting_sharp_bounds hρ hp hz (a := 20 * Δ) (c := 15 * Δ)
    (by positivity) (by positivity) (by nlinarith) (by nlinarith) hmeet
  refine ⟨h1, h2, h3.trans_le (by nlinarith), ?_⟩
  exact (h4 (20 * Δ) (by positivity)).trans (ball_subset_ball (by nlinarith))

/-- EGP02 (EL), slim line: slim support radius `901002 Δ`, `L = 10⁶ Δ`. -/
theorem edge_comparison_list_slim_bounds {ρ : X → ℝ} {Λ : NNReal} (hρ : LipschitzWith Λ ρ)
    {p z : X} (hp : 0 < ρ p) (hz : 0 < ρ z) {Δ : ℝ} (hΔ : 1 ≤ Δ)
    (hΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hmeet : (closedBall z (901002 * Δ * ρ z) ∩ ball p (20 * Δ * ρ p)).Nonempty) :
    99 / 100 < ρ z / ρ p ∧ ρ z / ρ p < 101 / 100 ∧
      dist p z < 92 / 100 * (1000000 * Δ) * ρ p ∧
      ball p (20 * Δ * ρ p) ⊆ ball z (91 / 100 * (1000000 * Δ) * ρ z) := by
  have hΛ0 := NNReal.coe_nonneg Λ
  obtain ⟨h1, h2, h3, h4⟩ := support_meeting_sharp_bounds hρ hp hz (a := 20 * Δ)
    (c := 901002 * Δ) (by positivity) (by positivity) (by nlinarith) (by nlinarith) hmeet
  refine ⟨h1, h2, h3.trans_le (by nlinarith), ?_⟩
  exact (h4 (20 * Δ) (by positivity)).trans (ball_subset_ball (by nlinarith))

/-- TCP01, circle line: `D = ball p (10 ρ p)`, circle support radius `10`. -/
theorem two_stratum_list_circle_bounds {ρ : X → ℝ} {Λ : NNReal} (hρ : LipschitzWith Λ ρ)
    {p z : X} (hp : 0 < ρ p) (hz : 0 < ρ z) {Δ : ℝ} (hΔ : 1 ≤ Δ)
    (hΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hmeet : (closedBall z (10 * ρ z) ∩ ball p (10 * ρ p)).Nonempty) :
    99 / 100 < ρ z / ρ p ∧ ρ z / ρ p < 101 / 100 ∧ dist p z < 21 * ρ p ∧
      ball p (10 * ρ p) ⊆ ball z (32 * ρ z) := by
  have hΛ0 := NNReal.coe_nonneg Λ
  obtain ⟨h1, h2, h3, h4⟩ := support_meeting_sharp_bounds hρ hp hz (a := 10) (c := 10)
    (by norm_num) (by norm_num) (by nlinarith) (by nlinarith) hmeet
  refine ⟨h1, h2, h3.trans_le (by nlinarith), ?_⟩
  exact (h4 10 (by norm_num)).trans (ball_subset_ball (by nlinarith))

/-- TCP01, edge line: `D = ball p (10 ρ p)` lies in the edge chart's own radius `36 Δ`. -/
theorem two_stratum_list_edge_bounds {ρ : X → ℝ} {Λ : NNReal} (hρ : LipschitzWith Λ ρ)
    {p z : X} (hp : 0 < ρ p) (hz : 0 < ρ z) {Δ : ℝ} (hΔ : 1 ≤ Δ)
    (hΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hmeet : (closedBall z (15 * Δ * ρ z) ∩ ball p (10 * ρ p)).Nonempty) :
    99 / 100 < ρ z / ρ p ∧ ρ z / ρ p < 101 / 100 ∧
      ball p (10 * ρ p) ⊆ ball z (36 * Δ * ρ z) := by
  have hΛ0 := NNReal.coe_nonneg Λ
  obtain ⟨h1, h2, -, h4⟩ := support_meeting_sharp_bounds hρ hp hz (a := 10) (c := 15 * Δ)
    (by norm_num) (by positivity) (by nlinarith) (by nlinarith) hmeet
  exact ⟨h1, h2, (h4 10 (by norm_num)).trans (ball_subset_ball (by nlinarith))⟩

/-- TCP01, slim line: `D = ball p (10 ρ p)` lies in the slim chart's own radius `.91 L`. -/
theorem two_stratum_list_slim_bounds {ρ : X → ℝ} {Λ : NNReal} (hρ : LipschitzWith Λ ρ)
    {p z : X} (hp : 0 < ρ p) (hz : 0 < ρ z) {Δ : ℝ} (hΔ : 1 ≤ Δ)
    (hΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hmeet : (closedBall z (901002 * Δ * ρ z) ∩ ball p (10 * ρ p)).Nonempty) :
    99 / 100 < ρ z / ρ p ∧ ρ z / ρ p < 101 / 100 ∧
      ball p (10 * ρ p) ⊆ ball z (91 / 100 * (1000000 * Δ) * ρ z) := by
  have hΛ0 := NNReal.coe_nonneg Λ
  obtain ⟨h1, h2, -, h4⟩ := support_meeting_sharp_bounds hρ hp hz (a := 10)
    (c := 901002 * Δ) (by norm_num) (by positivity) (by nlinarith) (by nlinarith) hmeet
  exact ⟨h1, h2, (h4 10 (by norm_num)).trans (ball_subset_ball (by nlinarith))⟩

/-- FC08 in its meeting-ball form: supports meeting `ball p (R ρ p)` are counted by any volume
ratio `b` of the enlarged balls `ball (c j) (4 (R + 2C + a) ρ (c j))` to the disjoint cores,
required only at the meeting indices. -/
theorem card_supports_meeting_ball_le {ι : Type*} [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (I : Finset ι) (c : ι → X) (S : ι → Set X) {ρ : X → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) {R C a b : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hbudget : Λ * max R C ≤ 1 / 4)
    (hS : ∀ j ∈ I, S j ⊆ closedBall (c j) (C * ρ (c j)))
    (hdisj : (I : Set ι).PairwiseDisjoint fun j => ball (c j) (a * ρ (c j))) (p : X)
    (hpos : ∀ j ∈ I, (S j ∩ ball p (R * ρ p)).Nonempty →
      0 < μ.real (ball (c j) (a * ρ (c j))))
    (hfin : ∀ j ∈ I, (S j ∩ ball p (R * ρ p)).Nonempty →
      μ (ball (c j) (4 * (R + 2 * C + a) * ρ (c j))) ≠ ∞)
    (hcomp : ∀ j ∈ I, (S j ∩ ball p (R * ρ p)).Nonempty →
      μ.real (ball (c j) (4 * (R + 2 * C + a) * ρ (c j))) ≤
        b * μ.real (ball (c j) (a * ρ (c j)))) :
    ({j | j ∈ I ∧ (S j ∩ ball p (R * ρ p)).Nonempty}.ncard : ℝ) ≤ b := by
  classical
  let J := I.filter fun j => (S j ∩ ball p (R * ρ p)).Nonempty
  have hset : {j | j ∈ I ∧ (S j ∩ ball p (R * ρ p)).Nonempty} = (J : Set ι) := by
    ext j
    simp only [mem_ofPred_eq, Finset.coe_filter, J]
  rw [hset, Set.ncard_coe_finset]
  have hJ (j : ι) (hj : j ∈ J) : j ∈ I ∧ (S j ∩ ball p (R * ρ p)).Nonempty :=
    Finset.mem_filter.mp hj
  have hmeet (j : ι) (hj : j ∈ J) :
      (closedBall (c j) (C * ρ (c j)) ∩ ball p (R * ρ p)).Nonempty := by
    obtain ⟨y, hyS, hyp⟩ := (hJ j hj).2
    exact ⟨y, hS j (hJ j hj).1 hyS, hyp⟩
  apply card_le_of_disjoint_measure_comparison μ J (fun j => ball (c j) (a * ρ (c j)))
    (fun j => ball (c j) (4 * (R + 2 * C + a) * ρ (c j))) hb
  · exact hdisj.subset (fun j hj => (hJ j hj).1)
  · intro j _
    exact isOpen_ball.measurableSet
  · intro j hj
    exact hpos j (hJ j hj).1 (hJ j hj).2
  · intro j hj
    exact hfin j (hJ j hj).1 (hJ j hj).2
  · intro i hi j hj
    have h := enlarged_core_ball_subset_of_supports_meeting hρ (hρpos p) (hρpos (c j))
      (hρpos (c i)) hR hC ha hbudget (hmeet j hj) (hmeet i hi)
    simpa only [mul_assoc] using h
  · intro j hj
    exact hcomp j (hJ j hj).1 (hJ j hj).2

end GC.MetricGeometry
