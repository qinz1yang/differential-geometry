import DifferentialGeometry.Analysis.Estimates.GaussianSeries
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Measure

def gaussianShell (d : ℕ) (decay : ℝ) (k : ℕ) : ℝ :=
  (((k + 1 : ℕ) : ℝ) ^ d) *
    Real.exp (-decay * (k : ℝ) ^ 2)

private def exponentialShell (d : ℕ) (decay : ℝ) (k : ℕ) : ℝ :=
  (((k + 1 : ℕ) : ℝ) ^ d) *
    Real.exp (-decay * (k : ℝ))

private theorem summable_exponentialShell (d : ℕ) {decay : ℝ} (hdecay : 0 < decay) :
    Summable (exponentialShell d decay) := by
  have hbase := Real.summable_pow_mul_exp_neg_nat_mul d hdecay
  have hsucc := hbase.comp_injective Nat.succ_injective
  have hmul := hsucc.mul_left (Real.exp decay)
  refine hmul.congr fun k ↦ ?_
  simp only [exponentialShell, Function.comp_apply, Nat.cast_succ]
  have hexp :
      Real.exp (-decay * (k : ℝ)) =
        Real.exp decay * Real.exp (-decay * ((k : ℝ) + 1)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

private theorem gaussianShell_le_exponentialShell (d : ℕ) {decay : ℝ} (hdecay : 0 < decay)
    (k : ℕ) : gaussianShell d decay k ≤ exponentialShell d decay k := by
  have hk_sq : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    cases k with
    | zero => norm_num
    | succ k =>
        have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
        nlinarith [sq_nonneg ((k : ℝ) + 1)]
  unfold gaussianShell exponentialShell
  apply mul_le_mul_of_nonneg_left
  · exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left hk_sq (neg_nonpos.mpr hdecay.le))
  · positivity

theorem summable_gaussianShell (d : ℕ) {decay : ℝ} (hdecay : 0 < decay) :
    Summable (gaussianShell d decay) :=
  Summable.of_nonneg_of_le
    (fun k => by unfold gaussianShell; positivity)
    (gaussianShell_le_exponentialShell d hdecay) (summable_exponentialShell d hdecay)

def gaussianTail (d : ℕ) (decay : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (gaussianShell d decay (k + N))

theorem tendsto_gaussianTail (d : ℕ) {decay : ℝ} (hdecay : 0 < decay) :
    Tendsto (gaussianTail d decay) atTop (nhds 0) := by
  exact ENNReal.tendsto_sum_nat_add
    (fun k => ENNReal.ofReal (gaussianShell d decay k))
    (summable_gaussianShell d hdecay).tsum_ofReal_ne_top

private def unitAnnulus {X : Type*} [PseudoMetricSpace X]
    (q : X) (N k : ℕ) : Set X :=
  {x | (((N + k : ℕ) : ℝ) ≤ dist q x) ∧
    dist q x < (((N + k + 1 : ℕ) : ℝ))}

private theorem compl_ball_subset_iUnion_unitAnnulus {X : Type*} [PseudoMetricSpace X]
    (q : X) (N : ℕ) :
    (Metric.ball q (N : ℝ))ᶜ ⊆ ⋃ k : ℕ, unitAnnulus q N k := by
  intro x hx
  have hxN : (N : ℝ) ≤ dist q x := by
    rw [mem_compl_iff, Metric.mem_ball, not_lt] at hx
    simpa only [dist_comm] using hx
  let a : ℝ := dist q x - (N : ℝ)
  have ha0 : 0 ≤ a := sub_nonneg.mpr hxN
  let k : ℕ := ⌊a⌋₊
  have hklo : (k : ℝ) ≤ a := Nat.floor_le ha0
  have hkhi : a < (k : ℝ) + 1 := Nat.lt_floor_add_one a
  refine mem_iUnion.2 ⟨k, ?_⟩
  constructor
  · norm_num only [Nat.cast_add]
    linarith
  · norm_num only [Nat.cast_add, Nat.cast_one]
    linarith

private theorem lintegral_gaussian_unitAnnulus_le {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] (μ : Measure X) (q : X) (d N k : ℕ)
    (C : ℝ≥0∞) {decay : ℝ} (hdecay : 0 < decay)
    (hball : ∀ r : ℝ, 1 ≤ r →
      μ (Metric.ball q r) ≤ C * ENNReal.ofReal (r ^ d)) :
    ∫⁻ x in unitAnnulus q N k,
        ENNReal.ofReal (Real.exp (-decay * dist q x ^ 2)) ∂μ ≤
      C * ENNReal.ofReal (gaussianShell d decay (N + k)) := by
  let r : ℝ := ((N + k : ℕ) : ℝ)
  let R : ℝ := ((N + k + 1 : ℕ) : ℝ)
  let e : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-decay * r ^ 2))
  have hr0 : 0 ≤ r := by positivity
  have hR1 : 1 ≤ R := by
    dsimp only [R]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (N + k))
  have hpoint : ∀ x ∈ unitAnnulus q N k,
      ENNReal.ofReal (Real.exp (-decay * dist q x ^ 2)) ≤ e := by
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonpos_left
    · exact (sq_le_sq₀ hr0 (dist_nonneg : 0 ≤ dist q x)).2 hx.1
    · exact neg_nonpos.mpr hdecay.le
  have hann_ball : unitAnnulus q N k ⊆ Metric.ball q R := by
    intro x hx
    rw [Metric.mem_ball, dist_comm]
    exact hx.2
  have hpoly0 : 0 ≤ R ^ d := pow_nonneg (by positivity) d
  calc
    (∫⁻ x in unitAnnulus q N k,
        ENNReal.ofReal (Real.exp (-decay * dist q x ^ 2)) ∂μ) ≤
        ∫⁻ _x in unitAnnulus q N k, e ∂μ :=
      setLIntegral_mono measurable_const hpoint
    _ = e * μ (unitAnnulus q N k) := setLIntegral_const _ _
    _ ≤ e * μ (Metric.ball q R) :=
      mul_le_mul_right (measure_mono hann_ball) e
    _ ≤ e * (C * ENNReal.ofReal (R ^ d)) :=
      mul_le_mul_right (hball R hR1) e
    _ = C * ENNReal.ofReal ((R ^ d) * Real.exp (-decay * r ^ 2)) := by
      dsimp only [e]
      rw [ENNReal.ofReal_mul hpoly0]
      ac_rfl
    _ = C * ENNReal.ofReal (gaussianShell d decay (N + k)) := by
      rfl

theorem lintegral_gaussian_le_of_ball_growth {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] (μ : Measure X) (q : X) (d : ℕ) (C : ℝ≥0∞)
    {decay : ℝ} (hdecay : 0 < decay)
    (hball : ∀ r : ℝ, 1 ≤ r →
      μ (Metric.ball q r) ≤ C * ENNReal.ofReal (r ^ d)) (N : ℕ) :
    ∫⁻ x in (Metric.ball q (N : ℝ))ᶜ,
        ENNReal.ofReal (Real.exp (-decay * dist q x ^ 2)) ∂μ ≤
      C * gaussianTail d decay N := by
  calc
    (∫⁻ x in (Metric.ball q (N : ℝ))ᶜ,
        ENNReal.ofReal (Real.exp (-decay * dist q x ^ 2)) ∂μ) ≤
        ∫⁻ x in ⋃ k : ℕ, unitAnnulus q N k,
          ENNReal.ofReal (Real.exp (-decay * dist q x ^ 2)) ∂μ :=
      lintegral_mono_set (compl_ball_subset_iUnion_unitAnnulus q N)
    _ ≤ ∑' k : ℕ, ∫⁻ x in unitAnnulus q N k,
          ENNReal.ofReal (Real.exp (-decay * dist q x ^ 2)) ∂μ :=
      lintegral_iUnion_le _ _
    _ ≤ ∑' k : ℕ,
        C * ENNReal.ofReal (gaussianShell d decay (N + k)) :=
      ENNReal.tsum_le_tsum fun k =>
        lintegral_gaussian_unitAnnulus_le μ q d N k C hdecay hball
    _ = C * gaussianTail d decay N := by
      rw [ENNReal.tsum_mul_left]
      unfold gaussianTail
      congr 1
      exact tsum_congr fun k => by rw [Nat.add_comm N k]


theorem lintegral_gaussian_lt_top_of_exponential_ball_growth
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (q : X) {C : ℝ≥0∞} (hC : C ≠ ∞) {growth decay : ℝ}
    (hdecay : 0 < decay)
    (hball : ∀ r : ℝ, 1 ≤ r →
      μ (Metric.ball q r) ≤ C * ENNReal.ofReal (Real.exp (growth * r))) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-decay * dist q x ^ 2)) ∂μ) < ∞ := by
  have hterm (k : ℕ) :
      (∫⁻ x in unitAnnulus q 0 k,
        ENNReal.ofReal (Real.exp (-decay * dist q x ^ 2)) ∂μ) ≤
      C * ENNReal.ofReal (Real.exp growth) *
        ENNReal.ofReal (Real.exp (-decay * (k : ℝ) ^ 2 + growth * k)) := by
    let e : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-decay * (k : ℝ) ^ 2))
    have hpoint : ∀ x ∈ unitAnnulus q 0 k,
        ENNReal.ofReal (Real.exp (-decay * dist q x ^ 2)) ≤ e := by
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hdecay.le)
      exact (sq_le_sq₀ (Nat.cast_nonneg k) dist_nonneg).2 (by simpa [unitAnnulus] using hx.1)
    have hsub : unitAnnulus q 0 k ⊆ Metric.ball q ((k : ℝ) + 1) := by
      intro x hx
      rw [Metric.mem_ball, dist_comm]
      simpa [unitAnnulus, Nat.cast_add, Nat.cast_one] using hx.2
    calc
      _ ≤ ∫⁻ _x in unitAnnulus q 0 k, e ∂μ := setLIntegral_mono measurable_const hpoint
      _ = e * μ (unitAnnulus q 0 k) := setLIntegral_const _ _
      _ ≤ e * μ (Metric.ball q ((k : ℝ) + 1)) :=
        mul_le_mul_right (measure_mono hsub) e
      _ ≤ e * (C * ENNReal.ofReal (Real.exp (growth * ((k : ℝ) + 1)))) :=
        mul_le_mul_right (hball _ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])) e
      _ = _ := by
        dsimp only [e]
        rw [show growth * ((k : ℝ) + 1) = growth + growth * k by ring,
          Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
          Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
        ac_rfl
  have hcover : (Set.univ : Set X) ⊆ ⋃ k : ℕ, unitAnnulus q 0 k := by
    simpa only [Nat.cast_zero, Metric.ball_zero, compl_empty] using
      compl_ball_subset_iUnion_unitAnnulus q 0
  calc
    _ = ∫⁻ x in (Set.univ : Set X),
        ENNReal.ofReal (Real.exp (-decay * dist q x ^ 2)) ∂μ := by rw [Measure.restrict_univ]
    _ ≤ ∫⁻ x in ⋃ k : ℕ, unitAnnulus q 0 k,
        ENNReal.ofReal (Real.exp (-decay * dist q x ^ 2)) ∂μ := lintegral_mono_set hcover
    _ ≤ ∑' k : ℕ, ∫⁻ x in unitAnnulus q 0 k,
        ENNReal.ofReal (Real.exp (-decay * dist q x ^ 2)) ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' k : ℕ, C * ENNReal.ofReal (Real.exp growth) *
        ENNReal.ofReal (Real.exp (-decay * (k : ℝ) ^ 2 + growth * k)) :=
      ENNReal.tsum_le_tsum hterm
    _ = (C * ENNReal.ofReal (Real.exp growth)) *
        ∑' k : ℕ, ENNReal.ofReal (Real.exp (-decay * (k : ℝ) ^ 2 + growth * k)) :=
      ENNReal.tsum_mul_left
    _ < ∞ := ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC) ENNReal.ofReal_lt_top)
      (DifferentialGeometry.Analysis.tsum_ofReal_exp_neg_mul_sq_add_mul_lt_top decay growth hdecay)

theorem integrable_gaussian_of_exponential_ball_growth
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (q : X) {C : ℝ≥0∞} (hC : C ≠ ∞) {growth decay : ℝ}
    (hdecay : 0 < decay)
    (hball : ∀ r : ℝ, 1 ≤ r →
      μ (Metric.ball q r) ≤ C * ENNReal.ofReal (Real.exp (growth * r))) :
    Integrable (fun x => Real.exp (-decay * dist q x ^ 2)) μ := by
  have hmeas : AEStronglyMeasurable (fun x => Real.exp (-decay * dist q x ^ 2)) μ :=
    (by fun_prop : Continuous (fun x => Real.exp (-decay * dist q x ^ 2))).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))]
  exact lintegral_gaussian_lt_top_of_exponential_ball_growth μ q hC hdecay hball

theorem integrable_mul_gaussian_of_exponential_ball_growth
    {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) (q : X) {C : ℝ≥0∞} (hC : C ≠ ∞) {growth decay : ℝ}
    (hdecay : 0 < decay)
    (hball : ∀ r : ℝ, 1 ≤ r →
      μ (Metric.ball q r) ≤ C * ENNReal.ofReal (Real.exp (growth * r)))
    {f : X → ℝ} (hf : AEStronglyMeasurable f μ) {K : ℝ}
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ K) :
    Integrable (fun x => f x * Real.exp (-decay * dist q x ^ 2)) μ := by
  have hg := integrable_gaussian_of_exponential_ball_growth μ q hC hdecay hball
  apply (hg.const_mul K).mono (hf.mul hg.aestronglyMeasurable)
  filter_upwards [hbound] with x hx
  change ‖f x * Real.exp (-decay * dist q x ^ 2)‖ ≤
    ‖K * Real.exp (-decay * dist q x ^ 2)‖
  rw [norm_mul, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact hx.trans (by simpa only [Real.norm_eq_abs] using le_abs_self K)

end DifferentialGeometry.Analysis.Measure

end

end

section

namespace DifferentialGeometry.Analysis.Measure

theorem antitone_gaussianTail_decay (d N : ℕ) :
    Antitone (fun decay : ℝ => gaussianTail d decay N) := by
  intro a b hab
  unfold gaussianTail
  apply ENNReal.tsum_le_tsum
  intro k
  apply ENNReal.ofReal_le_ofReal
  unfold gaussianShell
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (neg_le_neg hab) (sq_nonneg _))

end DifferentialGeometry.Analysis.Measure

end
