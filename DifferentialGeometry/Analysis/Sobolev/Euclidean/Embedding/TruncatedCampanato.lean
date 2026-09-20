import DifferentialGeometry.Analysis.Integration.Integral.AverageDifference
import DifferentialGeometry.Analysis.Integration.Measure.BallIntersection
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Poincare.Convex

noncomputable section

open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "D" => ball (0 : E) 1

private theorem truncated_ball_measure_pos
    {x : E} (hx : x ∈ closedBall (0 : E) 1) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    0 < volume.real (D ∩ ball x r) := by
  have h := volume_real_ball_inter_ball_fin_two_lower_bound (by norm_num : (0 : ℝ) < 1)
    hx hr (by linarith)
  exact (by positivity : (0 : ℝ) < Real.pi * r ^ 2 / 4).trans_le h

theorem tendsto_setAverage_truncated_ball_of_continuousAt
    {v : E → F} (hvm : MemLp v 2 (volume.restrict D))
    {x : E} (hx : x ∈ D) (hv : ContinuousAt v x)
    (rn : ℕ → ℝ) (hrn : ∀ n, 0 < rn n) (hrn1 : ∀ n, rn n ≤ 1)
    (hrlim : Tendsto rn atTop (𝓝 0)) :
    Tendsto (fun n => ⨍ y in D ∩ ball x (rn n), v y) atTop (𝓝 (v x)) := by
  let : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hiD : IntegrableOn v D := hvm.integrable (by norm_num)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδv⟩ := (Metric.continuousAt_iff.1 hv) (ε / 2) (half_pos hε)
  filter_upwards [(tendsto_order.1 hrlim).2 δ hδ] with n hn
  let S := D ∩ ball x (rn n)
  have hS : MeasurableSet S := measurableSet_ball.inter measurableSet_ball
  have hfinite : volume S < ∞ := (measure_mono inter_subset_left).trans_lt measure_ball_lt_top
  have hpos : 0 < volume.real S :=
    truncated_ball_measure_pos (ball_subset_closedBall hx) (hrn n) (hrn1 n)
  have hi : IntegrableOn v S := hiD.mono_set inter_subset_left
  have heq : (⨍ y in S, v y) - v x =
      (volume.real S)⁻¹ • ∫ y in S, v y - v x := by
    rw [setAverage_eq, integral_sub hi (integrableOn_const hfinite.ne),
      setIntegral_const, smul_sub, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
  have hb : ‖∫ y in S, v y - v x‖ ≤ (ε / 2) * volume.real S := by
    apply norm_setIntegral_le_of_norm_le_const_ae hfinite
    filter_upwards [ae_restrict_mem hS] with y hy
    have hdist : dist (v y) (v x) < ε / 2 := hδv (hy.2.trans hn)
    simpa only [dist_eq_norm] using hdist.le
  rw [dist_eq_norm, heq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
  calc
    _ ≤ (volume.real S)⁻¹ * ((ε / 2) * volume.real S) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hpos.le)
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

private theorem norm_setAverage_truncated_half_sub_le
    {v : E → F} (hvm : MemLp v 2 (volume.restrict D))
    {x : E} (hx : x ∈ closedBall (0 : E) 1) {r α V : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hV : 0 ≤ V)
    (hvar : (∫ y in D ∩ ball x r, ‖v y - ⨍ z in D ∩ ball x r, v z‖ ^ 2) ≤
      V * r ^ (2 + 2 * α)) :
    ‖(⨍ y in D ∩ ball x (r / 2), v y) - (⨍ y in D ∩ ball x r, v y)‖ ≤
      Real.sqrt (16 * V / Real.pi) * r ^ α := by
  let S := D ∩ ball x (r / 2)
  let T := D ∩ ball x r
  have hST : S ⊆ T := inter_subset_inter_right D (ball_subset_ball (by linarith))
  have hSpos : 0 < volume.real S :=
    truncated_ball_measure_pos hx (half_pos hr) (by linarith)
  have hTfin : volume T ≠ ∞ :=
    ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
  have hfT : MemLp v 2 (volume.restrict T) :=
    hvm.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  have hstep := norm_setAverage_sub_setAverage_sq_le hST hSpos hTfin hfT
  have hdensity : Real.pi * r ^ 2 / 16 ≤ volume.real S := by
    have h := volume_real_ball_inter_ball_fin_two_lower_bound (by norm_num : (0 : ℝ) < 1)
      hx (half_pos hr) (by linarith)
    convert h using 1
    ring
  have hinv : (volume.real S)⁻¹ ≤ (Real.pi * r ^ 2 / 16)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hdensity
  have hrpow : r ^ (2 + 2 * α) = r ^ 2 * (r ^ α) ^ 2 := by
    rw [Real.rpow_add hr, Real.rpow_two]
    congr 1
    rw [mul_comm (2 : ℝ) α, Real.rpow_mul hr.le, Real.rpow_two]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hr.le _))).mp
  calc
    _ ≤ (volume.real S)⁻¹ * ∫ y in T, ‖v y - ⨍ z in T, v z‖ ^ 2 := hstep
    _ ≤ (volume.real S)⁻¹ * (V * r ^ (2 + 2 * α)) :=
      mul_le_mul_of_nonneg_left hvar (inv_nonneg.mpr hSpos.le)
    _ ≤ (Real.pi * r ^ 2 / 16)⁻¹ * (V * r ^ (2 + 2 * α)) :=
      mul_le_mul_of_nonneg_right hinv (mul_nonneg hV (Real.rpow_nonneg hr.le _))
    _ = (Real.sqrt (16 * V / Real.pi) * r ^ α) ^ 2 := by
      rw [hrpow, mul_pow, Real.sq_sqrt (by positivity)]
      field_simp

theorem norm_sub_setAverage_truncated_ball_le_of_variance_bound
    {v : E → F} (hvm : MemLp v 2 (volume.restrict D)) (hv : ContinuousOn v D)
    {V α R₀ : ℝ} (hV : 0 ≤ V) (hα : 0 < α) (hR₀ : R₀ ≤ 1)
    {x : E} (hx : x ∈ D)
    (hvar : ∀ r : ℝ, 0 < r → r ≤ R₀ →
      (∫ y in D ∩ ball x r, ‖v y - ⨍ z in D ∩ ball x r, v z‖ ^ 2) ≤
        V * r ^ (2 + 2 * α))
    {r : ℝ} (hr : 0 < r) (hrR₀ : r ≤ R₀) :
    ‖v x - ⨍ y in D ∩ ball x r, v y‖ ≤
      Real.sqrt (16 * V / Real.pi) * r ^ α / (1 - (1 / 2 : ℝ) ^ α) := by
  let rn (n : ℕ) := r * (1 / 2 : ℝ) ^ n
  let av (n : ℕ) := ⨍ y in D ∩ ball x (rn n), v y
  have hrn (n : ℕ) : 0 < rn n := mul_pos hr (pow_pos (by norm_num) n)
  have hrnr (n : ℕ) : rn n ≤ r := by
    dsimp only [rn]
    exact mul_le_of_le_one_right hr.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hrnlim : Tendsto rn atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul r
  have havlim : Tendsto av atTop (𝓝 (v x)) :=
    tendsto_setAverage_truncated_ball_of_continuousAt hvm hx
      (hv.continuousAt (isOpen_ball.mem_nhds hx)) rn hrn
      (fun n => (hrnr n).trans (hrR₀.trans hR₀)) hrnlim
  have hρ : (1 / 2 : ℝ) ^ α < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hstep (n : ℕ) : dist (av n) (av (n + 1)) ≤
      (Real.sqrt (16 * V / Real.pi) * r ^ α) * ((1 / 2 : ℝ) ^ α) ^ n := by
    have h := norm_setAverage_truncated_half_sub_le hvm (ball_subset_closedBall hx)
      (hrn n) ((hrnr n).trans (hrR₀.trans hR₀)) hV
      (hvar (rn n) (hrn n) ((hrnr n).trans hrR₀))
    have hnext : rn (n + 1) = rn n / 2 := by dsimp only [rn]; rw [pow_succ]; ring
    have hrpow : (rn n) ^ α = r ^ α * ((1 / 2 : ℝ) ^ α) ^ n := by
      dsimp only [rn]
      rw [Real.mul_rpow hr.le (pow_nonneg (by norm_num) n),
        ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2) α n]
    simpa only [av, hnext, dist_eq_norm, norm_sub_rev, hrpow, mul_assoc] using h
  have h := dist_le_of_le_geometric_of_tendsto₀ ((1 / 2 : ℝ) ^ α)
    (Real.sqrt (16 * V / Real.pi) * r ^ α) hρ hstep havlim
  simpa only [av, rn, pow_zero, mul_one, dist_eq_norm, norm_sub_rev] using h

end DifferentialGeometry.Analysis

end

noncomputable section

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "D" => ball (0 : E) 1

private theorem norm_setAverage_truncated_sub_double_le
    {v : E → F} (hvm : MemLp v 2 (volume.restrict D)) {x y : E}
    (hy : y ∈ closedBall (0 : E) 1) {r α V : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hV : 0 ≤ V)
    (hsub : D ∩ ball y r ⊆ D ∩ ball x (2 * r))
    (hvar : (∫ z in D ∩ ball x (2 * r),
      ‖v z - ⨍ w in D ∩ ball x (2 * r), v w‖ ^ 2) ≤ V * (2 * r) ^ (2 + 2 * α)) :
    ‖(⨍ z in D ∩ ball y r, v z) - (⨍ z in D ∩ ball x (2 * r), v z)‖ ≤
      Real.sqrt (16 * V / Real.pi) * (2 * r) ^ α := by
  let S := D ∩ ball y r
  let T := D ∩ ball x (2 * r)
  have hdensity : Real.pi * r ^ 2 / 4 ≤ volume.real S :=
    volume_real_ball_inter_ball_fin_two_lower_bound (by norm_num : (0 : ℝ) < 1)
      hy hr (by linarith)
  have hSpos : 0 < volume.real S := (by positivity : 0 < Real.pi * r ^ 2 / 4).trans_le hdensity
  have hTfin : volume T ≠ ∞ :=
    ((measure_mono inter_subset_left).trans_lt measure_ball_lt_top).ne
  have hfT : MemLp v 2 (volume.restrict T) :=
    hvm.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  have hmean := norm_setAverage_sub_setAverage_sq_le hsub hSpos hTfin hfT
  have hinv : (volume.real S)⁻¹ ≤ (Real.pi * r ^ 2 / 4)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hdensity
  have hrpow : (2 * r) ^ (2 + 2 * α) = (2 * r) ^ 2 * ((2 * r) ^ α) ^ 2 := by
    rw [Real.rpow_add (by positivity : 0 < 2 * r), Real.rpow_two]
    congr 1
    rw [mul_comm (2 : ℝ) α, Real.rpow_mul (by positivity : 0 ≤ 2 * r), Real.rpow_two]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
    (Real.rpow_nonneg (by positivity : 0 ≤ 2 * r) _))).mp
  calc
    _ ≤ (volume.real S)⁻¹ * ∫ z in T, ‖v z - ⨍ w in T, v w‖ ^ 2 := hmean
    _ ≤ (volume.real S)⁻¹ * (V * (2 * r) ^ (2 + 2 * α)) :=
      mul_le_mul_of_nonneg_left hvar (inv_nonneg.mpr hSpos.le)
    _ ≤ (Real.pi * r ^ 2 / 4)⁻¹ * (V * (2 * r) ^ (2 + 2 * α)) :=
      mul_le_mul_of_nonneg_right hinv (mul_nonneg hV (Real.rpow_nonneg (by positivity) _))
    _ = (Real.sqrt (16 * V / Real.pi) * (2 * r) ^ α) ^ 2 := by
      rw [hrpow]
      simp only [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 16 * V / Real.pi)]
      field_simp
      ring

theorem exists_local_holder_bound_of_truncated_variance_bound
    {v : E → F} (hvm : MemLp v 2 (volume.restrict D)) (hv : ContinuousOn v D)
    {V α R₀ : ℝ} (hV : 0 ≤ V) (hα : 0 < α) (hR₀ : R₀ ≤ 1)
    (hvar : ∀ x ∈ closedBall (0 : E) 1, ∀ r : ℝ, 0 < r → r ≤ R₀ →
      (∫ y in D ∩ ball x r, ‖v y - ⨍ z in D ∩ ball x r, v z‖ ^ 2) ≤
        V * r ^ (2 + 2 * α)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ D, ∀ y ∈ D, dist x y < R₀ / 2 →
      ‖v x - v y‖ ≤ C * (dist x y) ^ α := by
  let A := Real.sqrt (16 * V / Real.pi)
  let q := (1 / 2 : ℝ) ^ α
  have hq : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hden : 0 < 1 - q := sub_pos.mpr hq
  let C := 2 * A * ((1 - q)⁻¹ + (2 : ℝ) ^ α)
  have hC : 0 ≤ C := by dsimp only [C, A]; positivity
  refine ⟨C, hC, ?_⟩
  intro x hx y hy hdist
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero, dist_self, Real.zero_rpow hα.ne', mul_zero, le_refl]
  let r := dist x y
  have hr : 0 < r := dist_pos.mpr hxy
  have hrR : r ≤ R₀ := by dsimp only [r]; linarith
  have hr1 : r ≤ 1 := hrR.trans hR₀
  have h2rR : 2 * r ≤ R₀ := by dsimp only [r]; linarith
  let mx := ⨍ z in D ∩ ball x r, v z
  let my := ⨍ z in D ∩ ball y r, v z
  let m := ⨍ z in D ∩ ball x (2 * r), v z
  have htailx : ‖v x - mx‖ ≤ A * r ^ α / (1 - q) :=
    norm_sub_setAverage_truncated_ball_le_of_variance_bound hvm hv hV hα hR₀ hx
      (hvar x (ball_subset_closedBall hx)) hr hrR
  have htaily : ‖v y - my‖ ≤ A * r ^ α / (1 - q) :=
    norm_sub_setAverage_truncated_ball_le_of_variance_bound hvm hv hV hα hR₀ hy
      (hvar y (ball_subset_closedBall hy)) hr hrR
  have hdouble := hvar x (ball_subset_closedBall hx) (2 * r) (by positivity) h2rR
  have hcrossx : ‖mx - m‖ ≤ A * (2 * r) ^ α :=
    norm_setAverage_truncated_sub_double_le hvm (ball_subset_closedBall hx) hr hr1 hV
      (inter_subset_inter_right D (ball_subset_ball (by linarith))) hdouble
  have hsuby : D ∩ ball y r ⊆ D ∩ ball x (2 * r) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    have hzy : dist z y < r := hz.2
    have hyx : dist y x = r := dist_comm y x
    exact (dist_triangle z y x).trans_lt (by linarith)
  have hcrossy : ‖my - m‖ ≤ A * (2 * r) ^ α :=
    norm_setAverage_truncated_sub_double_le hvm (ball_subset_closedBall hy) hr hr1 hV hsuby hdouble
  have htri : ‖v x - v y‖ ≤ ‖v x - mx‖ + ‖mx - m‖ + ‖my - m‖ + ‖v y - my‖ := by
    have h₁ := norm_sub_le_norm_sub_add_norm_sub (v x) mx (v y)
    have h₂ := norm_sub_le_norm_sub_add_norm_sub mx m (v y)
    have h₃ := norm_sub_le_norm_sub_add_norm_sub m my (v y)
    rw [norm_sub_rev m my, norm_sub_rev my (v y)] at h₃
    linarith
  calc
    ‖v x - v y‖ ≤ 2 * (A * r ^ α / (1 - q)) + 2 * (A * (2 * r) ^ α) := by
      linarith
    _ = C * (dist x y) ^ α := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le]
      dsimp only [C, r]
      ring

theorem uniformContinuousOn_of_truncated_variance_bound
    {v : E → F} (hvm : MemLp v 2 (volume.restrict D)) (hv : ContinuousOn v D)
    {V α R₀ : ℝ} (hV : 0 ≤ V) (hα : 0 < α) (hR₀ : 0 < R₀) (hR₀1 : R₀ ≤ 1)
    (hvar : ∀ x ∈ closedBall (0 : E) 1, ∀ r : ℝ, 0 < r → r ≤ R₀ →
      (∫ y in D ∩ ball x r, ‖v y - ⨍ z in D ∩ ball x r, v z‖ ^ 2) ≤
        V * r ^ (2 + 2 * α)) :
    UniformContinuousOn v D := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_local_holder_bound_of_truncated_variance_bound hvm hv hV hα hR₀1 hvar
  have hzero : ContinuousAt (fun r : ℝ => C * r ^ α) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 α (Or.inr hα.le))
  apply Metric.uniformContinuousOn_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδbound⟩ := Metric.continuousAt_iff.mp hzero ε hε
  refine ⟨min δ (R₀ / 2), lt_min hδ (half_pos hR₀), ?_⟩
  intro x hx y hy hxy
  have hsmall : dist x y < R₀ / 2 := hxy.trans_le (min_le_right _ _)
  have hclose : dist (dist x y) 0 < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using
      hxy.trans_le (min_le_left _ _)
  have h := hδbound hclose
  simp only [Real.zero_rpow hα.ne', mul_zero, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hC (Real.rpow_nonneg dist_nonneg _))] at h
  rw [dist_eq_norm]
  exact (hbound x hx y hy hsmall).trans_lt h

end DifferentialGeometry.Analysis

end

noncomputable section

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "E" => EuclideanSpace ℝ (Fin 2)

variable {ι : Type*} [Fintype ι]
local notation "F" => EuclideanSpace ℝ ι

theorem uniformContinuousOn_of_weak_gradient_power_bound_on_truncated_balls
    {v : E → F}
    (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) (ball (0 : E) 1))
    (hvc : ContinuousOn v (ball (0 : E) 1))
    {α C R₀ : ℝ} (hα : 0 < α) (hR₀ : 0 < R₀)
    (hpower : ∀ x ∈ closedBall (0 : E) 1, ∀ s : ℝ, 0 < s → s ≤ R₀ →
      (∫ y in ball (0 : E) 1 ∩ ball x s,
        ∑ j : Fin 2, ‖WithLp.toLp 2 (fun i => (hv i).weakGrad y j)‖ ^ 2) ≤
          C * s ^ (2 * α)) :
    UniformContinuousOn v (ball (0 : E) 1) := by
  have hC : 0 ≤ C := by
    have h := (integral_nonneg fun y =>
      Finset.sum_nonneg fun j _ => sq_nonneg
        ‖(WithLp.toLp 2 (fun i => (hv i).weakGrad y j) : F)‖).trans
      (hpower 0 (mem_closedBall_self zero_le_one) R₀ hR₀ le_rfl)
    nlinarith [Real.rpow_pos_of_pos hR₀ (2 * α)]
  have hvm : MemLp v 2 (volume.restrict (ball (0 : E) 1)) :=
    MemLp.of_eval_piLp fun i => (hv i).memLp
  apply DifferentialGeometry.Analysis.uniformContinuousOn_of_truncated_variance_bound
    hvm hvc (V := 16 * C) (mul_nonneg (by norm_num) hC) hα
    (lt_min hR₀ zero_lt_one) (min_le_right R₀ 1)
  intro x hx s hs hsR
  have hsum : (∑ i, ∫ y in ball (0 : E) 1 ∩ ball x s, ‖(hv i).weakGrad y‖ ^ 2) =
      ∫ y in ball (0 : E) 1 ∩ ball x s,
        ∑ j : Fin 2, ‖WithLp.toLp 2 (fun i => (hv i).weakGrad y j)‖ ^ 2 := by
    rw [← integral_finsetSum Finset.univ (fun i _ =>
      ((hv i).weakGrad_memLp.norm.integrable_sq).mono_measure
        (Measure.restrict_mono_set volume inter_subset_left))]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      simp only [EuclideanSpace.norm_sq_eq]
      rw [Finset.sum_comm]
  have hvar := integral_norm_sub_average_sq_inter_ball_le_weakGrad hv x s
  rw [hsum] at hvar
  norm_num only [Nat.reduceAdd, Nat.reducePow, Nat.cast_ofNat] at hvar
  calc
    _ ≤ 16 * s ^ 2 * (∫ y in ball (0 : E) 1 ∩ ball x s,
        ∑ j : Fin 2, ‖WithLp.toLp 2 (fun i => (hv i).weakGrad y j)‖ ^ 2) := hvar
    _ ≤ 16 * s ^ 2 * (C * s ^ (2 * α)) :=
      mul_le_mul_of_nonneg_left (hpower x hx s hs (hsR.trans (min_le_left R₀ 1))) (by positivity)
    _ = (16 * C) * s ^ (2 + 2 * α) := by
      rw [Real.rpow_add hs, Real.rpow_two]
      ring

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
