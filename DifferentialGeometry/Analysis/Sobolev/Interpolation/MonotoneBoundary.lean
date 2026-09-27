import DifferentialGeometry.Analysis.Calculus.Interpolation.MonotoneSpline
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem intervalIntegrable_norm_deriv_sq_of_lipschitz
    {f : ℝ → F} {K : ℝ≥0} (hf : LipschitzWith K f) (a b : ℝ) :
    IntervalIntegrable (fun t => ‖deriv f t‖ ^ 2) volume a b := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let : IsFiniteMeasure (volume.restrict (uIcc a b)) :=
    isFiniteMeasure_restrict.mpr isCompact_uIcc.measure_lt_top.ne
  have hLp : MemLp (deriv f) 2 (volume.restrict (uIcc a b)) := by
    apply MemLp.of_bound (aestronglyMeasurable_deriv f _) (K : ℝ)
    exact Filter.Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hf
  exact (intervalIntegrable_iff').mpr hLp.norm.integrable_sq

theorem integral_deriv_comp_piecewise_affine_lift_sq_le
    (ψ g : CircleDeg1Lift) {N : ℕ} (hN : 0 < N)
    (hcell : ∀ i < N, ∀ t ∈ Icc (i / (N : ℝ)) ((i + 1 : ℕ) / (N : ℝ)),
      g t = ψ (i / (N : ℝ)) +
        (ψ ((i + 1 : ℕ) / (N : ℝ)) - ψ (i / (N : ℝ))) * ((N : ℝ) * t - i))
    {Kg KΓ : ℝ≥0} (hg : LipschitzWith Kg g) {Γ : ℝ → F} (hΓ : LipschitzWith KΓ Γ) :
    (N : ℝ)⁻¹ * (∫ t in Icc (0 : ℝ) 1, ‖deriv (Γ ∘ g) t‖ ^ 2) ≤
      (KΓ : ℝ) ^ 2 * ∑ i ∈ Finset.range N,
        (ψ ((i + 1 : ℕ) / (N : ℝ)) - ψ (i / (N : ℝ))) ^ 2 := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  let a := fun i : ℕ => i / (N : ℝ)
  let Δ := fun i : ℕ => ψ (a (i + 1)) - ψ (a i)
  let b : ℝ → F := Γ ∘ g
  have hb : LipschitzWith (KΓ * Kg) b := hΓ.comp hg
  have hai (i : ℕ) : a i ≤ a (i + 1) :=
    div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ i) hNp.le
  have hint (i : ℕ) : IntervalIntegrable (fun t => ‖deriv b t‖ ^ 2) volume (a i) (a (i + 1)) :=
    intervalIntegrable_norm_deriv_sq_of_lipschitz hb _ _
  have hpart (i : ℕ) (hi : i < N) :
      (∫ t in a i..a (i + 1), ‖deriv b t‖ ^ 2) ≤ (KΓ : ℝ) ^ 2 * N * (Δ i) ^ 2 := by
    let L : ℝ≥0 := ⟨(KΓ : ℝ) * (N : ℝ) * Δ i, by
      have hd : 0 ≤ Δ i := ψ.uniform_partition_increment_nonneg N i
      positivity⟩
    have hlocal : LipschitzOnWith L b (Icc (a i) (a (i + 1))) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      apply (hΓ.dist_le_mul (g x) (g y)).trans
      rw [hcell i hi x hx, hcell i hi y hy]
      have heq : ψ (a i) + Δ i * ((N : ℝ) * x - i) -
          (ψ (a i) + Δ i * ((N : ℝ) * y - i)) = Δ i * (N : ℝ) * (x - y) := by ring
      rw [Real.dist_eq, heq, abs_mul, abs_mul,
        abs_of_nonneg (ψ.uniform_partition_increment_nonneg N i), abs_of_pos hNp]
      change (KΓ : ℝ) * (Δ i * (N : ℝ) * |x - y|) ≤
        ((KΓ : ℝ) * (N : ℝ) * Δ i) * dist x y
      rw [Real.dist_eq]
      ring_nf
      exact le_rfl
    have hpoint (t : ℝ) (ht : t ∈ Ioo (a i) (a (i + 1))) : ‖deriv b t‖ ^ 2 ≤ (L : ℝ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) L.coe_nonneg).mpr
        (norm_deriv_le_of_lipschitzOn (Icc_mem_nhds ht.1 ht.2) hlocal)
    have h := intervalIntegral.integral_mono_on_of_le_Ioo (hai i) (hint i)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (L : ℝ) ^ 2) volume _ _) hpoint
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    have heq : (a (i + 1) - a i) * (L : ℝ) ^ 2 = (KΓ : ℝ) ^ 2 * N * (Δ i) ^ 2 := by
      change (a (i + 1) - a i) * ((KΓ : ℝ) * (N : ℝ) * Δ i) ^ 2 = _
      dsimp only [a]
      push_cast
      field_simp
      ring
    exact h.trans_eq heq
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := a) (n := N) (fun i hi => hint i)
  have h01 : (∫ t in Icc (0 : ℝ) 1, ‖deriv b t‖ ^ 2) =
      ∑ i ∈ Finset.range N, ∫ t in a i..a (i + 1), ‖deriv b t‖ ^ 2 := by
    rw [hsum]
    simp only [a, Nat.cast_zero, zero_div, div_self hNp.ne']
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  change (N : ℝ)⁻¹ * (∫ t in Icc (0 : ℝ) 1, ‖deriv b t‖ ^ 2) ≤ _
  rw [h01]
  apply (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i hi => hpart i (Finset.mem_range.mp hi))
      (inv_nonneg.mpr hNp.le)).trans_eq
  rw [← Finset.mul_sum]
  change (N : ℝ)⁻¹ *
    (((KΓ : ℝ) ^ 2 * (N : ℝ)) * ∑ i ∈ Finset.range N, Δ i ^ 2) = _
  dsimp only [Δ, a]
  field_simp

omit [NormedSpace ℝ F] [CompleteSpace F] in
theorem integral_comp_monotone_lift_sub_sq_le_of_grid_knots
    (ψ g : CircleDeg1Lift) (hψ : Continuous ψ) {N : ℕ} (hN : 0 < N)
    (hknots : ∀ i ≤ N, g (i / (N : ℝ)) = ψ (i / (N : ℝ)))
    {Kg KΓ : ℝ≥0} (hg : LipschitzWith Kg g) {Γ : ℝ → F} (hΓ : LipschitzWith KΓ Γ) :
    (N : ℝ) * (∫ t in Icc (0 : ℝ) 1, ‖Γ (g t) - Γ (ψ t)‖ ^ 2) ≤
      (KΓ : ℝ) ^ 2 * ∑ i ∈ Finset.range N,
        (ψ ((i + 1 : ℕ) / (N : ℝ)) - ψ (i / (N : ℝ))) ^ 2 := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  let a := fun i : ℕ => i / (N : ℝ)
  let Δ := fun i : ℕ => ψ (a (i + 1)) - ψ (a i)
  let e := fun t => ‖Γ (g t) - Γ (ψ t)‖ ^ 2
  have he : Continuous e := ((hΓ.continuous.comp hg.continuous).sub
    (hΓ.continuous.comp hψ)).norm.pow 2
  have hai (i : ℕ) : a i ≤ a (i + 1) :=
    div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ i) hNp.le
  have hpart (i : ℕ) (hi : i < N) :
      (∫ t in a i..a (i + 1), e t) ≤ (N : ℝ)⁻¹ * (KΓ : ℝ) ^ 2 * (Δ i) ^ 2 := by
    have hpoint (t : ℝ) (ht : t ∈ Icc (a i) (a (i + 1))) :
        e t ≤ (KΓ : ℝ) ^ 2 * (Δ i) ^ 2 := by
      have hglo := g.monotone ht.1
      have hghi := g.monotone ht.2
      rw [hknots i hi.le] at hglo
      rw [hknots (i + 1) (by omega)] at hghi
      have hψlo := ψ.monotone ht.1
      have hψhi := ψ.monotone ht.2
      have hdiff : dist (g t) (ψ t) ≤ Δ i := by
        rw [Real.dist_eq, abs_le]
        constructor <;> dsimp only [Δ] <;> linarith
      have hn : ‖Γ (g t) - Γ (ψ t)‖ ≤ (KΓ : ℝ) * Δ i := by
        rw [← dist_eq_norm]
        exact (hΓ.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hdiff KΓ.coe_nonneg)
      have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg KΓ.coe_nonneg
        (ψ.uniform_partition_increment_nonneg N i))).mpr hn
      simpa only [mul_pow] using h
    have h := intervalIntegral.integral_mono_on (hai i) (he.intervalIntegrable _ _)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (KΓ : ℝ) ^ 2 * (Δ i) ^ 2)
        volume _ _) hpoint
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    apply h.trans_eq
    dsimp only [a]
    push_cast
    field_simp
    ring
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := a) (n := N) (fun _ _ => he.intervalIntegrable _ _)
  have h01 : (∫ t in Icc (0 : ℝ) 1, e t) =
      ∑ i ∈ Finset.range N, ∫ t in a i..a (i + 1), e t := by
    rw [hsum]
    simp only [a, Nat.cast_zero, zero_div, div_self hNp.ne']
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  change (N : ℝ) * (∫ t in Icc (0 : ℝ) 1, e t) ≤ _
  rw [h01]
  apply (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i hi => hpart i (Finset.mem_range.mp hi)) hNp.le).trans_eq
  rw [← Finset.mul_sum]
  dsimp only [Δ, a]
  field_simp

end DifferentialGeometry.Analysis

end

noncomputable section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Analysis

theorem integral_Icc_comp_sub_eq_of_periodic {f : ℝ → ℝ}
    (hf : Function.Periodic f 1) (d : ℝ) :
    (∫ t in Icc (0 : ℝ) 1, f (t - d)) = ∫ t in Icc (0 : ℝ) 1, f t := by
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_sub_right]
  have h := hf.intervalIntegral_add_eq (-d) 0
  simpa only [zero_add, add_zero, zero_sub, sub_eq_add_neg, add_comm] using h

theorem integral_deriv_comp_sub_sq_eq_of_periodic
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} (hf : Function.Periodic f 1) (d : ℝ) :
    (∫ t in Icc (0 : ℝ) 1, ‖deriv (fun s => f (s - d)) t‖ ^ 2) =
      ∫ t in Icc (0 : ℝ) 1, ‖deriv f t‖ ^ 2 := by
  have hder : Function.Periodic (deriv f) 1 := by
    intro t
    have heq : (fun s => f (s + 1)) = f := funext hf
    rw [← deriv_comp_add_const, heq]
  simp only [deriv_comp_sub_const]
  have hper : Function.Periodic (fun t => ‖deriv f t‖ ^ 2) 1 := by
    intro t
    change ‖deriv f (t + 1)‖ ^ 2 = ‖deriv f t‖ ^ 2
    rw [hder]
  exact integral_Icc_comp_sub_eq_of_periodic hper d

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_periodic_spline_boundary_approximation
    (ψ : CircleDeg1Lift) (hψ : Continuous ψ) {Γ : ℝ → F} {KΓ : ℝ≥0}
    (hΓ : LipschitzWith KΓ Γ) (hΓper : Function.Periodic Γ 1) :
    ∃ g : ℕ → CircleDeg1Lift,
      (∀ n, LipschitzWith ((3 * (n + 1) : ℕ) : ℝ≥0) (g n)) ∧
      (∀ (n i : ℕ), i < 3 * (n + 1) → ∀ t ∈ Icc (i / ((3 * (n + 1) : ℕ) : ℝ))
        ((i + 1 : ℕ) / ((3 * (n + 1) : ℕ) : ℝ)),
        g n t = ψ (i / ((3 * (n + 1) : ℕ) : ℝ)) +
          (ψ ((i + 1 : ℕ) / ((3 * (n + 1) : ℕ) : ℝ)) -
            ψ (i / ((3 * (n + 1) : ℕ) : ℝ))) * (((3 * (n + 1) : ℕ) : ℝ) * t - i)) ∧
      (∀ n, g n 0 = ψ 0 ∧ g n (1 / 3) = ψ (1 / 3) ∧ g n (2 / 3) = ψ (2 / 3)) ∧
      (∀ n, Function.Periodic (Γ ∘ g n) 1) ∧
      (∀ n, LipschitzWith (KΓ * ((3 * (n + 1) : ℕ) : ℝ≥0)) (Γ ∘ g n)) ∧
      TendstoUniformly (fun n t => Γ (g n t)) (Γ ∘ ψ) atTop ∧
      (∀ n,
        (((3 * (n + 1) : ℕ) : ℝ))⁻¹ *
          (∫ t in Icc (0 : ℝ) 1, ‖deriv (Γ ∘ g n) t‖ ^ 2) ≤
            (KΓ : ℝ) ^ 2 * ∑ i ∈ Finset.range (3 * (n + 1)),
              (ψ ((i + 1 : ℕ) / ((3 * (n + 1) : ℕ) : ℝ)) -
                ψ (i / ((3 * (n + 1) : ℕ) : ℝ))) ^ 2) ∧
      (∀ n,
        (((3 * (n + 1) : ℕ) : ℝ)) *
          (∫ t in Icc (0 : ℝ) 1, ‖Γ (g n t) - Γ (ψ t)‖ ^ 2) ≤
            (KΓ : ℝ) ^ 2 * ∑ i ∈ Finset.range (3 * (n + 1)),
              (ψ ((i + 1 : ℕ) / ((3 * (n + 1) : ℕ) : ℝ)) -
                ψ (i / ((3 * (n + 1) : ℕ) : ℝ))) ^ 2) ∧
      Tendsto (fun n => (((3 * (n + 1) : ℕ) : ℝ))⁻¹ *
        (∫ t in Icc (0 : ℝ) 1, ‖deriv (Γ ∘ g n) t‖ ^ 2)) atTop (𝓝 0) ∧
      Tendsto (fun n => (((3 * (n + 1) : ℕ) : ℝ)) *
        (∫ t in Icc (0 : ℝ) 1, ‖Γ (g n t) - Γ (ψ t)‖ ^ 2)) atTop (𝓝 0) := by
  obtain ⟨g, hLip, hcell, hknots, hmarks, hconv, hsum⟩ :=
    ψ.exists_uniform_piecewise_affine_sequence hψ
  have hper (n : ℕ) : Function.Periodic (Γ ∘ g n) 1 := by
    intro t
    change Γ (g n (t + 1)) = Γ (g n t)
    rw [(g n).map_add_one, hΓper]
  have hder (n : ℕ) := integral_deriv_comp_piecewise_affine_lift_sq_le ψ (g n)
    (show 0 < 3 * (n + 1) by omega) (hcell n) (hLip n) hΓ
  have herr (n : ℕ) := integral_comp_monotone_lift_sub_sq_le_of_grid_knots ψ (g n) hψ
    (show 0 < 3 * (n + 1) by omega) (hknots n) (hLip n) hΓ
  have hlim := hsum.const_mul ((KΓ : ℝ) ^ 2)
  simp only [mul_zero] at hlim
  refine ⟨g, hLip, hcell, hmarks, hper, (fun n => hΓ.comp (hLip n)),
    hΓ.uniformContinuous.comp_tendstoUniformly hconv, hder, herr, ?_, ?_⟩
  · exact squeeze_zero (fun n => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (integral_nonneg fun t => sq_nonneg _)) hder hlim
  · exact squeeze_zero (fun n => mul_nonneg (Nat.cast_nonneg _)
      (integral_nonneg fun t => sq_nonneg _)) herr hlim

end DifferentialGeometry.Analysis

end
