import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable

open Set MeasureTheory Metric
open scoped ENNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

noncomputable section

variable {X : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

omit [FiniteDimensional ℝ X] in
theorem exists_flat_deriv {T : ℝ} (hT : 0 < T) (v : timeL2 X T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (q : ℝ → X) (d : timeL2 X T),
      ContDiff ℝ (⊤ : ℕ∞) q ∧ Function.support q ⊆ Ioo 0 T ∧
        d =ᵐ[timeMeasure T] q ∧ dist d v < ε := by
  classical
  let η : ℝ := ε / 4
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨g, hg_comp, hg_smooth, hvg⟩ :=
    (Lp.memLp v).exist_eLpNorm_sub_le (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hη
  have hgLp : MemLp g 2 (timeMeasure T) :=
    hg_smooth.continuous.memLp_of_hasCompactSupport hg_comp
  obtain ⟨δ, hδ, hsmall⟩ :=
    hgLp.eLpNorm_indicator_le (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hη
  let ρ : ℝ := min (T / 8) (δ / 4)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by linarith) (by linarith)
  have hρT : ρ ≤ T / 8 := min_le_left _ _
  have h2ρδ : 2 * ρ ≤ δ := by
    have hρδ : ρ ≤ δ / 4 := min_le_right _ _
    linarith
  let S : Set ℝ := Icc 0 ρ ∪ Icc (T - ρ) T
  have hSmeas : MeasurableSet S := measurableSet_Icc.union measurableSet_Icc
  have hμS : timeMeasure T S ≤ ENNReal.ofReal δ := by
    calc
      timeMeasure T S ≤ volume S := Measure.restrict_le_self S
      _ ≤ volume (Icc 0 ρ) + volume (Icc (T - ρ) T) := measure_union_le _ _
      _ = ENNReal.ofReal ρ + ENNReal.ofReal ρ := by
        rw [Real.volume_Icc, Real.volume_Icc]
        congr 2 <;> ring
      _ = ENNReal.ofReal (2 * ρ) := by
        rw [show 2 * ρ = ρ + ρ by ring, ENNReal.ofReal_add hρ.le hρ.le]
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal h2ρδ
  have hSsmall : eLpNorm (S.indicator g) 2 (timeMeasure T) ≤ ENNReal.ofReal η :=
    hsmall S hSmeas hμS
  let χ : ContDiffBump (T / 2) :=
    ⟨T / 2 - ρ, T / 2 - ρ / 2, by linarith [hρT], by linarith [hρ]⟩
  let q : ℝ → X := fun t ↦ χ t • g t
  have hq_smooth : ContDiff ℝ (⊤ : ℕ∞) q := χ.contDiff.smul hg_smooth
  have hq_support : Function.support q ⊆ Ioo 0 T := by
    intro t ht
    have hχt : χ t ≠ 0 := by
      intro hzero
      apply ht
      simp [q, hzero]
    have htball : t ∈ ball (T / 2) χ.rOut := by
      rw [← χ.support_eq]
      exact hχt
    rw [Real.ball_eq_Ioo] at htball
    dsimp [χ] at htball
    constructor
    · linarith [htball.1, hρ]
    · linarith [htball.2, hρ]
  have hqLp : MemLp q 2 (timeMeasure T) :=
    memLp_of_continuousOn hq_smooth.continuous.continuousOn
  have hqg : eLpNorm (q - g) 2 (timeMeasure T) ≤ ENNReal.ofReal η := by
    refine (eLpNorm_mono_ae ?_).trans hSsmall
    unfold timeMeasure
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    by_cases htS : t ∈ S
    · rw [Set.indicator_of_mem htS]
      change ‖χ t • g t - g t‖ ≤ ‖g t‖
      have heq : χ t • g t - g t = (χ t - 1) • g t := by
        rw [sub_smul, one_smul]
      rw [heq, norm_smul, Real.norm_eq_abs]
      have habs : |χ t - 1| ≤ 1 := by
        rw [abs_of_nonpos (sub_nonpos.mpr (χ.le_one (x := t)))]
        linarith [χ.nonneg' t]
      nlinarith [norm_nonneg (g t)]
    · rw [Set.indicator_of_notMem htS]
      have hleft : ρ ≤ t := by
        by_contra h
        apply htS
        left
        exact ⟨ht.1, le_of_not_ge h⟩
      have hright : t ≤ T - ρ := by
        by_contra h
        apply htS
        right
        exact ⟨le_of_not_ge h, ht.2⟩
      have htclosed : t ∈ closedBall (T / 2) χ.rIn := by
        rw [Real.closedBall_eq_Icc]
        dsimp [χ]
        constructor <;> linarith
      change ‖χ t • g t - g t‖ ≤ ‖0‖
      rw [χ.one_of_mem_closedBall htclosed]
      simp
  let d : timeL2 X T := ofContinuousOn hq_smooth.continuous.continuousOn
  have hdq : d =ᵐ[timeMeasure T] q := coeFn_ofContinuousOn _
  have hdg : dist d (hgLp.toLp g) ≤ η := by
    rw [Lp.dist_def]
    refine ENNReal.toReal_le_of_le_ofReal hη.le ?_
    calc
      eLpNorm ((d : ℝ → X) - (hgLp.toLp g : ℝ → X)) 2 (timeMeasure T) =
          eLpNorm (q - g) 2 (timeMeasure T) := by
            apply eLpNorm_congr_ae
            exact hdq.sub hgLp.coeFn_toLp
      _ ≤ ENNReal.ofReal η := hqg
  have hgv : dist (hgLp.toLp g) v ≤ η := by
    rw [Lp.dist_def]
    refine ENNReal.toReal_le_of_le_ofReal hη.le ?_
    calc
      eLpNorm ((hgLp.toLp g : ℝ → X) - (v : ℝ → X)) 2 (timeMeasure T) =
          eLpNorm (g - (v : ℝ → X)) 2 (timeMeasure T) := by
            apply eLpNorm_congr_ae
            exact hgLp.coeFn_toLp.sub (by rfl)
      _ = eLpNorm ((v : ℝ → X) - g) 2 (timeMeasure T) :=
        eLpNorm_sub_comm _ _ _ _
      _ ≤ ENNReal.ofReal η := hvg
  refine ⟨q, d, hq_smooth, hq_support, hdq, ?_⟩
  calc
    dist d v ≤ dist d (hgLp.toLp g) + dist (hgLp.toLp g) v := dist_triangle _ _ _
    _ ≤ η + η := add_le_add hdg hgv
    _ < ε := by dsimp [η]; linarith

end

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
