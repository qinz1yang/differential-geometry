import DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {T : ℝ}

def timeMeasure (T : ℝ) : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) T)

instance instIsFiniteMeasureTimeMeasure (T : ℝ) : IsFiniteMeasure (timeMeasure T) := by
  unfold timeMeasure; infer_instance

theorem timeMeasure_univ (T : ℝ) :
    timeMeasure T Set.univ = ENNReal.ofReal T := by
  unfold timeMeasure
  rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]

theorem timeMeasure_eq_zero_of_nonpos {T : ℝ} (hT : T ≤ 0) :
    timeMeasure T = 0 := by
  refine Measure.measure_univ_eq_zero.1 ?_
  rw [timeMeasure_univ, ENNReal.ofReal_eq_zero]
  exact hT

theorem timeMeasure_real_univ {T : ℝ} (hT : 0 ≤ T) :
    (timeMeasure T).real Set.univ = T := by
  rw [measureReal_def, timeMeasure_univ, ENNReal.toReal_ofReal hT]

theorem timeMeasure_ne_zero {T : ℝ} (hT : 0 < T) :
    timeMeasure T ≠ 0 := by
  intro h
  have : timeMeasure T Set.univ = 0 := by rw [h]; rfl
  rw [timeMeasure_univ, ENNReal.ofReal_eq_zero] at this
  exact absurd this (not_le.2 hT)

theorem toReal_ofReal_rpow_half (T : ℝ) :
    (ENNReal.ofReal T ^ (1 / 2 : ℝ)).toReal = Real.sqrt T := by
  rcases le_or_gt 0 T with hT | hT
  · rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hT, ← Real.sqrt_eq_rpow]
  · rw [ENNReal.ofReal_eq_zero.2 hT.le, ENNReal.zero_rpow_of_pos (by norm_num),
      ENNReal.toReal_zero, Real.sqrt_eq_zero'.2 hT.le]

abbrev timeL2 (X : Type*) [NormedAddCommGroup X]
    (T : ℝ) : Type _ :=
  MeasureTheory.Lp X 2 (timeMeasure T)

example : NormedAddCommGroup (timeL2 X T) := inferInstance
example : NormedSpace ℝ (timeL2 X T) := inferInstance
example : CompleteSpace (timeL2 X T) := inferInstance

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem memLp_iff {f : ℝ → X} :
    MemLp f 2 (timeMeasure T) ↔ ∃ F : timeL2 X T, F =ᵐ[timeMeasure T] f :=
  ⟨fun h => ⟨h.toLp f, h.coeFn_toLp⟩, fun ⟨F, hF⟩ => (Lp.memLp F).ae_eq hF⟩

section Hilbert

variable [InnerProductSpace ℝ X]

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem inner_def (f g : timeL2 X T) :
    (inner ℝ f g : ℝ) = ∫ t in Set.Icc (0 : ℝ) T, inner ℝ (f t) (g t) := by
  rw [L2.inner_def]; rfl

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem norm_sq_eq_integral (f : timeL2 X T) :
    ‖f‖ ^ 2 = ∫ t in Set.Icc (0 : ℝ) T, ‖f t‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_def]
  exact integral_congr_ae (Eventually.of_forall fun t => real_inner_self_eq_norm_sq _)

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem norm_eq_sqrt_integral (f : timeL2 X T) :
    ‖f‖ = Real.sqrt (∫ t in Set.Icc (0 : ℝ) T, ‖f t‖ ^ 2) := by
  rw [← norm_sq_eq_integral, Real.sqrt_sq (norm_nonneg _)]

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem integral_norm_sq_nonneg (f : timeL2 X T) :
    0 ≤ ∫ t in Set.Icc (0 : ℝ) T, ‖f t‖ ^ 2 := by
  rw [← norm_sq_eq_integral]; positivity

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem abs_intervalIntegral_inner_le_norm
    (f g : timeL2 X T) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) T) (hb : b ∈ Set.Icc (0 : ℝ) T) :
    |∫ t in a..b, inner ℝ (f t) (g t)| ≤ ‖f‖ * ‖g‖ := by
  let ν : Measure ℝ := volume.restrict (Set.uIoc a b)
  have hsub : Set.uIoc a b ⊆ Set.Icc (0 : ℝ) T :=
    Set.uIoc_subset_uIcc.trans (Set.uIcc_subset_Icc ha hb)
  have hν : ν ≤ timeMeasure T := by
    exact Measure.restrict_mono hsub le_rfl
  have hf : MemLp (fun t => f t) 2 ν :=
    (Lp.memLp f).mono_measure hν
  have hg : MemLp (fun t => g t) 2 ν :=
    (Lp.memLp g).mono_measure hν
  have hprod : Integrable (fun t => ‖f t‖ * ‖g t‖) ν := by
    change Integrable ((fun t => ‖f t‖) * fun t => ‖g t‖) ν
    exact hf.norm.integrable_mul hg.norm
  have hinner : Integrable (fun t => inner ℝ (f t) (g t)) ν := by
    refine hprod.mono' (hf.1.inner hg.1) ?_
    filter_upwards [] with t
    exact norm_inner_le_norm _ _
  have hholder :
      (∫ t, ‖f t‖ * ‖g t‖ ∂ν) ≤
        Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂ν) *
          Real.sqrt (∫ t, ‖g t‖ ^ 2 ∂ν) := by
    have hf' : MemLp (fun t => f t) (ENNReal.ofReal (2 : ℝ)) ν := by
      simpa using hf
    have hg' : MemLp (fun t => g t) (ENNReal.ofReal (2 : ℝ)) ν := by
      simpa using hg
    have h := integral_mul_norm_le_Lp_mul_Lq
      (μ := ν) Real.HolderConjugate.two_two hf' hg'
    simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h
  have hfint : Integrable (fun t => ‖f t‖ ^ 2) (timeMeasure T) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp
      (Lp.memLp f)
  have hgint : Integrable (fun t => ‖g t‖ ^ 2) (timeMeasure T) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp
      (Lp.memLp g)
  have hfmono : (∫ t, ‖f t‖ ^ 2 ∂ν) ≤
      ∫ t, ‖f t‖ ^ 2 ∂(timeMeasure T) :=
    integral_mono_measure hν (Eventually.of_forall fun t => sq_nonneg ‖f t‖) hfint
  have hgmono : (∫ t, ‖g t‖ ^ 2 ∂ν) ≤
      ∫ t, ‖g t‖ ^ 2 ∂(timeMeasure T) :=
    integral_mono_measure hν (Eventually.of_forall fun t => sq_nonneg ‖g t‖) hgint
  calc
    |∫ t in a..b, inner ℝ (f t) (g t)| =
        ‖∫ t, inner ℝ (f t) (g t) ∂ν‖ := by
      rw [intervalIntegral.abs_intervalIntegral_eq]
      rfl
    _ ≤ ∫ t, ‖inner ℝ (f t) (g t)‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖f t‖ * ‖g t‖ ∂ν := by
      exact integral_mono_ae hinner.norm hprod
        (Eventually.of_forall fun t => norm_inner_le_norm _ _)
    _ ≤ Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂ν) *
        Real.sqrt (∫ t, ‖g t‖ ^ 2 ∂ν) := hholder
    _ ≤ Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂(timeMeasure T)) *
        Real.sqrt (∫ t, ‖g t‖ ^ 2 ∂(timeMeasure T)) := by
      gcongr
    _ = ‖f‖ * ‖g‖ := by
      have hfnorm : (∫ t, ‖f t‖ ^ 2 ∂(timeMeasure T)) = ‖f‖ ^ 2 := by
        simpa only [timeMeasure] using (norm_sq_eq_integral f).symm
      have hgnorm : (∫ t, ‖g t‖ ^ 2 ∂(timeMeasure T)) = ‖g‖ ^ 2 := by
        simpa only [timeMeasure] using (norm_sq_eq_integral g).symm
      rw [hfnorm, hgnorm,
        Real.sqrt_sq (norm_nonneg f), Real.sqrt_sq (norm_nonneg g)]

end Hilbert

section ContinuousEmbedding

variable {f : ℝ → X}

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem memLp_of_continuousOn (hf : ContinuousOn f (Set.Icc (0 : ℝ) T)) :
    MemLp f 2 (timeMeasure T) := by
  have hmeas : AEStronglyMeasurable f (timeMeasure T) := by
    unfold timeMeasure
    exact hf.aestronglyMeasurable measurableSet_Icc
  rcases le_or_gt 0 T with hT | hT
  · obtain ⟨t₀, _, ht₀max⟩ :=
      isCompact_Icc.exists_isMaxOn (s := Set.Icc (0 : ℝ) T) ⟨0, ⟨le_refl 0, hT⟩⟩ hf.norm
    refine MemLp.of_bound hmeas ‖f t₀‖ ?_
    unfold timeMeasure
    exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun t ht => ht₀max ht)
  · refine ⟨hmeas, ?_⟩
    rw [timeMeasure_eq_zero_of_nonpos hT.le, eLpNorm_measure_zero]
    exact ENNReal.zero_lt_top

def ofContinuousOn (hf : ContinuousOn f (Set.Icc (0 : ℝ) T)) : timeL2 X T :=
  (memLp_of_continuousOn hf).toLp f

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem coeFn_ofContinuousOn (hf : ContinuousOn f (Set.Icc (0 : ℝ) T)) :
    ofContinuousOn hf =ᵐ[timeMeasure T] f :=
  (memLp_of_continuousOn hf).coeFn_toLp

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem norm_ofContinuousOn_le_of_bound (hf : ContinuousOn f (Set.Icc (0 : ℝ) T))
    {C : ℝ} (hC : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖f t‖ ≤ C) :
    ‖ofContinuousOn hf‖ ≤ Real.sqrt T * C := by
  have hbound : ∀ᵐ t ∂(timeMeasure T), ‖f t‖ ≤ C := by
    unfold timeMeasure
    exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hC)
  rw [ofContinuousOn, Lp.norm_toLp]
  have hle := eLpNorm_le_of_ae_bound (μ := timeMeasure T) (p := 2) hbound
  rcases le_or_gt 0 C with hC0 | hC0
  · refine le_trans (ENNReal.toReal_mono ?_ hle) ?_
    · exact ENNReal.mul_ne_top
        (by rw [timeMeasure_univ]
            exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by finiteness))
        ENNReal.ofReal_ne_top
    · rw [ENNReal.toReal_mul, timeMeasure_univ,
        show ((2 : ℝ≥0∞).toReal)⁻¹ = (1 / 2 : ℝ) by norm_num,
        toReal_ofReal_rpow_half, ENNReal.toReal_ofReal hC0]
  · have hfzero : ∀ᵐ t ∂(timeMeasure T), f t = 0 := by
      filter_upwards [hbound] with t ht
      have : ‖f t‖ = 0 := le_antisymm (le_trans ht hC0.le) (norm_nonneg _)
      exact norm_eq_zero.1 this
    rw [eLpNorm_congr_ae hfzero, eLpNorm_zero', ENNReal.toReal_zero]
    have : 0 ≤ Real.sqrt T * C ∨ Real.sqrt T = 0 := by
      rcases le_or_gt 0 T with hT | hT
      · exact Or.inr (by rcases eq_or_lt_of_le hT with h | h
                         · rw [← h, Real.sqrt_zero]
                         · exact absurd (le_trans (norm_nonneg (f 0))
                             (hC 0 ⟨le_refl 0, hT⟩)) (not_le.2 hC0))
      · exact Or.inr (Real.sqrt_eq_zero'.2 hT.le)
    rcases this with h | h
    · exact h
    · rw [h, zero_mul]

end ContinuousEmbedding


section HilbertDuality

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [CompleteSpace Y]

private theorem dualRepresentative_aestronglyMeasurable_of_hilbertBasis
    {ι : Type*} [Encodable ι] (b : HilbertBasis ι ℝ Y)
    (F : ℝ → Y →L[ℝ] ℝ)
    (hF : ∀ y, AEStronglyMeasurable (fun t => F t y) (timeMeasure T)) :
    AEStronglyMeasurable (fun t => (InnerProductSpace.toDual ℝ Y).symm (F t))
      (timeMeasure T) := by
  classical
  let z : ℝ → Y := fun t => (InnerProductSpace.toDual ℝ Y).symm (F t)
  let s : ℕ → Finset ι := fun m =>
    (Finset.range m).preimage Encodable.encode Encodable.encode_injective.injOn
  let p : ℕ → ℝ → Y := fun m t => ∑ i ∈ s m, F t (b i) • b i
  have hs : Tendsto s atTop atTop :=
    (tendsto_finset_preimage_atTop_atTop Encodable.encode_injective).comp
      tendsto_finset_range
  have hp_meas : ∀ m, AEStronglyMeasurable (p m) (timeMeasure T) := by
    intro m
    convert Finset.aestronglyMeasurable_sum (s m) (fun i _ =>
      (hF (b i)).smul_const (b i)) using 1
    funext t
    simp only [p, Finset.sum_apply]
  have hp_tendsto : ∀ t, Tendsto (fun m => p m t) atTop (𝓝 (z t)) := by
    intro t
    have hsum := (b.hasSum_repr (z t)).comp hs
    convert hsum using 1
    funext m
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [b.repr_apply_apply, real_inner_comm]
    symm
    exact InnerProductSpace.toDual_symm_apply (x := b i) (y := F t)
  exact aestronglyMeasurable_of_tendsto_ae atTop hp_meas
    (Eventually.of_forall hp_tendsto)

omit [CompleteSpace Y] in
private theorem hilbertBasisIndex_countable
    {ι : Type*} (b : HilbertBasis ι ℝ Y) [TopologicalSpace.SeparableSpace Y] :
    Countable ι := by
  let B : ι → Set Y := fun i => Metric.ball (b i) (1 / 2 : ℝ)
  have hdisj : Pairwise (fun i j => Disjoint (B i) (B j)) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hinner : inner ℝ (b i) (b j) = 0 :=
      b.orthonormal.inner_eq_zero hij
    have hsq : ‖b i - b j‖ ^ 2 = 2 := by
      rw [norm_sub_sq_real, hinner, b.orthonormal.norm_eq_one,
        b.orthonormal.norm_eq_one]
      norm_num
    have hnorm : 1 ≤ ‖b i - b j‖ := by
      have hnonneg := norm_nonneg (b i - b j)
      nlinarith
    norm_num [B, dist_eq_norm]
    exact hnorm
  exact hdisj.countable_of_isOpen_disjoint
    (fun i => Metric.isOpen_ball) (fun i => Metric.nonempty_ball.2 (by norm_num))

theorem dualRepresentative_aestronglyMeasurable_of_apply_aestronglyMeasurable
    [TopologicalSpace.SeparableSpace Y]
    (F : ℝ → Y →L[ℝ] ℝ)
    (hF : ∀ y, AEStronglyMeasurable (fun t => F t y) (timeMeasure T)) :
    AEStronglyMeasurable (fun t => (InnerProductSpace.toDual ℝ Y).symm (F t))
      (timeMeasure T) := by
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis ℝ Y
  let _ : Countable ι := hilbertBasisIndex_countable b
  let _ : Encodable ι := Encodable.ofCountable ι
  exact dualRepresentative_aestronglyMeasurable_of_hilbertBasis b F hF

theorem dualRepresentative_aestronglyMeasurable_of_apply_continuousOn
    [TopologicalSpace.SeparableSpace Y]
    (F : ℝ → Y →L[ℝ] ℝ)
    (hF : ∀ y, ContinuousOn (fun t => F t y) (Set.Icc (0 : ℝ) T)) :
    AEStronglyMeasurable (fun t => (InnerProductSpace.toDual ℝ Y).symm (F t))
      (timeMeasure T) := by
  apply dualRepresentative_aestronglyMeasurable_of_apply_aestronglyMeasurable F
  intro y
  unfold timeMeasure
  exact (hF y).aestronglyMeasurable measurableSet_Icc

theorem dualRepresentative_memLp_of_apply_aestronglyMeasurable_of_bound
    [TopologicalSpace.SeparableSpace Y]
    (F : ℝ → Y →L[ℝ] ℝ)
    (hF : ∀ y, AEStronglyMeasurable (fun t => F t y) (timeMeasure T))
    {C : ℝ} (hC : ∀ᵐ t ∂(timeMeasure T), ‖F t‖ ≤ C) :
    MemLp (fun t => (InnerProductSpace.toDual ℝ Y).symm (F t)) 2
      (timeMeasure T) := by
  refine MemLp.of_bound
    (dualRepresentative_aestronglyMeasurable_of_apply_aestronglyMeasurable F hF) C ?_
  filter_upwards [hC] with t ht
  simpa using ht

theorem dualRepresentative_memLp_of_apply_continuousOn_of_bound
    [TopologicalSpace.SeparableSpace Y]
    (F : ℝ → Y →L[ℝ] ℝ)
    (hF : ∀ y, ContinuousOn (fun t => F t y) (Set.Icc (0 : ℝ) T))
    {C : ℝ} (hC : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖F t‖ ≤ C) :
    MemLp (fun t => (InnerProductSpace.toDual ℝ Y).symm (F t)) 2
      (timeMeasure T) := by
  apply dualRepresentative_memLp_of_apply_aestronglyMeasurable_of_bound F
  · intro y
    unfold timeMeasure
    exact (hF y).aestronglyMeasurable measurableSet_Icc
  · unfold timeMeasure
    refine (ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall fun t ht => ?_)
    exact hC t ht

theorem bilinear_left_representative_memLp
    {X : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [TopologicalSpace.SeparableSpace Y]
    (u : timeL2 X T)
    (B : ℝ → X →L[ℝ] Y →L[ℝ] ℝ)
    (hB : ∀ x y, AEStronglyMeasurable (fun t => B t x y) (timeMeasure T))
    {C : ℝ} (hC : ∀ᵐ t ∂(timeMeasure T), ‖B t‖ ≤ C) :
    MemLp (fun t => (InnerProductSpace.toDual ℝ Y).symm (B t (u t))) 2
      (timeMeasure T) := by
  let A : ℝ → X →L[ℝ] Y := fun t =>
    (InnerProductSpace.toDual ℝ Y).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (B t)
  have hA : ∀ x, AEStronglyMeasurable (fun t => A t x) (timeMeasure T) := by
    intro x
    exact dualRepresentative_aestronglyMeasurable_of_apply_aestronglyMeasurable
      (fun t => B t x) (hB x)
  have hmeas : AEStronglyMeasurable (fun t => A t (u t)) (timeMeasure T) :=
    AEStronglyMeasurable.clm_apply_of_apply_aestronglyMeasurable
      A hA u (Lp.aestronglyMeasurable u)
  refine MemLp.of_le_mul (c := max 0 C) (Lp.memLp u) ?_ ?_
  · refine hmeas.congr (Eventually.of_forall fun t => ?_)
    rfl
  · filter_upwards [hC] with t ht
    change ‖(InnerProductSpace.toDual ℝ Y).symm (B t (u t))‖ ≤
      max 0 C * ‖u t‖
    calc
      ‖(InnerProductSpace.toDual ℝ Y).symm (B t (u t))‖ = ‖B t (u t)‖ := by
        exact (InnerProductSpace.toDual ℝ Y).symm.norm_map _
      _ ≤ ‖B t‖ * ‖u t‖ := (B t).le_opNorm (u t)
      _ ≤ max 0 C * ‖u t‖ := by
        gcongr
        exact ht.trans (le_max_right 0 C)

theorem inner_ofContinuousOn_dualRepresentative
    (F : ℝ → Y →L[ℝ] ℝ) (hF : ContinuousOn F (Set.Icc (0 : ℝ) T))
    (u : timeL2 Y T) :
    inner ℝ u (ofContinuousOn
      (((InnerProductSpace.toDual ℝ Y).symm.continuous.comp_continuousOn hF))) =
      ∫ t in Set.Icc (0 : ℝ) T, F t (u t) := by
  rw [inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_ofContinuousOn
    (((InnerProductSpace.toDual ℝ Y).symm.continuous.comp_continuousOn hF))] with t ht
  rw [ht, real_inner_comm]
  exact InnerProductSpace.toDual_symm_apply

theorem tendsto_integral_apply_of_weakly_tendsto
    {U : ℕ → timeL2 Y T} {u : timeL2 Y T}
    (hU : ∀ z, Tendsto (fun m => inner ℝ (U m) z) atTop
      (𝓝 (inner ℝ u z)))
    (F : ℝ → Y →L[ℝ] ℝ) (hF : ContinuousOn F (Set.Icc (0 : ℝ) T)) :
    Tendsto (fun m => ∫ t in Set.Icc (0 : ℝ) T, F t (U m t)) atTop
      (𝓝 (∫ t in Set.Icc (0 : ℝ) T, F t (u t))) := by
  let z : timeL2 Y T := ofContinuousOn
    (((InnerProductSpace.toDual ℝ Y).symm.continuous.comp_continuousOn hF))
  simpa only [z, inner_ofContinuousOn_dualRepresentative F hF] using hU z

theorem tendsto_integral_apply_of_weakly_tendsto_of_apply_aestronglyMeasurable
    [TopologicalSpace.SeparableSpace Y]
    {U : ℕ → timeL2 Y T} {u : timeL2 Y T}
    (hU : ∀ z, Tendsto (fun m => inner ℝ (U m) z) atTop
      (𝓝 (inner ℝ u z)))
    (F : ℝ → Y →L[ℝ] ℝ)
    (hF : ∀ y, AEStronglyMeasurable (fun t => F t y) (timeMeasure T))
    {C : ℝ} (hC : ∀ᵐ t ∂(timeMeasure T), ‖F t‖ ≤ C) :
    Tendsto (fun m => ∫ t in Set.Icc (0 : ℝ) T, F t (U m t)) atTop
      (𝓝 (∫ t in Set.Icc (0 : ℝ) T, F t (u t))) := by
  let hz := dualRepresentative_memLp_of_apply_aestronglyMeasurable_of_bound F hF hC
  let z : timeL2 Y T := hz.toLp
    (fun t => (InnerProductSpace.toDual ℝ Y).symm (F t))
  have hinner : ∀ v : timeL2 Y T,
      inner ℝ v z = ∫ t in Set.Icc (0 : ℝ) T, F t (v t) := by
    intro v
    rw [inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hz.coeFn_toLp] with t ht
    rw [show z t = (InnerProductSpace.toDual ℝ Y).symm (F t) from ht,
      real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  simpa only [hinner] using hU z

theorem integrable_weighted_bilinear_of_apply_aestronglyMeasurable
    [TopologicalSpace.SeparableSpace Y]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (u : timeL2 Y T)
    (B : ℝ → Y →L[ℝ] Z →L[ℝ] ℝ)
    (hB : ∀ y z, AEStronglyMeasurable (fun t ↦ B t y z) (timeMeasure T))
    {C : ℝ} (hC : ∀ᵐ t ∂(timeMeasure T), ‖B t‖ ≤ C)
    (c : ℝ → ℝ) (hc : AEStronglyMeasurable c (timeMeasure T))
    {K : ℝ} (hK : ∀ᵐ t ∂(timeMeasure T), ‖c t‖ ≤ K)
    (z : Z) :
    Integrable (fun t ↦ c t * B t (u t) z) (timeMeasure T) := by
  let F : ℝ → Y →L[ℝ] ℝ := fun t ↦ c t • (B t).flip z
  have hF : ∀ y, AEStronglyMeasurable (fun t ↦ F t y) (timeMeasure T) := by
    intro y
    refine (hc.mul (hB y z)).congr (Eventually.of_forall fun t ↦ ?_)
    change c t * B t y z = (c t • (B t).flip z) y
    simp only [smul_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
  have hFbound : ∀ᵐ t ∂(timeMeasure T),
      ‖F t‖ ≤ max 0 K * (max 0 C * ‖z‖) := by
    filter_upwards [hC, hK] with t hBt hct
    calc
      ‖F t‖ ≤ ‖c t‖ * (‖B t‖ * ‖z‖) := by
        dsimp only [F]
        rw [norm_smul]
        gcongr
        simpa only [ContinuousLinearMap.opNorm_flip] using (B t).flip.le_opNorm z
      _ ≤ max 0 K * (max 0 C * ‖z‖) := by
        gcongr
        · exact hct.trans (le_max_right 0 K)
        · exact hBt.trans (le_max_right 0 C)
  let hv := dualRepresentative_memLp_of_apply_aestronglyMeasurable_of_bound
    F hF hFbound
  let v : timeL2 Y T := hv.toLp
    (fun t ↦ (InnerProductSpace.toDual ℝ Y).symm (F t))
  refine (MeasureTheory.L2.integrable_inner u v).congr ?_
  filter_upwards [hv.coeFn_toLp] with t ht
  rw [show v t = (InnerProductSpace.toDual ℝ Y).symm (F t) from ht]
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  simp only [F, smul_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]

theorem tendsto_integral_weighted_bilinear_of_weakly_tendsto_of_apply_aestronglyMeasurable
    [TopologicalSpace.SeparableSpace Y]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {U : ℕ → timeL2 Y T} {u : timeL2 Y T}
    (hU : ∀ z, Tendsto (fun m ↦ inner ℝ (U m) z) atTop
      (𝓝 (inner ℝ u z)))
    (B : ℝ → Y →L[ℝ] Z →L[ℝ] ℝ)
    (hB : ∀ y z, AEStronglyMeasurable (fun t ↦ B t y z) (timeMeasure T))
    {C : ℝ} (hC : ∀ᵐ t ∂(timeMeasure T), ‖B t‖ ≤ C)
    (c : ℝ → ℝ) (hc : AEStronglyMeasurable c (timeMeasure T))
    {K : ℝ} (hK : ∀ᵐ t ∂(timeMeasure T), ‖c t‖ ≤ K)
    (z : Z) :
    Tendsto (fun m ↦ ∫ t in Set.Icc (0 : ℝ) T, c t * B t (U m t) z) atTop
      (𝓝 (∫ t in Set.Icc (0 : ℝ) T, c t * B t (u t) z)) := by
  let F : ℝ → Y →L[ℝ] ℝ := fun t ↦ c t • (B t).flip z
  apply tendsto_integral_apply_of_weakly_tendsto_of_apply_aestronglyMeasurable hU F
  · intro y
    refine (hc.mul (hB y z)).congr (Eventually.of_forall fun t ↦ ?_)
    change c t * B t y z = (c t • (B t).flip z) y
    simp only [smul_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]
  · filter_upwards [hC, hK] with t hBt hct
    calc
      ‖F t‖ ≤ ‖c t‖ * (‖B t‖ * ‖z‖) := by
        dsimp only [F]
        rw [norm_smul]
        gcongr
        simpa only [ContinuousLinearMap.opNorm_flip] using (B t).flip.le_opNorm z
      _ ≤ max 0 K * (max 0 C * ‖z‖) := by
        gcongr
        · exact hct.trans (le_max_right 0 K)
        · exact hBt.trans (le_max_right 0 C)

theorem tendsto_integral_apply_of_weakly_tendsto_of_apply_continuousOn
    [TopologicalSpace.SeparableSpace Y]
    {U : ℕ → timeL2 Y T} {u : timeL2 Y T}
    (hU : ∀ z, Tendsto (fun m => inner ℝ (U m) z) atTop
      (nhds (inner ℝ u z)))
    (F : ℝ → Y →L[ℝ] ℝ)
    (hF : ∀ y, ContinuousOn (fun t => F t y) (Set.Icc (0 : ℝ) T))
    {C : ℝ} (hC : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖F t‖ ≤ C) :
    Tendsto (fun m => ∫ t in Set.Icc (0 : ℝ) T, F t (U m t)) atTop
      (nhds (∫ t in Set.Icc (0 : ℝ) T, F t (u t))) := by
  apply tendsto_integral_apply_of_weakly_tendsto_of_apply_aestronglyMeasurable hU F
  · intro y
    unfold timeMeasure
    exact (hF y).aestronglyMeasurable measurableSet_Icc
  · unfold timeMeasure
    exact (ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall fun t ht => hC t ht)

end HilbertDuality

section Const

def const (T : ℝ) (c : X) : timeL2 X T :=
  (memLp_const (μ := timeMeasure T) c).toLp _

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem coeFn_const (c : X) :
    const T c =ᵐ[timeMeasure T] (fun _ => c) :=
  (memLp_const (μ := timeMeasure T) c).coeFn_toLp

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem norm_const (T : ℝ) (c : X) :
    ‖const T c‖ = Real.sqrt T * ‖c‖ := by
  rw [const, Lp.norm_toLp]
  rcases le_or_gt 0 T with hT | hT
  · rcases eq_or_lt_of_le hT with hT0 | hTpos
    · rw [timeMeasure_eq_zero_of_nonpos (le_of_eq hT0.symm), eLpNorm_measure_zero,
        ENNReal.toReal_zero, ← hT0, Real.sqrt_zero, zero_mul]
    · rw [eLpNorm_const c (by norm_num) (timeMeasure_ne_zero hTpos), ENNReal.toReal_mul,
        show (1 / ENNReal.toReal 2) = (1 / 2 : ℝ) by norm_num, timeMeasure_univ,
        toReal_ofReal_rpow_half, toReal_enorm, mul_comm]
  · rw [timeMeasure_eq_zero_of_nonpos hT.le, eLpNorm_measure_zero, ENNReal.toReal_zero,
      Real.sqrt_eq_zero'.2 hT.le, zero_mul]

omit [NormedSpace ℝ X] [CompleteSpace X] in
@[simp]
theorem const_zero (T : ℝ) : const T (0 : X) = 0 := by
  rw [← norm_eq_zero, norm_const, norm_zero, mul_zero]

end Const

section IntervalIntegral

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem integrable (f : timeL2 X T) :
    Integrable (fun t => f t) (timeMeasure T) :=
  (Lp.memLp f).integrable (by norm_num)

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem integrableOn (f : timeL2 X T) :
    IntegrableOn (fun t => f t) (Set.Icc (0 : ℝ) T) :=
  integrable f

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem integral_norm_le (f : timeL2 X T) :
    ∫ t in Set.Icc (0 : ℝ) T, ‖f t‖ ≤ Real.sqrt T * ‖f‖ := by
  have hf1 : MemLp (fun t => f t) 1 (timeMeasure T) :=
    (Lp.memLp f).mono_exponent (by norm_num)
  have hint : ∫ t in Set.Icc (0 : ℝ) T, ‖f t‖
      = (eLpNorm (fun t => f t) 1 (timeMeasure T)).toReal := by
    rw [show (∫ t in Set.Icc (0 : ℝ) T, ‖f t‖) = ∫ t, ‖f t‖ ∂(timeMeasure T) from rfl,
      integral_norm_eq_lintegral_enorm hf1.1, eLpNorm_one_eq_lintegral_enorm]
  rw [hint, Lp.norm_def]
  have hholder := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := timeMeasure T) (p := 1) (q := 2) (by norm_num) (Lp.aestronglyMeasurable f)
  have hfin : eLpNorm (fun t => f t) 2 (timeMeasure T)
      * timeMeasure T Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ∞ := by
    refine ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) ?_
    rw [timeMeasure_univ]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by finiteness)
  refine le_trans (ENNReal.toReal_mono hfin hholder) ?_
  rw [ENNReal.toReal_mul, timeMeasure_univ,
    show (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) by norm_num,
    toReal_ofReal_rpow_half, mul_comm]

def timeIntegralₗ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (T : ℝ) : timeL2 X T →ₗ[ℝ] X where
  toFun f := ∫ t in Set.Icc (0 : ℝ) T, f t
  map_add' f g := by
    rw [← integral_add (integrableOn f) (integrableOn g)]
    refine integral_congr_ae ?_
    filter_upwards [(Lp.coeFn_add f g)] with t ht
    simp only [ht, Pi.add_apply]
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [(Lp.coeFn_smul c f)] with t ht
    simp only [ht, Pi.smul_apply]

def timeIntegral (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (T : ℝ) : timeL2 X T →L[ℝ] X :=
  LinearMap.mkContinuous (timeIntegralₗ X T) (Real.sqrt T) (fun f => by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    exact integral_norm_le f)

omit [CompleteSpace X] in
@[simp] theorem timeIntegral_apply (f : timeL2 X T) :
    timeIntegral X T f = ∫ t in Set.Icc (0 : ℝ) T, f t :=
  rfl

omit [CompleteSpace X] in
theorem norm_timeIntegral_le (f : timeL2 X T) :
    ‖∫ t in Set.Icc (0 : ℝ) T, f t‖ ≤ Real.sqrt T * ‖f‖ := by
  rw [← timeIntegral_apply]
  refine le_trans ((timeIntegral X T).le_opNorm f) ?_
  exact mul_le_mul_of_nonneg_right
    (LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg T) _) (norm_nonneg _)

theorem norm_timeIntegral_clm_le (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℝ X] (T : ℝ) :
    ‖timeIntegral X T‖ ≤ Real.sqrt T :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg T) _

theorem timeIntegral_const {T : ℝ} (hT : 0 ≤ T) (c : X) :
    timeIntegral X T (const T c) = T • c := by
  rw [timeIntegral_apply,
    integral_congr_ae (g := fun _ => c)
      (by filter_upwards [coeFn_const (T := T) c] with t ht using ht),
    setIntegral_const, measureReal_def, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hT]

end IntervalIntegral

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem integrable_bilinear_clm_apply_right
    {T : ℝ} (F : ℝ → X →L[ℝ] X →L[ℝ] ℝ)
    (hF : ∀ x y, AEStronglyMeasurable (fun t => F t x y) (timeMeasure T))
    {C : ℝ} (hC : ∀ᵐ t ∂timeMeasure T, ‖F t‖ ≤ C)
    (S : ℝ → X →L[ℝ] X) (hS : ContinuousOn S (Icc (0 : ℝ) T))
    (L : X →L[ℝ] X) (u v : timeL2 X T) :
    Integrable (fun t => F t (u t) (S t (L (v t)))) (timeMeasure T) := by
  let A : ℝ → X →L[ℝ] X →L[ℝ] ℝ := fun t =>
    (F t).bilinearComp (ContinuousLinearMap.id ℝ X) ((S t).comp L)
  have hA : ∀ x y, AEStronglyMeasurable (fun t => A t x y) (timeMeasure T) := by
    intro x y
    apply AEStronglyMeasurable.clm_apply_of_apply_aestronglyMeasurable
      (fun t => F t x) (hF x) (fun t => S t (L y))
    exact (memLp_of_continuousOn (hS.clm_apply continuousOn_const)).aestronglyMeasurable
  obtain ⟨CS, hCS⟩ := isCompact_Icc.exists_bound_of_continuousOn hS
  have hb : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ max C 0 * (max CS 0 * ‖L‖) := by
    filter_upwards [hC, ae_restrict_mem measurableSet_Icc] with t hFt ht
    dsimp only [A]
    rw [ContinuousLinearMap.bilinearComp, ContinuousLinearMap.comp_id, ContinuousLinearMap.opNorm_flip]
    calc
      _ ≤ ‖(F t).flip‖ * ‖(S t).comp L‖ := ((F t).flip).opNorm_comp_le _
      _ = ‖F t‖ * ‖(S t).comp L‖ := by rw [ContinuousLinearMap.opNorm_flip]
      _ ≤ max C 0 * (max CS 0 * ‖L‖) := by
        apply mul_le_mul (hFt.trans (le_max_left _ _)) _ (norm_nonneg _) (le_max_right _ _)
        exact ((S t).opNorm_comp_le L).trans
          (mul_le_mul_of_nonneg_right ((hCS t ht).trans (le_max_left _ _)) (norm_nonneg _))
  exact MeasureTheory.integrable_bilinear_of_apply_aestronglyMeasurable A hA hb (Lp.memLp u) (Lp.memLp v)

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
