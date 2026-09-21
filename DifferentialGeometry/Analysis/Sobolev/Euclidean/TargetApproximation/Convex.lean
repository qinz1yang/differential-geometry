import DifferentialGeometry.Analysis.Integration.Convolution.ConvexRange
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Mollification
import DifferentialGeometry.Analysis.Integration.Integral.QuadraticDerivative
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import DifferentialGeometry.Analysis.Integration.PlaneScaling

section

noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap Metric
open scoped ContDiff Topology ENNReal NNReal Convolution

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_smooth_lipschitz_convex_approximation_tendsto_energy_on_closedBall
    {K : Set F} (hK : IsCompact K) (hKconv : Convex ℝ K) (h0 : (0 : F) ∈ K)
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K)
    {c : E} {a : ℝ} (hball : closedBall c a ⊆ Ω) :
    ∃ (v : ℕ → E → F) (L : ℕ → ℝ≥0),
      (∀ n, ContDiff ℝ ∞ (v n)) ∧
      (∀ n, HasCompactSupport (v n)) ∧
      (∀ n, LipschitzWith (L n) (v n)) ∧
      (∀ n x, v n x ∈ K) ∧
      Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2
        (volume.restrict (closedBall c a))) atTop (𝓝 0) ∧
      (∀ j : Fin d, Tendsto (fun n => eLpNorm (fun x =>
        fderiv ℝ (v n) x (EuclideanSpace.single j 1) -
          WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        2 (volume.restrict (closedBall c a))) atTop (𝓝 0)) ∧
      (∀ᵐ x ∂volume.restrict (closedBall c a),
        Tendsto (fun n => v n x) atTop (𝓝 (f x))) ∧
      ∀ (A : F → F →L[ℝ] F →L[ℝ] ℝ), ContinuousOn A K →
        Tendsto (fun n => ∑ j : Fin d, ∫ x in closedBall c a,
          A (v n x) (fderiv ℝ (v n) x (EuclideanSpace.single j 1))
            (fderiv ℝ (v n) x (EuclideanSpace.single j 1))) atTop
          (𝓝 (∑ j : Fin d, ∫ x in closedBall c a,
            A (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
              (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)))) := by
  classical
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let φ (n : ℕ) := mollifierBumpEps (d := d) (hε n)
  let U (n : ℕ) := (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] (Ω.indicator f)
  have hfm : MemLp f 2 (volume.restrict Ω) := MemLp.of_eval_piLp fun i => (hf i).memLp
  have hglobal : LocallyIntegrable (Ω.indicator f) volume :=
    ((memLp_indicator_iff_restrict hΩ.measurableSet).mpr hfm).locallyIntegrable (by norm_num)
  have hUsmooth (n : ℕ) : ContDiff ℝ ∞ (U n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (φ n).contDiff_normed hglobal
  have hUK (n : ℕ) (x : E) : U n x ∈ K :=
    (φ n).normed_convolution_indicator_mem_of_ae_mem_closed_convex
      hΩ.measurableSet hglobal hKconv hK.isClosed h0 hfK x
  let ψ : ContDiffBump c := ⟨max a 0 + 1, max a 0 + 2, by positivity, by linarith⟩
  let w : ℕ → E → F := fun n x => ψ x • U n x
  have hwsmooth (n : ℕ) : ContDiff ℝ ∞ (w n) := ψ.contDiff.smul (hUsmooth n)
  have hwcompact (n : ℕ) : HasCompactSupport (w n) := ψ.hasCompactSupport.smul_right
  have hwLip (n : ℕ) : ∃ L : ℝ≥0, LipschitzWith L (w n) :=
    ContDiff.lipschitzWith_of_hasCompactSupport (hwcompact n) (hwsmooth n) (by simp)
  choose L hL using hwLip
  have hwK (n : ℕ) (x : E) : w n x ∈ K :=
    hKconv.smul_mem_of_zero_mem h0 (hUK n x) ⟨ψ.nonneg, ψ.le_one⟩
  have hgerm (n : ℕ) {x : E} (hx : x ∈ closedBall c a) : w n =ᶠ[𝓝 x] U n := by
    have hxin : x ∈ ball c ψ.rIn := by
      have hd := mem_closedBall.mp hx
      change dist x c < max a 0 + 1
      linarith [le_max_left a 0]
    filter_upwards [ψ.eventuallyEq_one_of_mem_ball hxin] with y hy
    simp only [w, hy, Pi.one_apply, one_smul]
  let μ : Measure E := volume.restrict (closedBall c a)
  have hwae (n : ℕ) : w n =ᵐ[μ] U n := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    exact (hgerm n hx).eq_of_nhds
  have hdwae (n : ℕ) : fderiv ℝ (w n) =ᵐ[μ] fderiv ℝ (U n) := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    exact (hgerm n hx).fderiv_eq
  have hvalU : Tendsto (fun n => eLpNorm (fun x => U n x - f x) 2 μ) atTop (𝓝 0) :=
    tendsto_eLpNorm_normed_convolution_indicator_sub hΩ.measurableSet hball hfm hε hε0
  have hval : Tendsto (fun n => eLpNorm (fun x => w n x - f x) 2 μ) atTop (𝓝 0) := by
    convert hvalU using 1
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [hwae n] with x hx
    rw [hx]
  have hder (j : Fin d) : Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (w n) x (EuclideanSpace.single j 1) -
        WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) 2 μ) atTop (𝓝 0) := by
    have h := tendsto_eLpNorm_partial_normed_convolution_indicator_sub_weakGrad
      hΩ (isCompact_closedBall c a) hball hf hε hε0 j
    convert h using 1
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [hdwae n] with x hx
    rw [hx]
  have hwmem (n : ℕ) : MemLp (w n) 2 μ :=
    (hwsmooth n).continuous.continuousOn.memLp_restrict_compact (isCompact_closedBall c a) 2
  have hfmem : MemLp f 2 μ := hfm.mono_measure (Measure.restrict_mono_set volume hball)
  obtain ⟨σ, hσ, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (fun n => (hwmem n).aestronglyMeasurable)
      hfmem.aestronglyMeasurable hval).exists_seq_tendsto_ae
  have hG (j : Fin d) : MemLp (fun x => WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) 2 μ :=
    MemLp.of_eval_piLp fun i => ((hf i).weakGrad_component_memLp j).mono_measure
      (Measure.restrict_mono_set volume hball)
  have hpartial (n : ℕ) (j : Fin d) : MemLp
      (fun x => fderiv ℝ (w n) x (EuclideanSpace.single j 1)) 2 μ := by
    have hc : Continuous (fun x => fderiv ℝ (w n) x (EuclideanSpace.single j 1)) :=
      ((hwsmooth n).continuous_fderiv (by simp)).clm_apply continuous_const
    exact hc.continuousOn.memLp_restrict_compact (isCompact_closedBall c a) 2
  refine ⟨w ∘ σ, L ∘ σ, fun n => hwsmooth (σ n), fun n => hwcompact (σ n),
    fun n => hL (σ n), fun n => hwK (σ n), hval.comp hσ.tendsto_atTop,
    fun j => (hder j).comp hσ.tendsto_atTop, hpoint, ?_⟩
  intro A hA
  exact tendsto_integral_target_metric_energy_of_strong_approximation
    measurableSet_closedBall Subset.rfl hK A hA f (w ∘ σ)
    (fun n => (hwsmooth (σ n)).contDiffOn.of_le (by simp))
    (fun n x _ => hwK (σ n) x)
    (ae_mono (Measure.restrict_mono_set volume hball) hfK) hpoint
    (fun j x => WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) hG
    (fun n j => hpartial (σ n) j) (fun j => (hder j).comp hσ.tendsto_atTop)

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end

section

noncomputable section

open Set Filter MeasureTheory Metric
open scoped ContDiff Topology ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

private theorem norm_plane_map_sq_le_columns
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] F) :
    ‖A‖ ^ 2 ≤ 2 * (‖A (EuclideanSpace.single 0 1)‖ ^ 2 +
      ‖A (EuclideanSpace.single 1 1)‖ ^ 2) := by
  have hA : ‖A‖ ≤ ‖A (EuclideanSpace.single 0 1)‖ +
      ‖A (EuclideanSpace.single 1 1)‖ := by
    apply A.opNorm_le_bound (add_nonneg (norm_nonneg _) (norm_nonneg _))
    intro x
    have hx : x = x 0 • EuclideanSpace.single 0 (1 : ℝ) +
        x 1 • EuclideanSpace.single 1 (1 : ℝ) := by
      ext i
      fin_cases i <;> simp
    have h0 : |x 0| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
    have h1 : |x 1| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 1
    calc
      ‖A x‖ = ‖x 0 • A (EuclideanSpace.single 0 1) +
          x 1 • A (EuclideanSpace.single 1 1)‖ := by
        apply congrArg norm
        simpa only [map_add, map_smul] using congrArg A hx
      _ ≤ |x 0| * ‖A (EuclideanSpace.single 0 1)‖ +
          |x 1| * ‖A (EuclideanSpace.single 1 1)‖ := by
        simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
          (x 0 • A (EuclideanSpace.single 0 1)) (x 1 • A (EuclideanSpace.single 1 1))
      _ ≤ (‖A (EuclideanSpace.single 0 1)‖ +
          ‖A (EuclideanSpace.single 1 1)‖) * ‖x‖ := by
        nlinarith [mul_le_mul_of_nonneg_right h0 (norm_nonneg (A (EuclideanSpace.single 0 1))),
          mul_le_mul_of_nonneg_right h1 (norm_nonneg (A (EuclideanSpace.single 1 1)))]
  have hAsq := (sq_le_sq₀ (norm_nonneg A)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hA
  nlinarith [hAsq,
    sq_nonneg (‖A (EuclideanSpace.single 0 1)‖ - ‖A (EuclideanSpace.single 1 1)‖)]

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_smooth_lipschitz_convex_approximation_tendsto_energy_on_subsets
    {K : Set F} (hK : IsCompact K) (hKconv : Convex ℝ K) (h0 : (0 : F) ∈ K)
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K)
    {c : E} {a : ℝ} (hball : closedBall c a ⊆ Ω) :
    ∃ (v : ℕ → E → F) (L : ℕ → ℝ≥0) (D : ℝ), 0 ≤ D ∧
      (∀ n, ContDiff ℝ ∞ (v n)) ∧ (∀ n, HasCompactSupport (v n)) ∧
      (∀ n, LipschitzWith (L n) (v n)) ∧ (∀ n x, v n x ∈ K) ∧
      (∀ n, (∑ j : Fin 2, ∫ x in closedBall c a,
        ‖fderiv ℝ (v n) x (EuclideanSpace.single j 1)‖ ^ 2) ≤ D) ∧
      (∀ n, (∫ x in closedBall c a, ‖fderiv ℝ (v n) x‖ ^ 2) ≤ 2 * D) ∧
      ∀ S : Set E, MeasurableSet S → S ⊆ closedBall c a →
        Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 (volume.restrict S))
          atTop (𝓝 0) ∧
        (∀ j : Fin 2, Tendsto (fun n => eLpNorm (fun x =>
          fderiv ℝ (v n) x (EuclideanSpace.single j 1) -
            WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) 2 (volume.restrict S)) atTop (𝓝 0)) ∧
        (∀ᵐ x ∂volume.restrict S, Tendsto (fun n => v n x) atTop (𝓝 (f x))) ∧
        ∀ (A : F → F →L[ℝ] F →L[ℝ] ℝ), ContinuousOn A K →
          Tendsto (fun n => ∑ j : Fin 2, ∫ x in S,
            A (v n x) (fderiv ℝ (v n) x (EuclideanSpace.single j 1))
              (fderiv ℝ (v n) x (EuclideanSpace.single j 1))) atTop
            (𝓝 (∑ j : Fin 2, ∫ x in S,
              A (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
                (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)))) := by
  obtain ⟨v, L, hv, hvc, hLip, hvK, hval, hder, hae, henergy⟩ :=
    exists_smooth_lipschitz_convex_approximation_tendsto_energy_on_closedBall
      hK hKconv h0 hΩ hf hfK hball
  let μ : Measure E := volume.restrict (closedBall c a)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (isCompact_closedBall c a).measure_ne_top
  have hpartial (n : ℕ) (j : Fin 2) : MemLp
      (fun x => fderiv ℝ (v n) x (EuclideanSpace.single j 1)) 2 μ := by
    have hc : Continuous (fun x => fderiv ℝ (v n) x (EuclideanSpace.single j 1)) :=
      ((hv n).continuous_fderiv (by simp)).clm_apply continuous_const
    exact hc.continuousOn.memLp_restrict_compact (isCompact_closedBall c a) 2
  have hnormeq (y : F) : (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) y y = ‖y‖ ^ 2 :=
    real_inner_self_eq_norm_sq y
  have hcols := henergy (fun _ => (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)) continuousOn_const
  simp only [hnormeq] at hcols
  obtain ⟨B, hB⟩ := hcols.bddAbove_range
  let D : ℝ := max B 0
  have hD : 0 ≤ D := le_max_right _ _
  have hcolbound (n : ℕ) : (∑ j : Fin 2, ∫ x in closedBall c a,
      ‖fderiv ℝ (v n) x (EuclideanSpace.single j 1)‖ ^ 2) ≤ D :=
    (hB (mem_range_self n)).trans (le_max_left _ _)
  have hnormbound (n : ℕ) : (∫ x in closedBall c a, ‖fderiv ℝ (v n) x‖ ^ 2) ≤ 2 * D := by
    have hdLp : MemLp (fun x => ‖fderiv ℝ (v n) x‖) 2 μ := by
      apply MemLp.of_bound (measurable_fderiv ℝ (v n)).norm.aestronglyMeasurable (L n)
      exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact norm_fderiv_le_of_lipschitz ℝ (hLip n)
    have hj0 := (hpartial n 0).norm.integrable_sq
    have hj1 := (hpartial n 1).norm.integrable_sq
    calc
      _ ≤ ∫ x, 2 * (‖fderiv ℝ (v n) x (EuclideanSpace.single 0 1)‖ ^ 2 +
          ‖fderiv ℝ (v n) x (EuclideanSpace.single 1 1)‖ ^ 2) ∂μ :=
        integral_mono hdLp.integrable_sq ((hj0.add hj1).const_mul 2)
          (fun x => norm_plane_map_sq_le_columns _)
      _ = 2 * (∑ j : Fin 2, ∫ x in closedBall c a,
          ‖fderiv ℝ (v n) x (EuclideanSpace.single j 1)‖ ^ 2) := by
        rw [integral_const_mul, integral_add hj0 hj1, Fin.sum_univ_two]
      _ ≤ 2 * D := mul_le_mul_of_nonneg_left (hcolbound n) (by norm_num)
  refine ⟨v, L, D, hD, hv, hvc, hLip, hvK, hcolbound, hnormbound, ?_⟩
  intro S hS hSsub
  have hvalS : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 (volume.restrict S))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hval (fun _ => zero_le)
      (fun _ => eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hSsub))
  have hderS (j : Fin 2) : Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (v n) x (EuclideanSpace.single j 1) -
        WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) 2 (volume.restrict S)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hder j) (fun _ => zero_le)
      (fun _ => eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hSsub))
  have haeS := ae_restrict_of_ae_restrict_of_subset hSsub hae
  refine ⟨hvalS, hderS, haeS, ?_⟩
  intro A hA
  have hG (j : Fin 2) : MemLp (fun x => WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
      2 (volume.restrict S) :=
    MemLp.of_eval_piLp fun i => ((hf i).weakGrad_component_memLp j).mono_measure
      (Measure.restrict_mono_set volume (hSsub.trans hball))
  exact tendsto_integral_target_metric_energy_of_strong_approximation
    hS hSsub hK A hA f v (fun n => (hv n).contDiffOn.of_le (by simp))
    (fun n x _ => hvK n x)
    (ae_mono (Measure.restrict_mono_set volume (hSsub.trans hball)) hfK) haeS
    (fun j x => WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) hG
    (fun n j => (hpartial n j).mono_measure (Measure.restrict_mono_set volume hSsub)) hderS

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end

section

noncomputable section

open Set Filter MeasureTheory Metric
open scoped ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_smooth_lipschitz_complex_convex_approximation_tendsto_energy
    {K : Set F} (hK : IsCompact K) (hKconv : Convex ℝ K) (h0 : (0 : F) ∈ K)
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K)
    {b : E} {a : ℝ} (hball : closedBall b a ⊆ Ω) :
    ∃ (q : ℕ → ℂ → F) (L : ℕ → ℝ≥0) (D : ℝ), 0 ≤ D ∧
      (∀ n, ContDiff ℝ ∞ (q n)) ∧ (∀ n, LipschitzWith (L n) (q n)) ∧
      (∀ n z, q n z ∈ K) ∧
      (∀ n, (∫ z in closedBall (0 : ℂ) a, ‖fderiv ℝ (q n) z‖ ^ 2) ≤ 2 * D) ∧
      (∀ᵐ z ∂volume.restrict (closedBall (0 : ℂ) a),
        Tendsto (fun n => q n z) atTop (𝓝 (f (b + Complex.orthonormalBasisOneI.repr z)))) ∧
      ∀ r : ℝ, r ≤ a → ∀ (A : F → F →L[ℝ] F →L[ℝ] ℝ), ContinuousOn A K →
        Tendsto (fun n => ∫ z in closedBall (0 : ℂ) r,
          (A (q n z) (fderiv ℝ (q n) z 1) (fderiv ℝ (q n) z 1) +
            A (q n z) (fderiv ℝ (q n) z Complex.I) (fderiv ℝ (q n) z Complex.I)) / 2) atTop
          (𝓝 ((1 / 2 : ℝ) * ∑ j : Fin 2, ∫ x in closedBall b r,
            A (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
              (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)))) := by
  obtain ⟨v, L, D, hD, hv, _, hLip, hvK, _, hnormbound, hsubsets⟩ :=
    exists_smooth_lipschitz_convex_approximation_tendsto_energy_on_subsets
      hK hKconv h0 hΩ hf hfK hball
  let e : ℂ ≃ₗᵢ[ℝ] E := Complex.orthonormalBasisOneI.repr
  let q : ℕ → ℂ → F := fun n z => v n (b + e z)
  have hq (n : ℕ) : ContDiff ℝ ∞ (q n) :=
    (hv n).comp (contDiff_const.add e.contDiff)
  have hqLip (n : ℕ) : LipschitzWith (L n) (q n) := by
    intro z z'
    simpa only [q, edist_add_left, e.isometry.edist_eq] using hLip n (b + e z) (b + e z')
  have hqnorm (n : ℕ) (z : ℂ) : ‖fderiv ℝ (q n) z‖ = ‖fderiv ℝ (v n) (b + e z)‖ := by
    have hd : fderiv ℝ (q n) z =
        (fderiv ℝ (v n) (b + e z)).comp e.toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      intro ξ
      exact DifferentialGeometry.Analysis.fderiv_comp_add_complex_coordinates (v n) b z ξ
    rw [hd]
    exact (fderiv ℝ (v n) (b + e z)).opNorm_comp_linearIsometryEquiv e
  have hnorm (n : ℕ) : (∫ z in closedBall (0 : ℂ) a, ‖fderiv ℝ (q n) z‖ ^ 2) ≤ 2 * D := by
    simp_rw [hqnorm]
    have heq := DifferentialGeometry.Analysis.integral_comp_add_complex_coordinates_closedBall
      (fun x => ‖fderiv ℝ (v n) x‖ ^ 2) b a
    exact heq.le.trans (hnormbound n)
  let T : ℂ ≃ᵐ E := e.toHomeomorph.toMeasurableEquiv.trans (MeasurableEquiv.addLeft b)
  have hT : MeasurePreserving T := (measurePreserving_add_left (volume : Measure E) b).comp
    e.measurePreserving
  have hpre : T ⁻¹' closedBall b a = closedBall (0 : ℂ) a := by
    ext z
    change dist (b + e z) b ≤ a ↔ dist z 0 ≤ a
    simp only [dist_eq_norm, add_sub_cancel_left, e.norm_map, sub_zero]
  have hTr := hT.restrict_preimage (s := closedBall b a) measurableSet_closedBall
  rw [hpre] at hTr
  have hpoint := hTr.quasiMeasurePreserving.ae
    (hsubsets (closedBall b a) measurableSet_closedBall Subset.rfl).2.2.1
  refine ⟨q, L, D, hD, hq, hqLip, fun n z => hvK n (b + e z), hnorm, hpoint, ?_⟩
  intro r hra A hA
  have henergy := (hsubsets (closedBall b r) measurableSet_closedBall
    (closedBall_subset_closedBall hra)).2.2.2 A hA
  have hint (n : ℕ) (j : Fin 2) : IntegrableOn (fun x =>
      A (v n x) (fderiv ℝ (v n) x (EuclideanSpace.single j 1))
        (fderiv ℝ (v n) x (EuclideanSpace.single j 1))) (closedBall b r) := by
    have hcA : ContinuousOn (fun x => A (v n x)) (closedBall b r) :=
      hA.comp (hv n).continuous.continuousOn (fun x _ => hvK n x)
    have hcD : ContinuousOn (fun x => fderiv ℝ (v n) x (EuclideanSpace.single j 1))
        (closedBall b r) :=
      (((hv n).continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
    exact ((hcA.clm_apply hcD).clm_apply hcD).integrableOn_compact (isCompact_closedBall b r)
  have heq (n : ℕ) : (∫ z in closedBall (0 : ℂ) r,
      (A (q n z) (fderiv ℝ (q n) z 1) (fderiv ℝ (q n) z 1) +
        A (q n z) (fderiv ℝ (q n) z Complex.I) (fderiv ℝ (q n) z Complex.I)) / 2) =
      (1 / 2 : ℝ) * ∑ j : Fin 2, ∫ x in closedBall b r,
        A (v n x) (fderiv ℝ (v n) x (EuclideanSpace.single j 1))
          (fderiv ℝ (v n) x (EuclideanSpace.single j 1)) :=
    DifferentialGeometry.Analysis.integral_quadratic_fderiv_comp_complex_coordinates_closedBall
      A (v n) b r (hint n)
  simpa only [heq] using henergy.const_mul (1 / 2 : ℝ)

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

end
