import DifferentialGeometry.Analysis.Sobolev.Euclidean.TargetApproximation.Convolution
import DifferentialGeometry.Analysis.Integration.Integral.QuadraticDerivative
import DifferentialGeometry.Analysis.Sobolev.Euclidean.LipschitzW1
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import DifferentialGeometry.Topology.MetricSpace.LipschitzExtension
import DifferentialGeometry.Analysis.Integration.LpNorm
import Mathlib.Topology.Order.LiminfLimsup
import DifferentialGeometry.Analysis.Integration.Measure.EuclideanPlane
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Operator.NormedSpace

noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped ContDiff Topology ENNReal NNReal Convolution

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_contDiffOn_mapsTo_tendsto_L2_weakGrad_on_ball
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (r : F → F) (hr : ContDiffOn ℝ ∞ r U) (hrK : MapsTo r U K)
    (hfix : ∀ y ∈ K, r y = y)
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K)
    {c : E} {a : ℝ} (hball : Metric.closedBall c a ⊆ Ω) :
    ∃ v : ℕ → E → F,
      (∀ n, ContDiffOn ℝ ∞ (v n) (Metric.closedBall c a)) ∧
      (∀ n, ∃ L : ℝ≥0, LipschitzOnWith L (v n) (Metric.closedBall c a)) ∧
      (∀ n, MapsTo (v n) (Metric.closedBall c a) K) ∧
      Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2
        (volume.restrict (Metric.ball c a))) atTop (𝓝 0) ∧
      ∀ j : Fin 2, Tendsto (fun n => eLpNorm (fun x =>
        fderiv ℝ (v n) x (EuclideanSpace.single j 1) -
          WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        2 (volume.restrict (Metric.ball c a))) atTop (𝓝 0) := by
  obtain ⟨ρ, hρ, hbound⟩ := exists_pos_contDiffOn_retracted_indicator_convolution
    hK hU hKU hΩ (isCompact_closedBall c a) hball f hf hfK r hr hrK
  let ε (n : ℕ) : ℝ := ρ / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, mul_one_div, mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ρ
  let φ (n : ℕ) := mollifierBumpEps (d := 2) (hε n)
  let v (n : ℕ) := r ∘ ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] (Ω.indicator f))
  have hrad (n : ℕ) : (φ n).rOut ≤ ρ := by
    change ρ / ((n : ℝ) + 1) ≤ ρ
    exact div_le_self hρ.le (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hratio (n : ℕ) : (φ n).rOut ≤ 2 * (φ n).rIn := by dsimp [φ, mollifierBumpEps]; linarith
  have hsm (n : ℕ) := (hbound (φ n) (hrad n) (hratio n)).2.1
  refine ⟨v, hsm, (fun n => (hsm n).exists_lipschitzOnWith (by simp)
      (convex_closedBall c a) (isCompact_closedBall c a)),
    (fun n => (hbound (φ n) (hrad n) (hratio n)).2.2), ?_, ?_⟩
  · have ht := tendsto_eLpNorm_retracted_convolution_sub_on_compact hK hU hKU r hr hfix
      hΩ (isCompact_closedBall c a) hball hf hfK hε hε0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
      (fun _ => eLpNorm_mono_measure _ (Measure.restrict_mono_set volume Metric.ball_subset_closedBall))
  · intro j
    exact tendsto_eLpNorm_partial_retracted_convolution_sub_weakGrad_on_ball
      hK hU hKU r hr hfix hΩ hf hfK hball hε hε0 j

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem exists_target_valued_smooth_approximation_tendsto_energy_on_ball
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (r : F → F) (hr : ContDiffOn ℝ ∞ r U) (hrK : MapsTo r U K)
    (hfix : ∀ y ∈ K, r y = y)
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K)
    {c : E} {a : ℝ} (hball : Metric.closedBall c a ⊆ Ω)
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K) :
    ∃ v : ℕ → E → F,
      (∀ n, ContDiffOn ℝ ∞ (v n) (Metric.closedBall c a)) ∧
      (∀ n, ∃ L : ℝ≥0, LipschitzOnWith L (v n) (Metric.closedBall c a)) ∧
      (∀ n, MapsTo (v n) (Metric.closedBall c a) K) ∧
      Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2
        (volume.restrict (Metric.ball c a))) atTop (𝓝 0) ∧
      (∀ j : Fin 2, Tendsto (fun n => eLpNorm (fun x =>
        fderiv ℝ (v n) x (EuclideanSpace.single j 1) -
          WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        2 (volume.restrict (Metric.ball c a))) atTop (𝓝 0)) ∧
      Tendsto (fun n => ∑ j : Fin 2, ∫ x in Metric.ball c a,
        A (v n x) (fderiv ℝ (v n) x (EuclideanSpace.single j 1))
          (fderiv ℝ (v n) x (EuclideanSpace.single j 1))) atTop
        (𝓝 (∑ j : Fin 2, ∫ x in Metric.ball c a,
          A (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)))) := by
  obtain ⟨v, hv, hvLip, hvK, hval, hder⟩ :=
    exists_contDiffOn_mapsTo_tendsto_L2_weakGrad_on_ball hK hU hKU r hr hrK hfix hΩ hf hfK hball
  let μ := volume.restrict (Metric.ball c a)
  have hBΩ : Metric.ball c a ⊆ Ω := Metric.ball_subset_closedBall.trans hball
  have hfm : MemLp f 2 μ := MemLp.of_eval_piLp fun i =>
    ((hf i).memLp).mono_measure (Measure.restrict_mono_set volume hBΩ)
  have hum (n : ℕ) : MemLp (v n) 2 μ :=
    ((hv n).continuousOn.memLp_restrict_compact (isCompact_closedBall c a) 2).mono_measure
      (Measure.restrict_mono_set volume Metric.ball_subset_closedBall)
  obtain ⟨φ, hφ, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (fun n => (hum n).aestronglyMeasurable) hfm.aestronglyMeasurable hval).exists_seq_tendsto_ae
  have hpartial (n : ℕ) (j : Fin 2) : MemLp
      (fun x => fderiv ℝ (v n) x (EuclideanSpace.single j 1)) 2 μ := by
    obtain ⟨L, hL⟩ := hvLip n
    let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    apply MemLp.of_bound (measurable_fderiv_apply_const ℝ (v n) _).aestronglyMeasurable L
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hn : ‖fderiv ℝ (v n) x‖ ≤ L := by
      exact norm_fderiv_le_of_lipschitzOn ℝ (Metric.closedBall_mem_nhds_of_mem hx) hL
    have hdir := (fderiv ℝ (v n) x).le_opNorm (EuclideanSpace.single j 1)
    simpa only [PiLp.norm_single, norm_one, mul_one] using hdir.trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  have hG (j : Fin 2) : MemLp (fun x => WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) 2 μ :=
    MemLp.of_eval_piLp fun i => ((hf i).weakGrad_component_memLp j).mono_measure
      (Measure.restrict_mono_set volume hBΩ)
  refine ⟨v ∘ φ, fun n => hv (φ n), fun n => hvLip (φ n), fun n => hvK (φ n),
    hval.comp hφ.tendsto_atTop, fun j => (hder j).comp hφ.tendsto_atTop, ?_⟩
  exact tendsto_integral_target_metric_energy_of_strong_approximation
    Metric.isOpen_ball.measurableSet Metric.ball_subset_closedBall hK A hA f (v ∘ φ)
    (fun n => (hv (φ n)).of_le (by simp)) (fun n => hvK (φ n))
    (ae_mono (Measure.restrict_mono_set volume hBΩ) hfK) hae
    (fun j x => WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) hG
    (fun n j => hpartial (φ n) j) (fun j => (hder j).comp hφ.tendsto_atTop)

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

private theorem tendsto_integral_norm_sq_of_tendsto_eLpNorm
    {X F : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f : ℕ → X → F} {g : X → F}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (h : Tendsto (fun n => eLpNorm (fun x => f n x - g x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖f n x‖ ^ 2 ∂μ) atTop (𝓝 (∫ x, ‖g x‖ ^ 2 ∂μ)) := by
  have hq := tendsto_integral_quadratic_of_tendsto_eLpNorm_of_ae_tendsto
    (fun _ _ => innerSL ℝ (E := F)) (fun _ => innerSL ℝ (E := F))
    (fun _ => aestronglyMeasurable_const)
    (C := ‖innerSL ℝ (E := F)‖) (fun _ => Eventually.of_forall fun _ => le_rfl)
    (Eventually.of_forall fun _ => tendsto_const_nhds) f g hf hg h
  have heq (y : F) : (innerSL ℝ (E := F)) y y = ‖y‖ ^ 2 :=
    real_inner_self_eq_norm_sq y
  simpa only [heq] using hq

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

theorem exists_globally_lipschitz_target_approximation_tendsto_energy_on_ball
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (r : F → F) (hr : ContDiffOn ℝ ∞ r U) (hrK : MapsTo r U K)
    (hfix : ∀ y ∈ K, r y = y)
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K)
    {c : E} {a : ℝ} (hball : Metric.closedBall c a ⊆ Ω)
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K) :
    ∃ (v : ℕ → E → F) (L : ℕ → ℝ≥0) (B : ℝ), 0 ≤ B ∧
      (∀ n, LipschitzWith (L n) (v n)) ∧
      (∀ n, ContDiffOn ℝ ∞ (v n) (Metric.closedBall c a)) ∧
      (∀ n, MapsTo (v n) (Metric.closedBall c a) K) ∧
      Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2
        (volume.restrict (Metric.ball c a))) atTop (𝓝 0) ∧
      (∀ j : Fin 2, Tendsto (fun n => eLpNorm (fun x =>
        fderiv ℝ (v n) x (EuclideanSpace.single j 1) -
          WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        2 (volume.restrict (Metric.ball c a))) atTop (𝓝 0)) ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball c a),
        Tendsto (fun n => v n x) atTop (𝓝 (f x))) ∧
      (∀ n, (∫ x in Metric.ball c a, ‖fderiv ℝ (v n) x‖ ^ 2) ≤ B) ∧
      Tendsto (fun n => ∑ j : Fin 2, ∫ x in Metric.ball c a,
        A (v n x) (fderiv ℝ (v n) x (EuclideanSpace.single j 1))
          (fderiv ℝ (v n) x (EuclideanSpace.single j 1))) atTop
        (𝓝 (∑ j : Fin 2, ∫ x in Metric.ball c a,
          A (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)))) := by
  classical
  obtain ⟨u, hu, huLip, huK, hval, hder, henergy⟩ :=
    exists_target_valued_smooth_approximation_tendsto_energy_on_ball
      hK hU hKU r hr hrK hfix hΩ hf hfK hball A hA
  have hext (n : ℕ) : ∃ (v : E → F) (L : ℝ≥0),
      LipschitzWith L v ∧ EqOn (u n) v (Metric.closedBall c a) := by
    obtain ⟨L, hL⟩ := huLip n
    exact hL.exists_lipschitz_extension
  choose v L hLip heq using hext
  let μ : Measure E := volume.restrict (Metric.ball c a)
  have hae (n : ℕ) : u n =ᵐ[μ] v n := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact heq n (Metric.ball_subset_closedBall hx)
  have hdeq (n : ℕ) : fderiv ℝ (u n) =ᵐ[μ] fderiv ℝ (v n) := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hgerm : u n =ᶠ[𝓝 x] v n := by
      filter_upwards [Metric.closedBall_mem_nhds_of_mem hx] with y hy
      exact heq n hy
    exact hgerm.fderiv_eq
  have hv (n : ℕ) : ContDiffOn ℝ ∞ (v n) (Metric.closedBall c a) :=
    (hu n).congr (heq n).symm
  have hvK (n : ℕ) : MapsTo (v n) (Metric.closedBall c a) K := by
    intro x hx
    rw [← heq n hx]
    exact huK n hx
  have hval' : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 μ) atTop (𝓝 0) := by
    convert hval using 1
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [hae n] with x hx
    rw [hx]
  have hder' (j : Fin 2) : Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (v n) x (EuclideanSpace.single j 1) -
        WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) 2 μ) atTop (𝓝 0) := by
    convert hder j using 1
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [hdeq n] with x hx
    rw [hx]
  have henergy' : Tendsto (fun n => ∑ j : Fin 2, ∫ x in Metric.ball c a,
      A (v n x) (fderiv ℝ (v n) x (EuclideanSpace.single j 1))
        (fderiv ℝ (v n) x (EuclideanSpace.single j 1))) atTop
      (𝓝 (∑ j : Fin 2, ∫ x in Metric.ball c a,
        A (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)))) := by
    convert henergy using 1
    funext n
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [hae n, hdeq n] with x hx hdx
    rw [hx, hdx]
  have hBΩ : Metric.ball c a ⊆ Ω := Metric.ball_subset_closedBall.trans hball
  have hfm : MemLp f 2 μ := MemLp.of_eval_piLp fun i =>
    ((hf i).memLp).mono_measure (Measure.restrict_mono_set volume hBΩ)
  have hvm (n : ℕ) : MemLp (v n) 2 μ :=
    ((hv n).continuousOn.memLp_restrict_compact (isCompact_closedBall c a) 2).mono_measure
      (Measure.restrict_mono_set volume Metric.ball_subset_closedBall)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hpartial (n : ℕ) (j : Fin 2) : MemLp
      (fun x => fderiv ℝ (v n) x (EuclideanSpace.single j 1)) 2 μ := by
    apply MemLp.of_bound (measurable_fderiv_apply_const ℝ (v n) _).aestronglyMeasurable (L n)
    exact Eventually.of_forall fun x => by
      have hd := (fderiv ℝ (v n) x).le_opNorm (EuclideanSpace.single j 1)
      simpa only [PiLp.norm_single, norm_one, mul_one] using hd.trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hLip n)) (norm_nonneg _))
  have hG (j : Fin 2) : MemLp (fun x => WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) 2 μ :=
    MemLp.of_eval_piLp fun i => ((hf i).weakGrad_component_memLp j).mono_measure
      (Measure.restrict_mono_set volume hBΩ)
  have hnorm (j : Fin 2) := tendsto_integral_norm_sq_of_tendsto_eLpNorm
    (fun n => hpartial n j) (hG j) (hder' j)
  have hsum := (hnorm 0).add (hnorm 1)
  obtain ⟨D, hD⟩ := hsum.bddAbove_range
  have hbound (n : ℕ) : (∫ x in Metric.ball c a, ‖fderiv ℝ (v n) x‖ ^ 2) ≤ 2 * max D 0 := by
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
      _ = 2 * ((∫ x, ‖fderiv ℝ (v n) x (EuclideanSpace.single 0 1)‖ ^ 2 ∂μ) +
          ∫ x, ‖fderiv ℝ (v n) x (EuclideanSpace.single 1 1)‖ ^ 2 ∂μ) := by
        rw [integral_const_mul, integral_add hj0 hj1]
      _ ≤ 2 * max D 0 := mul_le_mul_of_nonneg_left
        ((hD (mem_range_self n)).trans (le_max_left _ _)) (by norm_num)
  obtain ⟨φ, hφ, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (fun n => (hvm n).aestronglyMeasurable) hfm.aestronglyMeasurable hval').exists_seq_tendsto_ae
  exact ⟨v ∘ φ, L ∘ φ, 2 * max D 0, by positivity,
    fun n => hLip (φ n), fun n => hv (φ n), fun n => hvK (φ n),
    hval'.comp hφ.tendsto_atTop, fun j => (hder' j).comp hφ.tendsto_atTop,
    hpoint, fun n => hbound (φ n), henergy'.comp hφ.tendsto_atTop⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "E" => EuclideanSpace ℝ (Fin 2)


private theorem plane_repr_direction (j : Fin 2) :
    Complex.orthonormalBasisOneI.repr (Complex.orthonormalBasisOneI j) =
      EuclideanSpace.single j (1 : ℝ) :=
  Complex.orthonormalBasisOneI.repr_self j

private theorem fderiv_comp_plane_repr
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (z : ℂ) (j : Fin 2) :
    fderiv ℝ (f ∘ Complex.orthonormalBasisOneI.repr) z
      (Complex.orthonormalBasisOneI j) =
      fderiv ℝ f (Complex.orthonormalBasisOneI.repr z) (EuclideanSpace.single j 1) := by
  erw [Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'',
    plane_repr_direction]
  rfl

private theorem norm_fderiv_comp_plane_repr
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (z : ℂ) :
    ‖fderiv ℝ (f ∘ Complex.orthonormalBasisOneI.repr) z‖ =
      ‖fderiv ℝ f (Complex.orthonormalBasisOneI.repr z)‖ := by
  erw [Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.comp_right_fderiv]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _

private theorem eLpNorm_fderiv_sub_comp_plane_repr_ball
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u G : E → F) (j : Fin 2) (a : ℝ) :
    eLpNorm (fun z =>
        fderiv ℝ (u ∘ Complex.orthonormalBasisOneI.repr) z
          (Complex.orthonormalBasisOneI j) - G (Complex.orthonormalBasisOneI.repr z))
      2 (volume.restrict (Metric.ball (0 : ℂ) a)) =
      eLpNorm (fun x => fderiv ℝ u x (EuclideanSpace.single j 1) - G x)
        2 (volume.restrict (Metric.ball (0 : E) a)) := by
  simp only [fderiv_comp_plane_repr]
  exact eLpNorm_comp_complex_plane_repr_ball
    (fun x => fderiv ℝ u x (EuclideanSpace.single j 1) - G x) 2 a

variable {ι : Type*} [Fintype ι]
local notation "F" => EuclideanSpace ℝ ι

theorem exists_lipschitz_complex_target_approximation_tendsto_energy_on_ball
    {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (r : F → F) (hr : ContDiffOn ℝ ∞ r U) (hrK : MapsTo r U K)
    (hfix : ∀ y ∈ K, r y = y)
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K)
    {a : ℝ} (hball : Metric.closedBall (0 : E) a ⊆ Ω)
    (A : F → F →L[ℝ] F →L[ℝ] ℝ) (hA : ContinuousOn A K) :
    ∃ (v : ℕ → ℂ → F) (L : ℕ → ℝ≥0) (B : ℝ), 0 ≤ B ∧
      (∀ n, LipschitzWith (L n) (v n)) ∧
      (∀ n, ContDiffOn ℝ ∞ (v n) (Metric.closedBall (0 : ℂ) a)) ∧
      (∀ n, MapsTo (v n) (Metric.closedBall (0 : ℂ) a) K) ∧
      Tendsto (fun n => eLpNorm (fun z => v n z - f (Complex.orthonormalBasisOneI.repr z)) 2
        (volume.restrict (Metric.ball (0 : ℂ) a))) atTop (𝓝 0) ∧
      (∀ j : Fin 2, Tendsto (fun n => eLpNorm (fun z =>
        fderiv ℝ (v n) z (Complex.orthonormalBasisOneI j) -
          WithLp.toLp 2 (fun i => (hf i).weakGrad (Complex.orthonormalBasisOneI.repr z) j))
        2 (volume.restrict (Metric.ball (0 : ℂ) a))) atTop (𝓝 0)) ∧
      (∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) a),
        Tendsto (fun n => v n z) atTop (𝓝 (f (Complex.orthonormalBasisOneI.repr z)))) ∧
      (∀ n, (∫ z in Metric.ball (0 : ℂ) a, ‖fderiv ℝ (v n) z‖ ^ 2) ≤ B) ∧
      Tendsto (fun n => ∫ z in Metric.ball (0 : ℂ) a,
        (A (v n z) (fderiv ℝ (v n) z 1) (fderiv ℝ (v n) z 1) +
          A (v n z) (fderiv ℝ (v n) z Complex.I) (fderiv ℝ (v n) z Complex.I)) / 2) atTop
        (𝓝 ((∑ j : Fin 2, ∫ x in Metric.ball (0 : E) a,
          A (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) / 2)) := by
  obtain ⟨u, L, B, hB, huLip, hu, huK, hval, hder, hae, hbound, henergy⟩ :=
    exists_globally_lipschitz_target_approximation_tendsto_energy_on_ball
      hK hU hKU r hr hrK hfix hΩ hf hfK hball A hA
  let e := Complex.orthonormalBasisOneI.repr
  let v (n : ℕ) : ℂ → F := u n ∘ e
  have hmap : MapsTo e (Metric.closedBall (0 : ℂ) a) (Metric.closedBall (0 : E) a) := by
    intro z hz
    simpa only [Metric.mem_closedBall, dist_zero_right, e.norm_map] using hz
  have hvLip (n : ℕ) : LipschitzWith (L n) (v n) := by
    simpa only [mul_one] using (huLip n).comp e.isometry.lipschitz
  have hv (n : ℕ) : ContDiffOn ℝ ∞ (v n) (Metric.closedBall (0 : ℂ) a) :=
    (hu n).comp e.toContinuousLinearEquiv.contDiff.contDiffOn hmap
  have hvK (n : ℕ) : MapsTo (v n) (Metric.closedBall (0 : ℂ) a) K :=
    (huK n).comp hmap
  have hvval : Tendsto (fun n => eLpNorm (fun z => v n z - f (e z)) 2
      (volume.restrict (Metric.ball (0 : ℂ) a))) atTop (𝓝 0) := by
    have heq (n : ℕ) : eLpNorm (fun z => v n z - f (e z)) 2
        (volume.restrict (Metric.ball (0 : ℂ) a)) =
        eLpNorm (fun x => u n x - f x) 2 (volume.restrict (Metric.ball (0 : E) a)) :=
      eLpNorm_comp_complex_plane_repr_ball (fun x => u n x - f x) 2 a
    simpa only [heq] using hval
  have hvder (j : Fin 2) : Tendsto (fun n => eLpNorm (fun z =>
      fderiv ℝ (v n) z (Complex.orthonormalBasisOneI j) -
        WithLp.toLp 2 (fun i => (hf i).weakGrad (e z) j))
      2 (volume.restrict (Metric.ball (0 : ℂ) a))) atTop (𝓝 0) := by
    have heq (n : ℕ) : eLpNorm (fun z =>
        fderiv ℝ (v n) z (Complex.orthonormalBasisOneI j) -
          WithLp.toLp 2 (fun i => (hf i).weakGrad (e z) j))
        2 (volume.restrict (Metric.ball (0 : ℂ) a)) =
        eLpNorm (fun x => fderiv ℝ (u n) x (EuclideanSpace.single j 1) -
          WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
          2 (volume.restrict (Metric.ball (0 : E) a)) := by
      exact eLpNorm_fderiv_sub_comp_plane_repr_ball (u n)
        (fun x => WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) j a
    simpa only [heq] using hder j
  have hvae : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) a),
      Tendsto (fun n => v n z) atTop (𝓝 (f (e z))) :=
    (measurePreserving_complex_plane_repr_ball a).quasiMeasurePreserving.ae hae
  have hvbound (n : ℕ) : (∫ z in Metric.ball (0 : ℂ) a, ‖fderiv ℝ (v n) z‖ ^ 2) ≤ B := by
    simp only [v, e, norm_fderiv_comp_plane_repr]
    rw [integral_comp_complex_plane_repr_ball (fun x => ‖fderiv ℝ (u n) x‖ ^ 2) a]
    exact hbound n
  refine ⟨v, L, B, hB, hvLip, hv, hvK, hvval, hvder, hvae, hvbound, ?_⟩
  have hi (n : ℕ) (j : Fin 2) : IntegrableOn (fun x =>
      A (u n x) (fderiv ℝ (u n) x (EuclideanSpace.single j 1))
        (fderiv ℝ (u n) x (EuclideanSpace.single j 1))) (Metric.ball (0 : E) a) := by
    let μ : Measure E := volume.restrict (Metric.ball (0 : E) a)
    let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    have hAc : ContinuousOn (fun x => A (u n x)) (Metric.closedBall (0 : E) a) :=
      hA.comp (hu n).continuousOn (huK n)
    have hm : AEStronglyMeasurable (fun x => A (u n x)) μ :=
      (hAc.mono Metric.ball_subset_closedBall).aestronglyMeasurable Metric.isOpen_ball.measurableSet
    have hAnorm : ContinuousOn (fun y => ‖A y‖) K :=
      (@continuous_norm (F →L[ℝ] F →L[ℝ] ℝ) inferInstance).comp_continuousOn hA
    obtain ⟨C, hC⟩ := hK.bddAbove_image hAnorm
    have hb : ∀ᵐ x ∂μ, ‖A (u n x)‖ ≤ C := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      exact hC (mem_image_of_mem _ (huK n (Metric.ball_subset_closedBall hx)))
    have hdm : MemLp (fun x => fderiv ℝ (u n) x (EuclideanSpace.single j 1)) 2 μ := by
      apply MemLp.of_bound (measurable_fderiv_apply_const ℝ (u n) _).aestronglyMeasurable (L n)
      exact Eventually.of_forall fun x => by
        have hd := (fderiv ℝ (u n) x).le_opNorm (EuclideanSpace.single j 1)
        simpa only [PiLp.norm_single, norm_one, mul_one] using hd.trans
          (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (huLip n)) (norm_nonneg _))
    exact integrable_bilinear_of_apply_aestronglyMeasurable (fun x => A (u n x))
      (fun b c => (hm.apply_continuousLinearMap b).apply_continuousLinearMap c) hb hdm hdm
  have heq (n : ℕ) : (∫ z in Metric.ball (0 : ℂ) a,
      (A (v n z) (fderiv ℝ (v n) z 1) (fderiv ℝ (v n) z 1) +
        A (v n z) (fderiv ℝ (v n) z Complex.I) (fderiv ℝ (v n) z Complex.I)) / 2) =
      (∑ j : Fin 2, ∫ x in Metric.ball (0 : E) a,
        A (u n x) (fderiv ℝ (u n) x (EuclideanSpace.single j 1))
          (fderiv ℝ (u n) x (EuclideanSpace.single j 1))) / 2 := by
    have hd0 (z : ℂ) := fderiv_comp_plane_repr (u n) z 0
    have hd1 (z : ℂ) := fderiv_comp_plane_repr (u n) z 1
    simp only [Complex.coe_orthonormalBasisOneI, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hd0 hd1
    simp only [v, e] at hd0 hd1 ⊢
    simp_rw [hd0, hd1]
    simp only [Function.comp_apply]
    rw [integral_div, integral_comp_complex_plane_repr_ball (fun x =>
      A (u n x) (fderiv ℝ (u n) x (EuclideanSpace.single 0 1))
        (fderiv ℝ (u n) x (EuclideanSpace.single 0 1)) +
      A (u n x) (fderiv ℝ (u n) x (EuclideanSpace.single 1 1))
        (fderiv ℝ (u n) x (EuclideanSpace.single 1 1))) a]
    rw [Fin.sum_univ_two, integral_add (hi n 0) (hi n 1)]
  simpa only [heq] using henergy.div_const 2

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
