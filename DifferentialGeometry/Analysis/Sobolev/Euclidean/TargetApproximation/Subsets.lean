import DifferentialGeometry.Analysis.Sobolev.Euclidean.TargetApproximation.Energy
import DifferentialGeometry.Analysis.Integration.Lp.QuadraticConvergence
import DifferentialGeometry.Analysis.Integration.Integral.QuadraticDerivative

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]

private theorem metric_column_integrable
    {S : Set ℂ}
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K)
    (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : ContinuousOn A K) {f G : ℂ → EuclideanSpace ℝ ι}
    (hf : AEStronglyMeasurable f (volume.restrict S))
    (hfK : ∀ᵐ z ∂volume.restrict S, f z ∈ K) (hG : MemLp G 2 (volume.restrict S)) :
    IntegrableOn (fun z => A (f z) (G z) (G z)) S := by
  classical
  have hm : Measurable (K.piecewise A 0) :=
    hA.measurable_piecewise continuous_zero.continuousOn hK.measurableSet
  have hAm : AEStronglyMeasurable (fun z => A (f z)) (volume.restrict S) := by
    apply (hm.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable.congr
    filter_upwards [hfK] with z hz
    exact Set.piecewise_eq_of_mem K A 0 hz
  have hc : ContinuousOn (fun y => ‖A y‖) K :=
    (@continuous_norm (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
      inferInstance).comp_continuousOn hA
  obtain ⟨C, hC⟩ := hK.bddAbove_image hc
  have hb : ∀ᵐ z ∂volume.restrict S, ‖A (f z)‖ ≤ C :=
    hfK.mono fun z hz => hC (mem_image_of_mem _ hz)
  exact integrable_bilinear_of_apply_aestronglyMeasurable (fun z => A (f z))
    (fun v w => (hAm.apply_continuousLinearMap v).apply_continuousLinearMap w) hb hG hG

theorem tendsto_complex_target_energy_on_subset_of_strong_approximation
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K)
    (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : ContinuousOn A K)
    (u : ℕ → ℂ → EuclideanSpace ℝ ι) (L : ℕ → ℝ≥0)
    (hu : ∀ n, LipschitzWith (L n) (u n)) {a : ℝ}
    (huK : ∀ n, MapsTo (u n) (Metric.closedBall (0 : ℂ) a) K)
    (f : ℂ → EuclideanSpace ℝ ι) (G : Fin 2 → ℂ → EuclideanSpace ℝ ι)
    (hfK : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) a), f z ∈ K)
    (hae : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : ℂ) a),
      Tendsto (fun n => u n z) atTop (𝓝 (f z)))
    (hG : ∀ j, MemLp (G j) 2 (volume.restrict (Metric.ball (0 : ℂ) a)))
    (hder : ∀ j : Fin 2, Tendsto (fun n => eLpNorm (fun z =>
      fderiv ℝ (u n) z (Complex.orthonormalBasisOneI j) - G j z)
      2 (volume.restrict (Metric.ball (0 : ℂ) a))) atTop (𝓝 0))
    {S : Set ℂ} (hS : MeasurableSet S) (hSa : S ⊆ Metric.ball (0 : ℂ) a) :
    Tendsto (fun n => ∫ z in S,
      (A (u n z) (fderiv ℝ (u n) z 1) (fderiv ℝ (u n) z 1) +
        A (u n z) (fderiv ℝ (u n) z Complex.I) (fderiv ℝ (u n) z Complex.I)) / 2) atTop
      (𝓝 (∫ z in S, (A (f z) (G 0 z) (G 0 z) + A (f z) (G 1 z) (G 1 z)) / 2)) := by
  let μ := volume.restrict S
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    ((measure_mono (hSa.trans Metric.ball_subset_closedBall)).trans_lt
      (isCompact_closedBall (0 : ℂ) a).measure_lt_top).ne
  have hcol (n : ℕ) (j : Fin 2) : MemLp
      (fun z => fderiv ℝ (u n) z (Complex.orthonormalBasisOneI j)) 2 μ := by
    apply MemLp.of_bound (measurable_fderiv_apply_const ℝ (u n) _).aestronglyMeasurable (L n)
    exact Eventually.of_forall fun z => by
      have h := (fderiv ℝ (u n) z).le_opNorm (Complex.orthonormalBasisOneI j)
      simpa only [Complex.orthonormalBasisOneI.norm_eq_one, mul_one] using
        h.trans (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hu n))
          (norm_nonneg _))
  have hGS (j : Fin 2) : MemLp (G j) 2 μ :=
    (hG j).mono_measure (Measure.restrict_mono_set volume hSa)
  have hderS (j : Fin 2) : Tendsto (fun n => eLpNorm (fun z =>
      fderiv ℝ (u n) z (Complex.orthonormalBasisOneI j) - G j z) 2 μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hder j)
      (fun n => zero_le) (fun n => eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hSa))
  have hAm (n : ℕ) : AEStronglyMeasurable (fun z => A (u n z)) μ :=
    ((hA.comp (hu n).continuous.continuousOn (huK n)).mono
      (hSa.trans Metric.ball_subset_closedBall)).aestronglyMeasurable hS
  have hc : ContinuousOn (fun y => ‖A y‖) K :=
    (@continuous_norm (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
      inferInstance).comp_continuousOn hA
  obtain ⟨C, hC⟩ := hK.bddAbove_image hc
  have hb (n : ℕ) : ∀ᵐ z ∂μ, ‖A (u n z)‖ ≤ C := by
    filter_upwards [ae_restrict_mem hS] with z hz
    exact hC (mem_image_of_mem _ (huK n (Metric.ball_subset_closedBall (hSa hz))))
  have haeS := ae_restrict_of_ae_restrict_of_subset hSa hae
  have hfKS := ae_restrict_of_ae_restrict_of_subset hSa hfK
  have hAc : ∀ᵐ z ∂μ, Tendsto (fun n => A (u n z)) atTop (𝓝 (A (f z))) := by
    filter_upwards [haeS, hfKS, ae_restrict_mem hS] with z hz hzK hzS
    exact (hA (f z) hzK).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hz, Eventually.of_forall fun n => huK n (Metric.ball_subset_closedBall (hSa hzS))⟩)
  have hlim (j : Fin 2) := tendsto_integral_quadratic_of_tendsto_eLpNorm_of_ae_tendsto
    (fun n z => A (u n z)) (fun z => A (f z)) hAm hb hAc
    (fun n z => fderiv ℝ (u n) z (Complex.orthonormalBasisOneI j)) (G j)
    (fun n => hcol n j) (hGS j) (hderS j)
  have hfi : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hu n).continuous.aestronglyMeasurable) haeS
  have hi0 := metric_column_integrable hK A hA hfi hfKS (hGS 0)
  have hi1 := metric_column_integrable hK A hA hfi hfKS (hGS 1)
  have hi (n : ℕ) (j : Fin 2) := integrable_bilinear_of_apply_aestronglyMeasurable
    (fun z => A (u n z))
    (fun v w => ((hAm n).apply_continuousLinearMap v).apply_continuousLinearMap w)
    (hb n) (hcol n j) (hcol n j)
  have h := ((hlim 0).add (hlim 1)).div_const 2
  have heq (n : ℕ) : (∫ z in S,
      (A (u n z) (fderiv ℝ (u n) z 1) (fderiv ℝ (u n) z 1) +
        A (u n z) (fderiv ℝ (u n) z Complex.I) (fderiv ℝ (u n) z Complex.I)) / 2) =
      ((∫ z in S, A (u n z) (fderiv ℝ (u n) z (Complex.orthonormalBasisOneI 0))
        (fderiv ℝ (u n) z (Complex.orthonormalBasisOneI 0))) +
       (∫ z in S, A (u n z) (fderiv ℝ (u n) z (Complex.orthonormalBasisOneI 1))
        (fderiv ℝ (u n) z (Complex.orthonormalBasisOneI 1)))) / 2 := by
    have hi'0 := hi n 0
    have hi'1 := hi n 1
    simp only [Complex.coe_orthonormalBasisOneI, Matrix.cons_val_zero,
      Matrix.cons_val_one] at hi'0 hi'1 ⊢
    rw [integral_div, integral_add hi'0 hi'1]
  have heq0 : (∫ z in S, (A (f z) (G 0 z) (G 0 z) + A (f z) (G 1 z) (G 1 z)) / 2) =
      ((∫ z in S, A (f z) (G 0 z) (G 0 z)) + ∫ z in S, A (f z) (G 1 z) (G 1 z)) / 2 := by
    rw [integral_div, integral_add hi0 hi1]
  simpa only [heq, heq0] using h

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]

theorem tendsto_original_metric_energy_on_subset_of_strong_approximation
    {Ω : Set (EuclideanSpace ℝ (Fin 2))} {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ ι}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    {c : EuclideanSpace ℝ (Fin 2)} {a : ℝ} (hball : Metric.closedBall c a ⊆ Ω)
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K)
    (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K)
    (u : ℕ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ ι) (L : ℕ → ℝ≥0)
    (huLip : ∀ n, LipschitzWith (L n) (u n))
    (hu : ∀ n, ContDiffOn ℝ 1 (u n) (Metric.closedBall c a))
    (huK : ∀ n, MapsTo (u n) (Metric.closedBall c a) K)
    (hae : ∀ᵐ x ∂volume.restrict (Metric.ball c a),
      Tendsto (fun n => u n x) atTop (𝓝 (f x)))
    (hder : ∀ j : Fin 2, Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (u n) x (EuclideanSpace.single j 1) -
        WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
      2 (volume.restrict (Metric.ball c a))) atTop (𝓝 0))
    {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : MeasurableSet S) (hSa : S ⊆ Metric.ball c a)
    (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : ContinuousOn A K) :
    Tendsto (fun n => ∑ j : Fin 2, ∫ x in S,
      A (u n x) (fderiv ℝ (u n) x (EuclideanSpace.single j 1))
        (fderiv ℝ (u n) x (EuclideanSpace.single j 1))) atTop
      (𝓝 (∑ j : Fin 2, ∫ x in S,
        A (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)))) := by
  have hSΩ : S ⊆ Ω := hSa.trans (Metric.ball_subset_closedBall.trans hball)
  have hSclosed : S ⊆ Metric.closedBall c a := hSa.trans Metric.ball_subset_closedBall
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr
    ((measure_mono hSclosed).trans_lt (isCompact_closedBall c a).measure_lt_top).ne
  have hG (j : Fin 2) : MemLp
      (fun x => (WithLp.toLp 2 (fun i => (hf i).weakGrad x j) : EuclideanSpace ℝ ι))
      2 (volume.restrict S) :=
    MemLp.of_eval_piLp fun i => ((hf i).weakGrad_component_memLp j).mono_measure
      (Measure.restrict_mono_set volume hSΩ)
  have huD (n : ℕ) (j : Fin 2) : MemLp
      (fun x => fderiv ℝ (u n) x (EuclideanSpace.single j 1)) 2 (volume.restrict S) := by
    apply MemLp.of_bound (measurable_fderiv_apply_const ℝ (u n) _).aestronglyMeasurable (L n)
    exact Eventually.of_forall fun x => by
      have h := (fderiv ℝ (u n) x).le_opNorm (EuclideanSpace.single j 1)
      simpa only [PiLp.norm_single, norm_one, mul_one] using
        h.trans (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (huLip n))
          (norm_nonneg _))
  have hderS (j : Fin 2) : Tendsto (fun n => eLpNorm (fun x =>
      fderiv ℝ (u n) x (EuclideanSpace.single j 1) -
        WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
      2 (volume.restrict S)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hder j)
      (fun n => zero_le) (fun n => ?_)
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hSa)
  exact tendsto_integral_target_metric_energy_of_strong_approximation hS hSclosed hK A hA f u
    hu huK (ae_restrict_of_ae_restrict_of_subset hSΩ hfK)
    (ae_restrict_of_ae_restrict_of_subset hSa hae)
    (fun j x => WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) hG huD hderS

theorem exists_original_target_approximation_tendsto_metric_energy_on_subsets
    {K U : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (r : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (hr : ContDiffOn ℝ ∞ r U)
    (hrK : MapsTo r U K) (hfix : ∀ y ∈ K, r y = y)
    {Ω : Set (EuclideanSpace ℝ (Fin 2))} (hΩ : IsOpen Ω)
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ ι}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (hfK : ∀ᵐ x ∂volume.restrict Ω, f x ∈ K)
    {c : EuclideanSpace ℝ (Fin 2)} {a : ℝ} (hball : Metric.closedBall c a ⊆ Ω) :
    ∃ (u : ℕ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ ι) (L : ℕ → ℝ≥0)
      (B : ℝ), 0 ≤ B ∧
      (∀ n, LipschitzWith (L n) (u n)) ∧
      (∀ n, ContDiffOn ℝ ∞ (u n) (Metric.closedBall c a)) ∧
      (∀ n, MapsTo (u n) (Metric.closedBall c a) K) ∧
      Tendsto (fun n => eLpNorm (fun x => u n x - f x) 2
        (volume.restrict (Metric.ball c a))) atTop (𝓝 0) ∧
      (∀ j : Fin 2, Tendsto (fun n => eLpNorm (fun x =>
        fderiv ℝ (u n) x (EuclideanSpace.single j 1) -
          WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        2 (volume.restrict (Metric.ball c a))) atTop (𝓝 0)) ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball c a),
        Tendsto (fun n => u n x) atTop (𝓝 (f x))) ∧
      (∀ n, (∫ x in Metric.ball c a, ‖fderiv ℝ (u n) x‖ ^ 2) ≤ B) ∧
      ∀ (S : Set (EuclideanSpace ℝ (Fin 2))), MeasurableSet S → S ⊆ Metric.ball c a →
        ∀ A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ]
          EuclideanSpace ℝ ι →L[ℝ] ℝ, ContinuousOn A K →
          Tendsto (fun n => ∑ j : Fin 2, ∫ x in S,
            A (u n x) (fderiv ℝ (u n) x (EuclideanSpace.single j 1))
              (fderiv ℝ (u n) x (EuclideanSpace.single j 1))) atTop
            (𝓝 (∑ j : Fin 2, ∫ x in S,
              A (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
                (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)))) := by
  let A := fun _ : EuclideanSpace ℝ ι =>
    (innerSL ℝ : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
  obtain ⟨u, L, B, hB, huLip, hu, huK, hval, hder, hae, hbound, _⟩ :=
    exists_globally_lipschitz_target_approximation_tendsto_energy_on_ball
      hK hU hKU r hr hrK hfix hΩ hf hfK hball A continuousOn_const
  refine ⟨u, L, B, hB, huLip, hu, huK, hval, hder, hae, hbound, ?_⟩
  intro S hS hSa A hA
  exact tendsto_original_metric_energy_on_subset_of_strong_approximation hf hball hK hfK u L
    huLip (fun n => (hu n).of_le (by simp)) huK hae hder hS hSa A hA

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
