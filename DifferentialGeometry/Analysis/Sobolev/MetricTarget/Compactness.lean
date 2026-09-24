import DifferentialGeometry.Analysis.Integration.Lp.CountableCompactness
import DifferentialGeometry.Analysis.Calculus.Cutoff.BallExhaustion
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Rellich.ComplexCutoff
import DifferentialGeometry.Analysis.Integration.Measure.MetricTargetConvergence

section

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev

theorem exists_ae_tendsto_subseq_of_dist_energy_bounded
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    {a : ℕ → X} (ha : DenseRange a) (U : ℕ → ℂ → X)
    (hU : ∀ n i, ∃ K : ℝ≥0, LipschitzWith K (fun z => dist (U n z) (a i)))
    {A B : ℕ → ℝ}
    (hA : ∀ n i, (∫ z in ball (0 : ℂ) 1, dist (U n z) (a i) ^ 2) ≤ A i)
    (hB : ∀ n i, (∫ z in ball (0 : ℂ) 1,
      ‖fderiv ℝ (fun w => dist (U n w) (a i)) z‖ ^ 2) ≤ B i) :
    let e := Complex.orthonormalBasisOneI.repr.symm
    ∃ (φ : ℕ → ℕ) (v : EuclideanSpace ℝ (Fin 2) → X), StrictMono φ ∧
      ∀ᵐ x ∂volume.restrict (ball 0 1),
        Tendsto (fun n => U (φ n) (e x)) atTop (𝓝 (v x)) := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let μ : Measure (EuclideanSpace ℝ (Fin 2)) := volume.restrict (ball 0 1)
  obtain ⟨η, hη, hηone⟩ := exists_contDiff_cutoff_sequence_ball (0 : ℂ) 1
  let f : ℕ → ℕ × ℕ → EuclideanSpace ℝ (Fin 2) → ℝ :=
    fun n i x => η i.2 (e x) * dist (U n (e x)) (a i.1)
  have hf : ∀ n i, MemLp (f n i) 2 μ := by
    intro n i
    obtain ⟨K, hK⟩ := hU n i.1
    have hcont : Continuous (f n i) :=
      ((hη i.2).1.continuous.comp e.continuous).mul (hK.continuous.comp e.continuous)
    obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) hcont.continuousOn
    have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_ne_top
    exact MemLp.of_bound hcont.aestronglyMeasurable C
      (ae_restrict_of_forall_mem measurableSet_ball
        fun x hx => hC x (ball_subset_closedBall hx))
  have hcompact : ∀ i (σ : ℕ → ℕ), StrictMono σ →
      ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ g : EuclideanSpace ℝ (Fin 2) → ℝ,
        MemLp g 2 μ ∧
        Tendsto (fun n => eLpNorm (f (σ (τ n)) i - g) 2 μ) atTop (𝓝 0) := by
    intro i σ _
    obtain ⟨τ, g, hτ, hg, hlim⟩ := rellich_kondrachov_seq_complex_cutoff_of_lipschitz
      (hη i.2).1 (hη i.2).2.1 (hη i.2).2.2.1
      (fun n z => dist (U (σ n) z) (a i.1))
      (fun n => hU (σ n) i.1) (fun n => hA (σ n) i.1) (fun n => hB (σ n) i.1)
    exact ⟨τ, hτ, g, hg, hlim⟩
  obtain ⟨φ, g, hφ, _, hfg⟩ := exists_seq_tendsto_ae_of_countable_Lp_subseq
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) f hf hcompact
  have hdist : ∀ i, ∀ᵐ x ∂μ, ∃ r : ℝ,
      Tendsto (fun n => dist (U (φ n) (e x)) (a i)) atTop (𝓝 r) := by
    intro i
    filter_upwards [hfg, ae_restrict_mem measurableSet_ball] with x hx hxball
    have hex : e x ∈ ball (0 : ℂ) 1 := by
      simpa only [mem_ball_zero_iff, e.norm_map] using hxball
    obtain ⟨j, hj⟩ := (hηone (e x) hex).exists
    refine ⟨g (i, j) x, ?_⟩
    simpa only [f, hj, one_mul] using hx (i, j)
  obtain ⟨v, hv⟩ := ha.exists_ae_tendsto_of_ae_tendsto_dist μ
    (fun n x => U (φ n) (e x)) hdist
  exact ⟨φ, v, hφ, hv⟩

theorem exists_aemeasurable_ae_tendsto_subseq_of_dist_energy_bounded
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {a : ℕ → X} (ha : DenseRange a) (U : ℕ → ℂ → X)
    (hU : ∀ n i, ∃ K : ℝ≥0, LipschitzWith K (fun z => dist (U n z) (a i)))
    {A B : ℕ → ℝ}
    (hA : ∀ n i, (∫ z in ball (0 : ℂ) 1, dist (U n z) (a i) ^ 2) ≤ A i)
    (hB : ∀ n i, (∫ z in ball (0 : ℂ) 1,
      ‖fderiv ℝ (fun w => dist (U n w) (a i)) z‖ ^ 2) ≤ B i) :
    let e := Complex.orthonormalBasisOneI.repr.symm
    ∃ (φ : ℕ → ℕ) (v : EuclideanSpace ℝ (Fin 2) → X), StrictMono φ ∧
      AEMeasurable v (volume.restrict (ball 0 1)) ∧
      ∀ᵐ x ∂volume.restrict (ball 0 1),
        Tendsto (fun n => U (φ n) (e x)) atTop (𝓝 (v x)) := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  obtain ⟨φ, v, hφ, hv⟩ := exists_ae_tendsto_subseq_of_dist_energy_bounded ha U hU hA hB
  have hcont : ∀ n, Continuous (U n) := by
    intro n
    apply continuous_iff_continuousAt.mpr
    intro z
    apply ha.tendsto_of_tendsto_dist
    intro i
    obtain ⟨K, hK⟩ := hU n i
    exact hK.continuous.continuousAt
  have hum : ∀ n, AEMeasurable (fun x => U (φ n) (e x)) (volume.restrict (ball 0 1)) :=
    fun n => ((hcont (φ n)).comp e.continuous).measurable.aemeasurable
  exact ⟨φ, v, hφ, aemeasurable_of_tendsto_metrizable_ae' hum hv, hv⟩

end DifferentialGeometry.Analysis.Sobolev

end

section

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

namespace DifferentialGeometry.Analysis.Sobolev

theorem exists_aemeasurable_ae_tendsto_subseq_complex_of_dist_energy_bounded
    {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {a : ℕ → X} (ha : DenseRange a) (U : ℕ → ℂ → X)
    (hU : ∀ n i, ∃ K : ℝ≥0, LipschitzWith K (fun z => dist (U n z) (a i)))
    {A B : ℕ → ℝ}
    (hA : ∀ n i, (∫ z in ball (0 : ℂ) 1, dist (U n z) (a i) ^ 2) ≤ A i)
    (hB : ∀ n i, (∫ z in ball (0 : ℂ) 1,
      ‖fderiv ℝ (fun w => dist (U n w) (a i)) z‖ ^ 2) ≤ B i) :
    ∃ (φ : ℕ → ℕ) (v : ℂ → X), StrictMono φ ∧
      AEMeasurable v (volume.restrict (ball (0 : ℂ) 1)) ∧
      ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
        Tendsto (fun n => U (φ n) z) atTop (𝓝 (v z)) := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  obtain ⟨φ, w, hφ, hwm, hw⟩ :=
    exists_aemeasurable_ae_tendsto_subseq_of_dist_energy_bounded ha U hU hA hB
  have hball : e.symm ⁻¹' ball (0 : EuclideanSpace ℝ (Fin 2)) 1 = ball (0 : ℂ) 1 := by
    ext z
    simp only [mem_preimage, mem_ball_zero_iff, e.symm.norm_map]
  have he : MeasurePreserving e.symm (volume.restrict (ball (0 : ℂ) 1))
      (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) 1)) := by
    simpa only [hball] using e.symm.measurePreserving.restrict_preimage
      (s := ball (0 : EuclideanSpace ℝ (Fin 2)) 1) measurableSet_ball
  refine ⟨φ, w ∘ e.symm, hφ, hwm.comp_quasiMeasurePreserving he.quasiMeasurePreserving, ?_⟩
  change ∀ᵐ x ∂volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 2)) 1),
    Tendsto (fun n => U (φ n) (e x)) atTop (𝓝 (w x)) at hw
  simpa only [Function.comp_apply, e.apply_symm_apply] using he.quasiMeasurePreserving.ae hw

end DifferentialGeometry.Analysis.Sobolev

end
