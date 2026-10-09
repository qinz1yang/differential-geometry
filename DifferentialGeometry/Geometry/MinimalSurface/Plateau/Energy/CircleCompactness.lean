import DifferentialGeometry.Analysis.Integration.Integral.Subsequence
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.IntrinsicPolar
import DifferentialGeometry.Geometry.Metric.CurveEnergy.Compactness
import DifferentialGeometry.Analysis.Sobolev.Interval.EnergyCompactness
import DifferentialGeometry.Geometry.Metric.CurveEnergy.Composition
import DifferentialGeometry.Topology.LoopSpace.CircleParameter
import DifferentialGeometry.Topology.UniformConvergence

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem ae_exists_subseq_uniform_circle_energy_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : ℕ → ℂ → M)
    (hLip : ∀ n, ∃ K : ℝ≥0, ∀ z z',
      riemannianEDistOf g (u n z) (u n z') ≤ (K : ℝ≥0∞) * edist z z')
    {r R B : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (henergy : ∀ n, (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, diskMapEnergyDensity g (u n) z) ≤ B) :
    ∀ᵐ ρ ∂volume.restrict (Icc r R),
      (∀ n, IntegrableOn (fun t => (riemannianCurveSpeed g
        (fun s => u n (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t) ^ 2) (Icc (0 : ℝ) 1)) ∧
      ∃ (σ : ℕ → ℕ) (C : ℝ), StrictMono σ ∧ ∀ n,
        (∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g
          (fun s => u (σ n) (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t) ^ 2) ≤ C := by
  choose K hK using hLip
  have hdata (n : ℕ) := integrableOn_and_integral_circle_speed_sq_le_disk_energy g (hK n) hr hrR
  let d : ℕ → ℝ → ℝ := fun n ρ => ∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g
    (fun s => u n (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t) ^ 2
  have hb := MeasureTheory.ae_exists_subseq_bounded_of_integral_bound
    (fun n => (hdata n).2.1)
    (fun n => Eventually.of_forall fun ρ => integral_nonneg fun _ => sq_nonneg _)
    (fun n => ((hdata n).2.2).trans
      (mul_le_mul_of_nonneg_left (henergy n) (by have hR := hr.trans_le hrR; positivity)))
  filter_upwards [hb, ae_all_iff.mpr (fun n => (hdata n).1)] with ρ hρ hint
  exact ⟨hint, hρ⟩

theorem exists_radius_subseq_circle_energy_bound_and_ae_tendsto
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : ℕ → ℂ → M) (v : ℂ → M)
    (hLip : ∀ n, ∃ K : ℝ≥0, ∀ z z',
      riemannianEDistOf g (u n z) (u n z') ≤ (K : ℝ≥0∞) * edist z z')
    {r R B : ℝ} (hr : 0 < r) (hrR : r < R)
    (hae : ∀ᵐ z ∂volume.restrict {z : ℂ | ‖z‖ ∈ Icc r R},
      Tendsto (fun n => u n z) atTop (𝓝 (v z)))
    (henergy : ∀ n, (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, diskMapEnergyDensity g (u n) z) ≤ B) :
    ∃ ρ ∈ Icc r R, ∃ (σ : ℕ → ℕ) (C : ℝ), StrictMono σ ∧
      (∀ n, IntegrableOn (fun t => (riemannianCurveSpeed g
        (fun s => u (σ n) (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t) ^ 2) (Icc (0 : ℝ) 1)) ∧
      (∀ n, (∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g
        (fun s => u (σ n) (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t) ^ 2) ≤ C) ∧
      (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
        Tendsto (fun n => u (σ n) (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) atTop
          (𝓝 (v (circleMap 0 ρ (2 * Real.pi * t - Real.pi))))) := by
  let μ := volume.restrict (Icc r R)
  have hμ : μ ≠ 0 := by
    intro h
    have hz := congrArg (fun m : Measure ℝ => m univ) h
    have hp : 0 < volume (Icc r R) := by simp [Real.volume_Icc, hrR]
    exact hp.ne' (by
      simpa only [μ, Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using hz)
  let : NeZero μ := ⟨hμ⟩
  have hb := ae_exists_subseq_uniform_circle_energy_bound g u hLip hr hrR.le henergy
  have hs : MeasurableSet {z : ℂ | ‖z‖ ∈ Icc r R} :=
    measurableSet_Icc.preimage continuous_norm.measurable
  have hc := Analysis.ae_ae_comp_circleMap_normalized
    ((ae_restrict_iff' hs).mp hae) hr (R := R)
  obtain ⟨ρ, hρ, hρb, hρc⟩ := (ae_restrict_mem measurableSet_Icc |>.and (hb.and hc)).exists
  obtain ⟨σ, C, hσ, hσb⟩ := hρb.2
  exact ⟨ρ, hρ, σ, C, hσ, fun n => hρb.1 (σ n), hσb,
    hρc.mono fun t ht => (ht (by
      change ‖circleMap 0 ρ (2 * Real.pi * t - Real.pi)‖ ∈ Icc r R
      simpa only [norm_circleMap_zero, abs_of_pos (hr.trans_le hρ.1)] using hρ)).comp
        hσ.tendsto_atTop⟩

end DifferentialGeometry.Geometry

end

end

section

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M X F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M] [PseudoMetricSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_radius_subseq_uniform_circle_convergence_of_paired_energy_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (ι : X → M) (hι : ∀ x y, edist x y = riemannianEDistOf g (ι x) (ι y))
    (u : ℕ → ℂ → X) (v : ℂ → X) (q : ℕ → ℂ → F) (f : ℂ → F)
    (huLip : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (u n))
    (hqLip : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (q n))
    {r R B : ℝ} (hr : 0 < r) (hrR : r < R)
    (hv : ContinuousOn v {z : ℂ | ‖z‖ ∈ Icc r R})
    (hf : ContinuousOn f {z : ℂ | ‖z‖ ∈ Icc r R})
    (huae : ∀ᵐ z ∂volume.restrict {z : ℂ | ‖z‖ ∈ Icc r R},
      Tendsto (fun n => u n z) atTop (𝓝 (v z)))
    (hqae : ∀ᵐ z ∂volume.restrict {z : ℂ | ‖z‖ ∈ Icc r R},
      Tendsto (fun n => q n z) atTop (𝓝 (f z)))
    (henergy : ∀ n,
      (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, diskMapEnergyDensity g (ι ∘ u n) z) +
        (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, ‖fderiv ℝ (q n) z‖ ^ 2) ≤ B) :
    ∃ ρ ∈ Icc r R, ∃ (σ : ℕ → ℕ) (C : ℝ), StrictMono σ ∧
      (∀ n, IntegrableOn (fun t => (riemannianCurveSpeed g
        (fun s => ι (u (σ n) (circleMap 0 ρ (2 * Real.pi * s - Real.pi)))) t) ^ 2)
          (Icc (0 : ℝ) 1)) ∧
      (∀ n, IntegrableOn (fun t =>
        ‖deriv (fun s => q (σ n) (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t‖ ^ 2)
          (Icc (0 : ℝ) 1)) ∧
      (∀ n,
        (∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g
          (fun s => ι (u (σ n) (circleMap 0 ρ (2 * Real.pi * s - Real.pi)))) t) ^ 2) +
        (∫ t in Icc (0 : ℝ) 1,
          ‖deriv (fun s => q (σ n) (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t‖ ^ 2) ≤ C) ∧
      TendstoUniformlyOn (fun n t => u (σ n) (circleMap 0 ρ (2 * Real.pi * t - Real.pi)))
        (fun t => v (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) atTop (Icc (0 : ℝ) 1) ∧
      TendstoUniformlyOn (fun n t => q (σ n) (circleMap 0 ρ (2 * Real.pi * t - Real.pi)))
        (fun t => f (circleMap 0 ρ (2 * Real.pi * t - Real.pi))) atTop (Icc (0 : ℝ) 1) := by
  classical
  choose Ku hKu using huLip
  choose Kq hKq using hqLip
  have hMLip (n : ℕ) : ∀ z z', riemannianEDistOf g (ι (u n z)) (ι (u n z')) ≤
      (Ku n : ℝ≥0∞) * edist z z' := by
    intro z z'
    rw [← hι]
    exact hKu n z z'
  let c : ℝ → ℝ → ℂ := fun ρ t => circleMap 0 ρ (2 * Real.pi * t - Real.pi)
  have hc (ρ : ℝ) : ∃ K : ℝ≥0, LipschitzWith K (c ρ) := by
    have hθ : LipschitzWith (Real.nnabs (2 * Real.pi))
        (fun t : ℝ => 2 * Real.pi * t - Real.pi) := by
      apply LipschitzWith.of_dist_le_mul
      intro s t
      simp only [Real.dist_eq, sub_sub_sub_cancel_right, ← mul_sub, abs_mul,
        Real.coe_nnabs, le_refl]
    exact ⟨_, (lipschitzWith_circleMap 0 ρ).comp hθ⟩
  let dU : ℕ → ℝ → ℝ := fun n ρ => ∫ t in Icc (0 : ℝ) 1,
    (riemannianCurveSpeed g (ι ∘ u n ∘ c ρ) t) ^ 2
  let dQ : ℕ → ℝ → ℝ := fun n ρ => ∫ t in Icc (0 : ℝ) 1,
    ‖deriv (q n ∘ c ρ) t‖ ^ 2
  have hdU (n : ℕ) := integrableOn_and_integral_circle_speed_sq_le_disk_energy g (hMLip n) hr hrR.le
  have hdQ (n : ℕ) := Analysis.integrableOn_integral_norm_sq_deriv_circleMap (hKq n) hr hrR.le
  have hQint (n : ℕ) (ρ : ℝ) : IntegrableOn (fun t => ‖deriv (q n ∘ c ρ) t‖ ^ 2)
      (Icc (0 : ℝ) 1) := by
    obtain ⟨K, hK⟩ := hc ρ
    let : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
      isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
    have hLip := (hKq n).comp hK
    exact (MemLp.of_bound (aestronglyMeasurable_deriv (q n ∘ c ρ) _)
      (Kq n * K) (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hLip)).norm.integrable_sq
  have hdU0 (n : ℕ) (ρ : ℝ) : 0 ≤ dU n ρ := integral_nonneg fun _ => sq_nonneg _
  have hdQ0 (n : ℕ) (ρ : ℝ) : 0 ≤ dQ n ρ := integral_nonneg fun _ => sq_nonneg _
  have hUi (n : ℕ) : IntegrableOn (dU n) (Icc r R) := (hdU n).2.1
  have hQi (n : ℕ) : IntegrableOn (dQ n) (Icc r R) := hdQ n
  have hsumint (n : ℕ) : IntegrableOn (fun ρ => dU n ρ + dQ n ρ) (Icc r R) :=
    (hUi n).add (hQi n)
  have hsumbound (n : ℕ) : (∫ ρ in Icc r R, dU n ρ + dQ n ρ) ≤ (4 * Real.pi * R) * B := by
    rw [integral_add (hUi n) (hQi n)]
    have hqupper := Analysis.integral_norm_sq_deriv_circleMap_radial_le (hKq n) hr hrR.le
    have hqnonneg : 0 ≤ ∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, ‖fderiv ℝ (q n) z‖ ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    have hR : 0 < R := hr.trans hrR
    have hfactor : 2 * Real.pi * R ≤ 4 * Real.pi * R := by
      nlinarith [mul_pos Real.pi_pos hR]
    calc
      _ ≤ (4 * Real.pi * R) *
          (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, diskMapEnergyDensity g (ι ∘ u n) z) +
          (2 * Real.pi * R) *
          (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, ‖fderiv ℝ (q n) z‖ ^ 2) :=
        add_le_add (hdU n).2.2 hqupper
      _ ≤ (4 * Real.pi * R) *
          ((∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, diskMapEnergyDensity g (ι ∘ u n) z) +
          (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, ‖fderiv ℝ (q n) z‖ ^ 2)) := by
        rw [mul_add]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hfactor hqnonneg)
      _ ≤ _ := mul_le_mul_of_nonneg_left (henergy n) (by positivity)
  let μ := volume.restrict (Icc r R)
  have hμ : μ ≠ 0 := by
    intro h
    have hz := congrArg (fun m : Measure ℝ => m univ) h
    have hp : 0 < volume (Icc r R) := by simp [Real.volume_Icc, hrR]
    exact hp.ne' (by
      simpa only [μ, Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] using hz)
  let : NeZero μ := ⟨hμ⟩
  have hb := MeasureTheory.ae_exists_subseq_bounded_of_integral_bound hsumint
    (fun n => Eventually.of_forall fun ρ => add_nonneg (hdU0 n ρ) (hdQ0 n ρ)) hsumbound
  have hs : MeasurableSet {z : ℂ | ‖z‖ ∈ Icc r R} :=
    measurableSet_Icc.preimage continuous_norm.measurable
  have huconv := Analysis.ae_ae_comp_circleMap_normalized
    ((ae_restrict_iff' hs).mp huae) hr (R := R)
  have hqconv := Analysis.ae_ae_comp_circleMap_normalized
    ((ae_restrict_iff' hs).mp hqae) hr (R := R)
  have htraceint := ae_all_iff.mpr (fun n => (hdU n).1)
  obtain ⟨ρ, hρ, hρb, hρint, hρu, hρq⟩ :=
    (ae_restrict_mem measurableSet_Icc |>.and (hb.and (htraceint.and (huconv.and hqconv)))).exists
  obtain ⟨σ, C, hσ, hσbound⟩ := hρb
  have hcloop (t : ℝ) : c ρ t ∈ {z : ℂ | ‖z‖ ∈ Icc r R} := by
    simpa only [mem_ofPred_eq, c, norm_circleMap_zero, abs_of_pos (hr.trans_le hρ.1)] using hρ
  obtain ⟨Kc, hKc⟩ := hc ρ
  have huAE : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      Tendsto (fun n => u (σ n) (c ρ t)) atTop (𝓝 (v (c ρ t))) :=
    hρu.mono fun t ht => (ht (hcloop t)).comp hσ.tendsto_atTop
  have hqAE : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      Tendsto (fun n => q (σ n) (c ρ t)) atTop (𝓝 (f (c ρ t))) :=
    hρq.mono fun t ht => (ht (hcloop t)).comp hσ.tendsto_atTop
  have huBound (n : ℕ) : dU (σ n) ρ ≤ C :=
    (le_add_of_nonneg_right (hdQ0 (σ n) ρ)).trans (hσbound n)
  have hqBound (n : ℕ) : dQ (σ n) ρ ≤ C :=
    (le_add_of_nonneg_left (hdU0 (σ n) ρ)).trans (hσbound n)
  have huCurveLip (n : ℕ) : ∃ K : ℝ≥0, ∀ s t,
      riemannianEDistOf g (ι (u (σ n) (c ρ s))) (ι (u (σ n) (c ρ t))) ≤
        (K : ℝ≥0∞) * edist s t := by
    have hcomp := (hKu (σ n)).comp hKc
    exact ⟨_, fun s t => by rw [← hι]; exact hcomp s t⟩
  refine ⟨ρ, hρ, σ, C, hσ, fun n => hρint (σ n), fun n => hQint (σ n) ρ,
    hσbound, ?_, ?_⟩
  · exact tendstoUniformlyOn_of_ae_tendsto_of_intrinsic_curve_energy_bound g ι hι
      (fun n => u (σ n) ∘ c ρ) (v ∘ c ρ) huCurveLip zero_lt_one
      (fun n => hρint (σ n)) huBound
      (hv.comp hKc.continuous.continuousOn (fun t _ => hcloop t)) huAE
  · exact Analysis.tendstoUniformlyOn_of_ae_tendsto_of_curve_energy_bound
      (fun n => q (σ n) ∘ c ρ) (f ∘ c ρ)
      (fun n => ⟨_, (hKq (σ n)).comp hKc⟩) zero_lt_one hqBound
      (hf.comp hKc.continuous.continuousOn (fun t _ => hcloop t)) hqAE

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M X F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M] [PseudoMetricSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_compact_probe_circle_recovery_data
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (ι : X → M) (hι : ∀ x y, edist x y = riemannianEDistOf g (ι x) (ι y))
    {P : M → F} (hP : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 P) (hPc : HasCompactSupport P)
    (ψ : F → M) {O : Set X} (hO : IsOpen O)
    (hleft : ∀ x ∈ O, ψ (P (ι x)) = ι x)
    (u : ℕ → ℂ → X) (V : ℂ → X) (q : ℕ → ℂ → F)
    (huLip : ∀ n, ∃ L : ℝ≥0, LipschitzWith L (u n))
    (hqLip : ∀ n, ∃ L : ℝ≥0, LipschitzWith L (q n))
    {r R B : ℝ} (hr : 0 < r) (hrR : r < R)
    (hV : ContinuousOn V {z : ℂ | ‖z‖ ∈ Icc r R})
    (hVO : MapsTo V {z : ℂ | ‖z‖ ∈ Icc r R} O)
    {K : Set F} (hVK : MapsTo (fun z => P (ι (V z)))
      {z : ℂ | ‖z‖ ∈ Icc r R} (interior K))
    (huae : ∀ᵐ z ∂volume.restrict {z : ℂ | ‖z‖ ∈ Icc r R},
      Tendsto (fun n => u n z) atTop (𝓝 (V z)))
    (hqae : ∀ᵐ z ∂volume.restrict {z : ℂ | ‖z‖ ∈ Icc r R},
      Tendsto (fun n => q n z) atTop (𝓝 (P (ι (V z)))))
    (henergy : ∀ n,
      (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, diskMapEnergyDensity g (ι ∘ u n) z) +
        (∫ z in {z : ℂ | ‖z‖ ∈ Icc r R}, ‖fderiv ℝ (q n) z‖ ^ 2) ≤ B) :
    ∃ ρ ∈ Icc r R, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ Kp : ℕ → ℝ≥0, (∀ n, LipschitzWith (Kp n) (fun z => P (ι (u (σ n) z)))) ∧
      Tendsto (fun n => ∫ t in Icc (0 : ℝ) 1,
        ‖q (σ n) (circleMap 0 ρ (2 * Real.pi * t - Real.pi)) -
          P (ι (u (σ n) (circleMap 0 ρ (2 * Real.pi * t - Real.pi))))‖ ^ 2) atTop (𝓝 0) ∧
      (∃ D : ℝ, ∀ n, (∫ t in Icc (0 : ℝ) 1,
        ‖deriv (fun s => q (σ n) (circleMap 0 ρ (2 * Real.pi * s - Real.pi))) t‖ ^ 2 +
          ‖deriv (fun s => P (ι (u (σ n)
            (circleMap 0 ρ (2 * Real.pi * s - Real.pi))))) t‖ ^ 2) ≤ D) ∧
      (∀ᶠ n in atTop, MapsTo (fun z => P (ι (u (σ n) z))) (sphere (0 : ℂ) ρ) K) ∧
      (∀ᶠ n in atTop, ∀ z ∈ sphere (0 : ℂ) ρ,
        ψ (P (ι (u (σ n) z))) = ι (u (σ n) z)) := by
  classical
  obtain ⟨CP, _, hCP⟩ := exists_riemannian_lipschitz_of_contMDiff_of_hasCompactSupport g hP hPc
  let Q : X → F := P ∘ ι
  have hQ : LipschitzWith CP Q := by
    intro x y
    exact (hCP (ι x) (ι y)).trans_eq (by rw [← hι])
  choose Cu hCu using huLip
  choose Cq hCq using hqLip
  have hQV : ContinuousOn (Q ∘ V) {z : ℂ | ‖z‖ ∈ Icc r R} :=
    hQ.continuous.comp_continuousOn hV
  obtain ⟨ρ, hρ, σ, C, hσ, huInt, hqInt, hsum, huUnif, hqUnif⟩ :=
    exists_radius_subseq_uniform_circle_convergence_of_paired_energy_bound
      g ι hι u V q (Q ∘ V) (fun n => ⟨Cu n, hCu n⟩) (fun n => ⟨Cq n, hCq n⟩)
      hr hrR hV hQV huae hqae henergy
  let c : ℝ → ℂ := fun t => circleMap 0 ρ (2 * Real.pi * t - Real.pi)
  have hρpos := hr.trans_le hρ.1
  have hc : Continuous c := by fun_prop
  have hcAnn (t : ℝ) : c t ∈ {z : ℂ | ‖z‖ ∈ Icc r R} := by
    simpa only [c, mem_ofPred_eq, norm_circleMap_zero, abs_of_pos hρpos] using hρ
  have hVcurve : ContinuousOn (V ∘ c) (Icc (0 : ℝ) 1) :=
    hV.comp hc.continuousOn (fun t _ => hcAnn t)
  have hQcurve : ContinuousOn (Q ∘ V ∘ c) (Icc (0 : ℝ) 1) :=
    hQ.continuous.comp_continuousOn hVcurve
  have hpUnif : TendstoUniformlyOn (fun n t => Q (u (σ n) (c t)))
      (fun t => Q (V (c t))) atTop (Icc (0 : ℝ) 1) :=
    hQ.uniformContinuous.comp_tendstoUniformlyOn huUnif
  have hpLip (n : ℕ) : LipschitzWith (CP * Cu (σ n)) (Q ∘ u (σ n)) :=
    hQ.comp (hCu (σ n))
  have hgap := Analysis.tendsto_integral_curve_gap_sq_of_uniform_convergence
    (fun n => (hCq (σ n)).continuous.comp hc)
    (fun n => (hpLip n).continuous.comp hc) hqUnif hpUnif
  have hpKcurve := hpUnif.eventually_mapsTo_of_isCompact isCompact_Icc hQcurve isOpen_interior
    (fun t _ => hVK (hcAnn t))
  have huOcurve := huUnif.eventually_mapsTo_of_isCompact isCompact_Icc hVcurve hO
    (fun t _ => hVO (hcAnn t))
  have hpK : ∀ᶠ n in atTop, MapsTo (fun z => P (ι (u (σ n) z))) (sphere (0 : ℂ) ρ) K := by
    filter_upwards [hpKcurve] with n hn z hz
    obtain ⟨t, ht, rfl⟩ := Analysis.exists_circle_parameter_eq_of_mem_sphere hρpos hz
    exact interior_subset (hn ht)
  have hboundary : ∀ᶠ n in atTop, ∀ z ∈ sphere (0 : ℂ) ρ,
      ψ (P (ι (u (σ n) z))) = ι (u (σ n) z) := by
    filter_upwards [huOcurve] with n hn z hz
    obtain ⟨t, ht, rfl⟩ := Analysis.exists_circle_parameter_eq_of_mem_sphere hρpos hz
    exact hleft _ (hn ht)
  obtain ⟨Ccurve, _, hcurve⟩ := exists_curve_energy_bound_of_contMDiff_of_hasCompactSupport g hP hPc
  have hcLip : ∃ L : ℝ≥0, LipschitzWith L c := by
    have hθ : LipschitzWith (Real.nnabs (2 * Real.pi))
        (fun t : ℝ => 2 * Real.pi * t - Real.pi) := by
      apply LipschitzWith.of_dist_le_mul
      intro s t
      simp only [Real.dist_eq, sub_sub_sub_cancel_right, ← mul_sub, abs_mul,
        Real.coe_nnabs, le_refl]
    exact ⟨_, (lipschitzWith_circleMap 0 ρ).comp hθ⟩
  obtain ⟨Lc, hLc⟩ := hcLip
  have hOrigLip (n : ℕ) : ∀ s t,
      riemannianEDistOf g (ι (u (σ n) (c s))) (ι (u (σ n) (c t))) ≤
        (Cu (σ n) * Lc : ℝ≥0∞) * edist s t := by
    intro s t
    rw [← hι]
    exact ((hCu (σ n)).comp hLc) s t
  have hpInt (n : ℕ) := (hcurve (ι ∘ u (σ n) ∘ c) (Cu (σ n) * Lc)
    (hOrigLip n)).2.2 (Icc (0 : ℝ) 1) (huInt n)
  have hbound (n : ℕ) : (∫ t in Icc (0 : ℝ) 1,
      ‖deriv (fun s => q (σ n) (c s)) t‖ ^ 2 +
        ‖deriv (fun s => P (ι (u (σ n) (c s)))) t‖ ^ 2) ≤
        (1 + (Ccurve : ℝ) ^ 2) * C := by
    have hu0 : 0 ≤ ∫ t in Icc (0 : ℝ) 1,
        (riemannianCurveSpeed g (ι ∘ u (σ n) ∘ c) t) ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hq0 : 0 ≤ ∫ t in Icc (0 : ℝ) 1,
        ‖deriv (fun s => q (σ n) (c s)) t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hsum' := hsum n
    change (∫ t in Icc (0 : ℝ) 1,
      (riemannianCurveSpeed g (ι ∘ u (σ n) ∘ c) t) ^ 2) +
      (∫ t in Icc (0 : ℝ) 1, ‖deriv (fun s => q (σ n) (c s)) t‖ ^ 2) ≤ C at hsum'
    have huB := (le_add_of_nonneg_right hq0).trans hsum'
    have hqB := (le_add_of_nonneg_left hu0).trans hsum'
    have hqi : IntegrableOn (fun t => ‖deriv (fun s => q (σ n) (c s)) t‖ ^ 2)
        (Icc (0 : ℝ) 1) := hqInt n
    have hpi : IntegrableOn (fun t => ‖deriv (fun s => P (ι (u (σ n) (c s)))) t‖ ^ 2)
        (Icc (0 : ℝ) 1) := (hpInt n).1
    rw [integral_add hqi hpi]
    exact (add_le_add hqB ((hpInt n).2.trans
      (mul_le_mul_of_nonneg_left huB (sq_nonneg _)))).trans_eq (by ring)
  exact ⟨ρ, hρ, σ, hσ, fun n => CP * Cu (σ n), hpLip, hgap,
    ⟨(1 + (Ccurve : ℝ) ^ 2) * C, hbound⟩, hpK, hboundary⟩

end DifferentialGeometry.Geometry

end

end
