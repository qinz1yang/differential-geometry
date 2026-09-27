import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.LocalComparison
import DifferentialGeometry.Analysis.Integration.Lp.MovingBall
import Mathlib.Topology.Sequences

noncomputable section

open Manifold Set MeasureTheory Filter
open DifferentialGeometry.Topology
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.Geometry

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem sum_integral_quadratic_lp_columns_eq
    {b ρ : ℝ} (hρb : ρ ≤ b) (A : ℂ → F →L[ℝ] F →L[ℝ] ℝ)
    (hA : AEStronglyMeasurable A (volume.restrict (Metric.closedBall (0 : ℂ) b)))
    {C : ℝ} (hC : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) b), ‖A z‖ ≤ C)
    (f : ℂ → F) (G : Fin 2 → Lp F 2 (volume.restrict (Metric.closedBall (0 : ℂ) b)))
    (hG : ∀ j, (G j : ℂ → F) =ᵐ[volume.restrict (Metric.closedBall (0 : ℂ) b)]
      (fun z => fderiv ℝ f z (![1, Complex.I] j))) :
    (∑ j : Fin 2, ∫ z in Metric.closedBall (0 : ℂ) ρ,
      A z (G j z) (G j z) ∂volume.restrict (Metric.closedBall (0 : ℂ) b)) =
      2 * ∫ z in Metric.closedBall (0 : ℂ) ρ,
        (A z (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
          A z (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2 := by
  let μ := volume.restrict (Metric.closedBall (0 : ℂ) b)
  have hrestrict : μ.restrict (Metric.closedBall (0 : ℂ) ρ) =
      volume.restrict (Metric.closedBall (0 : ℂ) ρ) :=
    Measure.restrict_restrict_of_subset (Metric.closedBall_subset_closedBall hρb)
  have hbil (j : Fin 2) : Integrable (fun z => A z (G j z) (G j z)) μ :=
    integrable_bilinear_of_apply_aestronglyMeasurable A
      (fun x y => (hA.apply_continuousLinearMap x).apply_continuousLinearMap y)
      hC (Lp.memLp (G j)) (Lp.memLp (G j))
  have hi (j : Fin 2) : IntegrableOn (fun z =>
      A z (fderiv ℝ f z (![1, Complex.I] j)) (fderiv ℝ f z (![1, Complex.I] j)))
      (Metric.closedBall (0 : ℂ) ρ) := by
    have hi := (hbil j).integrableOn (s := Metric.closedBall (0 : ℂ) ρ)
    have heq : (fun z => A z (G j z) (G j z)) =ᵐ[μ.restrict (Metric.closedBall (0 : ℂ) ρ)]
        (fun z => A z (fderiv ℝ f z (![1, Complex.I] j))
          (fderiv ℝ f z (![1, Complex.I] j))) := by
      filter_upwards [ae_restrict_of_ae (hG j)] with z hz
      rw [hz]
    have hi' := hi.congr heq
    rwa [hrestrict] at hi'
  have heq (j : Fin 2) :
      (∫ z in Metric.closedBall (0 : ℂ) ρ, A z (G j z) (G j z) ∂μ) =
        ∫ z in Metric.closedBall (0 : ℂ) ρ,
          A z (fderiv ℝ f z (![1, Complex.I] j)) (fderiv ℝ f z (![1, Complex.I] j)) := by
    trans ∫ z in Metric.closedBall (0 : ℂ) ρ,
      A z (fderiv ℝ f z (![1, Complex.I] j)) (fderiv ℝ f z (![1, Complex.I] j)) ∂μ
    · apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (hG j)] with z hz
      rw [hz]
    · rw [hrestrict]
  change (∑ j : Fin 2, ∫ z in Metric.closedBall (0 : ℂ) ρ, A z (G j z) (G j z) ∂μ) = _
  simp_rw [heq]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [integral_div, integral_add (by simpa only [IntegrableOn, Matrix.cons_val_zero] using hi 0)
    (by simpa only [IntegrableOn, Matrix.cons_val_one, Matrix.cons_val_zero] using hi 1)]
  ring

end Normed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exists_pullback_quadratic_weak_limit_comparison
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Φ : M → F} (hΦ : Continuous Φ)
    {r : F → M} {U : Set F} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ r U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse r Φ)
    {γ : freeLoop M} (τ : ℕ → C(loopCircle, loopCircle))
    (hτ : ∀ n, IsWeaklyMonotoneOnce (τ n))
    (u v : ℕ → ℂ → F) (Ku Kv : ℕ → ℝ≥0)
    (hu : ∀ n, LipschitzWith (Ku n) (u n)) (hv : ∀ n, LipschitzWith (Kv n) (v n))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb1 : b ≤ 1)
    (huK : ∀ n, MapsTo (u n) (Metric.closedBall (0 : ℂ) 1) (range Φ))
    (hvK : ∀ n, MapsTo (v n) (Metric.closedBall (0 : ℂ) b) (range Φ))
    (htrace : ∀ n θ, u n (diskBoundary θ) = Φ (γ (τ n θ)))
    (hgap : Tendsto (fun n => ∫ z in {z : ℂ | ‖z‖ ∈ Icc a b},
      ‖u n z - v n z‖ ^ 2) atTop (𝓝 0))
    {B : ℝ} (henergy : ∀ n, (∫ z in {z : ℂ | ‖z‖ ∈ Icc a b},
      ‖fderiv ℝ (u n) z‖ ^ 2 + ‖fderiv ℝ (v n) z‖ ^ 2) ≤ B)
    {V : Set F} (hV : IsOpen V) (hKV : range Φ ⊆ V)
    (T : F → F) (hT : Differentiable ℝ T) {L : ℝ} (hL : ∀ x, ‖fderiv ℝ T x‖ ≤ L)
    (hTK : MapsTo T V (range Φ)) (hfix : ∀ y ∈ range Φ, T y = y)
    (hmin : Tendsto (fun n => ∫ z in Metric.closedBall (0 : ℂ) 1,
      (pullbackMetricCoefficients g r (u n z)
          (fderiv ℝ (u n) z 1) (fderiv ℝ (u n) z 1) +
        pullbackMetricCoefficients g r (u n z)
          (fderiv ℝ (u n) z Complex.I) (fderiv ℝ (u n) z Complex.I)) / 2) atTop
      (𝓝 (sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
        weaklyMonotoneDiskCompetitors g γ))))
    (u₀ v₀ : ℂ → F)
    (hu₀ : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) b),
      Tendsto (fun n => u n z) atTop (𝓝 (u₀ z)))
    (hv₀ : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) b),
      Tendsto (fun n => v n z) atTop (𝓝 (v₀ z)))
    (hu₀K : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) b), u₀ z ∈ range Φ)
    (hv₀K : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) b), v₀ z ∈ range Φ)
    (Gu Hv : Fin 2 → ℕ → Lp F 2 (volume.restrict (Metric.closedBall (0 : ℂ) b)))
    (G₀ H₀ : Fin 2 → Lp F 2 (volume.restrict (Metric.closedBall (0 : ℂ) b)))
    (hGu : ∀ j n, (Gu j n : ℂ → F) =ᵐ[volume.restrict (Metric.closedBall (0 : ℂ) b)]
      (fun z => fderiv ℝ (u n) z (![1, Complex.I] j)))
    (hHv : ∀ j n, (Hv j n : ℂ → F) =ᵐ[volume.restrict (Metric.closedBall (0 : ℂ) b)]
      (fun z => fderiv ℝ (v n) z (![1, Complex.I] j)))
    (hweak : ∀ j (ℓ : Lp F 2 (volume.restrict (Metric.closedBall (0 : ℂ) b)) →L[ℝ] ℝ),
      Tendsto (fun n => ℓ (Gu j n)) atTop (𝓝 (ℓ (G₀ j))))
    (hstrong : ∀ j, Tendsto (Hv j) atTop (𝓝 (H₀ j))) :
    ∃ ρ ∈ Icc a b,
      (∑ j : Fin 2, ∫ z in Metric.closedBall (0 : ℂ) ρ,
        pullbackMetricCoefficients g r (u₀ z) (G₀ j z) (G₀ j z)) ≤
        ∑ j : Fin 2, ∫ z in Metric.closedBall (0 : ℂ) ρ,
          pullbackMetricCoefficients g r (v₀ z) (H₀ j z) (H₀ j z) := by
  let μ := volume.restrict (Metric.closedBall (0 : ℂ) b)
  let A := pullbackMetricCoefficients g r
  let e : (ℂ → F) → ℂ → ℝ := fun f z =>
    (A (f z) (fderiv ℝ f z 1) (fderiv ℝ f z 1) +
      A (f z) (fderiv ℝ f z Complex.I) (fderiv ℝ f z Complex.I)) / 2
  let infimum := sInf ((fun w : C(closedDisk, M) => riemannianDiskEnergy g w) ''
    weaklyMonotoneDiskCompetitors g γ)
  have hAc : ContinuousOn A U := (contDiffOn_pullback_metric_coefficients g hU hr).continuousOn
  have hnorm : Continuous (fun A : F →L[ℝ] F →L[ℝ] ℝ => ‖A‖) :=
    @continuous_norm (F →L[ℝ] F →L[ℝ] ℝ) inferInstance
  have hnormA : ContinuousOn (fun y => ‖A y‖) (range Φ) :=
    hnorm.comp_continuousOn (hAc.mono hΦU)
  obtain ⟨C, hC⟩ := ((isCompact_range hΦ).image_of_continuousOn hnormA).bddAbove
  have huKb (n : ℕ) : MapsTo (u n) (Metric.closedBall (0 : ℂ) b) (range Φ) :=
    (huK n).mono_left (Metric.closedBall_subset_closedBall hb1)
  have hAu (n : ℕ) : AEStronglyMeasurable (fun z => A (u n z)) μ :=
    (hAc.comp (hu n).continuous.continuousOn (fun z hz => hΦU (huKb n hz))).aestronglyMeasurable
      measurableSet_closedBall
  have hAv (n : ℕ) : AEStronglyMeasurable (fun z => A (v n z)) μ :=
    (hAc.comp (hv n).continuous.continuousOn (fun z hz => hΦU (hvK n hz))).aestronglyMeasurable
      measurableSet_closedBall
  have hCu (n : ℕ) : ∀ᵐ z ∂μ, ‖A (u n z)‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    exact hC (mem_image_of_mem (fun y => ‖A y‖) (huKb n hz))
  have hCv (n : ℕ) : ∀ᵐ z ∂μ, ‖A (v n z)‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    exact hC (mem_image_of_mem (fun y => ‖A y‖) (hvK n hz))
  have hAulim : ∀ᵐ z ∂μ, Tendsto (fun n => A (u n z)) atTop (𝓝 (A (u₀ z))) := by
    filter_upwards [hu₀, hu₀K] with z hz hzK
    exact ((hAc (u₀ z) (hΦU hzK)).continuousAt (hU.mem_nhds (hΦU hzK))).tendsto.comp hz
  have hAvlim : ∀ᵐ z ∂μ, Tendsto (fun n => A (v n z)) atTop (𝓝 (A (v₀ z))) := by
    filter_upwards [hv₀, hv₀K] with z hz hzK
    exact ((hAc (v₀ z) (hΦU hzK)).continuousAt (hU.mem_nhds (hΦU hzK))).tendsto.comp hz
  obtain ⟨ρ, h, hρ, _, _, _, _, hε, hle⟩ :=
    exists_pullback_energy_comparison_sequence g hΦ hU hr hΦU hleft τ hτ u v Ku Kv
      hu hv ha hab hb1 huK hvK htrace hgap henergy hV hKV T hT hL hTK hfix hmin
  let ε : ℕ → ℝ := fun n =>
    (∫ z in Metric.closedBall (0 : ℂ) (ρ n) \ Metric.closedBall (0 : ℂ) (ρ n - h n),
      e (attachThinAnnulus (u n) (v n) T (ρ n) (h n)) z) +
        ((∫ z in Metric.closedBall (0 : ℂ) 1, e (u n) z) - infimum)
  change Tendsto ε atTop (𝓝 0) at hε
  change ∀ᶠ n in atTop, (∫ z in Metric.closedBall (0 : ℂ) (ρ n), e (u n) z) ≤
    (∫ z in Metric.closedBall (0 : ℂ) (ρ n), e (v n) z) + ε n at hle
  obtain ⟨ρ₀, hρ₀, σ, hσ, hρlim⟩ := isCompact_Icc.isSeqCompact hρ
  have hσlim : Tendsto σ atTop atTop := hσ.tendsto_atTop
  have hsphere : μ (Metric.sphere (0 : ℂ) ρ₀) = 0 :=
    le_antisymm
      ((Measure.restrict_apply_le (μ := volume) (Metric.closedBall (0 : ℂ) b)
        (Metric.sphere (0 : ℂ) ρ₀)).trans_eq (Measure.addHaar_sphere volume (0 : ℂ) ρ₀)) bot_le
  have hpos (n : ℕ) : ∀ᵐ z ∂μ, ∀ w, 0 ≤ A (u (σ n) z) w w :=
    Eventually.of_forall fun z w =>
      (pullbackMetricCoefficients_isPosSemidef g r (u (σ n) z)).isNonneg.nonneg w
  have hcomp : ∀ᶠ n in atTop,
      (∑ j : Fin 2, ∫ z in Metric.closedBall (0 : ℂ) (ρ (σ n)),
        A (u (σ n) z) (Gu j (σ n) z) (Gu j (σ n) z) ∂μ) ≤
      (∑ j : Fin 2, ∫ z in Metric.closedBall (0 : ℂ) (ρ (σ n)),
        A (v (σ n) z) (Hv j (σ n) z) (Hv j (σ n) z) ∂μ) + 2 * ε (σ n) := by
    filter_upwards [hσlim.eventually hle] with n hn
    rw [sum_integral_quadratic_lp_columns_eq (hρ (σ n)).2 _ (hAu (σ n)) (hCu (σ n))
      (u (σ n)) (fun j => Gu j (σ n)) (fun j => hGu j (σ n)),
      sum_integral_quadratic_lp_columns_eq (hρ (σ n)).2 _ (hAv (σ n)) (hCv (σ n))
        (v (σ n)) (fun j => Hv j (σ n)) (fun j => hHv j (σ n))]
    change 2 * (∫ z in Metric.closedBall (0 : ℂ) (ρ (σ n)), e (u (σ n)) z) ≤
      2 * (∫ z in Metric.closedBall (0 : ℂ) (ρ (σ n)), e (v (σ n)) z) + 2 * ε (σ n)
    linarith
  refine ⟨ρ₀, hρ₀, ?_⟩
  have hout := sum_integral_quadratic_closedBall_le_of_weak_of_tendsto_L2
    (fun n z => A (u (σ n) z)) (fun z => A (u₀ z))
    (fun n z => A (v (σ n) z)) (fun z => A (v₀ z))
    (fun n => hAu (σ n)) (fun n => hAv (σ n))
    (fun n => hCu (σ n)) (fun n => hCv (σ n)) hpos hρlim hsphere
    (hAulim.mono fun z hz => hz.comp hσlim) (hAvlim.mono fun z hz => hz.comp hσlim)
    (fun j n => Gu j (σ n)) G₀ (fun j n => Hv j (σ n)) H₀
    (fun j ℓ => (hweak j ℓ).comp hσlim) (fun j => (hstrong j).comp hσlim)
    (fun n => 2 * ε (σ n)) (by simpa using (hε.comp hσlim).const_mul 2) hcomp
  have hrestrict : μ.restrict (Metric.closedBall (0 : ℂ) ρ₀) =
      volume.restrict (Metric.closedBall (0 : ℂ) ρ₀) :=
    Measure.restrict_restrict_of_subset (Metric.closedBall_subset_closedBall hρ₀.2)
  simpa only [hrestrict, A] using hout

end DifferentialGeometry.Geometry

end
