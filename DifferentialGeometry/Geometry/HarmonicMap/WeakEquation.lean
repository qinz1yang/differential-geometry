import DifferentialGeometry.Analysis.Sobolev.Euclidean.MetricEnergy.WeakTests
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Compact
import DifferentialGeometry.Geometry.HarmonicMap.ChartMetric
import DifferentialGeometry.Analysis.Elliptic.MetricExtension

noncomputable section

open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev
open scoped Topology ContDiff Manifold ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local notation "P" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem integral_weak_chart_gradient_test_eq_christoffel
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M)
    {x₀ : P} {ρ : ℝ} {z : P → F}
    (hzc : ContinuousOn z (Metric.closedBall x₀ ρ))
    (hzmap : MapsTo z (Metric.closedBall x₀ ρ) (chartTargetEuclid (I := 𝓘(ℝ, E)) p))
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (Metric.ball x₀ ρ))
    (hEL :
      let Ψ : F → M := fun y => (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm y)
      let B := pullbackMetricCoefficients g Ψ
      ∀ φ : P → F, ContDiff ℝ ∞ φ → tsupport φ ⊆ Metric.ball x₀ ρ →
        (∫ x in Metric.ball x₀ ρ, ∑ j : Fin 2,
          ((fderiv ℝ B (z x) (φ x)) (DeGiorgi.weakGradientColumn hz x j)
              (DeGiorgi.weakGradientColumn hz x j) +
            2 * B (z x) (DeGiorgi.weakGradientColumn hz x j)
              (fderiv ℝ φ x (EuclideanSpace.single j 1)))) = 0)
    (k : Fin (Module.finrank ℝ E)) {ζ : P → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζsupp : tsupport ζ ⊆ Metric.ball x₀ ρ) :
    (∫ x in Metric.ball x₀ ρ, ∑ j : Fin 2,
      ((DeGiorgi.weakGradientColumn hz x j) k *
          fderiv ℝ ζ x (EuclideanSpace.single j 1) -
        ζ x * ∑ a, ∑ b,
          chartChristoffel g p a b k ((toEuclidean (E := E)).symm (z x)) *
            (DeGiorgi.weakGradientColumn hz x j) a *
            (DeGiorgi.weakGradientColumn hz x j) b)) = 0 := by
  classical
  let U := chartTargetEuclid (I := 𝓘(ℝ, E)) p
  let Ψ : F → M := fun y => (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm y)
  let B := pullbackMetricCoefficients g Ψ
  let K := z '' Metric.closedBall x₀ ρ
  have hK : IsCompact K := (isCompact_closedBall x₀ ρ).image_of_continuousOn hzc
  have hKU : K ⊆ U := by rintro y ⟨x, hx, rfl⟩; exact hzmap hx
  have hU : IsOpen U := chartTargetEuclid_isOpen p
  have hB : ContDiffOn ℝ 1 B U :=
    (contDiffOn_pullback_metric_coefficients g hU (contMDiffOn_chart_symm p)).of_le (by simp)
  let L₀ : F → F := fun y => WithLp.toLp 2 (fun i => invGramOnEuclid g p i k y)
  have hL₀ : ContDiffOn ℝ ∞ L₀ U := by
    exact (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin (Module.finrank ℝ E) => ℝ)).symm.contDiff.comp_contDiffOn
      (contDiffOn_pi.mpr fun i => invGramOnEuclid_contDiffOn g p i k)
  obtain ⟨L, hL, hLc, hLeq⟩ :=
    DifferentialGeometry.Analysis.exists_contDiff_compactSupport_extension_on_isCompact
      hK hU hKU hL₀
  obtain ⟨C, hC⟩ := (hL.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hLc.fderiv (𝕜 := ℝ))
  have hnear := hLeq.and (hU.mem_nhdsSet.mpr hKU)
  obtain ⟨W, hW, hKW, hWprop⟩ := eventually_nhdsSet_iff_exists.mp hnear
  have hWU : W ⊆ U := fun y hy => (hWprop y hy).2
  have hpair (y : F) (hy : y ∈ W) (v : F) : B y v (L y) = v k := by
    rw [(hWprop y hy).1]
    exact pullbackMetricCoefficients_inverse_chart_invGram_column g p (hWU hy) k v
  have hzK : ∀ᵐ x ∂volume.restrict (Metric.ball x₀ ρ), z x ∈ K := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact mem_image_of_mem z (Metric.ball_subset_closedBall hx)
  obtain ⟨a, haρ, hζa⟩ := exists_lt_subset_ball (isClosed_tsupport ζ) hζsupp
  have hzero := integral_weakGradientColumn_test_deriv_eq_metric_connection
    Metric.isOpen_ball (hzc.mono Metric.ball_subset_closedBall) hz hW (hB.mono hWU)
    hK hKW hzK (fun φ hφ _ hφsupp => hEL φ hφ hφsupp) L (hL.of_le (by simp)) hC
    (EuclideanSpace.proj k) hpair (Metric.closedBall_subset_ball haρ) hζ hζa
  let Γ (x : P) (j : Fin 2) := ∑ a, ∑ b,
    chartChristoffel g p a b k ((toEuclidean (E := E)).symm (z x)) *
      (DeGiorgi.weakGradientColumn hz x j) a * (DeGiorgi.weakGradientColumn hz x j) b
  have hrewrite :
      (fun x => ∑ j : Fin 2,
        (2 * (fderiv ℝ ζ x (EuclideanSpace.single j 1)) *
            (DeGiorgi.weakGradientColumn hz x j) k -
          ζ x * (2 * (fderiv ℝ B (z x) (DeGiorgi.weakGradientColumn hz x j))
              (DeGiorgi.weakGradientColumn hz x j) (L (z x)) -
            (fderiv ℝ B (z x) (L (z x)))
              (DeGiorgi.weakGradientColumn hz x j) (DeGiorgi.weakGradientColumn hz x j)))) =ᵐ[
        volume.restrict (Metric.ball x₀ a)]
      (fun x => 2 * ∑ j : Fin 2,
        ((DeGiorgi.weakGradientColumn hz x j) k *
          fderiv ℝ ζ x (EuclideanSpace.single j 1) - ζ x * Γ x j)) := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hxK : z x ∈ K := mem_image_of_mem z
      (Metric.ball_subset_closedBall (Metric.ball_subset_ball haρ.le hx))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hΓ := chartChristoffel_contraction_eq_inverse_chart_metric_derivative
      g p (hKU hxK) k (DeGiorgi.weakGradientColumn hz x j)
    change Γ x j = _ at hΓ
    have hLx : L (z x) = L₀ (z x) := (hWprop (z x) (hKW hxK)).1
    rw [hLx]
    dsimp only [L₀] at ⊢ hΓ
    change Γ x j = fderiv ℝ B (z x) _ _ _ - (1 / 2 : ℝ) * fderiv ℝ B (z x) _ _ _ at hΓ
    have hΓζ := congrArg (fun t : ℝ => ζ x * t) hΓ
    nlinarith [hΓζ]
  change (∫ x in Metric.ball x₀ a, ∑ j : Fin 2,
    (2 * (fderiv ℝ ζ x (EuclideanSpace.single j 1)) * (DeGiorgi.weakGradientColumn hz x j) k -
      ζ x * (2 * (fderiv ℝ B (z x) (DeGiorgi.weakGradientColumn hz x j))
          (DeGiorgi.weakGradientColumn hz x j) (L (z x)) -
        (fderiv ℝ B (z x) (L (z x)))
          (DeGiorgi.weakGradientColumn hz x j) (DeGiorgi.weakGradientColumn hz x j)))) = 0 at hzero
  rw [integral_congr_ae hrewrite, integral_const_mul] at hzero
  have hsmall : (∫ x in Metric.ball x₀ a, ∑ j : Fin 2,
      ((DeGiorgi.weakGradientColumn hz x j) k * fderiv ℝ ζ x (EuclideanSpace.single j 1) -
        ζ x * Γ x j)) = 0 := by linarith
  change (∫ x in Metric.ball x₀ ρ, ∑ j : Fin 2,
      ((DeGiorgi.weakGradientColumn hz x j) k * fderiv ℝ ζ x (EuclideanSpace.single j 1) -
        ζ x * Γ x j)) = 0
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet
    (Metric.ball_subset_ball haρ.le)]
  · exact hsmall
  · intro x hx
    have hxζ : x ∉ tsupport ζ := fun hx' => hx.2 (hζa hx')
    rw [image_eq_zero_of_notMem_tsupport hxζ, fderiv_of_notMem_tsupport ℝ hxζ]
    simp

theorem integrable_christoffel_weakGradientColumn_sum
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M)
    {x₀ : P} {ρ : ℝ} {z : P → F}
    (hzc : ContinuousOn z (Metric.closedBall x₀ ρ))
    (hzmap : MapsTo z (Metric.closedBall x₀ ρ) (chartTargetEuclid (I := 𝓘(ℝ, E)) p))
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (Metric.ball x₀ ρ))
    (k : Fin (Module.finrank ℝ E)) :
    IntegrableOn (fun x => ∑ j : Fin 2, ∑ a, ∑ b,
      chartChristoffel g p a b k ((toEuclidean (E := E)).symm (z x)) *
        (DeGiorgi.weakGradientColumn hz x j) a *
        (DeGiorgi.weakGradientColumn hz x j) b) (Metric.ball x₀ ρ) := by
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro a _
  apply integrable_finsetSum
  intro b _
  have hc : ContinuousOn (fun x => chartChristoffel g p a b k
      ((toEuclidean (E := E)).symm (z x))) (Metric.closedBall x₀ ρ) :=
    (chartChristoffel_contDiffOn_interior g p a b k).continuousOn.comp
      ((toEuclidean (E := E)).symm.continuous.comp_continuousOn hzc) (by
        intro x hx
        rw [(isOpen_extChartAt_target (I := 𝓘(ℝ, E)) p).interior_eq]
        exact toEuclidean_symm_mem_target (hzmap hx))
  obtain ⟨C, hC⟩ := (isCompact_closedBall x₀ ρ).exists_bound_of_continuousOn hc
  have hm : AEStronglyMeasurable (fun x => chartChristoffel g p a b k
      ((toEuclidean (E := E)).symm (z x))) (volume.restrict (Metric.ball x₀ ρ)) :=
    (hc.mono Metric.ball_subset_closedBall).aestronglyMeasurable Metric.isOpen_ball.measurableSet
  have hi := ((hz a).weakGrad_component_memLp j).integrable_mul
    ((hz b).weakGrad_component_memLp j)
  have hb : ∀ᵐ x ∂volume.restrict (Metric.ball x₀ ρ),
      ‖chartChristoffel g p a b k ((toEuclidean (E := E)).symm (z x))‖ ≤ C := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact hC x (Metric.ball_subset_closedBall hx)
  simpa only [DeGiorgi.weakGradientColumn, PiLp.toLp_apply, Pi.mul_apply, mul_assoc] using
    hi.bdd_mul hm hb

theorem integral_weak_chart_gradient_test_eq_integral_christoffel
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M)
    {x₀ : P} {ρ : ℝ} {z : P → F}
    (hzc : ContinuousOn z (Metric.closedBall x₀ ρ))
    (hzmap : MapsTo z (Metric.closedBall x₀ ρ) (chartTargetEuclid (I := 𝓘(ℝ, E)) p))
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (Metric.ball x₀ ρ))
    (hEL :
      let Ψ : F → M := fun y => (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm y)
      let B := pullbackMetricCoefficients g Ψ
      ∀ φ : P → F, ContDiff ℝ ∞ φ → tsupport φ ⊆ Metric.ball x₀ ρ →
        (∫ x in Metric.ball x₀ ρ, ∑ j : Fin 2,
          ((fderiv ℝ B (z x) (φ x)) (DeGiorgi.weakGradientColumn hz x j)
              (DeGiorgi.weakGradientColumn hz x j) +
            2 * B (z x) (DeGiorgi.weakGradientColumn hz x j)
              (fderiv ℝ φ x (EuclideanSpace.single j 1)))) = 0)
    (k : Fin (Module.finrank ℝ E)) {ζ : P → ℝ}
    (hζ : ContDiff ℝ ∞ ζ) (hζsupp : tsupport ζ ⊆ Metric.ball x₀ ρ) :
    (∫ x in Metric.ball x₀ ρ, ∑ j : Fin 2,
      (DeGiorgi.weakGradientColumn hz x j) k *
        fderiv ℝ ζ x (EuclideanSpace.single j 1)) =
      ∫ x in Metric.ball x₀ ρ, ζ x * (∑ j : Fin 2, ∑ a, ∑ b,
        chartChristoffel g p a b k ((toEuclidean (E := E)).symm (z x)) *
          (DeGiorgi.weakGradientColumn hz x j) a *
          (DeGiorgi.weakGradientColumn hz x j) b) := by
  have hζs : HasCompactSupport ζ :=
    (isCompact_closedBall x₀ ρ).of_isClosed_subset (isClosed_tsupport ζ)
      (hζsupp.trans Metric.ball_subset_closedBall)
  have hi : IntegrableOn (fun x => ∑ j : Fin 2,
      (DeGiorgi.weakGradientColumn hz x j) k * fderiv ℝ ζ x (EuclideanSpace.single j 1))
      (Metric.ball x₀ ρ) := by
    apply integrable_finsetSum
    intro j _
    have hdζ : MemLp (fun x => fderiv ℝ ζ x (EuclideanSpace.single j 1)) 2
        (volume.restrict (Metric.ball x₀ ρ)) :=
      (((hζ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hζs.fderiv_apply ℝ (EuclideanSpace.single j 1))).restrict _
    exact ((hz k).weakGrad_component_memLp j).integrable_mul hdζ
  obtain ⟨C, hC⟩ := hζ.continuous.bounded_above_of_compact_support hζs
  have hj := (integrable_christoffel_weakGradientColumn_sum g p hzc hzmap hz k).bdd_mul
    hζ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  have h := integral_weak_chart_gradient_test_eq_christoffel g p hzc hzmap hz hEL k hζ hζsupp
  simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  rw [integral_sub hi hj] at h
  exact sub_eq_zero.mp h

end DifferentialGeometry.Geometry

end
