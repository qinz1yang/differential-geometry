import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Affine
import DifferentialGeometry.Geometry.HarmonicMap.WeakEquation

section

noncomputable section

open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_weak_chart_equation_of_centered_metric_variation
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M) (y₀ : F)
    {c : V} {r : ℝ} {z : V → F}
    (hzc : ContinuousOn z (Metric.closedBall c r))
    (hzmap : MapsTo (fun x => z x + y₀) (Metric.closedBall c r)
      (chartTargetEuclid (I := 𝓘(ℝ, E)) p))
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (Metric.ball c r))
    (hEL :
      let Ψc : F → M := fun y =>
        (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm (y + y₀))
      let Bc := pullbackMetricCoefficients g Ψc
      ∀ φ : V → F, ContDiff ℝ ∞ φ → tsupport φ ⊆ Metric.ball c r →
        (∫ x in Metric.ball c r, ∑ j : Fin 2,
          ((fderiv ℝ Bc (z x) (φ x))
              (DeGiorgi.weakGradientColumn hz x j) (DeGiorgi.weakGradientColumn hz x j) +
            2 * Bc (z x) (DeGiorgi.weakGradientColumn hz x j)
              (fderiv ℝ φ x (EuclideanSpace.single j 1)))) = 0) :
    ∃ hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => (z x + y₀) i) (Metric.ball c r),
      (∀ i, (hw i).weakGrad = (hz i).weakGrad) ∧
      (∀ k, IntegrableOn (fun x => ∑ j : Fin 2, ∑ a, ∑ b,
        chartChristoffel g p a b k ((toEuclidean (E := E)).symm (z x + y₀)) *
          (DeGiorgi.weakGradientColumn hz x j) a *
          (DeGiorgi.weakGradientColumn hz x j) b) (Metric.ball c r)) ∧
      ∀ k (ζ : V → ℝ), ContDiff ℝ ∞ ζ → tsupport ζ ⊆ Metric.ball c r →
        (∫ x in Metric.ball c r, ∑ j : Fin 2,
          (DeGiorgi.weakGradientColumn hz x j) k *
            fderiv ℝ ζ x (EuclideanSpace.single j 1)) =
          ∫ x in Metric.ball c r, ζ x * (∑ j : Fin 2, ∑ a, ∑ b,
            chartChristoffel g p a b k ((toEuclidean (E := E)).symm (z x + y₀)) *
              (DeGiorgi.weakGradientColumn hz x j) a *
              (DeGiorgi.weakGradientColumn hz x j) b) := by
  let U := chartTargetEuclid (I := 𝓘(ℝ, E)) p
  let Ψ : F → M := fun y =>
    (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm y)
  let Ψc : F → M := fun y => Ψ (y + y₀)
  let B := pullbackMetricCoefficients g Ψ
  let Bc := pullbackMetricCoefficients g Ψc
  have hU : IsOpen U := chartTargetEuclid_isOpen p
  have hΨ : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ Ψ U := contMDiffOn_chart_symm p
  have hcoeff (y : F) (hy : y + y₀ ∈ U) : Bc y = B (y + y₀) := by
    ext ξ η
    have h := pullbackMetricCoefficients_fderiv_of_eventuallyEq
      (f := fun q : F => q + y₀) (ψ := Ψ) (r := Ψc) (x := y) g
      (by fun_prop) ((hΨ.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp))
      (Eventually.of_forall fun _ => rfl) ξ η
    simpa only [fderiv_add_const, fderiv_fun_id, ContinuousLinearMap.id_apply] using h.symm
  have hder (x : V) (hx : x ∈ Metric.ball c r) :
      fderiv ℝ Bc (z x) = fderiv ℝ B (z x + y₀) := by
    have hnear : Bc =ᶠ[𝓝 (z x)] (fun y => B (y + y₀)) := by
      filter_upwards [((continuous_id.add continuous_const).continuousAt.preimage_mem_nhds
        (hU.mem_nhds (hzmap (Metric.ball_subset_closedBall hx))))] with y hy
      exact hcoeff y hy
    rw [hnear.fderiv_eq]
    exact fderiv_comp_add_right (𝕜 := ℝ) (f := B) (x := z x) y₀
  let : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨hw, hgrad⟩ :=
    Analysis.Sobolev.Euclidean.exists_memW1pWitness_add_const Metric.isOpen_ball hz y₀
  have hcolumns (x : V) (j : Fin 2) :
      DeGiorgi.weakGradientColumn hw x j = DeGiorgi.weakGradientColumn hz x j := by
    unfold DeGiorgi.weakGradientColumn
    simp only [hgrad]
  have hELw : ∀ φ : V → F, ContDiff ℝ ∞ φ → tsupport φ ⊆ Metric.ball c r →
      (∫ x in Metric.ball c r, ∑ j : Fin 2,
        ((fderiv ℝ B (z x + y₀) (φ x))
            (DeGiorgi.weakGradientColumn hw x j) (DeGiorgi.weakGradientColumn hw x j) +
          2 * B (z x + y₀) (DeGiorgi.weakGradientColumn hw x j)
            (fderiv ℝ φ x (EuclideanSpace.single j 1)))) = 0 := by
    intro φ hφ hφsupp
    have h := hEL φ hφ hφsupp
    change (∫ x in Metric.ball c r, ∑ j : Fin 2,
      ((fderiv ℝ Bc (z x) (φ x))
          (DeGiorgi.weakGradientColumn hz x j) (DeGiorgi.weakGradientColumn hz x j) +
        2 * Bc (z x) (DeGiorgi.weakGradientColumn hz x j)
          (fderiv ℝ φ x (EuclideanSpace.single j 1)))) = 0 at h
    refine (integral_congr_ae ?_).trans h
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    simp only [hcolumns, hder x hx, hcoeff (z x) (hzmap (Metric.ball_subset_closedBall hx))]
  have hwc : ContinuousOn (fun x => z x + y₀) (Metric.closedBall c r) :=
    hzc.add continuousOn_const
  refine ⟨hw, hgrad, ?_, ?_⟩
  · intro k
    simpa only [hcolumns] using
      integrable_christoffel_weakGradientColumn_sum g p hwc hzmap hw k
  · intro k ζ hζ hζsupp
    simpa only [hcolumns] using
      integral_weak_chart_gradient_test_eq_integral_christoffel g p hwc hzmap hw hELw k hζ hζsupp

end DifferentialGeometry.Geometry

end

end
