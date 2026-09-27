import DifferentialGeometry.Geometry.Metric.Pullback.Chart
import DifferentialGeometry.Geometry.Metric.CompactSourceEllipticity
import DifferentialGeometry.Analysis.Elliptic.MetricExtension
import DifferentialGeometry.Analysis.Convex.CoordinateBox
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section
open Set Manifold
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_pos_mul_norm_sq_le_inverse_chart_metric
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M) {y : H}
    (hy : y ∈ chartTargetEuclid (I := 𝓘(ℝ, E)) p) :
    let Ψ : H → M := fun z => (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm z)
    ∃ lam : ℝ, 0 < lam ∧ ∀ v : H, lam * ‖v‖ ^ 2 ≤ pullbackMetricCoefficients g Ψ y v v := by
  let Uc := chartTargetEuclid (I := 𝓘(ℝ, E)) p
  have hUc : IsOpen Uc := chartTargetEuclid_isOpen (I := 𝓘(ℝ, E)) p
  let chart := extChartAtPartialDiffeomorph 𝓘(ℝ, E) ∞ p
  let Ψ : H → M := fun z => chart.symm ((toEuclidean (E := E)).symm z)
  have hΨ : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ Ψ Uc :=
    chart.contMDiffOn_invFun.comp (toEuclidean (E := E)).symm.contDiff.contMDiff.contMDiffOn
      (fun z hz => toEuclidean_symm_mem_target hz)
  have hlocal : IsLocalDiffeomorphAt 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ Ψ y :=
    ((toEuclidean (E := E)).symm.toDiffeomorph.isLocalDiffeomorph y).comp 𝓘(ℝ, E) M
      (chart.symm.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (toEuclidean_symm_mem_target hy))
  have hinj : Function.Injective (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, E) Ψ y) :=
    (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective
  obtain ⟨lam, A, hlam, _, hbound⟩ := exists_compact_source_metric_ellipticity g hUc
    (hΨ.of_le (by simp)) (isCompact_singleton (x := y)) (singleton_subset_iff.mpr hy)
    (fun x hx => by have heq := mem_singleton_iff.mp hx; subst x; exact hinj)
  exact ⟨lam, hlam, fun v => (hbound y (mem_singleton y) v).1⟩

theorem exists_pos_mul_norm_sq_le_centered_inverse_chart_metric
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M) {y : H}
    (hy : y ∈ chartTargetEuclid (I := 𝓘(ℝ, E)) p) :
    let Ψ : H → M := fun z =>
      (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm (z + y))
    ∃ lam : ℝ, 0 < lam ∧ ∀ v : H, lam * ‖v‖ ^ 2 ≤ pullbackMetricCoefficients g Ψ 0 v v := by
  let Ψ₀ : H → M := fun z => (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm z)
  let Ψ : H → M := fun z => Ψ₀ (z + y)
  obtain ⟨lam, hlam, hbound⟩ := exists_pos_mul_norm_sq_le_inverse_chart_metric g p hy
  refine ⟨lam, hlam, fun v => ?_⟩
  let chart := extChartAtPartialDiffeomorph 𝓘(ℝ, E) ∞ p
  have hΨ₀ : MDifferentiableAt 𝓘(ℝ, H) 𝓘(ℝ, E) Ψ₀ y :=
    ((chart.contMDiffOn_invFun.contMDiffAt
      (chart.open_target.mem_nhds (toEuclidean_symm_mem_target hy))).mdifferentiableAt
      (by simp)).comp y (toEuclidean (E := E)).symm.differentiableAt.mdifferentiableAt
  have heq := pullbackMetricCoefficients_fderiv_of_eventuallyEq
    (f := fun z : H => z + y) (ψ := Ψ₀) (r := Ψ) (x := 0) g
    (by fun_prop) (by simpa only [zero_add] using hΨ₀)
    (Filter.Eventually.of_forall fun z => rfl) v v
  simp only [fderiv_add_const, fderiv_fun_id, ContinuousLinearMap.id_apply, zero_add] at heq
  exact (hbound v).trans_eq heq

end DifferentialGeometry.Geometry

end

noncomputable section
open Set Manifold
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open scoped Topology Manifold ContDiff NNReal


namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local notation "H" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem exists_centered_chart_metric_bounds_on_coordinate_box
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M) (z₀ : H) (τ : ℝ)
    (hbox : ∀ y : H, (∀ k, |y k| ≤ τ) →
      y + z₀ ∈ chartTargetEuclid (I := 𝓘(ℝ, E)) p) :
    let Ψ : H → M := fun z =>
      (extChartAt 𝓘(ℝ, E) p).symm ((toEuclidean (E := E)).symm (z + z₀))
    let B := pullbackMetricCoefficients g Ψ
    ∃ lam : ℝ, ∃ L : ℝ≥0, 0 < lam ∧
      (∀ y : H, (∀ k, |y k| ≤ τ) → ∀ v : H, lam * ‖v‖ ^ 2 ≤ B y v v) ∧
      LipschitzOnWith L B {y : H | ∀ k, |y k| ≤ τ} := by
  let Uc := chartTargetEuclid (I := 𝓘(ℝ, E)) p
  have hUc : IsOpen Uc := chartTargetEuclid_isOpen (I := 𝓘(ℝ, E)) p
  let chart := extChartAtPartialDiffeomorph 𝓘(ℝ, E) ∞ p
  let Ψ₀ : H → M := fun z => chart.symm ((toEuclidean (E := E)).symm z)
  let Ψ : H → M := fun z => Ψ₀ (z + z₀)
  let K := {y : H | ∀ k, |y k| ≤ τ}
  let U := (fun y : H => y + z₀) ⁻¹' Uc
  have hU : IsOpen U := hUc.preimage (continuous_id.add continuous_const)
  have hΨ₀ : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ Ψ₀ Uc :=
    chart.contMDiffOn_invFun.comp (toEuclidean (E := E)).symm.contDiff.contMDiff.contMDiffOn
      (fun z hz => toEuclidean_symm_mem_target hz)
  have hΨ : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ Ψ U :=
    hΨ₀.comp ((contDiff_id.add contDiff_const).contMDiff.contMDiffOn) (fun _ hy => hy)
  have hinj (y : H) (hy : y ∈ K) : Function.Injective (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, E) Ψ y) := by
    have hlocal : IsLocalDiffeomorphAt 𝓘(ℝ, H) 𝓘(ℝ, E) ∞ Ψ₀ (y + z₀) :=
      ((toEuclidean (E := E)).symm.toDiffeomorph.isLocalDiffeomorph (y + z₀)).comp 𝓘(ℝ, E) M
        (chart.symm.isLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
          (toEuclidean_symm_mem_target (hbox y hy)))
    have hi := (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective
    have hdiff : MDifferentiableAt 𝓘(ℝ, H) 𝓘(ℝ, E) Ψ₀ (y + z₀) :=
      (hΨ₀.contMDiffAt (hUc.mem_nhds (hbox y hy))).mdifferentiableAt (by simp)
    have heq : (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, E) Ψ y : H →L[ℝ] E) =
        (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, E) Ψ₀ (y + z₀) : H →L[ℝ] E) := by
      have hadd : MDifferentiableAt 𝓘(ℝ, H) 𝓘(ℝ, H) (fun z : H => z + z₀) y :=
        (show DifferentiableAt ℝ (fun z : H => z + z₀) y from by fun_prop).mdifferentiableAt
      have hm := mfderiv_comp y hdiff hadd
      change (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, E) Ψ y : H →L[ℝ] E) =
        (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, E) Ψ₀ (y + z₀) : H →L[ℝ] E).comp
          (mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun z : H => z + z₀) y) at hm
      rw [mfderiv_eq_fderiv, fderiv_add_const, fderiv_fun_id] at hm
      ext v
      exact congrArg (fun A : H →L[ℝ] E => A v) hm
    rwa [heq]
  have hK : IsCompact K := DifferentialGeometry.Analysis.isCompact_coordinate_box (fun _ => τ)
  obtain ⟨lam, _, hlam, _, hbound⟩ := exists_compact_source_metric_ellipticity g hU
    (hΨ.of_le (by simp)) hK (fun y hy => hbox y hy) hinj
  have hB : ContDiffOn ℝ ∞ (pullbackMetricCoefficients g Ψ) K :=
    (contDiffOn_pullback_metric_coefficients g hU hΨ).mono (fun y hy => hbox y hy)
  obtain ⟨L, hL⟩ := hB.exists_lipschitzOnWith (by simp)
    (DifferentialGeometry.Analysis.convex_coordinate_box (fun _ => τ)) hK
  exact ⟨lam, L, hlam, fun y hy v => (hbound y hy v).1, hL⟩

end DifferentialGeometry.Geometry

end
