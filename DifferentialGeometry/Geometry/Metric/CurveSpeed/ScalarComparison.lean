import DifferentialGeometry.Geometry.Metric.CurveSpeedCalculus
import DifferentialGeometry.Geometry.Measure.Area.ManifoldComposition



noncomputable section

open Bundle Manifold Set DifferentialGeometry Filter
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry


theorem riemannianCurveSpeed_real (ν : ℝ → ℝ) (x : ℝ) :
    riemannianCurveSpeed (standardEuclideanMetric ℝ) ν x = |deriv ν x| := by
  unfold riemannianCurveSpeed
  rw [mfderiv_eq_fderiv]
  change Real.sqrt ((fderiv ℝ ν x) 1 * (fderiv ℝ ν x) 1) = |deriv ν x|
  rw [fderiv_apply_one_eq_deriv]
  rw [← sq, Real.sqrt_sq_eq_abs]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M]

set_option backward.isDefEq.respectTransparency false in


theorem abs_deriv_le_of_riemannian_distance_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {ν : ℝ → ℝ} {x : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ x) (hν : DifferentiableAt ℝ ν x)
    (hbound : ∀ y, |ν y - ν x| ≤ (riemannianEDistOf g (γ x) (γ y)).toReal) :
    |deriv ν x| ≤ riemannianCurveSpeed g γ x := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hdim
    have hlocal := eventuallyEq_const_of_model_subsingleton (E := E) hγ.continuousAt
    have hconst : ν =ᶠ[𝓝 x] (fun _ => ν x) := by
      filter_upwards [hlocal] with y hy
      have h := hbound y
      rw [hy, riemannianEDistOf_self, ENNReal.toReal_zero] at h
      exact sub_eq_zero.mp (abs_nonpos_iff.mp h)
    rw [hconst.deriv_eq, deriv_const, abs_zero]
    exact riemannianCurveSpeed_nonneg g γ x
  let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩
  have h := metric_differential_le_of_edist_le g (standardEuclideanMetric ℝ)
    (L := 1) hγ hν.mdifferentiableAt (fun y => by
      rw [riemannianEDistOf_standardEuclideanMetric, edist_dist, Real.dist_eq,
        ENNReal.coe_one, one_mul, abs_sub_comm]
      exact (ENNReal.ofReal_le_ofReal (hbound y)).trans ENNReal.ofReal_toReal_le) (1 : ℝ)
  change riemannianCurveSpeed (standardEuclideanMetric ℝ) ν x ≤
    (1 : ℝ≥0) * riemannianCurveSpeed g γ x at h
  simpa only [riemannianCurveSpeed_real, NNReal.coe_one, one_mul] using h

set_option backward.isDefEq.respectTransparency false in


theorem riemannianCurveSpeed_le_abs_deriv_of_distance_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M} {ν : ℝ → ℝ} {x : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ x) (hν : DifferentiableAt ℝ ν x)
    (hbound : ∀ y, riemannianEDistOf g (γ x) (γ y) ≤ ENNReal.ofReal |ν y - ν x|) :
    riemannianCurveSpeed g γ x ≤ |deriv ν x| := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hdim
    let : Subsingleton (TangentSpace 𝓘(ℝ, E) (γ x)) := ‹Subsingleton E›
    have hz : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ x 1 = (0 : E) := Subsingleton.elim _ _
    simp only [riemannianCurveSpeed, hz, map_zero, Real.sqrt_zero, abs_nonneg]
  let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩
  have h := metric_differential_le_of_edist_le (standardEuclideanMetric ℝ) g
    (L := 1) hν.mdifferentiableAt hγ (fun y => by
      rw [riemannianEDistOf_standardEuclideanMetric, edist_dist, Real.dist_eq,
        ENNReal.coe_one, one_mul, abs_sub_comm]
      exact hbound y) (1 : ℝ)
  change riemannianCurveSpeed g γ x ≤
    (1 : ℝ≥0) * riemannianCurveSpeed (standardEuclideanMetric ℝ) ν x at h
  simpa only [riemannianCurveSpeed_real, NNReal.coe_one, one_mul] using h

end DifferentialGeometry.Geometry
