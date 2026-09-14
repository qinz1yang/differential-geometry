import DifferentialGeometry.Geometry.Curvature.ConformalScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornEndFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelWitnesses
import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff
import DifferentialGeometry.Geometry.Operator.Cylinder
import Mathlib.Topology.MetricSpace.Completion

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
  [SigmaCompactSpace W]

omit [SigmaCompactSpace W] in
theorem not_completeSpace_of_nonempty_finiteHorn {g : SmoothRiemannianMetric I3 W}
    (h : Nonempty (FiniteHorn g)) : ¬ CompleteSpace W := by
  rintro hcomplete
  obtain ⟨H⟩ := h
  let e : UniformSpace.Completion W → W := UniformSpace.Completion.extension id
  have hcoe : ∀ x : W, e (x : UniformSpace.Completion W) = x := fun x =>
    UniformSpace.Completion.extension_coe uniformContinuous_id x
  have hfix : (fun z : UniformSpace.Completion W =>
      ((e z : W) : UniformSpace.Completion W)) = id :=
    DenseRange.equalizer UniformSpace.Completion.denseRange_coe
      ((UniformSpace.Completion.uniformContinuous_coe W).continuous.comp
        (UniformSpace.Completion.continuous_extension (f := id)))
      continuous_id (funext fun x => by simpa using hcoe x)
  exact H.endpoint_missing (e H.endpoint) (congrFun hfix H.endpoint)

omit [SigmaCompactSpace W] in
theorem not_nonempty_finiteHorn_of_completeSpace [CompleteSpace W]
    {g : SmoothRiemannianMetric I3 W} : ¬ Nonempty (FiniteHorn g) :=
  fun h => not_completeSpace_of_nonempty_finiteHorn h inferInstance

omit [SigmaCompactSpace W] in
theorem exists_axial_metricScalarAt_gt {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (C : ℝ) : ∃ s ∈ Set.Ioc 0 H.axial.length, C < metricScalarAt g (H.axial.point s) := by
  obtain ⟨i, hi⟩ := H.curvature_diverges C
  obtain ⟨d, hd, hdle, htail⟩ := H.cofinal_axial i
  exact ⟨d / 2, ⟨by linarith, by linarith⟩, hi _ (htail _ ⟨by linarith, by linarith⟩)⟩

omit [SigmaCompactSpace W] in
theorem exists_metricScalarAt_gt_of_nonempty_finiteHorn {g : SmoothRiemannianMetric I3 W}
    (h : Nonempty (FiniteHorn g)) (C : ℝ) : ∃ x : W, C < metricScalarAt g x := by
  obtain ⟨H⟩ := h
  obtain ⟨s, _hs, hsc⟩ := exists_axial_metricScalarAt_gt H C
  exact ⟨H.axial.point s, hsc⟩

def hornHeightProfile (delta : ℝ) : ℝ → ℝ :=
  fun s => -delta * s

theorem contDiff_hornHeightProfile (delta : ℝ) : ContDiff ℝ ∞ (hornHeightProfile delta) := by
  unfold hornHeightProfile
  fun_prop

theorem deriv_hornHeightProfile (delta : ℝ) :
    deriv (hornHeightProfile delta) = fun _ => -delta := by
  funext s
  change deriv (fun t : ℝ => (-delta) * t) s = -delta
  have h := ((hasDerivAt_id s).const_mul (-delta)).deriv
  rw [mul_one] at h
  exact h

def conformalCylinderMetric (delta : ℝ) : SmoothRiemannianMetric IC Cylinder :=
  conformalMetricOfContDiff (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
    (fun y : Cylinder => hornHeightProfile delta y.2)
    ((contDiff_hornHeightProfile delta).contMDiff.comp contMDiff_snd)

theorem finrank_cylinder_model : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by
  simp

theorem metricScalarAt_conformalCylinderMetric (delta : ℝ) (x : Cylinder) :
    metricScalarAt (conformalCylinderMetric delta) x =
      Real.exp (2 * delta * x.2) * (1 - 2 * delta ^ 2) := by
  have hcyl : roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2) =
      cylinderMetric (scaleMetric 2 (by norm_num)
        (DifferentialGeometry.Geometry.roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))) :=
    rfl
  have hlap : ΔG (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
      ⟨fun y : Cylinder => hornHeightProfile delta y.2,
        (contDiff_hornHeightProfile delta).contMDiff.comp contMDiff_snd⟩ x = 0 := by
    rw [hcyl]
    rw [laplaceBeltrami_comp_height_cylinderMetric (g := scaleMetric 2 (by norm_num)
      (DifferentialGeometry.Geometry.roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)))
      (hf := contDiff_hornHeightProfile delta) x, deriv_hornHeightProfile delta]
    simp
  have hgrad : (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x
      (gradFun (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
        (fun y : Cylinder => hornHeightProfile delta y.2) x)
      (gradFun (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
        (fun y : Cylinder => hornHeightProfile delta y.2) x) = delta ^ 2 := by
    rw [hcyl]
    rw [inner_gradFun_comp_height_cylinderMetric (g := scaleMetric 2 (by norm_num)
      (DifferentialGeometry.Geometry.roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)))
      (hf := contDiff_hornHeightProfile delta) x, deriv_hornHeightProfile delta]
    ring
  rw [conformalCylinderMetric,
    metricScalarAt_conformalMetric_three _ _ _ finrank_cylinder_model x,
    metricScalarAt_roundCylinderModel_eq_one x, hlap, hgrad]
  simp only [hornHeightProfile]
  ring_nf

theorem metricScalarAt_conformalCylinderMetric_pos {delta : ℝ} (hdelta : delta ^ 2 < 1 / 2)
    (x : Cylinder) : 0 < metricScalarAt (conformalCylinderMetric delta) x := by
  rw [metricScalarAt_conformalCylinderMetric]
  exact mul_pos (Real.exp_pos _) (by linarith)

theorem metricScalarAt_mul_inner_conformalCylinderMetric (delta : ℝ) (x : Cylinder)
    (v w : TangentSpace IC x) :
    metricScalarAt (conformalCylinderMetric delta) x *
        (conformalCylinderMetric delta).inner x v w =
      (1 - 2 * delta ^ 2) *
        (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x v w := by
  have hinner : (conformalCylinderMetric delta).inner x v w =
      Real.exp (-(2 * delta * x.2)) *
        (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x v w := by
    rw [conformalCylinderMetric, conformalMetricOfContDiff_inner]
    simp only [hornHeightProfile]
    rw [show 2 * (-delta * x.2) = -(2 * delta * x.2) by ring]
  have hexp : Real.exp (2 * delta * x.2) * Real.exp (-(2 * delta * x.2)) = 1 := by
    rw [← Real.exp_add, show 2 * delta * x.2 + -(2 * delta * x.2) = 0 by ring, Real.exp_zero]
  rw [metricScalarAt_conformalCylinderMetric, hinner]
  calc Real.exp (2 * delta * x.2) * (1 - 2 * delta ^ 2) *
        (Real.exp (-(2 * delta * x.2)) *
          (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x v w)
      = (1 - 2 * delta ^ 2) *
          (Real.exp (2 * delta * x.2) * Real.exp (-(2 * delta * x.2))) *
            (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x v w := by
        ring
    _ = (1 - 2 * delta ^ 2) *
          (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x v w := by
        rw [hexp]
        ring

theorem exists_metricScalarAt_conformalCylinderMetric_gt {delta : ℝ} (hdelta : 0 < delta)
    (hsmall : delta ^ 2 < 1 / 2) (C : ℝ) :
    ∃ x : Cylinder, C < metricScalarAt (conformalCylinderMetric delta) x := by
  have hpos : 0 < 1 - 2 * delta ^ 2 := by linarith
  obtain ⟨p⟩ : Nonempty (Sphere 2) := ⟨⟨EuclideanSpace.single 0 1, by simp⟩⟩
  refine ⟨(p, Real.log (max (C / (1 - 2 * delta ^ 2)) 0 + 1) / (2 * delta)), ?_⟩
  rw [metricScalarAt_conformalCylinderMetric]
  have hexp : Real.exp (2 * delta * (Real.log (max (C / (1 - 2 * delta ^ 2)) 0 + 1) /
      (2 * delta))) = max (C / (1 - 2 * delta ^ 2)) 0 + 1 := by
    rw [mul_div_cancel₀ _ (by positivity : (2 : ℝ) * delta ≠ 0), Real.exp_log]
    linarith [le_max_right (C / (1 - 2 * delta ^ 2)) (0 : ℝ)]
  rw [hexp]
  have hlt : C / (1 - 2 * delta ^ 2) < max (C / (1 - 2 * delta ^ 2)) 0 + 1 := by
    linarith [le_max_left (C / (1 - 2 * delta ^ 2)) (0 : ℝ)]
  have := mul_lt_mul_of_pos_right hlt hpos
  rwa [div_mul_cancel₀ C (ne_of_gt hpos)] at this

theorem not_scalarBoundedAbove_conformalCylinderMetric {delta : ℝ} (hdelta : 0 < delta)
    (hsmall : delta ^ 2 < 1 / 2) : ¬ ScalarBoundedAbove (conformalCylinderMetric delta) := by
  rintro ⟨C, hC⟩
  obtain ⟨x, hx⟩ := exists_metricScalarAt_conformalCylinderMetric_gt hdelta hsmall C
  exact absurd (hC x) (not_le.mpr hx)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
