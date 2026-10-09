import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Polar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Scalar
import DifferentialGeometry.Geometry.Neck.NormalizedDatum
import DifferentialGeometry.Geometry.Metric.CylinderAxial
import DifferentialGeometry.Geometry.Metric.PolarCoordinates
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : Fact (Module.finrank ℝ E3 = 3) := ⟨by simp⟩

private def shift (r δ : ℝ) : bufferedCylinder δ → S2 × ℝ :=
  fun q => cylinderAxialDiffeomorph (I := 𝓡 2) r 1 (by norm_num) q.val
private theorem shift_smooth (r δ : ℝ) : ContMDiff IC IC ∞ (shift r δ) :=
  (cylinderAxialDiffeomorph (I := 𝓡 2) r 1 (by norm_num)).contMDiff.comp contMDiff_subtype_val
private theorem shift_derivative (r δ : ℝ) (q : bufferedCylinder δ)
    (v : TangentSpace IC q) : mfderiv IC IC (shift r δ) q v = v := by
  have h := congrArg (fun D => D v) (mfderiv_comp q
    ((cylinderAxialDiffeomorph (I := 𝓡 2) r 1 (by norm_num)).contMDiff.mdifferentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0) q.val)
    ((contMDiff_subtype_val (I := IC) (U := bufferedCylinder δ)).mdifferentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0) q))
  change mfderiv IC IC (shift r δ) q v = _ at h
  rw [ContinuousLinearMap.comp_apply, mfderiv_subtype_val] at h
  rw [cylinderAxialDiffeomorph_mfderiv] at h
  change mfderiv IC IC (shift r δ) q v = (v.1, 1 * v.2) at h
  exact h.trans (by change (v.1, 1 * v.2) = v; rw [one_mul]; rfl)
private theorem shift_end {r δ : ℝ} (hr : transitionEnd + δ⁻¹ + 1 < r)
    (q : bufferedCylinder δ) : transitionEnd < (shift r δ q).2 := by
  change transitionEnd < r + 1 * q.val.2
  have hq := q.property.1
  linarith

def endNeckMap (r δ : ℝ) (q : bufferedCylinder δ) : E3 := euclideanPolarMap (shift r δ q)

theorem endNeckMap_apply (r δ : ℝ) (q : bufferedCylinder δ) :
    endNeckMap r δ q = (r + q.val.2) • (q.val.1 : E3) := by
  simp only [endNeckMap, euclideanPolarMap, shift, cylinderAxialDiffeomorph_apply, one_mul]

private theorem end_smooth (r δ : ℝ) : ContMDiff IC (𝓡 3) ∞ (endNeckMap r δ) :=
  euclideanPolarMap_smooth.comp (shift_smooth r δ)
private theorem end_derivative (r δ : ℝ) (q : bufferedCylinder δ) (v : TangentSpace IC q) :
    mfderiv IC (𝓡 3) (endNeckMap r δ) q v =
      mfderiv IC (𝓡 3) euclideanPolarMap (shift r δ q) v := by
  have h := congrArg (fun D => D v) (mfderiv_comp q
    (euclideanPolarMap_smooth.mdifferentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0) (shift r δ q))
    ((shift_smooth r δ).mdifferentiable (by decide : (∞ : WithTop ℕ∞) ≠ 0) q))
  change mfderiv IC (𝓡 3) (endNeckMap r δ) q v = _ at h
  rw [ContinuousLinearMap.comp_apply, shift_derivative] at h
  exact h
private theorem end_injective {r δ : ℝ} (hr : transitionEnd + δ⁻¹ + 1 < r) :
    Injective (endNeckMap r δ) := by
  intro q q' h
  have hs := euclideanPolarMap_injOn (transitionEnd_pos.trans (shift_end hr q))
    (transitionEnd_pos.trans (shift_end hr q')) h
  exact Subtype.val_injective
    ((cylinderAxialDiffeomorph (I := 𝓡 2) r 1 (by norm_num)).injective hs)
private theorem end_immersion {r δ : ℝ} (hr : transitionEnd + δ⁻¹ + 1 < r)
    (q : bufferedCylinder δ) : Injective (mfderiv IC (𝓡 3) (endNeckMap r δ) q) := by
  have hp := PartialDiffeomorph.isLocalDiffeomorphAt IC (𝓡 3) ∞
    (euclideanPolarDiffeomorph (n := 2))
    (transitionEnd_pos.trans (shift_end hr q))
  intro v w h
  rw [end_derivative, end_derivative] at h
  exact (hp.mfderivToContinuousLinearEquiv (by simp)).injective h

theorem endNeckMap_norm {r δ : ℝ} (hr : transitionEnd + δ⁻¹ + 1 < r)
    (q : bufferedCylinder δ) : ‖endNeckMap r δ q‖ = r + q.val.2 := by
  exact (euclideanPolarMap_norm_of_pos (transitionEnd_pos.trans (shift_end hr q))).trans
    (by simp only [shift, cylinderAxialDiffeomorph_apply, one_mul])

theorem endNeckMap_scalar {r δ : ℝ} (hr : transitionEnd + δ⁻¹ + 1 < r)
    (q : bufferedCylinder δ) : metricScalarAt metric (endNeckMap r δ q) = 1 := by
  apply metricScalarAt_cylindrical
  change transitionEnd ≤ ‖euclideanPolarMap (shift r δ q)‖
  rw [euclideanPolarMap_norm_of_pos (transitionEnd_pos.trans (shift_end hr q))]
  exact (shift_end hr q).le

private theorem end_tensor {r δ : ℝ} (hr : transitionEnd + δ⁻¹ + 1 < r)
    (q : bufferedCylinder δ) (v w : TangentSpace IC q) :
    metric.inner (endNeckMap r δ q)
      (mfderiv IC (𝓡 3) (endNeckMap r δ) q v)
    (mfderiv IC (𝓡 3) (endNeckMap r δ) q w) = (referenceMetric δ).inner q v w := by
  rw [end_derivative, end_derivative]
  rw [endNeckMap, referenceMetric, SmoothRiemannianMetric.restrictOpen_inner]
  let gS := scaleMetric 2 (by norm_num)
    (DifferentialGeometry.Geometry.roundMetric (E := E3) (n := 2))
  have hmetric := congrArg
    (fun g : SmoothRiemannianMetric IC (S2 × ℝ) => g.inner (q : S2 × ℝ) v w)
    (pullback_cylinderMetric_cylinderAxialDiffeomorph gS r 1 (by norm_num))
  have hpull := Diffeomorph.pullbackMetric_inner (cylinderMetric gS)
    (cylinderAxialDiffeomorph (I := 𝓡 2) r 1 (by norm_num))
    (q : S2 × ℝ) v w
  have htransport := hpull.symm.trans hmetric
  have hdv := cylinderAxialDiffeomorph_mfderiv
    (I := 𝓡 2) r 1 (by norm_num) (q : S2 × ℝ) v
  have hdw := cylinderAxialDiffeomorph_mfderiv
    (I := 𝓡 2) r 1 (by norm_num) (q : S2 × ℝ) w
  rw [hdv, hdw] at htransport
  simp only [one_mul] at htransport
  have hv : (v.1, v.2) = v := rfl
  have hw : (w.1, w.2) = w := rfl
  rw [hv, hw] at htransport
  have hgS : cylinderMetric gS = roundCylinderMetric (E := E3) (n := 2) := by
    rfl
  have hshift :
      cylinderAxialDiffeomorph (I := 𝓡 2) r 1 (by norm_num) (q : S2 × ℝ) =
        shift r δ q := by
    rfl
  rw [hgS, hshift] at htransport
  have htransport' :
      (roundCylinderMetric (E := E3) (n := 2)).inner (shift r δ q) v w =
        (roundCylinderMetric (E := E3) (n := 2)).inner (q : S2 × ℝ) v w := by
    exact htransport
  exact (metric_polar_pullback_cylindrical
    (shift r δ q) (shift_end hr q).le v w).trans htransport'

def endNeckDatum (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (side : Bool) :
    normalizedDatum metric (r • (spherePoint : E3)) δ k := by
  have hc : endNeckMap r δ (cylinderCenter δ hδ) = r • (spherePoint : E3) := by
    rw [endNeckMap_apply]; simp only [cylinderCenter, add_zero]
  have hscalar : metricScalarAt metric (r • (spherePoint : E3)) = 1 := by
    rw [← hc]; exact endNeckMap_scalar hr _
  have hp : 0 < metricScalarAt metric (r • (spherePoint : E3)) := by rw [hscalar]; norm_num
  have hloc := isLocalDiffeomorph_of_injective_mfderiv (endNeckMap r δ) (end_smooth r δ)
    (end_immersion hr) (by simp)
  have he : pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric _ hp metric)
      (endNeckMap r δ) hloc (end_injective hr) = referenceMetric δ := by
    apply SmoothRiemannianMetric.ext_inner
    intro q v w
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner, hscalar, one_mul]
    exact end_tensor hr q v w
  refine
    { precision_pos := hδ
      precision_lt_one := hδ1
      map := endNeckMap r δ
      smooth := end_smooth r δ
      injective := end_injective hr
      immersion := end_immersion hr
      center_eq := hc
      scalar_pos := hp
      retainedSide := side
      error_lt := ?_ }
  change metricDerivENormSupOn (controlledCylinder δ) k
    (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric _ hp metric)
      (endNeckMap r δ) hloc (end_injective hr)) (referenceMetric δ) (referenceMetric δ) < _
  rw [he, metricDerivENormSupOn_self]
  exact ENNReal.ofReal_pos.mpr hδ

theorem endNeckDatum_map (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (side : Bool) :
    (endNeckDatum r δ hδ hδ1 hr k side).map = endNeckMap r δ := rfl

theorem endNeckDatum_normalizedMetric (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (side : Bool) :
    (endNeckDatum r δ hδ hδ1 hr k side).normalizedMetric = referenceMetric δ := by
  apply SmoothRiemannianMetric.ext_inner
  intro q v w
  rw [normalizedDatum.normalizedMetric_inner]
  have hc : endNeckMap r δ (cylinderCenter δ hδ) = r • (spherePoint : E3) := by
    rw [endNeckMap_apply]; simp only [cylinderCenter, add_zero]
  have hscalar : metricScalarAt metric (r • (spherePoint : E3)) = 1 := by
    rw [← hc]; exact endNeckMap_scalar hr _
  rw [hscalar, one_mul]
  exact end_tensor hr q v w

theorem endNeckDatum_retainedSide (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (side : Bool) :
    (endNeckDatum r δ hδ hδ1 hr k side).retainedSide = side := rfl
end DifferentialGeometry.PDE.RicciFlow.StandardCap
