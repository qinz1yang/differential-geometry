import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation

set_option autoImplicit false

namespace GC.MetricGeometry.KleinerLottApprox

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
variable {p : X} {q : Y} {δ : ℝ}

def mapTargetIsometry (f : KleinerLottApprox p q δ) (e : Y ≃ᵢ Z) :
    KleinerLottApprox p (e q) δ where
  error_pos := f.error_pos
  error_lt_one := f.error_lt_one
  toFun x := e (f.toFun x)
  basepoint := congrArg e f.basepoint
  distortion x hx y hy := by
    simpa only [e.dist_eq] using f.distortion x hx y hy
  coverage z hz := by
    have hd : dist (e.symm z) q = dist z (e q) := by
      rw [← e.dist_eq, e.apply_symm_apply]
    have hh := f.coverage (e.symm z) (by rwa [hd])
    rw [← Metric.infDist_image e.isometry, e.apply_symm_apply, Set.image_image] at hh
    exact hh

theorem mapTargetIsometry_apply (f : KleinerLottApprox p q δ) (e : Y ≃ᵢ Z) (x : X) :
    (f.mapTargetIsometry e).toFun x = e (f.toFun x) := rfl

def mapTargetIsometryAt (f : KleinerLottApprox p q δ) (e : Y ≃ᵢ Z)
    (z : Z) (he : e q = z) : KleinerLottApprox p z δ where
  error_pos := f.error_pos
  error_lt_one := f.error_lt_one
  toFun x := e (f.toFun x)
  basepoint := by rw [f.basepoint, he]
  distortion := (f.mapTargetIsometry e).distortion
  coverage y hy := (f.mapTargetIsometry e).coverage y (by rwa [he])

theorem mapTargetIsometryAt_apply (f : KleinerLottApprox p q δ) (e : Y ≃ᵢ Z)
    (z : Z) (he : e q = z) (x : X) :
    (f.mapTargetIsometryAt e z he).toFun x = e (f.toFun x) := rfl

def comapSourceIsometryAt (f : KleinerLottApprox p q δ) (e : Z ≃ᵢ X)
    (z : Z) (he : e z = p) : KleinerLottApprox z q δ where
  error_pos := f.error_pos
  error_lt_one := f.error_lt_one
  toFun x := f.toFun (e x)
  basepoint := by rw [he, f.basepoint]
  distortion x hx y hy := by
    have hx' : e x ∈ Metric.ball p δ⁻¹ := by
      simpa only [Metric.mem_ball, ← he, e.dist_eq] using hx
    have hy' : e y ∈ Metric.ball p δ⁻¹ := by
      simpa only [Metric.mem_ball, ← he, e.dist_eq] using hy
    simpa only [e.dist_eq] using f.distortion (e x) hx' (e y) hy'
  coverage y hy := by
    have hm : (fun x => f.toFun (e x)) '' Metric.ball z δ⁻¹ =
        f.toFun '' Metric.ball p δ⁻¹ := by
      rw [← Set.image_image, e.image_ball, he]
    rw [hm]
    exact f.coverage y hy

theorem comapSourceIsometryAt_apply (f : KleinerLottApprox p q δ) (e : Z ≃ᵢ X)
    (z : Z) (he : e z = p) (x : Z) :
    (f.comapSourceIsometryAt e z he).toFun x = f.toFun (e x) := rfl

def comapSourceIsometry (f : KleinerLottApprox p q δ) (e : Z ≃ᵢ X) :
    KleinerLottApprox (e.symm p) q δ :=
  f.comapSourceIsometryAt e (e.symm p) (e.apply_symm_apply p)

theorem comapSourceIsometry_apply (f : KleinerLottApprox p q δ) (e : Z ≃ᵢ X) (x : Z) :
    (f.comapSourceIsometry e).toFun x = f.toFun (e x) := rfl

end GC.MetricGeometry.KleinerLottApprox
