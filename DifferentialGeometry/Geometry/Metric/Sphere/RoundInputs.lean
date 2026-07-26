import DifferentialGeometry.Geometry.Comparison.TangentNormDiamond
import DifferentialGeometry.Geometry.Metric.Sphere.RoundMetric

set_option autoImplicit false

/-!
# Standard inputs for the round sphere

This module packages the Riemannian-bundle instance defined by `roundMetric`
and canonical coordinate points on a Euclidean unit sphere.  These are the
instance and point inputs used by global round-sphere arguments.
-/

noncomputable section

open Bundle Metric
open scoped ENNReal Manifold

namespace DifferentialGeometry
namespace Geometry

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
variable {n : ℕ} [Fact (Module.finrank ℝ A = n + 1)]

/-- The tangent Riemannian-bundle structure induced by the round metric. -/
@[reducible] noncomputable def roundBundle :
    RiemannianBundle
      (fun x : sphere (0 : A) 1 => TangentSpace (𝓡 n) x) :=
  ⟨(roundMetric (E := A) (n := n)).toRiemannianMetric⟩

private instance sphereModel_neZero [NeZero n] :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]
  infer_instance

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- With `roundBundle` installed, the tangent extended norm is the square
root of the round-metric quadratic form. -/
theorem round_enorm [NeZero n] :
    letI : RiemannianBundle
        (fun x : sphere (0 : A) 1 => TangentSpace (𝓡 n) x) :=
      roundBundle (A := A) (n := n)
    ∀ (x : sphere (0 : A) 1) (w : TangentSpace (𝓡 n) x),
      ‖w‖ₑ = ENNReal.ofReal
        (Real.sqrt ((roundMetric (E := A) (n := n)).inner x w w)) := by
  letI : RiemannianBundle
      (fun x : sphere (0 : A) 1 => TangentSpace (𝓡 n) x) :=
    roundBundle (A := A) (n := n)
  intro x w
  simpa only using
    (Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
      (I := 𝓡 n) (roundMetric (E := A) (n := n)) x w)

/-- The coordinate unit vector indexed by `i`, regarded as a point of the
Euclidean unit sphere. -/
def sphereBasisPt {m : ℕ} (i : Fin m) :
    sphere (0 : EuclideanSpace ℝ (Fin m)) 1 :=
  ⟨EuclideanSpace.single i 1, by
    rw [mem_sphere_zero_iff_norm, PiLp.norm_single]
    norm_num⟩

/-- Distinct coordinate unit vectors give distinct points of the unit sphere. -/
theorem sphereBasisPt_ne {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    sphereBasisPt i ≠ sphereBasisPt j := by
  intro h
  have h' := congrArg
    (fun z : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      (z : EuclideanSpace ℝ (Fin m)) i) h
  simp [sphereBasisPt, hij] at h'

/-- Distinct coordinate unit vectors are not antipodal on the unit sphere. -/
theorem sphereBasisPt_ne_neg {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    sphereBasisPt j ≠ -sphereBasisPt i := by
  intro h
  have h' := congrArg
    (fun z : sphere (0 : EuclideanSpace ℝ (Fin m)) 1 =>
      (z : EuclideanSpace ℝ (Fin m)) j) h
  simp [sphereBasisPt, hij] at h'

/-- The first two coordinate unit vectors give distinct, non-antipodal
base points on the standard three-sphere. -/
theorem sphere3_basis :
    ∃ p q : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      p ≠ q ∧ q ≠ -p := by
  refine ⟨sphereBasisPt 0, sphereBasisPt 1, ?_, ?_⟩
  · exact sphereBasisPt_ne (by decide)
  · exact sphereBasisPt_ne_neg (by decide)

end Geometry
end DifferentialGeometry
