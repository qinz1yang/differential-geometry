import DifferentialGeometry.Topology.ProjectiveSpace.SphereQuotient
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section

namespace Poincare.ProjectiveSpace

def coordinateExtensionHomeomorph (n : ℕ) :
    Projectivization ℝ ((Fin n → ℝ) × ℝ) ≃ₜ Projectivization ℝ (Fin (n + 1) → ℝ) :=
  homeomorphMap ((ContinuousLinearEquiv.prodComm ℝ (Fin n → ℝ) ℝ).trans
    (Fin.consEquivL ℝ (fun _ : Fin (n + 1) ↦ ℝ)))


@[simp]
theorem coordinateExtensionHomeomorph_mk (n : ℕ) (v : Fin n → ℝ) (t : ℝ)
    (h : (v, t) ≠ 0) :
    coordinateExtensionHomeomorph n (Projectivization.mk ℝ (v, t) h) =
      Projectivization.mk ℝ (Fin.cons t v) (by
        intro he
        apply h
        exact Prod.ext (funext (fun i ↦ congrFun he i.succ)) (congrFun he 0)) := rfl

def euclideanCoordinateHomeomorph (n : ℕ) :
    Projectivization ℝ (EuclideanSpace ℝ (Fin n)) ≃ₜ Projectivization ℝ (Fin n → ℝ) :=
  homeomorphMap (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ))


@[simp]
theorem euclideanCoordinateHomeomorph_mk (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    euclideanCoordinateHomeomorph n (Projectivization.mk ℝ v hv) =
      Projectivization.mk ℝ (WithLp.ofLp v)
        ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).map_ne_zero_iff.mpr hv) := rfl

end Poincare.ProjectiveSpace
