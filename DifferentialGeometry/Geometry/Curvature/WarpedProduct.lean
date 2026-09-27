import DifferentialGeometry.Geometry.Geodesic.Equation.Koszul

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

def warpedPairing {F : Type*}
    (f : Real) (h : F → F → Real) (X Y : Real × F) : Real :=
  X.1 * Y.1 + f ^ 2 * h X.2 Y.2

def warpedRadialCurvature (f fpp : Real) : Real :=
  -fpp / f

def warpedTangentialCurvature (f fp : Real) : Real :=
  (1 - fp ^ 2) / f ^ 2

def warpedCurvatureNumerator {F : Type*} [AddCommGroup F] [Module Real F]
    (f fp fpp : Real) (h : F → F → Real)
    (fiberRm : F → F → F → F → Real)
    (a b : Real) (u v : F) : Real :=
  -(f * fpp) * h (a • v - b • u) (a • v - b • u)
    + f ^ 2 * fiberRm u v v u
    - f ^ 2 * fp ^ 2 * (h u u * h v v - h u v * h u v)

def warpedConnectionDifference {F : Type*} [AddCommGroup F] [Module Real F]
    (f fp : Real) (h : F → F → Real) (X Y : Real × F) : Real × F :=
  (-(f * fp * h X.2 Y.2),
    (fp / f) • (X.1 • Y.2 + Y.1 • X.2))

theorem koszulCov_eq_warpedPairing {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (f fp : Real) (hf : f ≠ 0)
    (h : F →ₗ[Real] F →ₗ[Real] Real)
    (D : (Real × F) →L[Real] (Real × F) →L[Real]
      (Real × F) →L[Real] Real)
    (hD : ∀ X Y Z, D X Y Z =
      2 * f * fp * X.1 * h Y.2 Z.2)
    (X Y Z : Real × F) :
    MetricKoszul.koszulCov D X Y Z =
      warpedPairing f (fun x y => h x y) (warpedConnectionDifference f fp
        (fun x y => h x y) X Y) Z := by
  rw [MetricKoszul.koszul_cov_apply, hD X Y Z, hD Y X Z, hD Z X Y]
  rcases X with ⟨a, u⟩
  rcases Y with ⟨b, v⟩
  rcases Z with ⟨c, w⟩
  simp [warpedPairing, warpedConnectionDifference]
  field_simp [hf]
  ring

def warpedConnectionDifferenceDerivative {F : Type*} [AddCommGroup F] [Module Real F]
    (f fp fpp : Real) (h : F → F → Real)
    (X Y Z : Real × F) : Real × F :=
  (-X.1 * (fp ^ 2 + f * fpp) * h Y.2 Z.2,
    (X.1 * ((f * fpp - fp ^ 2) / f ^ 2)) •
      (Y.1 • Z.2 + Z.1 • Y.2))

def warpedCurvatureOperator {F : Type*} [AddCommGroup F] [Module Real F]
    (f fp fpp : Real) (h : F → F → Real)
    (fiberR : F → F → F → F) (X Y Z : Real × F) : Real × F :=
  (0, fiberR X.2 Y.2 Z.2)
    + warpedConnectionDifferenceDerivative f fp fpp h X Y Z
    - warpedConnectionDifferenceDerivative f fp fpp h Y X Z
    + warpedConnectionDifference f fp h X (warpedConnectionDifference f fp h Y Z)
    - warpedConnectionDifference f fp h Y (warpedConnectionDifference f fp h X Z)

theorem warpedPairing_warpedCurvatureOperator {F : Type*} [AddCommGroup F] [Module Real F]
    (f fp fpp : Real) (hf : f ≠ 0)
    (h : F →ₗ[Real] F →ₗ[Real] Real)
    (hsymm : ∀ u v, h u v = h v u)
    (fiberR : F → F → F → F) (a b : Real) (u v : F) :
    warpedPairing f (fun x y => h x y) (a, u)
        (warpedCurvatureOperator f fp fpp (fun x y => h x y) fiberR
          (a, u) (b, v) (b, v)) =
      warpedCurvatureNumerator f fp fpp (fun x y => h x y)
        (fun x y z w => h w (fiberR x y z)) a b u v := by
  have hvu : h v u = h u v := hsymm v u
  simp [warpedPairing, warpedCurvatureOperator, warpedConnectionDifferenceDerivative,
    warpedConnectionDifference, warpedCurvatureNumerator, hvu]
  field_simp [hf]
  ring

theorem warpedCurvatureNumerator_eq_of_unit_curvature {F : Type*} [AddCommGroup F] [Module Real F]
    (f fp fpp : Real) (h : F → F → Real)
    (fiberRm : F → F → F → F → Real)
    (a b : Real) (u v : F)
    (hround : fiberRm u v v u = h u u * h v v - h u v * h u v) :
    warpedCurvatureNumerator f fp fpp h fiberRm a b u v =
      -(f * fpp) * h (a • v - b • u) (a • v - b • u)
        + f ^ 2 * (1 - fp ^ 2) *
          (h u u * h v v - h u v * h u v) := by
  rw [warpedCurvatureNumerator, hround]
  ring

theorem warpedPairing_warpedCurvatureOperator_eq_radial_add_tangential
    {F : Type*} [AddCommGroup F] [Module Real F]
    (f fp fpp : Real) (hf : f ≠ 0)
    (h : F →ₗ[Real] F →ₗ[Real] Real)
    (hsymm : ∀ u v, h u v = h v u)
    (fiberR : F → F → F → F) (a b : Real) (u v : F)
    (hround : h u (fiberR u v v) =
      h u u * h v v - h u v * h u v) :
    warpedPairing f (fun x y => h x y) (a, u)
        (warpedCurvatureOperator f fp fpp (fun x y => h x y) fiberR
          (a, u) (b, v) (b, v)) =
      warpedRadialCurvature f fpp *
          (f ^ 2 * h (a • v - b • u) (a • v - b • u))
        + warpedTangentialCurvature f fp *
          (f ^ 4 * (h u u * h v v - h u v * h u v)) := by
  calc
    _ = warpedCurvatureNumerator f fp fpp (fun x y => h x y)
        (fun x y z w => h w (fiberR x y z)) a b u v :=
      warpedPairing_warpedCurvatureOperator f fp fpp hf h hsymm fiberR a b u v
    _ = -(f * fpp) * h (a • v - b • u) (a • v - b • u)
        + f ^ 2 * (1 - fp ^ 2) *
          (h u u * h v v - h u v * h u v) :=
      warpedCurvatureNumerator_eq_of_unit_curvature f fp fpp (fun x y => h x y)
        (fun x y z w => h w (fiberR x y z)) a b u v hround
    _ = _ := by
      simp only [warpedRadialCurvature, warpedTangentialCurvature]
      field_simp [hf]

end Curvature
end Geometry
end DifferentialGeometry
