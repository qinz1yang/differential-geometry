import DifferentialGeometry.Geometry.Connection.MetricCompatibility.CovGradCovDerivSecondOrderCommutation
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.DifferentiatedSlotwiseCurvature

/-!
# Identifying the abstract second-order curvature with the differentiated `(0, s)`-tensor curvature

The rank-generic second-order curvature object `nablaTensorCurvSec`
(`CovGradCovDerivSecondOrderCommutation`) is the abstract differentiated Riemann curvature
`(∇_X R)(Y, Z) V` of *any* bundle covariant derivative `cov`, contracted on its two vector-field
slots and its section slot through the standard Leibniz formula. The differentiated `(0, s)`-tensor
curvature `nablaTensor0SCurv` (`DifferentiatedSlotwiseCurvature`) is the section-level differentiated
curvature of the *induced* `(0, s)`-tensor connection `tensor0SCovariantDerivative s (LeviCivita g)`,
phrased through the generic `nablaRiemannSec`.

This file identifies the two at the instantiation `cov = tensor0SCovariantDerivative s (LeviCivita g)`:
both unfold to the same four Leibniz terms — the leading connection-derivative of the section-level
curvature, the two antisymmetric vector-field slots differentiated by the *tangent* Levi-Civita
connection, and the section slot differentiated by the *tensor* connection. The identification is
therefore definitional. It mirrors the proven first-order identification
`nablaBaseSlotCurv_eq_nablaCurvSec` / `nablaCurvSec_eq_nablaRiemannSec` one bundle higher, and it is
the bridge that lets the abstract second-order machinery `thirdOrder_commutation_abstract` (which
emits `nablaTensorCurvSec` of the `(0, s)`-tensor connection) be consumed by the moving-frame
curvature-line assembly, which is phrased throughout in terms of `nablaTensor0SCurv` (and its slot-wise
transfer, frame trace, and cyclic second Bianchi).

## Main results

* `nablaTensorCurvSec_tensor0SCov_eq_nablaTensor0SCurv` — the pointwise identification: the abstract
  second-order curvature of the `(0, s)`-tensor connection equals the differentiated `(0, s)`-tensor
  curvature, both at the four-Leibniz-term level (definitional).
* `nablaTensorCurvSec_diag_frameSum_eq_nablaTensor0SCurv_diag_frameSum` — the diagonal orthonormal-frame
  sum the kernel consumer pairs against: summing the abstract second-order curvature over the diagonal
  derivative/first-antisymmetric-slot pair `(Bᵢ, Bᵢ)` of the orthonormal frame equals the corresponding
  diagonal frame sum of `nablaTensor0SCurv`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open Tensor0SBundle Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

/-- **The abstract second-order curvature of the `(0, s)`-tensor connection is the differentiated
`(0, s)`-tensor curvature.** Instantiating the rank-generic differentiated curvature `nablaTensorCurvSec`
(`CovGradCovDerivSecondOrderCommutation`) at the induced tensor connection
`cov := tensor0SCovariantDerivative s (LeviCivita g)`, and feeding it the underlying raw fields of the
smooth tangent sections `X, Y, Z`, yields exactly the differentiated `(0, s)`-tensor curvature
`nablaTensor0SCurv g s X Y Z A` (`DifferentiatedSlotwiseCurvature`).

Both sides unfold to the same four Leibniz terms (`nablaTensorCurvSec_def`, `nablaTensor0SCurv_def`
through `nablaRiemannSec_def`): the leading derivative `cov.toFun (R(Y, Z) A) x (X x)` of the
section-level curvature `R(Y, Z) A = riemannSec cov Y Z A`, the two antisymmetric vector-field slots
`covApply (LeviCivita g) X Y`, `covApply (LeviCivita g) X Z` differentiated by the *tangent*
Levi-Civita connection, and the section slot `covApply cov X A` differentiated by the *tensor*
connection `cov`. The identification is therefore definitional, mirroring the first-order
`nablaCurvSec_eq_nablaRiemannSec` one bundle higher. -/
theorem nablaTensorCurvSec_tensor0SCov_eq_nablaTensor0SCurv
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (x : M) :
    nablaTensorCurvSec (I := I) g
        (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
        (fun b => X b) (fun b => Y b) (fun b => Z b) A x =
      nablaTensor0SCurv (I := I) g s X Y Z A x :=
  rfl

/-- **The diagonal orthonormal-frame sum of the abstract second-order curvature equals the diagonal
frame sum of the differentiated `(0, s)`-tensor curvature.** Summing the abstract second-order
curvature `nablaTensorCurvSec` of the `(0, s)`-tensor connection over the diagonal pair
`(Bᵢ, Bᵢ)` — the derivative direction and the first antisymmetric curvature slot both running over the
smooth `g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i` — paired with a fixed second
antisymmetric slot `Z` and section `A`, equals the corresponding diagonal frame sum of
`nablaTensor0SCurv`. This is the frame-summed shape produced by the abstract third-order commutation
`thirdOrder_commutation_abstract` (whose curvature class is `nablaTensorCurvSec g cov Bᵢ Bᵢ Z A`),
delivered in the `nablaTensor0SCurv` vocabulary the moving-frame curvature-line assembly consumes; it
is `nablaTensorCurvSec_tensor0SCov_eq_nablaTensor0SCurv` summed over the frame. -/
theorem nablaTensorCurvSec_diag_frameSum_eq_nablaTensor0SCurv_diag_frameSum
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (x : M) :
    ∑ i : Fin (Module.finrank ℝ E),
        nablaTensorCurvSec (I := I) g
          (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i)
          (fun b => Z b) A x =
      ∑ i : Fin (Module.finrank ℝ E),
        nablaTensor0SCurv (I := I) g s
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i))
          (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame_smooth (I := I) g x i)) Z A x :=
  Finset.sum_congr rfl fun i _ =>
    nablaTensorCurvSec_tensor0SCov_eq_nablaTensor0SCurv (I := I) g s
      (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i))
      (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i)) Z A x

end Connection
end Integral
end DifferentialGeometry
