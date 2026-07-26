import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorSlotwiseCurvature
import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorSlotwiseCurvatureRS
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace

/-!
# Slot-trace tools for the integrated tensor Bochner–Weitzenböck identity

For the Levi-Civita connection `LeviCivita g` of a smooth Riemannian metric `g`, this file records the
pointwise **slot-trace tools** feeding the integrated tensor Bochner–Weitzenböck identity (the
curvature line's terminal quantitative content). They are unit-evaluation corollaries of the slot-wise
curvature formula `riemannSec_tensorCov_apply_eval` (`TensorSlotwiseCurvatureRS`) and the base-tangent
slot expansion `riemannSec_tensor0SCov_apply_eval` (`TensorSlotwiseCurvature`), packaged at the level
the moving-frame remainder bracket-sum consumes.

## Main results

* `riemannSec_tensorCov_baseSlot_eval` — the slot-trace bridge: the `(0, s)`-tensor Riemann curvature
  applied to a section value, read on a covariant tuple, is the negated base-tangent slot sum across
  the tensor's covariant slots (the `r = 0` specialisation of the rank-generic formula, with both
  residual curvatures expanded by the base-slot sum).
* `smoothOrthoFrame_riemannOp_trace_eq_ricci` — the frame-trace → Ricci collapse: the
  `smoothOrthoFrame`-trace of the base-tangent curvature `Z ↦ R(Bᵢ, v) w` is the Ricci tensor
  `Ric(v, w)`, the defining relation of the leading-slot Ricci contraction.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle Tensor0SNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

/-- **The slot-trace bridge for the `(0, s)`-tensor Riemann curvature on a section value (base-slot
sum form).** For smooth tangent fields `X, W`, a smooth `(0, s)`-tensor section `A`, a point `x`, and a
covariant tuple `u : Fin s → T_x M`, the Riemann curvature of the `(0, s)`-tensor connection acts as
the negated base-tangent slot sum across the covariant slots:

```
toModel (R^{(0,s)}(X, W) A x) u
  = − ∑ₖ toModel (A x) (Function.update u k (baseSlotCurv g X W x (u k))).
```

This is the `r = 0` specialisation of the rank-generic slot-wise formula
`riemannSec_tensorCov_apply_eval` (no contravariant slots), read directly from the base-tangent slot
expansion `riemannSec_tensor0SCov_apply_eval`; it is the single pointwise curvature ingredient of the
moving-frame remainder bracket-sum. -/
theorem riemannSec_tensorCov_baseSlot_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun b => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) b (A b)))
    (x : M) (u : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
          (fun b => X b) (fun b => W b) A x) u =
      - ∑ k : Fin s,
          Tensor0SSpace.toModel (A x)
            (Function.update u k (baseSlotCurv (I := I) g X W x (u k))) :=
  riemannSec_tensor0SCov_apply_eval (I := I) (M := M) g s X W A hA x u

/-- **The `smoothOrthoFrame`-trace of the base-tangent curvature is the Ricci tensor.** For the smooth
`g_x`-orthonormal frame `Bᵢ := smoothOrthoFrame g x i` and tangent vectors `v, w`, the orthonormal
trace of the curvature endomorphism `Z ↦ R(Bᵢ, v) w` is the Ricci tensor:
```
∑ᵢ g_x(R(Bᵢ, v) w, Bᵢ) = Ric(v, w).
```
This is the orthonormal-trace Ricci formula `ricciTensor_eq_orthonormal_trace` specialised to the
center-orthonormal smooth frame `smoothOrthoFrame g x` (`smoothOrthoFrame_orthonormal_at_center`). It
is the frame-Ricci collapse feeding the leading-slot Ricci-trace contraction of the moving-frame
remainder. -/
theorem smoothOrthoFrame_riemannOp_trace_eq_ricci
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
        g.inner x (riemannOp (LeviCivita (I := I) g) x
          (smoothOrthoFrame (I := I) g x i x) v w)
          (smoothOrthoFrame (I := I) g x i x) =
      ricciTensor (I := I) g x v w :=
  (ricciTensor_eq_orthonormal_trace (I := I) g x v w
    (fun i => smoothOrthoFrame (I := I) g x i x)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)).symm

end Connection
end Integral
end DifferentialGeometry

end
