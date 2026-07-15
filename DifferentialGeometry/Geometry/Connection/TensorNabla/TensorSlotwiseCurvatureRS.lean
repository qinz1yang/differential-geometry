import DifferentialGeometry.Geometry.Connection.TensorNabla.TensorSlotwiseCurvature

/-!
# Slot-wise curvature formula for the covariant `(r, s)`-tensor connection

For the Levi-Civita connection `LeviCivita g` of a smooth Riemannian metric `g`, the induced
covariant derivative `tensorCov g r s` on the `(r, s)`-tensor bundle has a Riemann curvature
operator that acts **slot-wise** through the base-tangent curvature, with the *covariant* slots
contributing as in the pure `(0, t)` case and the *contravariant* slots contributing with the
opposite sign (the adjoint action). This is the rank-generic analogue of the proven `(0, t)`
slot-wise formula `riemannSec_tensor0SCov_apply_eval`.

The `(r, s)`-tensor bundle is, by definition, the Hom-bundle
`TensorRSSpace r s I x = Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x`, and the `(r, s)`-tensor
connection `tensorCov g r s = tensorRSCovariantDerivative r s (LeviCivita g)` is, by construction
(`TensorRSNabla.lean`), the **single** generic Hom-bundle covariant derivative
`homBundleCovariantDerivativeGen` with source bundle the `(0, r)`-tensors and target bundle the
`(0, s)`-tensors. Consequently its curvature is governed by the generic Hom curvature–Leibniz rule
`riemannSec_homBundleGen_apply_eq` (`HomBundleCurvatureLeibniz.lean`):

```
R^{Hom}(X, W) φ = R_V ∘ φ − φ ∘ R_U,
```

where `R_V = R^{(0,s)}` is the target `(0, s)`-tensor curvature (the *covariant* slots) and
`R_U = R^{(0,r)}` is the source `(0, r)`-tensor curvature (the *contravariant* slots, entering
through the `U`-side of the Hom structure with the opposite sign). The contravariant slots are not
represented by dual spaces or iterated Hom: they are exactly the source bundle of the one Hom step,
and the `U`-side term `φ ∘ R_U` of the generic Hom curvature is precisely the contravariant
direction.

## Main result

* `riemannSec_tensorCov_apply_eval` — the rank-generic slot-wise curvature formula in the
  `(r, s)` fibre-evaluation idiom: the `(r, s)`-tensor curvature applied to an `(r, s)`-tensor
  section `τ`, evaluated on a `(0, r)`-tensor section `Y` and read on a covariant tuple
  `u : Fin s → T_x M`, equals the `(0, s)`-tensor curvature of the paired section `b ↦ τ b (Y b)`
  (covariant slots) minus the value of `τ x` on the `(0, r)`-tensor curvature of `Y` (contravariant
  slots, opposite sign). Both right-hand curvatures are the proven `(0, t)` tensor curvatures, each
  of which expands slot-wise through the base-tangent curvature by
  `riemannSec_tensor0SCov_apply_eval`.
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

/-- **Rank-generic slot-wise curvature formula for the covariant `(r, s)`-tensor connection.**
For smooth tangent fields `X, W`, a smooth `(r, s)`-tensor section `τ`, a smooth `(0, r)`-tensor
section `Y`, a point `x`, and a covariant tuple `u : Fin s → T_x M`, the Riemann curvature of the
`(r, s)`-tensor connection `tensorCov g r s`, applied to `τ`, evaluated on `Y x`, and read on `u`,
decomposes as

```
toModel ((R^{(r,s)}(X, W) τ x)(Y x)) u
  = toModel (R^{(0,s)}(X, W) (b ↦ τ b (Y b)) x) u            -- covariant slots
    − toModel (τ x (R^{(0,r)}(X, W) Y x)) u,                  -- contravariant slots (opposite sign)
```

where `R^{(r,s)} = riemannSec (tensorCov g r s)`, `R^{(0,s)} = riemannSec (tensor0SCovariantDerivative s …)`
and `R^{(0,r)} = riemannSec (tensor0SCovariantDerivative r …)` are the tensor Riemann curvatures of
the corresponding induced connections.

This is the rank-`r` lift of the slot-wise `(0, t)` formula. The `(r, s)`-tensor bundle is the
Hom-bundle from `(0, r)`- to `(0, s)`-tensors and the `(r, s)`-connection is the single generic
Hom-bundle covariant derivative `homBundleCovariantDerivativeGen` on it; the displayed identity is
the generic Hom curvature–Leibniz rule `riemannSec_homBundleGen_apply_eq` for that one step,
`R^{Hom} φ = R_V ∘ φ − φ ∘ R_U`, read fibrewise on `u`. The covariant slots are the target side
`R_V = R^{(0,s)}` (paired section) and the contravariant slots are the source side `R_U = R^{(0,r)}`
acting through `τ x` with the opposite sign. Each of the two right-hand `(0, t)` curvatures expands
into the explicit base-tangent slot sum by `riemannSec_tensor0SCov_apply_eval`. -/
theorem riemannSec_tensorCov_apply_eval
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (X W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (τ : Cₛ^∞⟮I; TensorRSModel r s ℝ E, (fun x : M => TensorRSSpace r s I x)⟯)
    (Y : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun x : M => Tensor0SSpace r I x)⟯)
    (x : M) (u : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            riemannSec (tensorCov (I := I) g r s)
              (fun b => X b) (fun b => W b) (fun b => τ b) x) (Y x)) u =
      Tensor0SSpace.toModel
          (riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (fun b => X b) (fun b => W b)
            (fun b => (show Tensor0SSpace r I b →L[ℝ] Tensor0SSpace s I b from τ b) (Y b)) x) u -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from τ x)
            (riemannSec (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
              (fun b => X b) (fun b => W b) (fun b => Y b) x)) u := by
  classical
  have hkey :=
    HomConnectionGen.riemannSec_homBundleGen_apply_eq I M
      (Tensor0SModel r ℝ E) (fun x : M => Tensor0SSpace r I x)
      (Tensor0SModel s ℝ E) (fun x : M => Tensor0SSpace s I x)
      (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
      (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
      X W τ Y x

  have heq :
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          riemannSec (tensorCov (I := I) g r s)
            (fun b => X b) (fun b => W b) (fun b => τ b) x) (Y x) =
        riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (fun b => X b) (fun b => W b)
            (HomConnectionGen.pairedSection (M := M)
              (U := fun x : M => Tensor0SSpace r I x) (V := fun x : M => Tensor0SSpace s I x)
              (fun b => τ b) (fun b => Y b)) x -
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from τ x)
            (riemannSec (tensor0SCovariantDerivative I M r (LeviCivita (I := I) g))
              (fun b => X b) (fun b => W b) (fun b => Y b) x) := hkey
  rw [heq, Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rfl

end Connection
end Integral
end DifferentialGeometry

end
