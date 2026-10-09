import DifferentialGeometry.Geometry.Measure.Area.Riemannian
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # First variation of a two-dimensional Gram density

Both tangent vectors and their base point may move, and the metric may vary.
Independence is required only at the contact parameter; conformality is not
required.
-/

noncomputable section

open Bundle Manifold DifferentialGeometry
open scoped Bundle Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Differentiate the actual area density of an independent moving tangent pair
from the derivatives of its three actual Gram coefficients. -/
theorem hasDerivAt_tangentTwoJacobian
    {G : ℝ → SmoothRiemannianMetric I M} {x : ℝ → M}
    {v w : ∀ r, TangentSpace I (x r)} {t A' B' C' : ℝ}
    (hA : HasDerivAt (fun r => (G r).inner (x r) (v r) (v r)) A' t)
    (hB : HasDerivAt (fun r => (G r).inner (x r) (v r) (w r)) B' t)
    (hC : HasDerivAt (fun r => (G r).inner (x r) (w r) (w r)) C' t)
    (hframe : LinearIndependent ℝ ![v t, w t]) :
    HasDerivAt (fun r => tangentTwoJacobian (G r) (v r) (w r))
      (((G t).inner (x t) (w t) (w t) * A' +
          (G t).inner (x t) (v t) (v t) * C' -
          2 * (G t).inner (x t) (v t) (w t) * B') /
        (2 * tangentTwoJacobian (G t) (v t) (w t))) t := by
  have hpos : 0 < tangentTwoJacobian (G t) (v t) (w t) := by
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(G t).toRiemannianMetric⟩
    change 0 < twoJacobian (v t) (w t)
    rw [twoJacobian_eq_sqrt_det_gram]
    exact Real.sqrt_pos.mpr (Matrix.posDef_gram_of_linearIndependent hframe).det_pos
  have hdet : (G t).inner (x t) (v t) (v t) * (G t).inner (x t) (w t) (w t) -
      (G t).inner (x t) (v t) (w t) ^ 2 ≠ 0 := (Real.sqrt_pos.mp hpos).ne'
  have hd := ((hA.mul hC).sub (hB.pow 2)).sqrt hdet
  simpa only [tangentTwoJacobian, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply,
    Nat.reduceSub, pow_one, Nat.cast_ofNat,
    mul_comm A' ((G t).inner (x t) (w t) (w t))] using hd

end DifferentialGeometry.Geometry
