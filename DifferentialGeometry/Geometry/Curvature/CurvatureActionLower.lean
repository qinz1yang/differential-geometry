import DifferentialGeometry.Tensor.RSTensor.CurvatureAction
import DifferentialGeometry.Geometry.Curvature.Contractions

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The curvature action expressed through the lowered `(0,4)` curvature tensor

Route-4 foundation for the curvature-action Leibniz `∇(Rm ∗ S) = ∇Rm ∗ S + Rm ∗ ∇S`
(`Geometry/Flow/RicciFlow/Evolution/BBSAllKBundledRoute.md`): rewrite the
`(1,3)`-based slotwise curvature action `curvatureAction0SAt (Rm13) (S)` as a pure
inverse-metric contraction of the **lowered** `(0,4)` curvature tensor `Rm04`
against `S`, with no `(1,3)` tensor remaining.  This is what lets the covariant
derivative of the curvature action be taken via the bundled tensor-product Leibniz
(`nabla0SFun_product_eval`) and `∇g⁻¹ = 0`, replacing the unavailable `∇(rm13)` with
the available `∇(Rm04) = nablaRm04Field`.

Assembled from `rm13_oneForm_apply_eq_sum_inv_flat` (`Geometry/Curvature/Contractions.lean`)
and `Rm04LowersRm13At` (`Geometry/Curvature/Components/Lowering.lean`).
-/

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
variable {x : M}

/-- **The slotwise curvature action through the lowered curvature tensor.**  In a
basis with inverse metric `gInv`, the `(1,3)` curvature action on a covariant
tensor `S` equals the inverse-metric contraction of the lowered `(0,4)` curvature
tensor `Rm04` against `S`:

`curvatureAction0SAt Rm13 S X Y slots =
  −Σ_q Σ_p (Σ_r gⁱ ᵖ ʳ · S(slots[q ↦ e_r])) · Rm04(X, Y, slots_q, e_p)`.

No `(1,3)` tensor remains on the right — only `Rm04`, `gInv`, and `S` — so its
covariant derivative is reachable by the tensor-product Leibniz + `∇g⁻¹ = 0`. -/
theorem curvatureAction0SAt_eq_rm04 {s : ℕ}
    (g : SmoothRiemannianMetric I M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasis_gen (I := I) g x basis gInv)
    (Rm13 : Tensor13Section (I := I) (M := M))
    (Rm04 : Tensor04At (I := I) (M := M) x)
    (hLower : Rm04LowersRm13At (I := I) g x (Rm13 x) Rm04)
    (S : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (X Y : TangentSpace I x) (slots : Fin s -> TangentSpace I x) :
    curvatureAction0SAt (I := I) Rm13 S X Y slots =
      -∑ q : Fin s, ∑ p : Idx,
        (∑ r : Idx, gInv p r * S (Function.update slots q (basis r))) *
          Rm04 (vec4 (I := I) X Y (slots q) (basis p)) := by
  unfold curvatureAction0SAt
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [rm13_oneForm_apply_eq_sum_inv_flat (I := I) g basis gInv hinv (Rm13 x)
    (oneFormAtSlot0S (I := I) S slots q) X Y (slots q)]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [oneFormAtSlot0S_apply]
  rw [(hLower X Y (slots q) (basis p)).symm]

end DifferentialGeometry.Integral.Connection
