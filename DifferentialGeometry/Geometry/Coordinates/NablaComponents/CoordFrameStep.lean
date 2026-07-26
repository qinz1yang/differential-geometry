import DifferentialGeometry.Geometry.Coordinates.NablaComponents.Tensor0S
import DifferentialGeometry.Geometry.Coordinates.Christoffel
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.Tensor0S

/-!
# Rank-general coordinate covariant-step component formula (P3 Gap B, producer 2)

The `(0,s)` coordinate-frame evaluation of the covariant derivative, for ARBITRARY
rank `s` — the generalisation of `nabla0SFun_two_eval_coordFrame` past rank 2.
Proved by specialising the rank-general moving-slot formula
`nabla0SFun_eval_coordFrame_moving_raw` to the coordinate frame (whose model
representation is the constant `finBasis`, trivialising the moving-slot
differentiability hypotheses), using `extDerivFun_real_eq_mfderiv` to identify the
directional term with `coordDeriv0SAt` and the Christoffel expansion of `cov`.

**DONE + axiom-clean** (`propext, Classical.choice, Quot.sound`).
`hpair` (coordinate-frame component smoothness) is discharged by the same-tree lemma
`tensor0S_eval_coordinateFrame_contMDiffAt` (Tensor0S.lean) — NOT by re-deriving via
`contMDiffAt_section_apply_gen`, which would have hit the two-tree `Tensor0SModel`
`NormedSpace` instance diamond in this file.  `term2` is the Christoffel expansion:
expand `(cov frame_a)(X) = Σ_k Γ^k_a • frame_k` (single-vector frame expansion via
`IsLocalFrameOn.toBasisAt.sum_repr`, coefficients identified with
`christoffelAlongInFrame`), push it through `α x₀`'s update slot by
`MultilinearMap.map_update_sum` + `ContinuousMultilinearMap.map_update_smul`, and
rewrite each `α x₀ (update V a frame_k)` as `coordComponent0SAt (α x₀)(update I0 a k)`
via `Function.update`/`coordinateFrameAt_toBasis_apply`.  term1 (extDerivFun →
`coordDeriv0SAt`) closes by `extDerivFun_real_eq_mfderiv` + `congr 1` (defeq).
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.Tensor.Coordinates

open Bundle Set Tensor0SBundle TensorLieDeriv
open scoped BigOperators Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ∞ M]
variable [IsManifold I (∞ : WithTop ℕ∞) M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

/-- **Producer (2): rank-general coordinate covariant-step component formula.** -/
theorem nabla0SFun_eval_coordFrame {s : ℕ}
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (α : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (x₀ : M) (I0 : Fin s → CoordinateIdx (𝕜 := Real) E) :
    (nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s cov X α x₀)
        (fun a => coordinateFrameAt (I := I) x₀ (I0 a) x₀) =
      coordDeriv0SAt (I := I) (fun x => X x) x₀ (fun x => α x) I0 -
        ∑ a : Fin s, ∑ k : CoordinateIdx (𝕜 := Real) E,
          christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
            (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ (X x₀) (I0 a) k *
            coordComponent0SAt (I := I) (α x₀) (Function.update I0 a k) := by
  rw [nabla0SFun_eval_coordFrame_moving_raw cov X
    (fun a => coordinateFrameAt (I := I) x₀ (I0 a)) α x₀ ?hpair ?hV ?hVmodel ?hcoord]
  · rw [extDerivFun_real_eq_mfderiv]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    have hcov :
        (cov (coordinateFrameAt (I := I) x₀ (I0 a)) x₀) (X x₀) =
          ∑ k : CoordinateIdx (𝕜 := Real) E,
            christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
              (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ (X x₀) (I0 a) k •
              coordinateFrameAt (I := I) x₀ k x₀ := by
      have hx₀ := coordinateFrameAt_mem (I := I) x₀
      simpa [christoffelAlongInFrame, IsLocalFrameOn.coeff, hx₀,
        IsLocalFrameOn.toBasisAt_coe] using
        (((coordinateFrameAt_isLocalFrame_one (I := I) x₀).toBasisAt hx₀).sum_repr
          ((cov (coordinateFrameAt (I := I) x₀ (I0 a)) x₀) (X x₀))).symm
    calc
      α x₀ (Function.update (fun b : Fin s => coordinateFrameAt (I := I) x₀ (I0 b) x₀) a
            ((cov (coordinateFrameAt (I := I) x₀ (I0 a)) x₀) (X x₀)))
          = α x₀ (Function.update (fun b : Fin s => coordinateFrameAt (I := I) x₀ (I0 b) x₀) a
              (∑ k : CoordinateIdx (𝕜 := Real) E,
                christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                  (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ (X x₀) (I0 a) k •
                  coordinateFrameAt (I := I) x₀ k x₀)) := by rw [hcov]
      _ = ∑ k : CoordinateIdx (𝕜 := Real) E,
            α x₀ (Function.update (fun b : Fin s => coordinateFrameAt (I := I) x₀ (I0 b) x₀) a
              (christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ (X x₀) (I0 a) k •
                coordinateFrameAt (I := I) x₀ k x₀)) := by
            simpa using
              (α x₀).toMultilinearMap.map_update_sum
                (Finset.univ : Finset (CoordinateIdx (𝕜 := Real) E)) a
                (fun k : CoordinateIdx (𝕜 := Real) E =>
                  christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
                    (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ (X x₀) (I0 a) k •
                    coordinateFrameAt (I := I) x₀ k x₀)
                (fun b : Fin s => coordinateFrameAt (I := I) x₀ (I0 b) x₀)
      _ = ∑ k : CoordinateIdx (𝕜 := Real) E,
            christoffelAlongInFrame cov (coordinateFrameAt (I := I) x₀)
              (coordinateFrameAt_isLocalFrame_one (I := I) x₀) x₀ (X x₀) (I0 a) k *
              coordComponent0SAt (I := I) (α x₀) (Function.update I0 a k) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            have hslot :
                (fun b : Fin s => coordinateFrameAt (I := I) x₀ (Function.update I0 a k b) x₀) =
                  Function.update (fun b : Fin s => coordinateFrameAt (I := I) x₀ (I0 b) x₀) a
                    (coordinateFrameAt (I := I) x₀ k x₀) := by
              funext b
              by_cases hb : b = a
              · subst hb; simp
              · simp [hb]
            have hcomp :
                coordComponent0SAt (I := I) (α x₀) (Function.update I0 a k) =
                  α x₀ (Function.update (fun b : Fin s => coordinateFrameAt (I := I) x₀ (I0 b) x₀) a
                    (coordinateFrameAt (I := I) x₀ k x₀)) := by
              simp only [coordComponent0SAt, component0S, coordinateFrameAt_toBasis_apply]
              rw [hslot]
            rw [(α x₀).map_update_smul, hcomp, smul_eq_mul]
  case hpair =>
    exact (tensor0S_eval_coordinateFrame_contMDiffAt (I := I) α x₀ I0).mdifferentiableAt
      (by simp)
  case hV => exact fun a => coordinateFrameAt_mdifferentiableAt (I := I) x₀ (I0 a)
  case hVmodel =>
    intro a
    exact tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
      (coordinateFrameAt (I := I) x₀ (I0 a)) x₀
      ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
        (coordinateFrameSet_open (I := I) x₀) (coordinateFrameAt_mem (I := I) x₀) (I0 a))
  case hcoord =>
    intro a i
    exact tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
      (coordinateFrameAt (I := I) x₀ (I0 a)) x₀
      ((coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
        (coordinateFrameSet_open (I := I) x₀) (coordinateFrameAt_mem (I := I) x₀) (I0 a)) i

end DifferentialGeometry.Tensor.Coordinates
