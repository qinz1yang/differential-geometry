import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Smooth inverse Gram operators recover the actual orthogonal normal projector. -/

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace GC.MetricGeometry

variable {E H X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [NormedAddCommGroup X] [NormedSpace ℝ X]

def normalGramOperator (A : E →L[ℝ] H) : E →L[ℝ] E := A.adjoint.comp A

def normalGramProjector (A : E →L[ℝ] H) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H - A.comp ((normalGramOperator A).inverse.comp A.adjoint)

theorem normalGramOperator_isInvertible (A : E →L[ℝ] H) (hA : Function.Injective A) :
    (normalGramOperator A).IsInvertible := by
  have hi : Function.Injective (normalGramOperator A) :=
    (A.adjoint_comp_self_injective_iff).mpr hA
  let e := (LinearEquiv.ofBijective (normalGramOperator A).toLinearMap
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

theorem normalGramProjector_eq_starProjection (A : E →L[ℝ] H)
    (hA : Function.Injective A) :
    normalGramProjector A = (LinearMap.range A.toLinearMap)ᗮ.starProjection := by
  let R := LinearMap.range A.toLinearMap
  have hG := normalGramOperator_isInvertible A hA
  have hp : A.comp ((normalGramOperator A).inverse.comp A.adjoint) = R.starProjection := by
    ext u
    symm
    apply R.eq_starProjection_of_mem_orthogonal
    · exact ⟨_, rfl⟩
    · rw [Submodule.mem_orthogonal']
      rintro w ⟨v, rfl⟩
      have hz : A.adjoint (u - A ((normalGramOperator A).inverse (A.adjoint u))) = 0 := by
        rw [map_sub]
        change A.adjoint u - normalGramOperator A
          ((normalGramOperator A).inverse (A.adjoint u)) = 0
        rw [hG.self_apply_inverse, sub_self]
      change inner ℝ (u - A ((normalGramOperator A).inverse (A.adjoint u))) (A v) = 0
      rw [← A.adjoint_inner_left]
      simp only [hz, inner_zero_left]
  rw [Submodule.starProjection_orthogonal]
  exact congrArg (fun B : H →L[ℝ] H => ContinuousLinearMap.id ℝ H - B) hp

theorem contDiffAt_normalGramProjector {n : WithTop ℕ∞} {A : X → E →L[ℝ] H} {x : X}
    (hA : ContDiffAt ℝ n A x) (hinj : Function.Injective (A x)) :
    ContDiffAt ℝ n (fun y => normalGramProjector (A y)) x := by
  let J : (E →L[ℝ] H) →L[ℝ] (H →L[ℝ] E) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have ha : ContDiffAt ℝ n (fun y => (A y).adjoint) x := J.contDiff.contDiffAt.comp x hA
  have hg : ContDiffAt ℝ n (fun y => normalGramOperator (A y)) x := ha.clm_comp hA
  have hi0 : ContDiffAt ℝ n (fun B : E →L[ℝ] E => B.inverse)
      (normalGramOperator (A x)) :=
    (normalGramOperator_isInvertible (A x) hinj).contDiffAt_map_inverse
  have hi : ContDiffAt ℝ n (fun y => (normalGramOperator (A y)).inverse) x :=
    ContDiffAt.comp (f := fun y => normalGramOperator (A y))
      (g := fun B : E →L[ℝ] E => B.inverse) x hi0 hg
  exact contDiffAt_const.sub (hA.clm_comp (hi.clm_comp ha))

theorem normalGramProjector_identity : normalGramProjector (ContinuousLinearMap.id ℝ E) = 0 := by
  rw [normalGramProjector_eq_starProjection _ Function.injective_id]
  simp

theorem contDiff_normalGramProjector_identity :
    ContDiff ℝ ∞ (fun _x : E => normalGramProjector (ContinuousLinearMap.id ℝ E)) :=
  contDiff_const

end GC.MetricGeometry
