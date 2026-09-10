import Batteries.Tactic.Alias
import DifferentialGeometry.Geometry.Submanifold.NormalBundle.Defs
import DifferentialGeometry.Bundle.Point

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion

variable {EN HN N E H M : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {gN : SmoothRiemannianMetric IN N}
  {gM : SmoothRiemannianMetric I M} {iota : N → M}

theorem normalSpaceAt_eq_top_of_subsingleton [Subsingleton N]
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N) :
    h.normalSpaceAt x = ⊤ := by
  apply h.normalSpaceAt_eq_top_of_derivative_eq_zero
  have hi : iota = fun _ ↦ iota x :=
    funext fun y ↦ congrArg iota (Subsingleton.elim y x)
  exact (mfderiv_congr hi).trans mfderiv_const

def normalSpaceAtContinuousLinearEquivTangentSpace [Subsingleton N]
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N) :
    h.normalSpaceAt x ≃L[ℝ] TangentSpace I (iota x) :=
  (ContinuousLinearEquiv.ofEq _ _ (h.normalSpaceAt_eq_top_of_subsingleton x)).trans
    Submodule.topContEquiv

@[simp]
theorem normalSpaceAtContinuousLinearEquivTangentSpace_apply [Subsingleton N]
    (h : IsRiemannianIsometricImmersion gN gM iota) (x : N) (v : h.normalSpaceAt x) :
    h.normalSpaceAtContinuousLinearEquivTangentSpace x v = (v : TangentSpace I (iota x)) :=
  rfl

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (h : IsRiemannianIsometricImmersion gN gM iota)
  [TopologicalSpace (TotalSpace F (fun x ↦ h.normalSpaceAt x))]
  [FiberBundle F (fun x ↦ h.normalSpaceAt x)]
  [VectorBundle ℝ F (fun x ↦ h.normalSpaceAt x)]

def normalBundleDiffeomorphTangentSpaceAt [Subsingleton N] (x : N) :
    TotalSpace F (fun y ↦ h.normalSpaceAt y)
      ≃ₘ⟮IN.prod 𝓘(ℝ, F), 𝓘(ℝ, TangentSpace I (iota x))⟯ TangentSpace I (iota x) :=
  (vectorBundleFiberDiffeomorph (IB := IN) (F := F) x).symm.trans
    (h.normalSpaceAtContinuousLinearEquivTangentSpace x).toDiffeomorph

@[simp]
theorem normalBundleDiffeomorphTangentSpaceAt_mk [Subsingleton N]
    (x : N) (v : h.normalSpaceAt x) :
    h.normalBundleDiffeomorphTangentSpaceAt F x (TotalSpace.mk x v) =
      (v : TangentSpace I (iota x)) := by
  simp [normalBundleDiffeomorphTangentSpaceAt]

theorem normalBundleDiffeomorphTangentSpaceAt_symm_coe [Subsingleton N]
    (x : N) (v : h.normalSpaceAt x) :
    (h.normalBundleDiffeomorphTangentSpaceAt F x).symm (v : TangentSpace I (iota x)) =
      TotalSpace.mk x v := by
  apply (h.normalBundleDiffeomorphTangentSpaceAt F x).injective
  simp

@[simp]
theorem normalBundleDiffeomorphTangentSpaceAt_zeroSection [Subsingleton N] (x : N) :
    h.normalBundleDiffeomorphTangentSpaceAt F x
      (Bundle.zeroSection F (fun y ↦ h.normalSpaceAt y) x) = 0 :=
  h.normalBundleDiffeomorphTangentSpaceAt_mk F x 0

@[simp]
theorem normalBundleDiffeomorphTangentSpaceAt_symm_zero [Subsingleton N] (x : N) :
    (h.normalBundleDiffeomorphTangentSpaceAt F x).symm 0 =
      Bundle.zeroSection F (fun y ↦ h.normalSpaceAt y) x := by
  apply (h.normalBundleDiffeomorphTangentSpaceAt F x).injective
  simp

end DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion

namespace Poincare.Geometry.IsRiemannianIsometricImmersion

alias normalSpaceAt_eq_top_of_subsingleton := DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalSpaceAt_eq_top_of_subsingleton
@[reducible] alias normalSpaceAtContinuousLinearEquivTangentSpace := DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalSpaceAtContinuousLinearEquivTangentSpace
alias normalSpaceAtContinuousLinearEquivTangentSpace_apply := DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalSpaceAtContinuousLinearEquivTangentSpace_apply
@[reducible] alias normalBundleDiffeomorphTangentSpaceAt := DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalBundleDiffeomorphTangentSpaceAt
alias normalBundleDiffeomorphTangentSpaceAt_mk := DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalBundleDiffeomorphTangentSpaceAt_mk
alias normalBundleDiffeomorphTangentSpaceAt_symm_coe := DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalBundleDiffeomorphTangentSpaceAt_symm_coe
alias normalBundleDiffeomorphTangentSpaceAt_zeroSection := DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalBundleDiffeomorphTangentSpaceAt_zeroSection
alias normalBundleDiffeomorphTangentSpaceAt_symm_zero := DifferentialGeometry.Geometry.IsRiemannianIsometricImmersion.normalBundleDiffeomorphTangentSpaceAt_symm_zero

end Poincare.Geometry.IsRiemannianIsometricImmersion
