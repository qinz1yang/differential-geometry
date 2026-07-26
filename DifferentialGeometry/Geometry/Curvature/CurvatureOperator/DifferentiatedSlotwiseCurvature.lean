import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ContractedBianchi

/-!
# The differentiated slot-wise curvature transfer

For the Levi-Civita connection `LeviCivita g` of a smooth Riemannian metric `g` on a closed manifold,
this file connects the **tangent-level** differentiated curvature `nablaCurvSec` (the Leibniz-contracted
`∇R` of `SecondBianchi`) to the **tensor-level** differentiated curvature action on `(0, s)`-tensors,
*slot by slot*. It is the differentiated analogue of the (undifferentiated) slot-wise curvature formula
`riemannSec_tensor0SCov_apply_eval` (`TensorSlotwiseCurvature`): where the undifferentiated tensor
curvature `R^{(s)}(X, W)` acts slot-wise through the base-tangent curvature `R^{TM}(X, W)`, the
differentiated tensor curvature `(∇_X R^{(s)})(Y, ·)` acts slot-wise through the tangent-level
`(∇_X R^{TM})(Y, ·) = nablaCurvSec (LeviCivita g) X Y · ·`.

## The differentiated curvature of a bundle covariant derivative

`nablaRiemannSec covT covV X Y Z A x` is the Leibniz-contracted covariant derivative of the
section-level Riemann curvature `riemannSec covV Y Z A` along the derivative direction `X`, for a
*bundle* covariant derivative `covV` on a vector bundle `V` whose two antisymmetric curvature slots
`Y, Z` are tangent fields differentiated by the *tangent* covariant derivative `covT`:
$$
  (\nabla_X R)(Y, Z) A := \nabla_X\bigl(R(Y, Z) A\bigr)
    - R(\nabla_X Y, Z) A - R(Y, \nabla_X Z) A - R(Y, Z)(\nabla_X A),
$$
with the outer derivative and the `∇_X A` correction taken in `covV`, and the slot derivatives
`∇_X Y, ∇_X Z` taken in `covT`. When `V` is the tangent bundle and `covV = covT`, this is exactly
`nablaCurvSec` (`nablaCurvSec_eq_nablaRiemannSec`); the genuine content here is the case `covV =
tensor0SCovariantDerivative s (LeviCivita g)`, the induced `(0, s)`-tensor connection.

## Main results

* `nablaRiemannSec` — the generic differentiated curvature of a bundle covariant derivative, the
  rank-`s` lift of `nablaCurvSec`.
* `nablaCurvSec_eq_nablaRiemannSec` — the tangent-bundle case is `nablaCurvSec` (the `s = 1` litmus
  collapses to this through the slot-wise transfer).
* `nablaTensor0SCurv_succ_consEval` — the differentiated leading-slot peel (the single inductive
  slot-algebra coherence brick), the differentiated analogue of
  `riemannSec_tensor0SCov_succ_consEval`.
* `nablaTensor0SCurv_apply_eval` — **the transfer**: the differentiated `(0, s)`-tensor curvature
  acts as the negated base-tangent slot sum through the tangent-level `nablaCurvSec`,
  $$
    \mathrm{toModel}\bigl((\nabla_X R^{(s)})(Y, \cdot) A\bigr)(u)
      = -\sum_k \mathrm{toModel}(A_x)\bigl(\mathrm{update}\,u\,k\,(\nabla_X R^{TM})(Y)(u_k)\bigr).
  $$
* `nablaTensorCov_baseSlot_eval` — the `(0, s)`-tensor restatement at the level the moving-frame
  remainder bracket-sum consumes, the differentiated analogue of `riemannSec_tensorCov_baseSlot_eval`.
* `nablaTensorCurv_frame_trace_eq_nablaRicci` — **the frame-traced trace bridge**: the orthonormal-frame
  trace of the differentiated base-slot curvature in its first antisymmetric slot, metric-paired against
  the frame, folds into the covariant derivative of the Ricci tensor (`nablaRicci`), through
  `nablaRicci_eq_frame_trace_nablaCurvSec`.
* `frame_sum_nablaTensor0SCurv_baseSlot_eval` — **the frame-traced corollary** consumed by the
  curvature-line assembly: the orthonormal-frame sum (over the leading antisymmetric curvature slot) of
  the differentiated `(0, s)`-tensor curvature is the negated slot sum of the frame-summed differentiated
  base-tangent curvature `∑ᵢ (∇_X R)(Bᵢ, Z)(·)` — the tensor-level Ricci/Bianchi fold, which collapses
  through `nablaTensorCurv_frame_trace_eq_nablaRicci` and the contracted second Bianchi identity
  `contracted_second_bianchi` (`div Ric = ½ d scal`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set FiberBundle NormedSpace Filter CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open Tensor0SBundle Tensor0SNabla

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- **The differentiated curvature of a bundle covariant derivative.** For a tangent covariant
derivative `covT` (differentiating the antisymmetric curvature slots `Y, Z`) and a bundle covariant
derivative `covV` on `V` (acting on the section `A` and the outer derivative), this is the standard
Leibniz formula
$$
  (\nabla_X R)(Y, Z) A := \nabla_X\bigl(R(Y, Z) A\bigr)
    - R(\nabla_X Y, Z) A - R(Y, \nabla_X Z) A - R(Y, Z)(\nabla_X A),
$$
with `R(Y, Z) A = riemannSec covV Y Z A` the section-level curvature operator of `covV`, the slot
derivatives `∇_X Y = covApply covT X Y` taken in the tangent connection, and `∇_X A = covApply covV X A`
in the bundle connection. This is the rank-generic lift of `nablaCurvSec` (`SecondBianchi`); the latter
is the special case `V = tangent bundle`, `covV = covT`. -/
def nablaRiemannSec (covT : CovariantDerivative I E (TangentSpace I : M → Type _))
    (covV : CovariantDerivative I F V)
    (X Y Z : Π b : M, TangentSpace I b) (A : Π b : M, V b) (x : M) : V x :=
  covV.toFun (fun b => riemannSec covV Y Z A b) x (X x)
    - riemannSec covV (covApply covT X Y) Z A x
    - riemannSec covV Y (covApply covT X Z) A x
    - riemannSec covV Y Z (covApply covV X A) x

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] [VectorBundle ℝ F V] in
/-- Definitional unfolding of `nablaRiemannSec`. -/
lemma nablaRiemannSec_def (covT : CovariantDerivative I E (TangentSpace I : M → Type _))
    (covV : CovariantDerivative I F V)
    (X Y Z : Π b : M, TangentSpace I b) (A : Π b : M, V b) (x : M) :
    nablaRiemannSec covT covV X Y Z A x =
      covV.toFun (fun b => riemannSec covV Y Z A b) x (X x)
        - riemannSec covV (covApply covT X Y) Z A x
        - riemannSec covV Y (covApply covT X Z) A x
        - riemannSec covV Y Z (covApply covV X A) x := rfl

end Generic

section TangentCase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] in
/-- **The tangent-bundle case of `nablaRiemannSec` is `nablaCurvSec`.** For a tangent covariant
derivative `cov`, the differentiated curvature `nablaRiemannSec cov cov X Y Z W` of the bundle
`covV := cov` on the tangent bundle is definitionally `nablaCurvSec cov X Y Z W` (`SecondBianchi`).
This is the `s = 1` litmus reference: the single-slot differentiated tensor curvature reduces to the
tangent-level differentiated curvature directly through the slot-wise transfer. -/
lemma nablaCurvSec_eq_nablaRiemannSec
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z W : Π b : M, TangentSpace I b) (x : M) :
    nablaCurvSec cov X Y Z W x = nablaRiemannSec cov cov X Y Z W x := rfl

end TangentCase

section GenericNablaHomLeibniz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
variable {E_U : Type*} [NormedAddCommGroup E_U] [NormedSpace ℝ E_U]
  [FiniteDimensional ℝ E_U] [CompleteSpace E_U]
variable {U : M → Type*} [∀ x, AddCommGroup (U x)] [∀ x, Module ℝ (U x)]
  [∀ x, TopologicalSpace (U x)]
  [TopologicalSpace (TotalSpace E_U U)] [FiberBundle E_U U] [VectorBundle ℝ E_U U]
  [∀ x, IsTopologicalAddGroup (U x)] [∀ x, ContinuousSMul ℝ (U x)]
  [ContMDiffVectorBundle ∞ E_U U I]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F]
variable {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [ContMDiffVectorBundle ∞ F V I]

/-- **Differentiated curvature–Leibniz rule for the generic Hom-bundle.** For a tangent covariant
derivative `covT` differentiating the antisymmetric/derivative slots, source/target bundle covariant
derivatives `cov_U`, `cov_V`, the induced Hom-bundle covariant derivative
`covHom := homBundleCovariantDerivativeGen cov_U cov_V`, smooth tangent fields `X, Y, Z`, a smooth
Hom-section `τ`, and a smooth `U`-section `W`, the differentiated Hom-bundle curvature applied to `τ`
and paired with `W x` splits through the source and target differentiated curvatures:
```
(nablaRiemannSec covT covHom X Y Z τ x)(W x) =
  nablaRiemannSec covT cov_V X Y Z (pairedSection τ W) x − τ x (nablaRiemannSec covT cov_U X Y Z W x).
```
This is the covariant derivative (along `X`, with the antisymmetric/section slots differentiated by
`covT`/`covHom`/`cov_V`/`cov_U`) of the undifferentiated curvature–Leibniz rule
`riemannSec_homBundleGen_apply_eq`; the eight mixed `(∇τ)(∇W)` cross terms generated by the second
differentiation cancel — the leading connection-derivative term's product-rule split against the
paired curvature section and the section-additivity split of the `∇_X(τ·W)`-correction term produce
the same two mixed monomials with opposite signs. It is the differentiated analogue of the single
inductive ingredient from which the differentiated slot-wise tensor curvature formula is assembled. -/
lemma nablaRiemannSec_homBundleGen_apply_eq
    (cov_U : CovariantDerivative I E_U U) [ContMDiffCovariantDerivative cov_U ∞]
    (cov_V : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov_V ∞]
    (covT : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative covT ∞]
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (τ : Cₛ^∞⟮I; E_U →L[ℝ] F, (fun x : M => U x →L[ℝ] V x)⟯)
    (W : Cₛ^∞⟮I; E_U, U⟯) (x : M) :
    (nablaRiemannSec covT (HomConnectionGen.homBundleCovariantDerivativeGen I M E_U U F V cov_U cov_V)
        (fun b => X b) (fun b => Y b) (fun b => Z b) (fun b => τ b) x) (W x) =
      nablaRiemannSec covT cov_V (fun b => X b) (fun b => Y b) (fun b => Z b)
          (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => W b)) x
        - τ x (nablaRiemannSec covT cov_U (fun b => X b) (fun b => Y b) (fun b => Z b)
            (fun b => W b) x) := by
  classical
  set covHom := HomConnectionGen.homBundleCovariantDerivativeGen I M E_U U F V cov_U cov_V with hcovHom

  set BXY : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (covApply covT (fun b => X b) (fun b => Y b))
      (covApply_contMDiff (cov := covT) X.contMDiff Y.contMDiff) with hBXY
  set BXZ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (covApply covT (fun b => X b) (fun b => Z b))
      (covApply_contMDiff (cov := covT) X.contMDiff Z.contMDiff) with hBXZ
  set RUW : Cₛ^∞⟮I; E_U, U⟯ :=
    ContMDiffSection.mk (fun b => riemannSec cov_U (fun b => Y b) (fun b => Z b) (fun b => W b) b)
      (riemannSec_contMDiff (cov := cov_U) Y.contMDiff Z.contMDiff W.contMDiff) with hRUW
  set DXW : Cₛ^∞⟮I; E_U, U⟯ :=
    ContMDiffSection.mk (covApply cov_U (fun b => X b) (fun b => W b))
      (covApply_contMDiff (cov := cov_U) X.contMDiff W.contMDiff) with hDXW
  set Dτ : Cₛ^∞⟮I; E_U →L[ℝ] F, (fun x : M => U x →L[ℝ] V x)⟯ :=
    ContMDiffSection.mk (covApply covHom (fun b => X b) (fun b => τ b))
      (covApply_contMDiff (cov := covHom) X.contMDiff τ.contMDiff) with hDτ

  have hτat : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U →L[ℝ] F))
      (fun y : M => TotalSpace.mk' (E_U →L[ℝ] F)
        (E := fun z : M => (U z →L[ℝ] V z)) y (τ y)) x :=
    (τ.contMDiff x).mdifferentiableAt (by simp)
  have hWat : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U))
      (fun y : M => TotalSpace.mk' E_U (E := U) y (W y)) x :=
    (W.contMDiff x).mdifferentiableAt (by simp)
  have hXat : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y => TotalSpace.mk' E (E := TangentSpace I) y (X y)) x :=
    (X.contMDiff x).mdifferentiableAt (by simp)
  have hRHτ_smooth : ContMDiff I (I.prod 𝓘(ℝ, E_U →L[ℝ] F)) ∞
      (fun b => TotalSpace.mk' (E_U →L[ℝ] F)
        (E := fun z : M => (U z →L[ℝ] V z)) b
          (riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b)) :=
    riemannSec_contMDiff (cov := covHom) Y.contMDiff Z.contMDiff τ.contMDiff
  have hRHτ_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U →L[ℝ] F))
      (fun b => TotalSpace.mk' (E_U →L[ℝ] F)
        (E := fun z : M => (U z →L[ℝ] V z)) b
          (riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b)) x :=
    (hRHτ_smooth x).mdifferentiableAt (by simp)
  have hRUW_at : MDifferentiableAt I (I.prod 𝓘(ℝ, E_U))
      (fun y : M => TotalSpace.mk' E_U (E := U) y (RUW y)) x :=
    (RUW.contMDiff x).mdifferentiableAt (by simp)

  have hPsec : (HomConnectionGen.pairedSection (M := M) (U := U) (V := V)
        (fun b => riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b) (fun b => W b)) =
      (fun b => riemannSec cov_V (fun b => Y b) (fun b => Z b)
          (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => W b)) b)
        - (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b)
            (fun b => RUW b)) := by
    funext b
    have hstar := HomConnectionGen.riemannSec_homBundleGen_apply_eq I M E_U U F V cov_U cov_V
      Y Z τ W b
    simp only [HomConnectionGen.pairedSection, Pi.sub_apply]
    rw [show RUW b = riemannSec cov_U (fun b => Y b) (fun b => Z b) (fun b => W b) b from rfl]
    rw [hstar]

  have hsm1 : MDiffAt (T% (fun b => riemannSec cov_V (fun b => Y b) (fun b => Z b)
      (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => W b)) b)) x := by
    have := riemannSec_contMDiff (cov := cov_V) Y.contMDiff Z.contMDiff
      (T := HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => W b))
      (ContMDiff.clm_bundle_apply (b := id) τ.contMDiff W.contMDiff)
    exact (this x).mdifferentiableAt (by simp)
  have hsm2 : MDiffAt (T% (HomConnectionGen.pairedSection (M := M) (U := U) (V := V)
      (fun b => τ b) (fun b => RUW b))) x :=
    ((ContMDiff.clm_bundle_apply (b := id) τ.contMDiff RUW.contMDiff) x).mdifferentiableAt (by simp)

  have hVadd : cov_V.toFun (fun b => riemannSec cov_V (fun b => Y b) (fun b => Z b)
          (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => W b)) b)
          x (X x) =
      cov_V.toFun (HomConnectionGen.pairedSection (M := M) (U := U) (V := V)
          (fun b => riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b)
          (fun b => W b)) x (X x)
        + cov_V.toFun (HomConnectionGen.pairedSection (M := M) (U := U) (V := V)
            (fun b => τ b) (fun b => RUW b)) x (X x) := by
    have hsplit : (fun b => riemannSec cov_V (fun b => Y b) (fun b => Z b)
          (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => W b)) b) =
        HomConnectionGen.pairedSection (M := M) (U := U) (V := V)
            (fun b => riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b) (fun b => W b)
          + HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => RUW b) := by
      rw [hPsec]; abel
    have hsmσW : MDiffAt (T% (HomConnectionGen.pairedSection (M := M) (U := U) (V := V)
        (fun b => riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b) (fun b => W b))) x :=
      ((ContMDiff.clm_bundle_apply (b := id) hRHτ_smooth W.contMDiff) x).mdifferentiableAt (by simp)
    rw [hsplit, cov_V.isCovariantDerivativeOnUniv.add hsmσW hsm2]
    rfl

  rw [nablaRiemannSec_def]
  simp only [ContinuousLinearMap.sub_apply]

  rw [show covHom.toFun
        (fun b => riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b) x (X x) (W x) =
      cov_V.toFun (HomConnectionGen.pairedSection (M := M) (U := U) (V := V)
          (fun b => riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b)
          (fun b => W b)) x (X x)
        - (riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) x)
            (cov_U.toFun (fun b => W b) x (X x)) from by
    have h := HomConnectionGen.cov_V_toFun_pairedSection_apply I M E_U U F V cov_U cov_V
      (σ := fun b => riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b)
      (Y := fun b => W b) hRHτ_at hWat (X x)
    rw [← hcovHom] at h
    rw [h]
    abel]
  rw [show cov_V.toFun (HomConnectionGen.pairedSection (M := M) (U := U) (V := V)
          (fun b => τ b) (fun b => RUW b)) x (X x) =
      (covHom.toFun (fun b => τ b) x (X x)) (RUW x)
        + τ x (cov_U.toFun (fun b => RUW b) x (X x)) from by
    have h := HomConnectionGen.cov_V_toFun_pairedSection_apply I M E_U U F V cov_U cov_V
      (σ := fun b => τ b) (Y := fun b => RUW b) hτat hRUW_at (X x)
    rw [← hcovHom] at h
    exact h] at hVadd

  rw [show cov_V.toFun (HomConnectionGen.pairedSection (M := M) (U := U) (V := V)
          (fun b => riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) b)
          (fun b => W b)) x (X x) =
      cov_V.toFun (fun b => riemannSec cov_V (fun b => Y b) (fun b => Z b)
          (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => W b)) b)
          x (X x)
        - ((covHom.toFun (fun b => τ b) x (X x)) (RUW x)
            + τ x (cov_U.toFun (fun b => RUW b) x (X x))) from
    (eq_sub_of_add_eq hVadd.symm)]

  rw [show riemannSec covHom (covApply covT (fun b => X b) (fun b => Y b)) (fun b => Z b)
        (fun b => τ b) x (W x) =
      (riemannSec covHom (fun b => BXY b) (fun b => Z b) (fun b => τ b) x) (W x) from rfl,
    HomConnectionGen.riemannSec_homBundleGen_apply_eq I M E_U U F V cov_U cov_V BXY Z τ W x]
  rw [show riemannSec covHom (fun b => Y b) (covApply covT (fun b => X b) (fun b => Z b))
        (fun b => τ b) x (W x) =
      (riemannSec covHom (fun b => Y b) (fun b => BXZ b) (fun b => τ b) x) (W x) from rfl,
    HomConnectionGen.riemannSec_homBundleGen_apply_eq I M E_U U F V cov_U cov_V Y BXZ τ W x]
  rw [show riemannSec covHom (fun b => Y b) (fun b => Z b)
        (covApply covHom (fun b => X b) (fun b => τ b)) x (W x) =
      (riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => Dτ b) x) (W x) from rfl,
    HomConnectionGen.riemannSec_homBundleGen_apply_eq I M E_U U F V cov_U cov_V Y Z Dτ W x]

  rw [show (riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) x)
        (cov_U.toFun (fun b => W b) x (X x)) =
      (riemannSec covHom (fun b => Y b) (fun b => Z b) (fun b => τ b) x) (DXW x) from rfl,
    HomConnectionGen.riemannSec_homBundleGen_apply_eq I M E_U U F V cov_U cov_V Y Z τ DXW x]

  rw [nablaRiemannSec_def, nablaRiemannSec_def, map_sub, map_sub, map_sub]

  rw [show covApply cov_V (fun b => X b)
        (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => W b)) =
      HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => Dτ b) (fun b => W b)
        + HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => DXW b) from by
    have h := HomConnectionGen.covApply_cov_V_pairedSection_eq I M E_U U F V cov_U cov_V X τ W
    rw [← hcovHom] at h
    rw [h]
    rfl]

  rw [show riemannSec cov_V (fun b => Y b) (fun b => Z b)
        (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => Dτ b) (fun b => W b)
          + HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => DXW b))
        x =
      riemannSec cov_V (fun b => Y b) (fun b => Z b)
          (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => Dτ b) (fun b => W b)) x
        + riemannSec cov_V (fun b => Y b) (fun b => Z b)
            (HomConnectionGen.pairedSection (M := M) (U := U) (V := V) (fun b => τ b) (fun b => DXW b)) x
      from by
    have hP1sm : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (HomConnectionGen.pairedSection
        (M := M) (U := U) (V := V) (fun b => Dτ b) (fun b => W b))) :=
      ContMDiff.clm_bundle_apply (b := id) Dτ.contMDiff W.contMDiff
    have hP2sm : ContMDiff I (I.prod 𝓘(ℝ, F)) ∞ (T% (HomConnectionGen.pairedSection
        (M := M) (U := U) (V := V) (fun b => τ b) (fun b => DXW b))) :=
      ContMDiff.clm_bundle_apply (b := id) τ.contMDiff DXW.contMDiff
    exact riemannSec_add_third (cov := cov_V)
      (Filter.Eventually.of_forall (fun b => (hP1sm b).mdifferentiableAt (by simp)))
      (Filter.Eventually.of_forall (fun b => (hP2sm b).mdifferentiableAt (by simp)))
      ((covApply_contMDiff (cov := cov_V) Z.contMDiff hP1sm x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov_V) Z.contMDiff hP2sm x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov_V) Z.contMDiff (hP1sm.add_section hP2sm) x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov_V) Y.contMDiff hP1sm x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov_V) Y.contMDiff hP2sm x).mdifferentiableAt (by simp))
      ((covApply_contMDiff (cov := cov_V) Y.contMDiff (hP1sm.add_section hP2sm) x).mdifferentiableAt (by simp))]

  simp only [hBXY, hBXZ, hDτ, hDXW, hRUW, ContMDiffSection.coeFn_mk]
  rw [show covApply covHom (fun b => X b) (fun b => τ b) x =
      covHom.toFun (fun b => τ b) x (X x) from rfl]
  abel

end GenericNablaHomLeibniz

section TensorTransfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] [I.Boundaryless]

/-- Smoothness predicate for a raw `(0, s)`-tensor section: the total-space map is `C^∞`. -/
private abbrev TensorSmooth (s : ℕ) (A : Π b : M, Tensor0SSpace s I b) : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
    (fun b => TotalSpace.mk' (Tensor0SModel s ℝ E)
      (E := fun z : M => Tensor0SSpace s I z) b (A b))

/-- **The differentiated base-tangent curvature acting on a fixed slot vector.** The tangent-level
differentiated curvature `(∇_X R^{TM})(Y, Z) u = nablaCurvSec (LeviCivita g) X Y Z (ext u) x`
(`SecondBianchi`), packaged on a fixed slot vector `u` through a smooth extension `ext u =
smoothExtensionTangent x u`. This is the differentiated analogue of `baseSlotCurv`; because
`nablaCurvSec` is the Leibniz-contracted curvature, this value is independent of the smooth extension
chosen (the `∇_X(ext u)`-correction in `nablaCurvSec` cancels the extension-dependence of the leading
derivative), so it is the genuine differentiated curvature `(∇_X R)(Y, Z) u` as a tensor in `u`. -/
def nablaBaseSlotCurv
    (g : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    TangentSpace I x :=
  nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
    (fun b => smoothExtensionTangent (I := I) x u b) x

/-- **The differentiated `(0, s)`-tensor curvature, the section-level differentiated curvature of the
induced `(0, s)`-tensor connection.** This specialises the generic `nablaRiemannSec` to the bundle
covariant derivative `covV := tensor0SCovariantDerivative s (LeviCivita g)` with antisymmetric slots
differentiated by the tangent connection `covT := LeviCivita g`. Its value at `x` is the
`(0, s)`-tensor `(∇_X R^{(s)})(Y, Z) A`, the Leibniz-contracted covariant derivative of the tensor
Riemann curvature `R^{(s)}(Y, Z) A = riemannSec (tensor0SCovariantDerivative s …) Y Z A`. -/
def nablaTensor0SCurv
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (x : M) : Tensor0SSpace s I x :=
  nablaRiemannSec (LeviCivita (I := I) g)
    (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
    (fun b => X b) (fun b => Y b) (fun b => Z b) A x

/-- Definitional unfolding of `nablaTensor0SCurv` into the four Leibniz terms. -/
lemma nablaTensor0SCurv_def
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (x : M) :
    nablaTensor0SCurv (I := I) g s X Y Z A x =
      (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)).toFun
          (fun b => riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (fun b => Y b) (fun b => Z b) A b) x (X x)
        - riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b)) (fun b => Z b) A x
        - riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (fun b => Y b) (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Z b)) A x
        - riemannSec (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
            (fun b => Y b) (fun b => Z b)
            (covApply (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
              (fun b => X b) A) x :=
  rfl

/-- The scalar `(0, 0)`-tensor curvature vanishes for *any* smooth raw direction fields `P, Q` and
smooth scalar section `A` (the rank-`0` flatness of the scalar connection, raw-field form). This
specialises `riemannSec_tensor0SCov_zero_eq_zero` after packaging the raw smooth fields as smooth
sections. -/
private lemma riemannSec_tensor0SCov_zero_raw_eq_zero
    (g : SmoothRiemannianMetric I M)
    {P Q : Π b : M, TangentSpace I b}
    (hP : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% P))
    (hQ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Q))
    (A : Π b : M, Tensor0SSpace 0 I b) (hA : TensorSmooth (I := I) 0 A) (x : M) :
    riemannSec (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)) P Q A x = 0 := by
  have hz := riemannSec_tensor0SCov_zero_eq_zero (I := I) (M := M) g
    (ContMDiffSection.mk P hP) (ContMDiffSection.mk Q hQ) A hA x
  simpa using hz

/-- **Base case `s = 0` of the differentiated slot-wise transfer.** The differentiated scalar
`(0, 0)`-tensor curvature vanishes: the scalar connection is flat, so its curvature is the zero
section and the differentiated curvature (the Leibniz contraction of a zero section) is zero. -/
theorem nablaTensor0SCurv_zero_eq_zero
    (g : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace 0 I b) (hA : TensorSmooth (I := I) 0 A) (x : M) :
    nablaTensor0SCurv (I := I) g 0 X Y Z A x = 0 := by
  classical
  rw [nablaTensor0SCurv_def]
  have hzero_sec : (fun b => riemannSec (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
      (fun b => Y b) (fun b => Z b) A b) = (0 : Π b : M, Tensor0SSpace 0 I b) := by
    funext b
    exact riemannSec_tensor0SCov_zero_eq_zero (I := I) (M := M) g Y Z A hA b
  rw [hzero_sec]
  have hlead : (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)).toFun
      (0 : Π b : M, Tensor0SSpace 0 I b) x (X x) = 0 := by
    rw [(tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)).isCovariantDerivativeOnUniv.zero
      (Set.mem_univ x)]
    simp
  rw [hlead]
  have hXY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply (LeviCivita (I := I) g)
      (fun b => X b) (fun b => Y b))) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) X.contMDiff Y.contMDiff
  have hXZ : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (covApply (LeviCivita (I := I) g)
      (fun b => X b) (fun b => Z b))) :=
    covApply_contMDiff (cov := LeviCivita (I := I) g) X.contMDiff Z.contMDiff
  rw [riemannSec_tensor0SCov_zero_raw_eq_zero (I := I) (M := M) g hXY Z.contMDiff A hA x,
    riemannSec_tensor0SCov_zero_raw_eq_zero (I := I) (M := M) g Y.contMDiff hXZ A hA x]
  have hcXA : TensorSmooth (I := I) 0 (covApply
      (tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)) (fun b => X b) A) :=
    covApply_contMDiff (cov := tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
      X.contMDiff hA
  rw [riemannSec_tensor0SCov_zero_raw_eq_zero (I := I) (M := M) g Y.contMDiff Z.contMDiff _ hcXA x]
  abel

/-- **Curry-conjugation of the differentiated `(0, s + 1)`-tensor curvature through `tensor0S_curry`.**
For smooth fields `X, Y, Z`, a smooth `(0, s + 1)`-tensor section `A`, and a point `x`, the curry of
the differentiated `(0, s + 1)`-tensor curvature coincides with the generic Hom-bundle differentiated
curvature `nablaRiemannSec` of the `homGenS` connection on the curried section:
```
tensor0S_curry s x (nablaTensor0SCurv g (s + 1) X Y Z A x) =
  nablaRiemannSec (LeviCivita g) (homGenS g s) X Y Z (curriedSection A) x.
```
This is the differentiated analogue of the curvature conjugation
`tensor0S_curry_riemannSec_tensor0SCov_succ_eq` (`TensorSlotwiseCurvature`): the four Leibniz terms of
`nablaTensor0SCurv` (`nablaTensor0SCurv_def`) are curried term by term — the three curvature terms by
the undifferentiated curvature conjugation `tensor0S_curry_riemannSec_tensor0SCov_succ_eq`, the leading
connection-derivative term and the inner-`covApply` section slot by the section conjugation
`tensor0S_curry_tensor0SCov_succ_eq_homGenS` — landing on the four Leibniz terms of `nablaRiemannSec`
of `homGenS` (`nablaRiemannSec_def`). -/
lemma tensor0S_curry_nablaTensor0SCurv_succ_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace (s + 1) I b) (hA : TensorSmooth (I := I) (s + 1) A) (x : M) :
    tensor0S_curry (I := I) (M := M) s x
        (nablaTensor0SCurv (I := I) g (s + 1) X Y Z A x) =
      nablaRiemannSec (LeviCivita (I := I) g) (homGenS (I := I) (M := M) g s)
        (fun b => X b) (fun b => Y b) (fun b => Z b) (curriedSection I M A) x := by
  classical

  have hA1 : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ((∞ : WithTop ℕ∞) + 1)
      (fun b => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) b (A b)) := by
    rw [show (∞ : WithTop ℕ∞) + 1 = ∞ from by simp]; exact hA
  have hAatAll : ∀ b : M, TensorSectionMDiffAt (I := I) (s + 1) A b := fun b =>
    (hA b).mdifferentiableAt (by simp)

  have hRYZ_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun b => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) b
          (riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (fun b => Y b) (fun b => Z b) A b)) :=
    riemannSec_contMDiff (cov := tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
      Y.contMDiff Z.contMDiff hA
  have hRYZ_at : TensorSectionMDiffAt (I := I) (s + 1)
      (fun b => riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => Y b) (fun b => Z b) A b) x :=
    (hRYZ_smooth x).mdifferentiableAt (by simp)

  have hcovApply_at : ∀ (P : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      TensorSectionMDiffAt (I := I) (s + 1)
        (covApply (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
          (fun b => P b) A) x := by
    intro P
    have hsm := covApply_contMDiffOn (cov := tensor0SCovariantDerivative I M (s + 1)
      (LeviCivita (I := I) g)) P.contMDiff hA1
    exact (hsm.contMDiffAt (Filter.univ_mem)).mdifferentiableAt (by simp)

  have hcurry_covApply : ∀ (P : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      curriedSection I M
          (covApply (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (fun b => P b) A) =
        covApply (homGenS (I := I) (M := M) g s) (fun b => P b) (curriedSection I M A) := by
    intro P
    funext b
    rw [curriedSection_apply, covApply_apply, covApply_apply,
      tensor0S_curry_tensor0SCov_succ_eq_homGenS (I := I) (M := M) g s A (hAatAll b) (P b)]

  have hcurry_RYZ :
      curriedSection I M
          (fun b => riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
            (fun b => Y b) (fun b => Z b) A b) =
        (fun b => riemannSec (homGenS (I := I) (M := M) g s)
          (fun b => Y b) (fun b => Z b) (curriedSection I M A) b) := by
    funext b
    rw [curriedSection_apply,
      tensor0S_curry_riemannSec_tensor0SCov_succ_eq (I := I) (M := M) g s Y Z A hA b]

  rw [nablaTensor0SCurv_def, nablaRiemannSec_def]
  rw [map_sub, map_sub, map_sub]

  rw [tensor0S_curry_tensor0SCov_succ_eq_homGenS (I := I) (M := M) g s
      (fun b => riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => Y b) (fun b => Z b) A b) hRYZ_at (X x), hcurry_RYZ]

  rw [show riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b)) (fun b => Z b) A x =
      riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => (ContMDiffSection.mk
          (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b))
          (covApply_contMDiff (cov := LeviCivita (I := I) g) X.contMDiff Y.contMDiff) : Π b : M, TangentSpace I b) b)
        (fun b => Z b) A x from rfl,
    tensor0S_curry_riemannSec_tensor0SCov_succ_eq (I := I) (M := M) g s
      (ContMDiffSection.mk (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b))
        (covApply_contMDiff (cov := LeviCivita (I := I) g) X.contMDiff Y.contMDiff)) Z A hA x]
  rw [show riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => Y b) (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Z b)) A x =
      riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => Y b)
        (fun b => (ContMDiffSection.mk
          (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Z b))
          (covApply_contMDiff (cov := LeviCivita (I := I) g) X.contMDiff Z.contMDiff) : Π b : M, TangentSpace I b) b)
        A x from rfl,
    tensor0S_curry_riemannSec_tensor0SCov_succ_eq (I := I) (M := M) g s Y
      (ContMDiffSection.mk (covApply (LeviCivita (I := I) g) (fun b => X b) (fun b => Z b))
        (covApply_contMDiff (cov := LeviCivita (I := I) g) X.contMDiff Z.contMDiff)) A hA x]
  rw [show riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => Y b) (fun b => Z b)
        (covApply (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
          (fun b => X b) A) x =
      riemannSec (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => Y b) (fun b => Z b)
        (covApply (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
          (fun b => X b) A) x from rfl]
  rw [tensor0S_curry_riemannSec_tensor0SCov_succ_eq (I := I) (M := M) g s Y Z
      (covApply (tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        (fun b => X b) A)
      (covApply_contMDiff (cov := tensor0SCovariantDerivative I M (s + 1) (LeviCivita (I := I) g))
        X.contMDiff hA) x,
    hcurry_covApply X]

  rfl

/-- **The differentiated leading-slot peel of the tensor curvature (the single inductive slot-algebra
coherence brick).** For smooth fields `X, Y, Z`, a smooth `(0, s + 1)`-tensor section `A`, a leading
slot vector `u₀ : T_x M` and a residual tuple `u' : Fin s → T_x M`, the differentiated
`(0, s + 1)`-tensor curvature evaluated on the cons-tuple peels its leading argument: it equals the
differentiated `(0, s)`-tensor curvature of the leading-slot paired section (the contraction of `A`
against a smooth extension of `u₀` in the leading argument), read on `u'`, minus the value of `A` with
the *differentiated* base-tangent curvature `nablaBaseSlotCurv g X Y Z x u₀ = (∇_X R^{TM})(Y, Z) u₀`
inserted into the leading slot:

```
toModel(nablaTensor0SCurv g (s + 1) X Y Z A x)(Fin.cons u₀ u')
  = toModel(nablaTensor0SCurv g s X Y Z (b ↦ A b ⌟ ext u₀ b) x)(u')
    − toModel(A x)(Fin.cons (nablaBaseSlotCurv g X Y Z x u₀) u').
```

**Why this is TRUE.** This is the covariant derivative (along the derivative direction `X`) of the
*undifferentiated* leading-slot peel `riemannSec_tensor0SCov_succ_consEval`, taken term by term through
the curried first-order product rule `tensor0SCovariantDerivative_succ_consEval_peel`
(`TensorMetricCompatible`). Differentiating the undifferentiated peel — whose proof is the generic
Hom-bundle curvature–Leibniz rule `riemannSec_homBundleGen_apply_eq` transported through the fibrewise
currying `tensor0S_curry` — once more in the `X` direction produces, in addition to the rank-`s`
differentiated curvature of the paired section and the leading-slot *differentiated* base curvature,
the same four mixed `(∇A)(∇ext)` cross terms that already cancel between the two derivative orderings
`∇_X ∇_Y` and `∇_X ∇_Z` together with the bracket term in the undifferentiated identity. The Leibniz
`∇_X A`-correction of `nablaTensor0SCurv` is precisely what absorbs the derivative of the leading-slot
contraction `A ⌟ ext u₀` against the leading-slot peel, so the residual base term is the
*extension-independent* differentiated curvature `nablaBaseSlotCurv g X Y Z x u₀` (the symmetric,
torsion-free correction `∇_X(ext u₀)` cancels exactly as in the undifferentiated peel's
`baseSlotCurv`). It is the differentiated analogue of the single inductive ingredient
`riemannSec_tensor0SCov_succ_consEval` of the undifferentiated slot-wise curvature formula.

**Litmus.** At `s = 0` the residual tuple is empty and the paired-section term is the differentiated
*scalar* curvature `nablaTensor0SCurv g 0 …`, which vanishes (`nablaTensor0SCurv_zero_eq_zero`); the
identity reduces to the single-slot peel `toModel(nablaTensor0SCurv g 1 X Y Z A x)(![u₀]) =
−toModel(A x)(![nablaBaseSlotCurv g X Y Z x u₀])`, the `s = 1` collapse to the tangent-level
differentiated curvature (`nablaCurvSec_eq_nablaRiemannSec`).

**Non-vacuity.** The peel is *not* trivially satisfied by the zero family: its leading-slot residue
`nablaBaseSlotCurv g X Y Z x u₀` is the genuine differentiated tangent curvature `nablaCurvSec`, which
is nonzero on a non-flat manifold with a non-parallel curvature (the second Bianchi identity
`second_bianchi_levi_civita` shows its cyclic sum vanishes but the individual term does not), so the
right-hand side genuinely depends on the curvature derivative — replacing `nablaBaseSlotCurv` by `0`
breaks the identity precisely when `∇R ≠ 0`. -/
theorem nablaTensor0SCurv_succ_consEval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace (s + 1) I b) (hA : TensorSmooth (I := I) (s + 1) A)
    (x : M) (u₀ : TangentSpace I x) (u' : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (nablaTensor0SCurv (I := I) g (s + 1) X Y Z A x) (Fin.cons u₀ u') =
      Tensor0SSpace.toModel
          (nablaTensor0SCurv (I := I) g s X Y Z
            (fun b => curriedSection I M A b
              (smoothExtensionTangent (I := I) x u₀ b)) x) u' -
        Tensor0SSpace.toModel (A x)
          (Fin.cons (nablaBaseSlotCurv (I := I) g X Y Z x u₀) u') := by
  classical
  set Y₀ : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ContMDiffSection.mk (smoothExtensionTangent (I := I) x u₀)
      (smoothExtensionTangent_contMDiff (I := I) x u₀) with hY₀_def
  have hY₀x : (Y₀ : Π b : M, TangentSpace I b) x = u₀ := smoothExtensionTangent_eq (I := I) x u₀
  set Acurry : Cₛ^∞⟮I; E →L[ℝ] Tensor0SModel s ℝ E,
      (fun x : M => TangentSpace I x →L[ℝ] Tensor0SSpace s I x)⟯ :=
    ContMDiffSection.mk (curriedSection I M A)
      ((contMDiff_curriedSection_iff_section I M A).mp hA) with hAcurry_def

  rw [← TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := nablaTensor0SCurv (I := I) g (s + 1) X Y Z A x) (v0 := u₀) (vs := u')]

  rw [tensor0S_curry_nablaTensor0SCurv_succ_eq (I := I) g s X Y Z A hA x]

  rw [show nablaRiemannSec (LeviCivita (I := I) g) (homGenS (I := I) (M := M) g s)
        (fun b => X b) (fun b => Y b) (fun b => Z b) (curriedSection I M A) x =
      nablaRiemannSec (LeviCivita (I := I) g)
          (HomConnectionGen.homBundleCovariantDerivativeGen I M E
            (TangentSpace I : M → Type _) (Tensor0SModel s ℝ E)
            (fun x : M => Tensor0SSpace s I x)
            (LeviCivita (I := I) g)
            (tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)))
          (fun b => X b) (fun b => Y b) (fun b => Z b) (fun b => Acurry b) x from rfl]
  conv_lhs => rw [show (u₀ : TangentSpace I x) = (Y₀ : Π b : M, TangentSpace I b) x from hY₀x.symm]
  rw [nablaRiemannSec_homBundleGen_apply_eq (I := I) (M := M)
    (E_U := E) (U := (TangentSpace I : M → Type _)) (F := Tensor0SModel s ℝ E)
    (V := (fun x : M => Tensor0SSpace s I x))
    (cov_U := LeviCivita (I := I) g)
    (cov_V := tensor0SCovariantDerivative I M s (LeviCivita (I := I) g))
    (covT := LeviCivita (I := I) g) X Y Z Acurry Y₀ x]

  rw [Tensor0SBundle.Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]

  rw [show (Acurry : Π b : M, TangentSpace I b →L[ℝ] Tensor0SSpace s I b) x =
      curriedSection I M A x from rfl, curriedSection_apply,
    show (nablaRiemannSec (LeviCivita (I := I) g) (LeviCivita (I := I) g)
        (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => (Y₀ : Π b : M, TangentSpace I b) b) x) =
      nablaBaseSlotCurv (I := I) g X Y Z x u₀ from rfl,
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := A x) (v0 := nablaBaseSlotCurv (I := I) g X Y Z x u₀) (vs := u')]

  rfl

/-- **The differentiated slot-wise curvature transfer (tuple form).** For smooth tangent fields
`X, Y, Z`, a smooth `(0, t)`-tensor section `A`, a point `x`, and a tangent tuple
`u : Fin t → T_x M`, the differentiated Riemann curvature of the `(0, t)`-tensor connection acts as the
negated sum of the *differentiated* base-tangent curvature inserted into each argument slot:

```
toModel(nablaTensor0SCurv g t X Y Z A x)(u)
  = − ∑ₖ toModel(A x)(Function.update u k (nablaBaseSlotCurv g X Y Z x (u k))),
```

where `nablaBaseSlotCurv g X Y Z x u = (∇_X R^{TM})(Y, Z) u = nablaCurvSec (LeviCivita g) X Y Z (ext u) x`
is the tangent-level differentiated curvature acting on the `k`-th slot. This is the differentiated
analogue of the slot-wise curvature formula `riemannSec_tensor0SCov_apply_eval` (`TensorSlotwiseCurvature`):
where the undifferentiated tensor curvature `R^{(t)}(X, W)` acts slot-wise through the base-tangent
curvature `R^{TM}(X, W) = baseSlotCurv`, the differentiated tensor curvature `(∇_X R^{(t)})(Y, ·)` acts
slot-wise through the tangent-level differentiated curvature `nablaCurvSec`. It is proved by induction
on `t` using the differentiated leading-slot peel `nablaTensor0SCurv_succ_consEval` (inductive step)
over the differentiated scalar flatness `nablaTensor0SCurv_zero_eq_zero` (base case), mirroring the
undifferentiated induction verbatim. -/
theorem nablaTensor0SCurv_apply_eval
    (g : SmoothRiemannianMetric I M) (t : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∀ (A : Π b : M, Tensor0SSpace t I b), TensorSmooth (I := I) t A →
      ∀ (x : M) (u : Fin t → TangentSpace I x),
      Tensor0SSpace.toModel
          (nablaTensor0SCurv (I := I) g t X Y Z A x) u =
        - ∑ k : Fin t,
            Tensor0SSpace.toModel (A x)
              (Function.update u k (nablaBaseSlotCurv (I := I) g X Y Z x (u k))) := by
  induction t with
  | zero =>
      intro A hA x u
      rw [nablaTensor0SCurv_zero_eq_zero (I := I) g X Y Z A hA x]
      simp
  | succ s ih =>
      intro A hA x u
      classical
      have hpaired_smooth : TensorSmooth (I := I) s
          (fun b => curriedSection I M A b (smoothExtensionTangent (I := I) x (u 0) b)) :=
        ContMDiff.clm_bundle_apply (b := id)
          ((contMDiff_curriedSection_iff_section I M A).mp hA)
          (smoothExtensionTangent_contMDiff (I := I) x (u 0))
      rw [show u = Fin.cons (u 0) (Fin.tail u) from (Fin.cons_self_tail u).symm,
        nablaTensor0SCurv_succ_consEval (I := I) g s X Y Z A hA x (u 0) (Fin.tail u)]
      have hih := ih (fun b => curriedSection I M A b (smoothExtensionTangent (I := I) x (u 0) b))
        hpaired_smooth x (Fin.tail u)
      rw [hih]
      have hpx : ∀ v : Fin s → TangentSpace I x,
          Tensor0SSpace.toModel
              (curriedSection I M A x (smoothExtensionTangent (I := I) x (u 0) x)) v =
            Tensor0SSpace.toModel (A x) (Fin.cons (u 0) v) := by
        intro v
        rw [curriedSection_apply, smoothExtensionTangent_eq (I := I) x (u 0),
          TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
            (T := A x) (v0 := u 0) (vs := v)]
      rw [Finset.sum_congr rfl (fun k _ => by
        rw [hpx (Function.update (Fin.tail u) k (nablaBaseSlotCurv (I := I) g X Y Z x (Fin.tail u k)))])]
      have hcons_lead :
          Fin.cons (nablaBaseSlotCurv (I := I) g X Y Z x (u 0)) (Fin.tail u) =
            Function.update u 0 (nablaBaseSlotCurv (I := I) g X Y Z x (u 0)) := by
        rw [← Fin.update_cons_zero (x := u 0) (p := Fin.tail u)
          (z := nablaBaseSlotCurv (I := I) g X Y Z x (u 0)), Fin.cons_self_tail]
      have hcons_succ : ∀ (k : Fin s),
          Fin.cons (u 0) (Function.update (Fin.tail u) k
              (nablaBaseSlotCurv (I := I) g X Y Z x (Fin.tail u k))) =
            Function.update u k.succ (nablaBaseSlotCurv (I := I) g X Y Z x (u k.succ)) := by
        intro k
        have htk : Fin.tail u k = u k.succ := rfl
        rw [htk, Fin.cons_update (x := u 0) (p := Fin.tail u) (i := k)
          (y := nablaBaseSlotCurv (I := I) g X Y Z x (u k.succ)), Fin.cons_self_tail]
      rw [Finset.sum_congr rfl (fun k _ => by rw [hcons_succ k]), hcons_lead]
      rw [show (- ∑ k : Fin s,
            Tensor0SSpace.toModel (A x)
              (Function.update u k.succ (nablaBaseSlotCurv (I := I) g X Y Z x (u k.succ)))) -
          Tensor0SSpace.toModel (A x)
            (Function.update u 0 (nablaBaseSlotCurv (I := I) g X Y Z x (u 0))) =
          - (Tensor0SSpace.toModel (A x)
              (Function.update u 0 (nablaBaseSlotCurv (I := I) g X Y Z x (u 0))) +
              ∑ k : Fin s,
                Tensor0SSpace.toModel (A x)
                  (Function.update u k.succ (nablaBaseSlotCurv (I := I) g X Y Z x (u k.succ)))) from by
        ring]
      rw [Fin.cons_self_tail]
      congr 1
      rw [Fin.sum_univ_succ
        (f := fun k : Fin (s + 1) =>
          Tensor0SSpace.toModel (A x)
            (Function.update u k (nablaBaseSlotCurv (I := I) g X Y Z x (u k))))]

/-- **The `(0, s)`-tensor restatement of the differentiated slot-wise transfer (base-slot sum form).**
For smooth tangent fields `X, Y, Z`, a smooth `(0, s)`-tensor section `A`, a point `x`, and a covariant
tuple `u : Fin s → T_x M`, the differentiated Riemann curvature of the `(0, s)`-tensor connection acts
as the negated *differentiated* base-tangent slot sum across the covariant slots:

```
toModel(nablaTensor0SCurv g s X Y Z A x)(u)
  = − ∑ₖ toModel(A x)(Function.update u k (nablaBaseSlotCurv g X Y Z x (u k))).
```

This is the differentiated analogue of `riemannSec_tensorCov_baseSlot_eval`
(`TensorWeitzenbockIdentity`), packaged at the level the moving-frame remainder bracket-sum consumes;
it is `nablaTensor0SCurv_apply_eval` read directly on the tuple. -/
theorem nablaTensorCov_baseSlot_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A)
    (x : M) (u : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (nablaTensor0SCurv (I := I) g s X Y Z A x) u =
      - ∑ k : Fin s,
          Tensor0SSpace.toModel (A x)
            (Function.update u k (nablaBaseSlotCurv (I := I) g X Y Z x (u k))) :=
  nablaTensor0SCurv_apply_eval (I := I) g s X Y Z A hA x u

/-- **The differentiated base-slot curvature is the tangent-level `nablaCurvSec`, raw-field form.**
For smooth raw tangent fields `X, Y, Z` (packaged as smooth sections) and a fixed slot vector `u`, the
differentiated base-slot curvature `nablaBaseSlotCurv` equals the tangent-level differentiated Riemann
curvature `nablaCurvSec (LeviCivita g) X Y Z (ext u) x` (`SecondBianchi`) — by definition. This is the
bridge identifying the slot quantity of the differentiated tensor transfer with the differentiated
tangent curvature consumed by the contracted-Bianchi frame folds. -/
lemma nablaBaseSlotCurv_eq_nablaCurvSec
    (g : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g X Y Z x u =
      nablaCurvSec (LeviCivita (I := I) g) (fun b => X b) (fun b => Y b) (fun b => Z b)
        (fun b => smoothExtensionTangent (I := I) x u b) x := rfl

/-- **The inner cyclic differentiated base-tangent curvature vanishes (the tangent second Bianchi on a
slot vector).** For smooth tangent fields `X, Y, Z` and a fixed slot vector `u`, the cyclic sum of the
differentiated base-tangent curvature `nablaBaseSlotCurv g · · · x u = (∇_· R^{TM})(·, ·) u` over the
three antisymmetric-slot/derivative arrangements vanishes:
$$
  (\nabla_X R)(Y, Z) u + (\nabla_Y R)(Z, X) u + (\nabla_Z R)(X, Y) u = 0 .
$$
This is the second (differential) Bianchi identity `second_bianchi_levi_civita_metric` (`SecondBianchi`)
read on the smooth extension `ext u = smoothExtensionTangent x u` of the slot vector, through the
definitional identification `nablaBaseSlotCurv g X Y Z x u = nablaCurvSec (LeviCivita g) X Y Z (ext u) x`
(`nablaBaseSlotCurv_eq_nablaCurvSec`). It is the per-slot tangent-curvature ingredient that, summed
across the tensor slots, yields the tensor-level second Bianchi. -/
private lemma nablaBaseSlotCurv_cyclic_eq_zero
    (g : SmoothRiemannianMetric I M)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (u : TangentSpace I x) :
    nablaBaseSlotCurv (I := I) g X Y Z x u
      + nablaBaseSlotCurv (I := I) g Y Z X x u
      + nablaBaseSlotCurv (I := I) g Z X Y x u = 0 := by
  rw [nablaBaseSlotCurv_eq_nablaCurvSec, nablaBaseSlotCurv_eq_nablaCurvSec,
      nablaBaseSlotCurv_eq_nablaCurvSec]
  exact second_bianchi_levi_civita_metric (I := I) g X.contMDiff Y.contMDiff Z.contMDiff
    (smoothExtensionTangent_contMDiff (I := I) x u)

/-- **The second (differential) Bianchi identity for the `(0, s)`-tensor connection.** For the induced
`(0, s)`-tensor covariant derivative `tensor0SCovariantDerivative s (LeviCivita g)` of a smooth
Riemannian metric `g` on a closed manifold, smooth tangent fields `X, Y, Z`, and a smooth `(0, s)`-tensor
section `A`, the cyclic sum of the differentiated tensor Riemann curvature `nablaTensor0SCurv g s` in its
derivative slot and its two antisymmetric vector-field slots vanishes:
$$
  (\nabla_X R^{(s)})(Y, Z) A + (\nabla_Y R^{(s)})(Z, X) A + (\nabla_Z R^{(s)})(X, Y) A = 0 .
$$

This is the tensor-bundle lift of the tangent-bundle second Bianchi `second_bianchi_levi_civita`
(`SecondBianchi`), the genuine bedrock of the rank-`0` Bochner curvature line. Through the definitional
identification `nablaTensor0SCurv g s X Y Z A x = nablaTensorCurvSec g (tensor0SCovariantDerivative s
(LeviCivita g)) X Y Z A x` (both unfold to the same four Leibniz terms, the vector-field slots
differentiated by the tangent Levi-Civita connection and the section slot by the tensor connection), it
also gives the cyclic Bianchi for the abstract differentiated curvature `nablaTensorCurvSec` of the
`(0, s)`-tensor connection that the moving-frame curvature-class pairing consumes.

**Proof (the slot-wise peel).** The `(0, s)`-tensor curvature acts *slot-wise* through the base-tangent
curvature: by the differentiated slot-wise transfer `nablaTensorCov_baseSlot_eval`,
`toModel(nablaTensor0SCurv g s X Y Z A x)(u) = − ∑ₖ toModel(A x)(update u k (nablaBaseSlotCurv g X Y Z x
(u k)))`. Reading the cyclic sum on any tuple `u` (through the injective `Tensor0SSpace.toModel`,
`ContinuousMultilinearMap.ext`), the three terms share the same negated slot sum; collecting them slot by
slot (the multilinearity of `toModel(A x)` in each argument, `ContinuousMultilinearMap.map_update_add`)
replaces the `k`-th slot vector by the inner cyclic differentiated tangent curvature
`nablaBaseSlotCurv g X Y Z x (u k) + nablaBaseSlotCurv g Y Z X x (u k) + nablaBaseSlotCurv g Z X Y x
(u k)`, which is `0` by the tangent second Bianchi `nablaBaseSlotCurv_cyclic_eq_zero`. A multilinear map
with a zero argument vanishes (`ContinuousMultilinearMap.map_coord_zero`), so every slot summand is `0`
and the whole cyclic sum is the zero `(0, s)`-tensor.

**s = 0 litmus.** At rank `0` the section slot is a scalar with flat connection, so `nablaTensor0SCurv g
0 = 0` (`nablaTensor0SCurv_zero_eq_zero`); the cyclic sum is `0 + 0 + 0 = 0`, the scalar third-order
Bianchi that holds vacuously because the scalar bundle carries no Riemann curvature. -/
theorem nablaTensor0SCurv_cyclic_eq_zero
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A) (x : M) :
    nablaTensor0SCurv (I := I) g s X Y Z A x
      + nablaTensor0SCurv (I := I) g s Y Z X A x
      + nablaTensor0SCurv (I := I) g s Z X Y A x = 0 := by
  classical
  apply Tensor0SSpace.toModel_injective
  simp only [Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_zero]
  apply ContinuousMultilinearMap.ext
  intro u
  rw [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.add_apply,
      ContinuousMultilinearMap.zero_apply]
  rw [nablaTensorCov_baseSlot_eval (I := I) g s X Y Z A hA x u,
      nablaTensorCov_baseSlot_eval (I := I) g s Y Z X A hA x u,
      nablaTensorCov_baseSlot_eval (I := I) g s Z X Y A hA x u]
  have hkey : ∀ k : Fin s,
      Tensor0SSpace.toModel (A x)
          (Function.update u k (nablaBaseSlotCurv (I := I) g X Y Z x (u k)))
        + Tensor0SSpace.toModel (A x)
          (Function.update u k (nablaBaseSlotCurv (I := I) g Y Z X x (u k)))
        + Tensor0SSpace.toModel (A x)
          (Function.update u k (nablaBaseSlotCurv (I := I) g Z X Y x (u k))) = 0 := by
    intro k
    rw [← (Tensor0SSpace.toModel (A x)).map_update_add u k
          (nablaBaseSlotCurv (I := I) g X Y Z x (u k))
          (nablaBaseSlotCurv (I := I) g Y Z X x (u k))]
    rw [← (Tensor0SSpace.toModel (A x)).map_update_add u k
          (nablaBaseSlotCurv (I := I) g X Y Z x (u k)
            + nablaBaseSlotCurv (I := I) g Y Z X x (u k))
          (nablaBaseSlotCurv (I := I) g Z X Y x (u k))]
    rw [nablaBaseSlotCurv_cyclic_eq_zero (I := I) g X Y Z x (u k)]
    exact (Tensor0SSpace.toModel (A x)).map_coord_zero k (by rw [Function.update_self])
  rw [← neg_add, ← neg_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_eq_zero (fun k _ => hkey k), neg_zero]

/-- **The frame-traced corollary — the Ricci fold at the tensor level.** The orthonormal-frame trace of
the differentiated base-slot curvature in its first antisymmetric slot, metric-paired against the same
frame, folds into the covariant derivative of the Ricci tensor: for smooth tangent fields `X, V`, the
orthonormal frame `Bᵢ := smoothOrthoFrame g x i`, and a fixed slot vector `w`,
$$
  \sum_i g_x\bigl((\nabla_X R)(B_i, V)\,w,\; B_i\bigr)
    = (\nabla_X \mathrm{Ric})(V, \tilde w),
$$
with `(∇_X R)(B_i, V) w = nablaCurvSec (LeviCivita g) X Bᵢ V (ext w) x` the differentiated tangent
curvature on the slot vector `w`, and `ž = ext w = smoothExtensionTangent x w` a smooth extension of
`w`. This is the trace bridge `nablaRicci_eq_frame_trace_nablaCurvSec` read on the slot vector through a
smooth extension: it is the slot-wise Ricci contraction of the differentiated tensor curvature, the
per-slot fold the curvature-line assembly composes with the contracted second Bianchi identity
`contracted_second_bianchi` (`div Ric = ½ d scal`) to collapse the divergence of the differentiated
tensor curvature. -/
theorem nablaTensorCurv_frame_trace_eq_nablaRicci
    (g : SmoothRiemannianMetric I M)
    {X V : Π b : M, TangentSpace I b} {x : M}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X))
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V)) (w : TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
        g.inner x (nablaCurvSec (LeviCivita (I := I) g) X
          (smoothOrthoFrame (I := I) g x i) V
          (fun b => smoothExtensionTangent (I := I) x w b) x)
          (smoothOrthoFrame (I := I) g x i x) =
      nablaRicci (I := I) g X V (fun b => smoothExtensionTangent (I := I) x w b) x := by
  have hext : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b => smoothExtensionTangent (I := I) x w b)) :=
    smoothExtensionTangent_contMDiff (I := I) x w
  exact (nablaRicci_eq_frame_trace_nablaCurvSec (I := I) g hX hV hext).symm

/-- **The frame-summed differentiated tensor curvature, slot-wise (the divergence-of-curvature tensor
transfer).** For a fixed derivative direction `X`, a smooth `(0, s)`-tensor section `A`, a covariant
tuple `u`, the orthonormal-frame sum (over the *first antisymmetric* curvature slot `Bᵢ :=
smoothOrthoFrame g x i`) of the differentiated `(0, s)`-tensor curvature acts as the negated slot sum of
the frame-summed differentiated base-tangent curvature:

```
∑ᵢ toModel(nablaTensor0SCurv g s X Bᵢ Z A x)(u)
  = − ∑ₖ ∑ᵢ toModel(A x)(Function.update u k (nablaBaseSlotCurv g X Bᵢ Z x (u k))).
```

This is `nablaTensorCov_baseSlot_eval` (the per-frame transfer) summed over the frame and the finite
slot/frame sums interchanged. It is the divergence-of-curvature shape: tracing the leading antisymmetric
curvature slot against the frame puts each slot of the differentiated tensor curvature into the
frame-summed differentiated tangent curvature `∑ᵢ (∇_X R)(Bᵢ, Z)(·)`, which folds — through the trace
bridge `nablaTensorCurv_frame_trace_eq_nablaRicci` (metric-paired against the frame, per slot) and the
contracted second Bianchi identity `contracted_second_bianchi` (`div Ric = ½ d scal`) — into the
covariant derivative of the Ricci tensor. It is the tensor-level Ricci/Bianchi fold the curvature-line
assembly consumes. -/
theorem frame_sum_nablaTensor0SCurv_baseSlot_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (X Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A)
    (x : M) (u : Fin s → TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (nablaTensor0SCurv (I := I) g s X
            (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
              (smoothOrthoFrame_smooth (I := I) g x i)) Z A x) u =
      - ∑ k : Fin s, ∑ i : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel (A x)
            (Function.update u k
              (nablaBaseSlotCurv (I := I) g X
                (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                  (smoothOrthoFrame_smooth (I := I) g x i)) Z x (u k))) := by
  classical
  rw [Finset.sum_congr rfl (fun i _ => nablaTensorCov_baseSlot_eval (I := I) g s X
    (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame_smooth (I := I) g x i)) Z A hA x u)]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]

/-- **The once-contracted second Bianchi identity (the first-slot divergence of the Riemann tensor,
paired form).** For the smooth `g_x`-orthonormal frame `B_i := smoothOrthoFrame g x i` and smooth
tangent fields `Y, W, U`, the orthonormal-frame trace of the differentiated tangent curvature
`(∇_{B_i} R^{TM})(B_i, Y) W` over the **diagonal** derivative-and-first-antisymmetric-slot pair
`(B_i, B_i)`, metric-paired against `U`, equals the differentiated-Ricci difference
$$
  \sum_i g_x\bigl((\nabla_{B_i} R)(B_i, Y) W,\, U\bigr)
    = (\nabla_U \mathrm{Ric})(Y, W) - (\nabla_W \mathrm{Ric})(U, Y) .
$$

This is the divergence-form contraction `div R = δ R` of the second Bianchi identity, one contraction
shallower than `contracted_second_bianchi` (`div Ric = ½ d scal`): tracing the second Bianchi identity
over the derivation index against the first antisymmetric slot collapses the differentiated full Riemann
curvature onto the differentiated Ricci tensor.

**Proof (the single contraction of the paired second Bianchi).** The diagonal trace `Φ(Y, W, U) :=
∑_i g_x((∇_{B_i} R)(B_i, Y) W, U)` is first re-expressed, by the value-level differentiated-curvature
symmetries (`nablaCurvSec_metric_skew45`, `nablaCurvSec_inner_pair_symm` — no derivative is taken), as
the conjugate trace `S(U, W, Y) := ∑_i g_x((∇_{B_i} R)(U, W) Y, B_i)` with the frame in the derivation
and pairing slots. For that trace the paired second Bianchi `nablaCurvSec_bianchi_paired` (cyclic in the
derivation and two antisymmetric slots) applied to `(B_i, U, W)` acting on `Y`, paired against `B_i`,
summed over `i`, has its three cyclic terms collapse through the metric antisymmetry
(`nablaCurvSec_metric_skew45`), the pair symmetry (`nablaCurvSec_inner_pair_symm`), and the frame-trace
Ricci bridge `nablaRicci_eq_frame_trace_nablaCurvSec` (`∑_i g_x((∇_X R)(B_i, V) Z, B_i) = ∇_X Ric(V, Z)`)
into the two differentiated-Ricci traces, giving `S(U, W, Y) = ∇_U Ric(Y, W) − ∇_W Ric(U, Y)`. -/
theorem nablaCurvSec_diag_frame_trace_eq_nablaRicci_sub
    (g : SmoothRiemannianMetric I M)
    {Y W U : Π b : M, TangentSpace I b} {x : M}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% U)) :
    ∑ i : Fin (Module.finrank ℝ E),
        g.inner x (nablaCurvSec (LeviCivita (I := I) g)
          (smoothOrthoFrame (I := I) g x i) (smoothOrthoFrame (I := I) g x i) Y W x) (U x) =
      nablaRicci (I := I) g U Y W x - nablaRicci (I := I) g W U Y x := by
  classical
  set cov := LeviCivita (I := I) g with hcov_def
  set B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b :=
    fun i => smoothOrthoFrame (I := I) g x i with hB_def
  have hBsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)) :=
    fun i => smoothOrthoFrame_smooth (I := I) g x i

  have hconj : ∀ i,
      g.inner x (nablaCurvSec cov (B i) (B i) Y W x) (U x) =
        g.inner x (nablaCurvSec cov (B i) U W Y x) (B i x) := by
    intro i

    have hsk1 : g.inner x (nablaCurvSec cov (B i) (B i) Y W x) (U x) =
        - g.inner x (nablaCurvSec cov (B i) (B i) Y U x) (W x) := by
      have h := nablaCurvSec_metric_skew45 (I := I) g (X := B i) (Y := B i) (Z := Y) (W := W)
        (U := U) (x := x) (hBsm i) (hBsm i) hY hW hU
      linarith [h]

    have hps : g.inner x (nablaCurvSec cov (B i) (B i) Y U x) (W x) =
        g.inner x (nablaCurvSec cov (B i) U W (B i) x) (Y x) := by
      exact nablaCurvSec_inner_pair_symm (I := I) g (X := B i) (Y := B i) (Z := Y) (W := U)
        (U := W) (hBsm i) (hBsm i) hY hU hW

    have hsk2 : g.inner x (nablaCurvSec cov (B i) U W (B i) x) (Y x) =
        - g.inner x (nablaCurvSec cov (B i) U W Y x) (B i x) := by
      have h := nablaCurvSec_metric_skew45 (I := I) g (X := B i) (Y := U) (Z := W) (W := B i)
        (U := Y) (x := x) (hBsm i) hU hW (hBsm i) hY
      linarith [h]
    rw [hsk1, hps, hsk2]; ring
  rw [Finset.sum_congr rfl (fun i _ => hconj i)]

  have hbi : ∀ i,
      g.inner x (nablaCurvSec cov (B i) U W Y x) (B i x)
        + g.inner x (nablaCurvSec cov U W (B i) Y x) (B i x)
        + g.inner x (nablaCurvSec cov W (B i) U Y x) (B i x) = 0 := by
    intro i
    exact nablaCurvSec_bianchi_paired (I := I) g (X := B i) (Y := U) (Z := W) (W := Y)
      (U := B i) (x := x) (hBsm i) hU hW hY

  have hrew : ∀ i,
      g.inner x (nablaCurvSec cov (B i) U W Y x) (B i x) =
        - g.inner x (nablaCurvSec cov U W (B i) Y x) (B i x)
        - g.inner x (nablaCurvSec cov W (B i) U Y x) (B i x) := by
    intro i; linarith [hbi i]
  rw [Finset.sum_congr rfl (fun i _ => hrew i)]
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]

  have hterm3 : ∑ i : Fin (Module.finrank ℝ E),
      g.inner x (nablaCurvSec cov W (B i) U Y x) (B i x) =
      nablaRicci (I := I) g W U Y x := by
    rw [nablaRicci_eq_frame_trace_nablaCurvSec (I := I) g hW hU hY]

  have hterm2 : ∑ i : Fin (Module.finrank ℝ E),
      g.inner x (nablaCurvSec cov U W (B i) Y x) (B i x) =
      - nablaRicci (I := I) g U Y W x := by
    have hconv : ∀ i,
        g.inner x (nablaCurvSec cov U W (B i) Y x) (B i x) =
          - g.inner x (nablaCurvSec cov U (B i) Y W x) (B i x) := by
      intro i

      have hps : g.inner x (nablaCurvSec cov U W (B i) Y x) (B i x) =
          g.inner x (nablaCurvSec cov U Y (B i) W x) (B i x) :=
        nablaCurvSec_inner_pair_symm (I := I) g (X := U) (Y := W) (Z := B i) (W := Y)
          (U := B i) hU hW (hBsm i) hY (hBsm i)

      rw [hps, nablaCurvSec_swap23 (I := I) g (X := U) (Y := Y) (Z := B i) (W := W) (x := x)
        hY (hBsm i) hW, map_neg, ContinuousLinearMap.neg_apply]
    rw [Finset.sum_congr rfl (fun i _ => hconv i), Finset.sum_neg_distrib,
      nablaRicci_eq_frame_trace_nablaCurvSec (I := I) g hU hY hW]
  rw [hterm2, hterm3]
  ring

/-- **The diagonal divergence of the `(0, s)`-tensor Riemann curvature, slot-wise (the divergence of
curvature `div R^{(s)}`).** Tracing the differentiated `(0, s)`-tensor curvature `nablaTensor0SCurv g s`
over the orthonormal frame `B_i := smoothOrthoFrame g x i` placed simultaneously in the **derivation**
direction and the **first antisymmetric** curvature slot — the genuine *diagonal* trace, in contrast to
the fixed-derivation-direction trace `frame_sum_nablaTensor0SCurv_baseSlot_eval` — acts slot-wise as the
negated slot sum of the *frame-summed differentiated base-tangent curvature* `∑_i (∇_{B_i} R)(B_i, Y)(·)`,
the first-slot divergence of the tangent Riemann curvature:
```
∑_i toModel(nablaTensor0SCurv g s B_i B_i Y A x)(u)
  = − ∑_k toModel(A_x)(Function.update u k (∑_i nablaBaseSlotCurv g B_i B_i Y x (u k))).
```

This is the tensor-level lift of the divergence-of-curvature identity: each covariant slot of the diagonal
divergence is contracted into the frame-summed differentiated tangent curvature `∑_i (∇_{B_i} R)(B_i, Y) v`,
whose metric pairing collapses, through the once-contracted second Bianchi identity
`nablaCurvSec_diag_frame_trace_eq_nablaRicci_sub` (`∑_i g((∇_{B_i} R)(B_i, Y) v, U) = ∇_U Ric(Y, v) −
∇_v Ric(U, Y)`), onto the differentiated Ricci content. It is `nablaTensorCov_baseSlot_eval` (the per-frame
transfer) summed over the diagonal frame, with the finite slot/frame sums interchanged
(`Finset.sum_comm`) and the inner frame sum pulled through the multilinear update slot
(`MultilinearMap.map_update_sum`). It is the diagonal companion to
`frame_sum_nablaTensor0SCurv_baseSlot_eval`, the shape the rank-`0` Bochner tension-field
covariant-divergence nullity consumes. -/
theorem frame_sum_nablaTensor0SCurv_diag_baseSlot_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (A : Π b : M, Tensor0SSpace s I b) (hA : TensorSmooth (I := I) s A)
    (x : M) (u : Fin s → TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (nablaTensor0SCurv (I := I) g s
            (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
              (smoothOrthoFrame_smooth (I := I) g x i))
            (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
              (smoothOrthoFrame_smooth (I := I) g x i)) Y A x) u =
      - ∑ k : Fin s,
          Tensor0SSpace.toModel (A x)
            (Function.update u k
              (∑ i : Fin (Module.finrank ℝ E),
                nablaBaseSlotCurv (I := I) g
                  (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                    (smoothOrthoFrame_smooth (I := I) g x i))
                  (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
                    (smoothOrthoFrame_smooth (I := I) g x i)) Y x (u k))) := by
  classical
  rw [Finset.sum_congr rfl (fun i _ => nablaTensorCov_baseSlot_eval (I := I) g s
    (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame_smooth (I := I) g x i))
    (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
      (smoothOrthoFrame_smooth (I := I) g x i)) Y A hA x u)]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact ((Tensor0SSpace.toModel (A x)).toMultilinearMap.map_update_sum Finset.univ k
    (fun i => nablaBaseSlotCurv (I := I) g
      (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i))
      (ContMDiffSection.mk (smoothOrthoFrame (I := I) g x i)
        (smoothOrthoFrame_smooth (I := I) g x i)) Y x (u k)) u).symm

end TensorTransfer

end Connection
end Integral
end DifferentialGeometry

end
