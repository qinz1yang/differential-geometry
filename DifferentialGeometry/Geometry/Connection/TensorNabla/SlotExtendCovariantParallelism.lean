import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldCovariantCalculus

/-! # Covariant parallelism of the leading-passenger-slot extension of an operator field

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)` modelled on a real
inner-product space `E`, the leading-passenger-slot extension `slotExtend g₀ r s Φ` of a smooth
`(r, s)`-operator field inserts an extra covariant passenger slot at the front, read identically on
source and target and parallel-transported trivially.  This file records the two generic
`∇₀`-compatibility facts of `slotExtend`, building blocks of any passenger-slot parallel recursion
(e.g. the cometric `g₀⁻¹` double-trace parallelism propagated through its gradient-shift recursion):

* `tensorCovDerivAt_slotExtend_eq` — the atomic **directional** commutation: the directional covariant
  derivative of `slotExtend g₀ r s Φ` is the `slotExtendFib` of the directional covariant derivative of
  `Φ` (the connection differentiates only the contraction coefficient, which `slotExtend` relabels
  without touching the passenger slot);
* `covGrad_slotExtend_eq_zero_of_covGrad_eq_zero` — the section-level consequence: the covariant
  gradient annihilates the slot-extension of a `∇₀`-parallel field (`covGrad Φ = 0 ⟹ covGrad (slotExtend
  Φ) = 0`).

These are generic operator-field covariant-calculus facts — no metric-trace, no cometric, no DeTurck
content — and are the slot-recursion engine on which a parallel passenger-passing contraction's
parallelism propagates (`Analysis/Spectral/Tensor/CovGrad/CometricDoubleTraceParallelContraction.lean`,
`Analysis/Spectral/Intrinsic/DeTurck/SegmentMetricCurvatureDifferenceCovJet.lean`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace DeTurck

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **Leading-passenger-slot reading of the directional covariant derivative of a slot-extension.**
Reading the leading covariant passenger slot (via `tensor0S_curry`) of the directional covariant
derivative of the slot-extended operator field `slotExtend g₀ r s Φ`, in direction `v0`, recovers the
directional covariant derivative `tensorCovDerivAt g₀ r s Φ x v` acting on the curried passenger
reading of the input:
```
tensor0S_curry s x ((∇_v (slotExtend Φ)) D) v0 = (∇_v Φ) (tensor0S_curry r x D v0).
```
Tested on a local smooth `(0, r + 1)`-section `w` (`w x = D`) and a local smooth vector field `Y`
(`Y x = v0`): the Hom-connection product rule `tensorRSCovariantDerivative_apply` expands both
`∇_v (slotExtend Φ)` (on `w`) and `∇_v Φ` (on the curried passenger section
`y ↦ tensor0S_curry r y (w y) (Y y)`); the curry-Leibniz
`tensor0SCovariantDerivative_curriedSection_hom_leibniz` (applied to the uncurried slot-extension
section `y ↦ (slotExtend Φ)(y)(w y)` and, separately, to `w`) passes the connection through the
leading-slot curry, and `slotExtendFib_apply` reads the slot-extended fibre operator as left-composition
by `Φ`; the shared `∇^{(0,s)}`-of-composition term cancels and the moving-passenger corrections match,
leaving the claimed identity. -/
private theorem core_curry_reading (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : Integral.L2.SmoothCcTensor g₀ r s) (x : M) (v : E)
    (D : Tensor0SBundle.Tensor0SSpace (r + 1) I x) (v0 : E) :
    (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SBundle.Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (s + 1) I x from
          Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ (r + 1) (s + 1)
            (Integral.Connection.slotExtend (I := I) (M := M) g₀ r s Φ) x v) D)) v0 =
      (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
        Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ r s Φ x v)
        ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) D v0) := by
  classical
  obtain ⟨w, hw⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel (r + 1) ℝ E) (V := fun y : M => Tensor0SSpace (r + 1) I y)
    (n := (⊤ : ℕ∞)) x D
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x v0
  have hwcurry_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) y
        ((Tensor0SNabla.curriedSection (I := I) (M := M) (fun z : M => w z) y) (Y y))) := by
    have hcurried : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] Tensor0SModel r ℝ E)) ∞
        (fun y : M => TotalSpace.mk' (E →L[ℝ] Tensor0SModel r ℝ E)
          (E := fun z : M => TangentSpace I z →L[ℝ] Tensor0SSpace r I z) y
          (Tensor0SNabla.curriedSection (I := I) (M := M) (fun z : M => w z) y)) :=
      fun y => TensorMultilinear.contMDiffAt_curriedSection_of_contMDiffAt_section (I := I) (M := M)
        (fun z : M => w z) y (w.contMDiff y)
    exact ContMDiff.clm_bundle_apply (b := id) hcurried Y.contMDiff
  let wcurry : Cₛ^∞⟮I; Tensor0SModel r ℝ E, (fun y : M => Tensor0SSpace r I y)⟯ :=
    ⟨fun y : M => (Tensor0SNabla.curriedSection (I := I) (M := M) (fun z : M => w z) y) (Y y), hwcurry_smooth⟩
  set SEΦ := Integral.Connection.slotExtend (I := I) (M := M) g₀ r s Φ with hSEΦ
  have hU_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel (s + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (s + 1) I z) y
        ((show Tensor0SSpace (r + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from SEΦ.toSection y) (w y))) :=
    ContMDiff.clm_bundle_apply (b := id) SEΦ.toSection.contMDiff w.contMDiff
  have hU_at : TensorSectionMDiffAt (I := I) (s + 1)
      (fun y : M => (show Tensor0SSpace (r + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from SEΦ.toSection y) (w y)) x :=
    (hU_smooth x).mdifferentiableAt (by norm_num)
  have hw_at : TensorSectionMDiffAt (I := I) (r + 1) (fun y : M => w y) x :=
    (w.contMDiff x).mdifferentiableAt (by norm_num)
  have hCL_U := Integral.Connection.tensor0SCovariantDerivative_curriedSection_hom_leibniz (I := I) (M := M) g₀ s
    (fun y : M => (show Tensor0SSpace (r + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from SEΦ.toSection y) (w y))
    (x := x) hU_at Y v
  have hCL_w := Integral.Connection.tensor0SCovariantDerivative_curriedSection_hom_leibniz (I := I) (M := M) g₀ r
    (fun y : M => w y) (x := x) hw_at Y v
  have hHL_Φ := TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) r s (LeviCivita (I := I) g₀)
    Φ.toSection wcurry x v
  have hHL_SE := TensorRSNabla.tensorRSCovariantDerivative_apply (I := I) (M := M) (r + 1) (s + 1) (LeviCivita (I := I) g₀)
    SEΦ.toSection w x v
  have hfun : (fun y : M =>
        (Tensor0SNabla.curriedSection I M
            (fun y : M => (show Tensor0SSpace (r + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from
              SEΦ.toSection y) (w y)) y) (Y y)) =
      (fun y : M => (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y) (wcurry y)) := by
    funext y
    change (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s y
        ((show Tensor0SSpace (r + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from SEΦ.toSection y) (w y))) (Y y) =
      (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace s I y from Φ.toSection y)
        ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r y (w y)) (Y y))
    rw [hSEΦ, Integral.Connection.slotExtend_toSection, Integral.Connection.slotExtendFib_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply]
  rw [← hw, ← hY,
    Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_def (I := I) (M := M) g₀ (r + 1) (s + 1) SEΦ x v,
    Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_def (I := I) (M := M) g₀ r s Φ x v]
  rw [show ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) (w x)) (Y x) = wcurry x from rfl]
  rw [hHL_Φ]
  rw [hHL_SE, map_sub, ContinuousLinearMap.sub_apply]
  rw [eq_sub_of_add_eq hCL_U.symm]
  rw [hfun]
  rw [hSEΦ, Integral.Connection.slotExtend_toSection, Integral.Connection.slotExtendFib_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply]
  have hcurU_op : (Tensor0SNabla.curriedSection I M
        (fun y : M => (show Tensor0SSpace (r + 1) I y →L[ℝ] Tensor0SSpace (s + 1) I y from
          SEΦ.toSection y) (w y)) x) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x).comp
        (Tensor0SNabla.curriedSection I M (fun y : M => w y) x) := by
    apply ContinuousLinearMap.ext
    intro t
    change (Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
        ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from SEΦ.toSection x) (w x))) t =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x)
        ((Tensor0SBundle.tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x (w x)) t)
    rw [hSEΦ, Integral.Connection.slotExtend_toSection, Integral.Connection.slotExtendFib_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply]
  rw [show (⇑wcurry) = (fun y : M => (Tensor0SNabla.curriedSection I M (fun z : M => w z) y) (Y y)) from rfl,
    hCL_w, map_add]
  rw [hcurU_op, ContinuousLinearMap.comp_apply]
  abel

set_option linter.unusedSectionVars false in
/-- **(POSIT — the directional covariant-derivative commutation with the leading-passenger-slot
extension.)**  The atomic commutation fact beneath the slot-extension parallelism step: the directional
covariant derivative of the passenger-slot-extended operator field `slotExtend g r s Φ` is the
slot-extension of the directional covariant derivative of `Φ`:
```
tensorCovDerivAt g (r + 1) (s + 1) (slotExtend g r s Φ) x v = slotExtendFib g r s x (tensorCovDerivAt g r s Φ x v).
```
The leading passenger covariant slot is read identically on source and target (`slotExtendFib_apply_eval`)
and is parallel-transported trivially, so differentiating the slot-extended operator commutes with the
slot insertion: the connection differentiates only the *contraction coefficient*, which `slotExtend`
relabels without touching the passenger slot.  This is the genuine deep covariant-derivative ×
slot-insertion commutation (the directional, hence permute-free, form on which the section-level
parallelism step is built).  It is **non-vacuous**: it is a genuine commutation, false for a connection
that does not parallel-transport the passenger slot.

**Proof.**  Both sides are `(r + 1, s + 1)`-tensors; test on a `(0, r + 1)`-tensor `D` and a tuple
`Fin.cons (m 0) (vecTail m)`.  The right side reads off the new passenger slot first
(`slotExtendFib_apply_eval`); reading the left side's leading slot through `tensor0S_curry`
(`tensor0S_curry_apply_eval`), the equality reduces to the leading-passenger-slot reading
`core_curry_reading` of the directional covariant derivative of the slot extension. -/
theorem tensorCovDerivAt_slotExtend_eq (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : Integral.L2.SmoothCcTensor g₀ r s) (x : M) (v : E) :
    Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ (r + 1) (s + 1)
        (Integral.Connection.slotExtend (I := I) (M := M) g₀ r s Φ) x v =
      (show Tensor0SBundle.Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (s + 1) I x from
        Integral.Connection.slotExtendFib (I := I) (M := M) g₀ r s x
          (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
            Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ r s Φ x v)) := by
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [show m = Fin.cons (m 0) (Matrix.vecTail m) from (Fin.cons_self_tail m).symm]
  rw [Integral.Connection.slotExtendFib_apply_eval (I := I) (M := M) g₀ r s x
    (show Tensor0SBundle.Tensor0SSpace r I x →L[ℝ] Tensor0SBundle.Tensor0SSpace s I x from
      Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ r s Φ x v)
    D (m 0) (Matrix.vecTail m)]
  rw [← TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    (T := (show Tensor0SBundle.Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SBundle.Tensor0SSpace (s + 1) I x from
      Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ (r + 1) (s + 1)
        (Integral.Connection.slotExtend (I := I) (M := M) g₀ r s Φ) x v) D) (v0 := m 0) (vs := Matrix.vecTail m)]
  congr 1
  exact core_curry_reading (I := I) (M := M) g₀ r s Φ x v D (m 0)

set_option linter.unusedSectionVars false in
/-- **The covariant gradient annihilates a leading-passenger-slot extension of a parallel field.**  The
covariant gradient commutes with the leading-passenger-slot extension `slotExtend`: if a smooth
`(r, s)`-operator field `Φ` is `∇₀`-parallel (`covGrad g r s Φ = 0`), then its leading-passenger-slot
extension `slotExtend g r s Φ` is also `∇₀`-parallel:
```
covGrad g r s Φ = 0  ⟹  covGrad g (r + 1) (s + 1) (slotExtend g r s Φ) = 0.
```

**Decomposition.**  `covGrad Φ = 0` forces the directional covariant derivative `tensorCovDerivAt g r s Φ
x v` to vanish at every base point and direction (`covGrad_toSection_apply_eval` reads the gradient slot
as the directional derivative).  By the directional commutation `tensorCovDerivAt_slotExtend_eq` the
directional derivative of `slotExtend Φ` is `slotExtendFib` of that vanishing directional derivative, and
`slotExtendFib` is `ℝ`-linear (it sends the zero fibre operator to the zero fibre operator,
`map_zero`), so the directional derivative of `slotExtend Φ` vanishes — hence so does its covariant
gradient.  It is **non-vacuous**: the structural step propagating the cometric parallelism through the
passenger-slot recursion (a nonzero `covGrad Φ` would have a nonzero extension). -/
theorem covGrad_slotExtend_eq_zero_of_covGrad_eq_zero (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : Integral.L2.SmoothCcTensor g₀ r s)
    (hΦ : Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ r s Φ = 0) :
    Analysis.Parabolic.TensorSpectral.covGrad (I := I) (M := M) g₀ (r + 1) (s + 1)
        (Integral.Connection.slotExtend (I := I) (M := M) g₀ r s Φ) = 0 := by
  classical

  have hslotZero : ∀ (y : M),
      Integral.Connection.slotExtendFib (I := I) (M := M) g₀ r s y
          (0 : Tensor0SBundle.Tensor0SSpace r I y →L[ℝ] Tensor0SBundle.Tensor0SSpace s I y) =
        (0 : Tensor0SBundle.Tensor0SSpace (r + 1) I y →L[ℝ] Tensor0SBundle.Tensor0SSpace (s + 1) I y) := by
    intro y
    apply ContinuousLinearMap.ext
    intro D
    rw [Integral.Connection.slotExtendFib_apply, ContinuousLinearMap.zero_comp, map_zero,
      ContinuousLinearMap.zero_apply]

  have hdir : ∀ (x : M) (v : E),
      Analysis.Parabolic.TensorSpectral.tensorCovDerivAt (I := I) (M := M) g₀ r s Φ x v = 0 := by
    intro x v
    apply ContinuousLinearMap.ext
    intro D
    apply Tensor0SBundle.Tensor0SSpace.toModel_injective
    refine ContinuousMultilinearMap.ext (fun m => ?_)

    have heval := Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval
      (I := I) (M := M) g₀ r s Φ x D (Fin.cons v m)
    rw [hΦ, Integral.L2.SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero, Pi.zero_apply,
      ContinuousLinearMap.zero_apply, Tensor0SBundle.Tensor0SSpace.toModel_zero,
      ContinuousMultilinearMap.zero_apply] at heval
    rw [Fin.cons_zero, show (Matrix.vecTail (Fin.cons v m)) = m from funext (fun j => by
      simp [Matrix.vecTail, Fin.cons_succ])] at heval
    beta_reduce
    rw [ContinuousLinearMap.zero_apply, Tensor0SBundle.Tensor0SSpace.toModel_zero,
      ContinuousMultilinearMap.zero_apply]
    exact heval.symm

  apply Integral.L2.SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SBundle.Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [Integral.L2.SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero, Pi.zero_apply,
    ContinuousLinearMap.zero_apply, Tensor0SBundle.Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply,
    Analysis.Parabolic.TensorSpectral.covGrad_toSection_apply_eval
    (I := I) (M := M) g₀ (r + 1) (s + 1) (Integral.Connection.slotExtend (I := I) (M := M) g₀ r s Φ)
    x D m, tensorCovDerivAt_slotExtend_eq (I := I) (M := M) g₀ r s Φ x (m 0), hdir x (m 0),
    hslotZero x, ContinuousLinearMap.zero_apply, Tensor0SBundle.Tensor0SSpace.toModel_zero,
    ContinuousMultilinearMap.zero_apply]

end DeTurck
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
