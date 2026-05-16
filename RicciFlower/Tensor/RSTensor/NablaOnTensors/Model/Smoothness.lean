import RicciFlower.Tensor.RSTensor.NablaOnTensors.Model.TensorRS

/-!
# Smoothness of model-space tensor covariant derivative formulas
-/
namespace TensorLieDeriv

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Bundle Set IsManifold ContinuousLinearMap VectorField Filter Tensor0SBundle Function
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

variable [CompleteSpace 𝕜]

section ModelCovariantDerivative

/-!
## Implementation layer: model-space tensor formula

These definitions are the fixed-vector-space formulas used after trivializing
the tensor bundle in a chart.  They are deliberately lower-level than
`nabla0SFun` / `nablaRSFun`.
-/

/-- Pointwise model formula for the covariant derivative of a covariant tensor.

The input `dα_X` is the first-order derivative of the tensor components in the
direction `X`, while `ΓX` is the connection endomorphism acting on each input
slot. -/
theorem contDiffWithinAt_covariantDeriv_tensor0SModelWithin (s : ℕ)
    {m n' : WithTop ℕ∞} {X : E → E} {ΓX : E → E →L[𝕜] E}
    {α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s}
    {u : Set E} {x : E}
    (hα : ContDiffWithinAt 𝕜 n' α u x)
    (hX : ContDiffWithinAt 𝕜 m X u x)
    (hΓ : ContDiffWithinAt 𝕜 m ΓX u x)
    (hu : UniqueDiffOn 𝕜 u) (hmn : m + 1 ≤ n') (hx : x ∈ u) :
    ContDiffWithinAt 𝕜 m
      (fun y => covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E)
        s X ΓX α u y) u x := by
  have hprincipal :
      ContDiffWithinAt 𝕜 m
        (fun y => fderivWithin 𝕜 α u y (X y)) u x :=
    hα.fderivWithin_right_apply hX hu hmn hx
  have hα_m : ContDiffWithinAt 𝕜 m α u x :=
    hα.of_le (le_trans le_self_add hmn)
  have hCorrOp :
      ContDiffWithinAt 𝕜 m
        (fun y => lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s (ΓX y)) u x := by
    simpa using
      hΓ.continuousLinearMap_comp
        (lieDeriv_correctionOpL (𝕜 := 𝕜) (E := E) s)
  have hCorr :
      ContDiffWithinAt 𝕜 m
        (fun y => lieDeriv_correction (𝕜 := 𝕜) (E := E) s (ΓX y) (α y)) u x := by
    simpa [lieDeriv_correctionL] using hCorrOp.clm_apply hα_m
  simpa [covariantDeriv_tensor0SModelWithin, covariantDeriv_tensor0SModelAt] using
    hprincipal.sub hCorr

/-- Smoothness of the fixed-set model covariant derivative of a mixed tensor.

This is the mixed-tensor analogue of
`contDiffWithinAt_covariantDeriv_tensor0SModelWithin`: the principal term is
`DT(X)`, the output covariant slots are corrected by precomposition with
`C_s(ΓX)`, and the input covariant slots by postcomposition with `C_r(ΓX)`. -/
theorem contDiffWithinAt_covariantDeriv_tensorRSModelWithin (r s : ℕ)
    {m n' : WithTop ℕ∞} {X : E → E} {ΓX : E → E →L[𝕜] E}
    {T : E → TensorRSModel r s 𝕜 E}
    {u : Set E} {x : E}
    (hT : ContDiffWithinAt 𝕜 n' T u x)
    (hX : ContDiffWithinAt 𝕜 m X u x)
    (hΓ : ContDiffWithinAt 𝕜 m ΓX u x)
    (hu : UniqueDiffOn 𝕜 u) (hmn : m + 1 ≤ n') (hx : x ∈ u) :
    ContDiffWithinAt 𝕜 m
      (fun y => covariantDeriv_tensorRSModelWithin (𝕜 := 𝕜) (E := E)
        r s X ΓX T u y) u x := by
  have hprincipal :
      ContDiffWithinAt 𝕜 m
        (fun y => fderivWithin 𝕜 T u y (X y)) u x :=
    hT.fderivWithin_right_apply hX hu hmn hx
  have hT_m : ContDiffWithinAt 𝕜 m T u x :=
    hT.of_le (le_trans le_self_add hmn)
  have hCorrS :
      ContDiffWithinAt 𝕜 m
        (fun y => lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s (ΓX y)) u x := by
    simpa using
      hΓ.continuousLinearMap_comp
        (lieDeriv_correctionOpL (𝕜 := 𝕜) (E := E) s)
  have hCorrR :
      ContDiffWithinAt 𝕜 m
        (fun y => lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r (ΓX y)) u x := by
    simpa using
      hΓ.continuousLinearMap_comp
        (lieDeriv_correctionOpL (𝕜 := 𝕜) (E := E) r)
  have hOut :
      ContDiffWithinAt 𝕜 m
        (fun y => (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s (ΓX y)).comp (T y)) u x :=
    hCorrS.clm_comp hT_m
  have hIn :
      ContDiffWithinAt 𝕜 m
        (fun y => (T y).comp (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) r (ΓX y))) u x :=
    hT_m.clm_comp hCorrR
  simpa [covariantDeriv_tensorRSModelWithin, covariantDeriv_tensorRSModelAt] using
    (hprincipal.sub hOut).add hIn

/- Reusable slot-correction Leibniz rule for the covariant tensor product.

This is the same algebra proved for Lie derivatives; the only semantic change
is that `ΓX` is read as the connection endomorphism in the `X` direction. -/
omit [CompleteSpace 𝕜] in
lemma covariantSlotCorrection_modelProduct (s q : ℕ) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (β : Tensor0SModel (𝕜 := 𝕜) (E := E) q) :
    lieDeriv_correction (s + q) ΓX
        (Bundle.continuousMultilinearMap.modelProduct s q α β) =
      Bundle.continuousMultilinearMap.modelProduct s q
          (lieDeriv_correction s ΓX α) β +
        Bundle.continuousMultilinearMap.modelProduct s q
          α (lieDeriv_correction q ΓX β) :=
  lieDeriv_correction_modelProduct (𝕜 := 𝕜) (E := E) s q ΓX α β
end ModelCovariantDerivative

end

end TensorLieDeriv
