import RicciFlower.Tensor.RSTensor.LieDerivative
import RicciFlower.Tensor.RSTensor.Basis
import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap

/-!
# Model-space covariant derivative for covariant tensors
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
def covariantDeriv_tensor0SModelAt (s : ℕ)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  dα_X - lieDeriv_correction s ΓX α

omit [CompleteSpace 𝕜] in
@[simp] lemma covariantDeriv_tensor0SModelAt_apply (s : ℕ)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s dα_X ΓX α =
      dα_X - lieDeriv_correction s ΓX α := by
  rfl

/-- The continuous linear map on model covariant tensors induced by a slot permutation. -/
noncomputable def tensor0SModelDomDomCongrL {s q : ℕ} (e : Fin s ≃ Fin q) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s →L[𝕜]
      Tensor0SModel (𝕜 := 𝕜) (E := E) q :=
  (ContinuousMultilinearMap.domDomCongrₗᵢ 𝕜 E 𝕜 e).toContinuousLinearEquiv

@[simp]
theorem tensor0SModelDomDomCongrL_apply {s q : ℕ} (e : Fin s ≃ Fin q)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    tensor0SModelDomDomCongrL (𝕜 := 𝕜) (E := E) e α = α.domDomCongr e := rfl

/-- Differentiating a slot-permuted model tensor field permutes the ordinary
model derivative. -/
theorem fderivWithin_tensor0SModelDomDomCongrL_apply {s q : ℕ}
    (e : Fin s ≃ Fin q)
    (α : E -> Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    {u : Set E} {y : E}
    (hα : DifferentiableWithinAt 𝕜 α u y)
    (hu : UniqueDiffWithinAt 𝕜 u y) :
    fderivWithin 𝕜
        (fun z : E => tensor0SModelDomDomCongrL (𝕜 := 𝕜) (E := E) e (α z))
        u y =
      (tensor0SModelDomDomCongrL (𝕜 := 𝕜) (E := E) e).comp
        (fderivWithin 𝕜 α u y) := by
  let L := tensor0SModelDomDomCongrL (𝕜 := 𝕜) (E := E) e
  have hlin : DifferentiableAt 𝕜 (fun w => L w) (α y) := L.differentiableAt
  have hcomp :=
    fderivWithin_comp (x := y) (f := α) (g := fun w => L w)
      (s := u) (t := Set.univ)
      (by simpa using hlin.differentiableWithinAt)
      hα (by intro z hz; simp) hu
  rw [L.fderivWithin (s := Set.univ) (x := α y) uniqueDiffWithinAt_univ] at hcomp
  simpa [L, Function.comp_def] using hcomp

/-- Model-space covariant derivative of a covariant tensor field.

This is the chart-level formula
`∇_X α = Dα(X) - Σᵢ α(..., Γ_X -, ...)`. -/
def covariantDeriv_tensor0SModel (s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s
    (fderiv 𝕜 α x (X x)) (ΓX x) (α x)

/-- Within-set variant of `covariantDeriv_tensor0SModel`. -/
def covariantDeriv_tensor0SModelWithin (s : ℕ)
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (u : Set E) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s
    (fderivWithin 𝕜 α u x (X x)) (ΓX x) (α x)

theorem covariantDeriv_tensor0SModelAt_apply_slots {s : ℕ}
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (slots : Fin s → E) :
    covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s dα_X ΓX α slots =
      dα_X slots -
        ∑ a : Fin s, α (Function.update slots a (ΓX (slots a))) := by
  classical
  unfold covariantDeriv_tensor0SModelAt lieDeriv_correction substituteArg
  simp only [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  funext b
  by_cases hb : b = a
  · subst hb
    simp
  · simp [Function.update, hb]

/-- Model covariant differentiation commutes with a covariant-slot permutation,
provided the ordinary derivative term has already been permuted. -/
theorem covariantDeriv_tensor0SModelAt_domDomCongr_apply_slots {s q : ℕ}
    (e : Fin s ≃ Fin q)
    (dα_X : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (dβ_X : Tensor0SModel (𝕜 := 𝕜) (E := E) q)
    (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (hD : ∀ slots : Fin q -> E, dβ_X slots = dα_X (fun a : Fin s => slots (e a)))
    (slots : Fin q -> E) :
    covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) q dβ_X ΓX
        (α.domDomCongr e) slots =
      covariantDeriv_tensor0SModelAt (𝕜 := 𝕜) (E := E) s dα_X ΓX α
        (fun a : Fin s => slots (e a)) := by
  classical
  rw [covariantDeriv_tensor0SModelAt_apply_slots,
    covariantDeriv_tensor0SModelAt_apply_slots, hD slots]
  congr 1
  symm
  refine Fintype.sum_equiv e
    (fun a : Fin s =>
      α (Function.update (fun a : Fin s => slots (e a)) a (ΓX (slots (e a)))))
    (fun b : Fin q =>
      (α.domDomCongr e) (Function.update slots b (ΓX (slots b)))) ?_
  intro a
  simp only [ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext c
  by_cases hca : c = a
  · subst c
    simp
  · have hne : e c ≠ e a := fun h => hca (e.injective h)
    simp [Function.update_of_ne, hca, hne]

theorem covariantDeriv_tensor0SModelWithin_apply_slots {s : ℕ}
    (X : E → E) (ΓX : E → E →L[𝕜] E)
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (u : Set E) (x : E)
    (slots : Fin s → E) :
    covariantDeriv_tensor0SModelWithin (𝕜 := 𝕜) (E := E) s X ΓX α u x slots =
      fderivWithin 𝕜 α u x (X x) slots -
        ∑ a : Fin s, α x (Function.update slots a (ΓX x (slots a))) := by
  unfold covariantDeriv_tensor0SModelWithin
  exact covariantDeriv_tensor0SModelAt_apply_slots (𝕜 := 𝕜) (E := E)
    (fderivWithin 𝕜 α u x (X x)) (ΓX x) (α x) slots

/-- Evaluation of the covariant-slot correction operator on explicit slots. -/
theorem lieDeriv_correctionL_apply_slots {s : ℕ}
    (ΓX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (slots : Fin s → E) :
    (lieDeriv_correctionL (𝕜 := 𝕜) (E := E) s ΓX α) slots =
      ∑ a : Fin s, α (Function.update slots a (ΓX (slots a))) := by
  classical
  rw [lieDeriv_correctionL_apply]
  unfold lieDeriv_correction substituteArg
  simp only [ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  funext b
  by_cases hb : b = a
  · subst hb
    simp
  · simp [Function.update, hb]

/-- Product rule for evaluating a model `(0,s)` tensor on variable model slots
written as continuous linear maps from `𝕜` and then evaluated on fixed scalar
slots. This is the pure model-space calculus input behind the moving-slot
derivation formula. -/
theorem fderivWithin_tensor0SModel_eval_linear_slots {s : ℕ}
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (L : Fin s → E → 𝕜 →L[𝕜] E)
    (u : Set E) (y Xy : E)
    (hα : DifferentiableWithinAt 𝕜 α u y)
    (hL : ∀ a : Fin s, DifferentiableWithinAt 𝕜 (L a) u y)
    (hu : UniqueDiffWithinAt 𝕜 u y)
    (c : Fin s → 𝕜) :
    fderivWithin 𝕜 (fun z : E => α z (fun a : Fin s => L a z (c a))) u y Xy =
      fderivWithin 𝕜 α u y Xy (fun a : Fin s => L a y (c a)) +
        ∑ a : Fin s,
          α y (Function.update (fun b : Fin s => L b y (c b)) a
            (fderivWithin 𝕜 (L a) u y Xy (c a))) := by
  classical
  let F : E → ContinuousMultilinearMap 𝕜 (fun _ : Fin s => 𝕜) 𝕜 :=
    fun z => (α z).compContinuousLinearMap (fun a : Fin s => L a z)
  have hFdiff : DifferentiableWithinAt 𝕜 F u y := by
    exact hα.continuousMultilinearMapCompContinuousLinearMap hL
  have happly :=
    fderivWithin_continuousMultilinear_apply_const_apply
      (𝕜 := 𝕜) (s := u) (x := y) (c := F) hu hFdiff c Xy
  change fderivWithin 𝕜 (fun z : E => F z c) u y Xy =
    (fderivWithin 𝕜 F u y) Xy c at happly
  change fderivWithin 𝕜 (fun z : E => F z c) u y Xy =
    fderivWithin 𝕜 α u y Xy (fun a : Fin s => L a y (c a)) +
      ∑ a : Fin s,
        α y (Function.update (fun b : Fin s => L b y (c b)) a
          (fderivWithin 𝕜 (L a) u y Xy (c a)))
  rw [happly]
  have hF :=
    fderivWithin_continuousMultilinearMapCompContinuousLinearMap
      (𝕜 := 𝕜) (f := α) (g := L) (s := u) (x := y) hα hL hu
  rw [hF]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.add_apply]
  change
    ((fderivWithin 𝕜 α u y) Xy).compContinuousLinearMap
        (fun x : Fin s => L x y) c +
      (ContinuousMultilinearMap.fderivCompContinuousLinearMap (α y)
        (fun x : Fin s => L x y)
        (fun i : Fin s => (fderivWithin 𝕜 (L i) u y) Xy)) c =
    ((fderivWithin 𝕜 α u y) Xy) (fun a : Fin s => L a y (c a)) +
      ∑ a : Fin s,
        α y (Function.update (fun a : Fin s => L a y (c a)) a
          (((fderivWithin 𝕜 (L a) u y) Xy) (c a)))
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.fderivCompContinuousLinearMap_apply]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  funext b
  by_cases hb : b = a
  · subst hb
    simp
  · simp [Function.update, hb]

/-- Product rule for evaluating a model `(0,s)` tensor on genuinely `E`-valued
variable model slots. -/
theorem fderivWithin_tensor0SModel_eval_slots {s : ℕ}
    (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (V : Fin s → E → E)
    (u : Set E) (y Xy : E)
    (hα : DifferentiableWithinAt 𝕜 α u y)
    (hV : ∀ a : Fin s, DifferentiableWithinAt 𝕜 (V a) u y)
    (hu : UniqueDiffWithinAt 𝕜 u y) :
    fderivWithin 𝕜 (fun z : E => α z (fun a : Fin s => V a z)) u y Xy =
      fderivWithin 𝕜 α u y Xy (fun a : Fin s => V a y) +
        ∑ a : Fin s,
          α y (Function.update (fun b : Fin s => V b y) a
            (fderivWithin 𝕜 (V a) u y Xy)) := by
  classical
  let one : 𝕜 →L[𝕜] 𝕜 := 1
  let A : E →L[𝕜] (𝕜 →L[𝕜] E) :=
    ContinuousLinearMap.smulRightL 𝕜 𝕜 E one
  let L : Fin s → E → 𝕜 →L[𝕜] E := fun a z => A (V a z)
  have hL : ∀ a : Fin s, DifferentiableWithinAt 𝕜 (L a) u y := by
    intro a
    exact A.differentiableWithinAt.comp y (hV a) (Set.mapsTo_univ _ _)
  have h := fderivWithin_tensor0SModel_eval_linear_slots
    (𝕜 := 𝕜) (E := E) (s := s) α L u y Xy hα hL hu (fun _ => (1 : 𝕜))
  have hderiv (a : Fin s) :
      ((fderivWithin 𝕜 (L a) u y) Xy) (1 : 𝕜) =
        fderivWithin 𝕜 (V a) u y Xy := by
    have hA :
        fderivWithin 𝕜 (L a) u y =
          A.comp (fderivWithin 𝕜 (V a) u y) := by
      have hcomp := A.hasFDerivAt.comp_hasFDerivWithinAt y (hV a).hasFDerivWithinAt
      simpa [L, Function.comp_def] using hcomp.fderivWithin hu
    rw [hA]
    simp [A, one, ContinuousLinearMap.smulRight_apply]
  calc
    fderivWithin 𝕜 (fun z : E => α z (fun a : Fin s => V a z)) u y Xy
        = fderivWithin 𝕜 (fun z : E => α z (fun a : Fin s => L a z (1 : 𝕜))) u y Xy := by
            simp [L, A, one, ContinuousLinearMap.smulRight_apply]
    _ = fderivWithin 𝕜 α u y Xy (fun a : Fin s => L a y (1 : 𝕜)) +
        ∑ a : Fin s,
          α y (Function.update (fun b : Fin s => L b y (1 : 𝕜)) a
            (((fderivWithin 𝕜 (L a) u y) Xy) (1 : 𝕜))) := h
    _ = fderivWithin 𝕜 α u y Xy (fun a : Fin s => V a y) +
        ∑ a : Fin s,
          α y (Function.update (fun b : Fin s => V b y) a
            (fderivWithin 𝕜 (V a) u y Xy)) := by
            congr 1
            · congr
              funext a
              simp [L, A, one, ContinuousLinearMap.smulRight_apply]
            · refine Finset.sum_congr rfl fun a _ => ?_
              congr 1
              funext b
              by_cases hb : b = a
              · subst hb
                simpa using hderiv b
              · simp [Function.update, hb, L, A, one, ContinuousLinearMap.smulRight_apply]

end ModelCovariantDerivative

end

end TensorLieDeriv
