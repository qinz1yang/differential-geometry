/-
Author: Yuan Liao
Coauthor: Ayush Khaitan, Jack McCarthy
-/
import DifferentialGeometry.Tensor.RSTensor.Defs
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorField.Pullback
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field

namespace DifferentialGeometry
namespace TensorLieDeriv

noncomputable section


open Bundle Set IsManifold ContinuousLinearMap VectorField Filter
    DifferentialGeometry.Tensor0SBundle Function
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable (n : WithTop ℕ∞ := ⊤) [IsManifold I n M]
variable {x x₀ : M} {s : Set M}

section VectorSpaceLieDeriv

variable {s : ℕ}

noncomputable def fderivTensor0S (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (x : E) : E →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  fderiv 𝕜 α x

noncomputable def vectorFieldActionOnTensor0S
    (X : E → E) (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  fderivTensor0S α x (X x)

noncomputable def substituteArg (s : ℕ) (i : Fin s)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (f : E →L[𝕜] E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  α.compContinuousLinearMap (fun j => if j = i then f else ContinuousLinearMap.id 𝕜 E)

noncomputable def lieDerivCorrection (s : ℕ)
    (DX : E →L[𝕜] E) (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  ∑ i : Fin s, substituteArg s i α DX

noncomputable def lieDerivTensor0S (s : ℕ)
    (X : E → E) (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  vectorFieldActionOnTensor0S X α x - lieDerivCorrection s (fderiv 𝕜 X x) (α x)

noncomputable def lieDerivTensor0SWithin (s : ℕ)
    (X : E → E) (α : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s) (t : Set E) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  fderivWithin 𝕜 α t x (X x) - lieDerivCorrection s (fderivWithin 𝕜 X t x) (α x)

end VectorSpaceLieDeriv

section ManifoldLieDeriv

variable {s : ℕ}

abbrev Tensor0SBundle (s : ℕ) (I : ModelWithCorners 𝕜 E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :=
  TotalSpace (Tensor0SModel (𝕜 := 𝕜) (E := E) s) (fun x : M => Tensor0SSpace s I x)

noncomputable def mpullbackTensor0S
    {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I 1 M]
    (f : M → M')
    (α : (x : M') → ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I' x) 𝕜)
    (x : M) :
    Tensor0SSpace s I x :=
  (α (f x)).compContinuousLinearMap
    (fun _ => (mfderiv I I' f x).comp
      (ContinuousLinearMap.id 𝕜 (TangentSpace I x)))

noncomputable def mpullbackWithinTensor0S
    {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I 1 M]
    (f : M → M') (t : Set M)
    (α : (x : M') → ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I' x) 𝕜)
    (x : M) :
    Tensor0SSpace s I x :=
  (α (f x)).compContinuousLinearMap
    (fun _ => (mfderivWithin I I' f t x).comp
      (ContinuousLinearMap.id 𝕜 (TangentSpace I x)))

section SmoothVectorFieldLieDeriv

variable [IsManifold I 1 M]

noncomputable def mlieDerivTensor0SWithin (s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : (x : M) → Tensor0SSpace s I x)
    (t : Set M)
    (x₀ : M) :
    Tensor0SSpace s I x₀ := by
  let X' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I)
  let α' : E → Tensor0SModel (𝕜 := 𝕜) (E := E) s := fun y =>
    α ((extChartAt I x₀).symm y)
  let result := lieDerivTensor0SWithin s X' α'
    ((extChartAt I x₀).symm ⁻¹' t ∩ range I)
    (extChartAt I x₀ x₀)
  exact result

noncomputable def mlieDerivTensor0S (s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (α : (x : M) → Tensor0SSpace s I x)
    (x₀ : M) :
    Tensor0SSpace s I x₀ :=
  mlieDerivTensor0SWithin (n := n) s X α univ x₀

variable {s : ℕ}
variable {X : ContMDiffSection I E n (TangentSpace I : M → Type _)}
variable {α β : (x : M) → Tensor0SSpace s I x}

omit [IsManifold I n M] in
@[simp] lemma mlieDeriv_tensor0SWithin_univ :
    mlieDerivTensor0SWithin (I := I) (n := n) s X α univ = mlieDerivTensor0S (n := n) s X α := rfl

end SmoothVectorFieldLieDeriv

lemma lieDeriv_correction_add (DX : E →L[𝕜] E)
    (α β : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    lieDerivCorrection s DX (α + β) =
    lieDerivCorrection s DX α + lieDerivCorrection s DX β := by
  unfold lieDerivCorrection
  rw [← Finset.sum_add_distrib]
  congr 1

lemma lieDeriv_correction_smul (DX : E →L[𝕜] E) (c : 𝕜)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    lieDerivCorrection s DX (c • α) = c • lieDerivCorrection s DX α := by
  unfold lieDerivCorrection
  rw [Finset.smul_sum]
  congr 1

lemma substituteArg_add_right (i : Fin s)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (DX DY : E →L[𝕜] E) :
    substituteArg s i α (DX + DY) = substituteArg s i α DX + substituteArg s i α DY := by
  ext v
  simp only [substituteArg, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    add_apply]
  convert α.map_update_add (fun j => v j) i (DX (v i)) (DY (v i))
  all_goals
    rename_i j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]

lemma substituteArg_smul_right (i : Fin s)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) (c : 𝕜) (DX : E →L[𝕜] E) :
    substituteArg s i α (c • DX) = c • substituteArg s i α DX := by
  ext v
  simp only [substituteArg, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    smul_apply]
  convert α.map_update_smul (fun j => v j) i c (DX (v i))
  all_goals
    rename_i j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]

lemma lieDeriv_correction_add_right (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (DX DY : E →L[𝕜] E) :
    lieDerivCorrection s (DX + DY) α =
      lieDerivCorrection s DX α + lieDerivCorrection s DY α := by
  unfold lieDerivCorrection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact substituteArg_add_right (s := s) i α DX DY

lemma lieDeriv_correction_smul_right (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (c : 𝕜) (DX : E →L[𝕜] E) :
    lieDerivCorrection s (c • DX) α = c • lieDerivCorrection s DX α := by
  unfold lieDerivCorrection
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact substituteArg_smul_right (s := s) i α c DX

lemma lieDeriv_correction_zero (DX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) 0) :
    lieDerivCorrection 0 DX α = 0 := by
  dsimp[lieDerivCorrection]
  simp only [Finset.univ_eq_empty, Finset.sum_empty]

lemma lieDeriv_correction_modelProduct (s q : ℕ) (DX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (β : Tensor0SModel (𝕜 := 𝕜) (E := E) q) :
    lieDerivCorrection (s + q) DX
        (Bundle.continuousMultilinearMap.modelProduct s q α β) =
      Bundle.continuousMultilinearMap.modelProduct s q
          (lieDerivCorrection s DX α) β +
        Bundle.continuousMultilinearMap.modelProduct s q
          α (lieDerivCorrection q DX β) := by
  ext v
  rw [lieDerivCorrection, Fin.sum_univ_add]
  simp only [lieDerivCorrection, sum_apply,
    add_apply, Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [substituteArg, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      Bundle.continuousMultilinearMap.modelProduct_apply, Function.comp_apply]
    congr 1
    · congr 1
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
    · congr 1
      funext j
      have hneq : Fin.natAdd s j ≠ Fin.castAdd q i := by
        intro h
        have hval := congrArg Fin.val h
        simp [Fin.val_natAdd, Fin.val_castAdd] at hval
        omega
      simp [hneq]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [substituteArg, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      Bundle.continuousMultilinearMap.modelProduct_apply, Function.comp_apply]
    congr 1
    · congr 1
      funext j
      have hneq : Fin.castAdd q j ≠ Fin.natAdd s i := by
        intro h
        have hval := congrArg Fin.val h
        simp [Fin.val_natAdd, Fin.val_castAdd] at hval
        omega
      simp [hneq]
    · congr 1
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]

variable [CompleteSpace 𝕜]

noncomputable def lieDerivCorrectionL (s : ℕ) (DX : E →L[𝕜] E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) s →L[𝕜]
      Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  LinearMap.toContinuousLinearMap
    { toFun := fun α => lieDerivCorrection s DX α
      map_add' := fun α β => lieDeriv_correction_add (s := s) DX α β
      map_smul' := fun c α => lieDeriv_correction_smul (s := s) DX c α }

@[simp]
theorem lieDeriv_correctionL_apply (DX : E →L[𝕜] E)
    (α : Tensor0SModel (𝕜 := 𝕜) (E := E) s) :
    lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s DX α = lieDerivCorrection s DX α := by
  simp [lieDerivCorrectionL]

noncomputable def lieDerivCorrectionOpL (s : ℕ) :
    (E →L[𝕜] E) →L[𝕜]
      (Tensor0SModel (𝕜 := 𝕜) (E := E) s →L[𝕜]
        Tensor0SModel (𝕜 := 𝕜) (E := E) s) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun DX => lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s DX
      map_add' := fun DX DY => by
        ext α
        simp [lieDeriv_correction_add_right]
      map_smul' := fun c DX => by
        ext α
        simp [lieDeriv_correction_smul_right] }

@[simp]
theorem lieDeriv_correctionOpL_apply (DX : E →L[𝕜] E) :
    lieDerivCorrectionOpL (𝕜 := 𝕜) (E := E) s DX =
      lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s DX := by
  simp [lieDerivCorrectionOpL]

noncomputable def directionalDerivTensorRSWithin (r s : ℕ)
    (X : E → E)
    (T : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (t : Set E) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  fderivWithin 𝕜 T t x (X x)

noncomputable def directionalDerivTensorRS (r s : ℕ)
    (X : E → E)
    (T : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  fderiv 𝕜 T x (X x)

noncomputable def lieDerivTensorRSWithin (r s : ℕ)
    (X : E → E)
    (T : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (t : Set E) (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  let DX := fderivWithin 𝕜 X t x
  fderivWithin 𝕜 T t x (X x)
    - (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s DX).comp (T x)
    + (T x).comp (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) r DX)

noncomputable def lieDerivTensorRS (r s : ℕ)
    (X : E → E)
    (T : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s)
    (x : E) :
    Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
  let DX := fderiv 𝕜 X x
  fderiv 𝕜 T x (X x)
    - (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s DX).comp (T x)
    + (T x).comp (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) r DX)

omit [CompleteSpace 𝕜] in
theorem contDiffWithinAt_directionalDeriv_tensorRSWithin (r s : ℕ) {m n' : WithTop ℕ∞}
    {X : E → E}
    {T : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s}
    {u : Set E} {x : E}
    (hT : ContDiffWithinAt 𝕜 n' T u x)
    (hX : ContDiffWithinAt 𝕜 m X u x)
    (hu : UniqueDiffOn 𝕜 u) (hmn : m + 1 ≤ n') (hx : x ∈ u) :
    ContDiffWithinAt 𝕜 m (fun y => directionalDerivTensorRSWithin r s X T u y) u x := by
  simpa [directionalDerivTensorRSWithin] using hT.fderivWithin_right_apply hX hu hmn hx

theorem contDiffWithinAt_lieDeriv_tensorRSWithin (r s : ℕ) {m n' : WithTop ℕ∞}
    {X : E → E}
    {T : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s}
    {u : Set E} {x : E}
    (hT : ContDiffWithinAt 𝕜 n' T u x)
    (hX : ContDiffWithinAt 𝕜 n' X u x)
    (hu : UniqueDiffOn 𝕜 u) (hmn : m + 1 ≤ n') (hx : x ∈ u) :
    ContDiffWithinAt 𝕜 m (fun y => lieDerivTensorRSWithin r s X T u y) u x := by
  have hprincipal :
      ContDiffWithinAt 𝕜 m (fun y => directionalDerivTensorRSWithin r s X T u y) u x :=
    contDiffWithinAt_directionalDeriv_tensorRSWithin r s hT
      (hX.of_le (le_trans le_self_add hmn)) hu hmn hx
  have hT_m : ContDiffWithinAt 𝕜 m T u x :=
    hT.of_le (le_trans le_self_add hmn)
  have hDX : ContDiffWithinAt 𝕜 m (fun y => fderivWithin 𝕜 X u y) u x :=
    hX.fderivWithin_right hu hmn hx
  have hCorrS :
      ContDiffWithinAt 𝕜 m
        (fun y => lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s
          (fderivWithin 𝕜 X u y)) u x := by
    exact (hDX.continuousLinearMap_comp
      (lieDerivCorrectionOpL (𝕜 := 𝕜) (E := E) s)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl) rfl
  have hCorrR :
      ContDiffWithinAt 𝕜 m
        (fun y => lieDerivCorrectionL (𝕜 := 𝕜) (E := E) r
          (fderivWithin 𝕜 X u y)) u x := by
    exact (hDX.continuousLinearMap_comp
      (lieDerivCorrectionOpL (𝕜 := 𝕜) (E := E) r)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl) rfl
  have hOut :
      ContDiffWithinAt 𝕜 m
        (fun y => (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) s
          (fderivWithin 𝕜 X u y)).comp (T y)) u x :=
    hCorrS.clm_comp hT_m
  have hIn :
      ContDiffWithinAt 𝕜 m
        (fun y => (T y).comp (lieDerivCorrectionL (𝕜 := 𝕜) (E := E) r
          (fderivWithin 𝕜 X u y))) u x :=
    hT_m.clm_comp hCorrR
  simpa [lieDerivTensorRSWithin, directionalDerivTensorRSWithin] using
    (hprincipal.sub hOut).add hIn

section SmoothVectorFieldRSLieDeriv

variable [IsManifold I 1 M] [IsManifold I (n + 1) M]

noncomputable def mdirectionalDerivTensorRSWithin (r s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (u : Set M) (x₀ : M) : TensorRSSpace r s I x₀ := by
  let X' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm X (range I)
  let T' : E → Tensor0SModel (𝕜 := 𝕜) (E := E) r →L[𝕜] Tensor0SModel (𝕜 := 𝕜) (E := E) s :=
    fun y => tensorRSSpaceContinuousLinearEquiv (I := I) r s
      ((extChartAt I x₀).symm y) (T.toFun ((extChartAt I x₀).symm y))
  exact (tensorRSSpaceContinuousLinearEquiv (I := I) r s x₀).symm
    (lieDerivTensorRSWithin r s X' T'
      ((extChartAt I x₀).symm ⁻¹' u ∩ range I)
      (extChartAt I x₀ x₀))

noncomputable def mdirectionalDerivTensorRS (r s : ℕ)
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _))
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s)
    (x₀ : M) : TensorRSSpace r s I x₀ :=
  mdirectionalDerivTensorRSWithin (n := n) r s X T univ x₀

end SmoothVectorFieldRSLieDeriv

end ManifoldLieDeriv

end

end TensorLieDeriv
end DifferentialGeometry
