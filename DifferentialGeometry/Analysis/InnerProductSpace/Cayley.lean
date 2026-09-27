import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section

open scoped InnerProductSpace ContDiff

namespace skewAdjoint

variable {k E : Type*} [RCLike k] [NormedAddCommGroup E] [InnerProductSpace k E]
  [CompleteSpace E]

theorem inner_map_add_inner_map_eq_zero (K : skewAdjoint (E →L[k] E)) (x y : E) :
    inner k ((K : E →L[k] E) x) y + inner k x ((K : E →L[k] E) y) = 0 := by
  have h := (K : E →L[k] E).adjoint_inner_left y x
  rw [← ContinuousLinearMap.star_eq_adjoint, star_val_eq,
    neg_apply, inner_neg_left] at h
  linear_combination -h

theorem re_inner_map_self_eq_zero (K : skewAdjoint (E →L[k] E)) (x : E) :
    RCLike.re (inner k ((K : E →L[k] E) x) x) = 0 := by
  have h := congrArg RCLike.re (inner_map_add_inner_map_eq_zero K x x)
  rw [map_add, map_zero, inner_re_symm x] at h
  linarith

theorem isUnit_one_add (K : skewAdjoint (E →L[k] E)) :
    IsUnit (1 + (K : E →L[k] E)) := by
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _ (c := 1) zero_lt_one
  intro x
  have h : RCLike.re (inner k ((1 + (K : E →L[k] E)) x) x) = ‖x‖ ^ 2 := by
    simp only [add_apply, one_apply_eq_self,
      inner_add_left, map_add, re_inner_map_self_eq_zero K, add_zero]
    exact (InnerProductSpace.norm_sq_eq_re_inner x).symm
  simpa only [NNReal.coe_one, mul_one, h] using
    RCLike.re_le_norm (inner k ((1 + (K : E →L[k] E)) x) x)

theorem isUnit_one_sub (K : skewAdjoint (E →L[k] E)) :
    IsUnit (1 - (K : E →L[k] E)) := by
  simpa only [AddSubgroup.coe_neg, ← sub_eq_add_neg] using isUnit_one_add (-K)

private def oneAddEquiv (K : skewAdjoint (E →L[k] E)) : E ≃L[k] E :=
  ContinuousLinearEquiv.ofUnit (isUnit_one_add K).unit

private theorem oneAddEquiv_apply (K : skewAdjoint (E →L[k] E)) (x : E) :
    oneAddEquiv K x = x + (K : E →L[k] E) x := by
  change ((isUnit_one_add K).unit : E →L[k] E) x = _
  rw [(isUnit_one_add K).unit_spec]
  rfl

private theorem inner_one_sub_eq_inner_one_add (K : skewAdjoint (E →L[k] E)) (x y : E) :
    inner k (x - (K : E →L[k] E) x) (y - (K : E →L[k] E) y) =
      inner k (x + (K : E →L[k] E) x) (y + (K : E →L[k] E) y) := by
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right]
  linear_combination -2 * inner_map_add_inner_map_eq_zero K x y

def cayleyTransform (K : skewAdjoint (E →L[k] E)) : E ≃ₗᵢ[k] E :=
  ((oneAddEquiv K).symm.trans (oneAddEquiv (-K))).toLinearEquiv.isometryOfInner (by
    intro x y
    change inner k (oneAddEquiv (-K) ((oneAddEquiv K).symm x))
      (oneAddEquiv (-K) ((oneAddEquiv K).symm y)) = _
    simp only [oneAddEquiv_apply, AddSubgroup.coe_neg, neg_apply,
      ← sub_eq_add_neg]
    rw [inner_one_sub_eq_inner_one_add]
    simp only [← oneAddEquiv_apply, ContinuousLinearEquiv.apply_symm_apply])

@[simp]
theorem cayleyTransform_apply_one_add (K : skewAdjoint (E →L[k] E)) (x : E) :
    cayleyTransform K (x + (K : E →L[k] E) x) = x - (K : E →L[k] E) x := by
  change oneAddEquiv (-K) ((oneAddEquiv K).symm (x + (K : E →L[k] E) x)) = _
  rw [← oneAddEquiv_apply K, ContinuousLinearEquiv.symm_apply_apply, oneAddEquiv_apply]
  simp only [AddSubgroup.coe_neg, neg_apply, sub_eq_add_neg]

@[simp]
theorem cayleyTransform_zero : cayleyTransform (0 : skewAdjoint (E →L[k] E)) =
    LinearIsometryEquiv.refl k E := by
  ext x
  simpa using cayleyTransform_apply_one_add (0 : skewAdjoint (E →L[k] E)) x

@[simp]
theorem cayleyTransform_neg (K : skewAdjoint (E →L[k] E)) :
    cayleyTransform (-K) = (cayleyTransform K).symm := by
  ext x
  apply (cayleyTransform K).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  change oneAddEquiv (-K) ((oneAddEquiv K).symm
    (oneAddEquiv (- -K) ((oneAddEquiv (-K)).symm x))) = x
  simp only [neg_neg, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearEquiv.apply_symm_apply]

theorem cayleyTransform_toContinuousLinearMap (K : skewAdjoint (E →L[k] E)) :
    (cayleyTransform K : E →L[k] E) =
      (1 - (K : E →L[k] E)) * Ring.inverse (1 + (K : E →L[k] E)) := by
  have h : (cayleyTransform K : E →L[k] E) * (1 + (K : E →L[k] E)) =
      1 - (K : E →L[k] E) := by
    ext x
    exact cayleyTransform_apply_one_add K x
  calc
    (cayleyTransform K : E →L[k] E) =
        ((cayleyTransform K : E →L[k] E) * (1 + (K : E →L[k] E))) *
          Ring.inverse (1 + (K : E →L[k] E)) := by
      rw [mul_assoc, Ring.mul_inverse_cancel _ (isUnit_one_add K), mul_one]
    _ = _ := congrArg (fun L : E →L[k] E => L * Ring.inverse (1 + (K : E →L[k] E))) h

theorem one_add_cayleyTransform (K : skewAdjoint (E →L[k] E)) :
    1 + (cayleyTransform K : E →L[k] E) =
      (2 : k) • Ring.inverse (1 + (K : E →L[k] E)) := by
  ext x
  obtain ⟨y, rfl⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mp (isUnit_one_add K)).2 x
  have hinv : Ring.inverse (1 + (K : E →L[k] E)) (y + (K : E →L[k] E) y) = y :=
    congrArg (fun L : E →L[k] E => L y) (Ring.inverse_mul_cancel _ (isUnit_one_add K))
  change (y + (K : E →L[k] E) y) +
    cayleyTransform K (y + (K : E →L[k] E) y) =
      (2 : k) • Ring.inverse (1 + (K : E →L[k] E)) (y + (K : E →L[k] E) y)
  rw [cayleyTransform_apply_one_add, hinv]
  module

theorem isUnit_one_add_cayleyTransform (K : skewAdjoint (E →L[k] E)) :
    IsUnit (1 + (cayleyTransform K : E →L[k] E)) := by
  rw [one_add_cayleyTransform, Algebra.smul_def]
  apply IsUnit.mul
  · exact IsUnit.map (algebraMap k (E →L[k] E)) (isUnit_iff_ne_zero.mpr two_ne_zero)
  · rw [← (isUnit_one_add K).unit_spec, Ring.inverse_unit]
    exact Units.isUnit _

end skewAdjoint

namespace LinearIsometryEquiv

variable {k E : Type*} [RCLike k] [NormedAddCommGroup E] [InnerProductSpace k E]
  [CompleteSpace E]

private def inverseCayleyMap (p : E ≃ₗᵢ[k] E) : E →L[k] E :=
  (1 - (p : E →L[k] E)) * Ring.inverse (1 + (p : E →L[k] E))

omit [CompleteSpace E] in
private theorem inverseCayleyMap_apply_one_add (p : E ≃ₗᵢ[k] E)
    (hp : IsUnit (1 + (p : E →L[k] E))) (x : E) :
    inverseCayleyMap p (x + p x) = x - p x := by
  have h : inverseCayleyMap p * (1 + (p : E →L[k] E)) = 1 - (p : E →L[k] E) := by
    rw [inverseCayleyMap, mul_assoc, Ring.inverse_mul_cancel _ hp, mul_one]
  exact congrArg (fun L : E →L[k] E => L x) h

omit [CompleteSpace E] in
private theorem inverseCayleyMap_inner_add (p : E ≃ₗᵢ[k] E)
    (hp : IsUnit (1 + (p : E →L[k] E))) (x y : E) :
    inner k (inverseCayleyMap p x) y + inner k x (inverseCayleyMap p y) = 0 := by
  have hs : Function.Surjective ((1 + (p : E →L[k] E)) : E →L[k] E) := by
    rw [← hp.unit_spec]
    exact (ContinuousLinearEquiv.ofUnit hp.unit).surjective
  obtain ⟨x, rfl⟩ := hs x
  obtain ⟨y, rfl⟩ := hs y
  change inner k (inverseCayleyMap p (x + p x)) (y + p y) +
    inner k (x + p x) (inverseCayleyMap p (y + p y)) = 0
  rw [inverseCayleyMap_apply_one_add p hp, inverseCayleyMap_apply_one_add p hp]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right]
  linear_combination -2 * p.inner_map_map x y

def inverseCayleyTransform (p : E ≃ₗᵢ[k] E) (hp : IsUnit (1 + (p : E →L[k] E))) :
    skewAdjoint (E →L[k] E) :=
  ⟨inverseCayleyMap p, by
    rw [skewAdjoint.mem_iff]
    ext x
    apply ext_inner_right k
    intro y
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
      neg_apply, inner_neg_left]
    linear_combination inverseCayleyMap_inner_add p hp x y⟩

theorem inverseCayleyTransform_toContinuousLinearMap (p : E ≃ₗᵢ[k] E)
    (hp : IsUnit (1 + (p : E →L[k] E))) :
    (p.inverseCayleyTransform hp : E →L[k] E) =
      (1 - (p : E →L[k] E)) * Ring.inverse (1 + (p : E →L[k] E)) := rfl

@[simp]
theorem inverseCayleyTransform_apply_one_add (p : E ≃ₗᵢ[k] E)
    (hp : IsUnit (1 + (p : E →L[k] E))) (x : E) :
    (p.inverseCayleyTransform hp : E →L[k] E) (x + p x) = x - p x :=
  inverseCayleyMap_apply_one_add p hp x

@[simp]
theorem cayleyTransform_inverseCayleyTransform (p : E ≃ₗᵢ[k] E)
    (hp : IsUnit (1 + (p : E →L[k] E))) :
    skewAdjoint.cayleyTransform (p.inverseCayleyTransform hp) = p := by
  ext x
  have h := skewAdjoint.cayleyTransform_apply_one_add (p.inverseCayleyTransform hp) (x + p x)
  rw [inverseCayleyTransform_apply_one_add] at h
  have ha : (x + p x) + (x - p x) = (2 : k) • x := by module
  have hs : (x + p x) - (x - p x) = (2 : k) • p x := by module
  rw [ha, hs, map_smul] at h
  exact smul_right_injective E (two_ne_zero : (2 : k) ≠ 0) h

end LinearIsometryEquiv

namespace skewAdjoint

variable {k E : Type*} [RCLike k] [NormedAddCommGroup E] [InnerProductSpace k E]
  [CompleteSpace E]

@[simp]
theorem inverseCayleyTransform_cayleyTransform (K : skewAdjoint (E →L[k] E)) :
    (cayleyTransform K).inverseCayleyTransform (isUnit_one_add_cayleyTransform K) = K := by
  apply Subtype.ext
  ext x
  have h := LinearIsometryEquiv.inverseCayleyTransform_apply_one_add
    (cayleyTransform K) (isUnit_one_add_cayleyTransform K) (x + (K : E →L[k] E) x)
  rw [cayleyTransform_apply_one_add] at h
  have ha : (x + (K : E →L[k] E) x) + (x - (K : E →L[k] E) x) = (2 : k) • x := by
    module
  have hs : (x + (K : E →L[k] E) x) - (x - (K : E →L[k] E) x) =
      (2 : k) • (K : E →L[k] E) x := by module
  rw [ha, hs, map_smul] at h
  exact smul_right_injective E (two_ne_zero : (2 : k) ≠ 0) h

def cayleyEquiv : skewAdjoint (E →L[k] E) ≃
    {p : E ≃ₗᵢ[k] E | IsUnit (1 + (p : E →L[k] E))} where
  toFun K := ⟨cayleyTransform K, isUnit_one_add_cayleyTransform K⟩
  invFun p := p.1.inverseCayleyTransform p.2
  left_inv := inverseCayleyTransform_cayleyTransform
  right_inv p := Subtype.ext (p.1.cayleyTransform_inverseCayleyTransform p.2)

@[simp]
theorem cayleyEquiv_apply (K : skewAdjoint (E →L[k] E)) :
    ((cayleyEquiv K).1 : E ≃ₗᵢ[k] E) = cayleyTransform K := rfl

@[simp]
theorem cayleyEquiv_symm_apply
    (p : {p : E ≃ₗᵢ[k] E | IsUnit (1 + (p : E →L[k] E))}) :
    cayleyEquiv.symm p = p.1.inverseCayleyTransform p.2 := rfl


end skewAdjoint

namespace skewAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem contDiff_cayleyTransform_toContinuousLinearMap {n : ℕ∞ω} :
    ContDiff ℝ n (fun K : skewAdjoint.submodule ℝ (E →L[ℝ] E) =>
      (cayleyTransform K : E →L[ℝ] E)) := by
  rw [contDiff_iff_contDiffAt]
  intro K
  let L : skewAdjoint.submodule ℝ (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (skewAdjoint.submodule ℝ (E →L[ℝ] E)).subtypeL
  have hL : ContDiff ℝ n L := ContinuousLinearMap.contDiff
    (𝕜 := ℝ) (E := skewAdjoint.submodule ℝ (E →L[ℝ] E)) (F := E →L[ℝ] E) L
  have hplus : ContDiff ℝ n (fun K => 1 + L K) := contDiff_const.add hL
  have hminus : ContDiff ℝ n (fun K => 1 - L K) := contDiff_const.sub hL
  have hinv : ContDiffAt ℝ n Ring.inverse (1 + (K : E →L[ℝ] E)) := by
    simpa only [(isUnit_one_add K).unit_spec] using
      contDiffAt_ringInverse ℝ (n := n) (isUnit_one_add K).unit
  have h := hminus.contDiffAt.mul (hinv.comp K hplus.contDiffAt)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall cayleyTransform_toContinuousLinearMap)

end skewAdjoint

namespace skewAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem hasFDerivAt_cayleyTransform_toContinuousLinearMap_zero :
    HasFDerivAt (fun K : skewAdjoint.submodule ℝ (E →L[ℝ] E) =>
      (cayleyTransform K : E →L[ℝ] E))
      ((-2 : ℝ) • (skewAdjoint.submodule ℝ (E →L[ℝ] E)).subtypeL) 0 := by
  let L : skewAdjoint.submodule ℝ (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (skewAdjoint.submodule ℝ (E →L[ℝ] E)).subtypeL
  have hL : HasFDerivAt L L (0 : skewAdjoint.submodule ℝ (E →L[ℝ] E)) :=
    ContinuousLinearMap.hasFDerivAt L
  have hc : HasFDerivAt (fun _ : skewAdjoint.submodule ℝ (E →L[ℝ] E) =>
      (1 : E →L[ℝ] E)) 0 0 := hasFDerivAt_const (𝕜 := ℝ) _ _
  have hplus : HasFDerivAt (fun K => 1 + L K) L 0 := by
    convert! HasFDerivAt.add (𝕜 := ℝ) (E := skewAdjoint.submodule ℝ (E →L[ℝ] E))
      (F := E →L[ℝ] E) hc hL using 1
    simp
  have hminus : HasFDerivAt (fun K => 1 - L K) (-L) 0 := by
    convert! HasFDerivAt.sub (𝕜 := ℝ) (E := skewAdjoint.submodule ℝ (E →L[ℝ] E))
      (F := E →L[ℝ] E) hc hL using 1
    simp
  have hring : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) 1 1) (1 + L 0) := by
    simpa only [map_zero, add_zero, inv_one, Units.val_one] using
      hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (E →L[ℝ] E)ˣ)
  have hinv := HasFDerivAt.comp (𝕜 := ℝ)
    (E := skewAdjoint.submodule ℝ (E →L[ℝ] E)) (F := E →L[ℝ] E) (G := E →L[ℝ] E)
    (0 : skewAdjoint.submodule ℝ (E →L[ℝ] E)) hring hplus
  have h := HasFDerivAt.clm_comp (𝕜 := ℝ)
    (E := skewAdjoint.submodule ℝ (E →L[ℝ] E)) hminus hinv
  convert! h using 1
  · funext K
    exact cayleyTransform_toContinuousLinearMap K
  · ext K x
    simp [L]
    module

end skewAdjoint
