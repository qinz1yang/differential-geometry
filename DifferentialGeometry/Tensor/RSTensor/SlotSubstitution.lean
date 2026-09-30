import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Bundle.TangentSpace
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff BigOperators
namespace DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

def tangentSlotCLM (n : ℕ) {b : M}
    (k : Fin n) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    (i : Fin n) : TangentSpace I b →L[ℝ] TangentSpace I b :=
  if i = k then Φ else ContinuousLinearMap.id ℝ (TangentSpace I b)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
lemma tangentSlotCLM_self (n : ℕ) {b : M}
    (k : Fin n) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b) :
    tangentSlotCLM (I := I) n k Φ k = Φ := by
  unfold tangentSlotCLM
  simp

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
lemma tangentSlotCLM_other (n : ℕ) {b : M}
    (k : Fin n) (Φ : TangentSpace I b →L[ℝ] TangentSpace I b)
    {i : Fin n} (h : i ≠ k) :
    tangentSlotCLM (I := I) n k Φ i = ContinuousLinearMap.id ℝ (TangentSpace I b) := by
  unfold tangentSlotCLM
  simp [h]

noncomputable def tangentCompCLM (n : ℕ) (b : M)
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ :=
  ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (E := fun _ : Fin n => E) (F := ℝ)
    (show Fin n → (E →L[ℝ] E) from Φ)

noncomputable def tensorSlotSubstCLM (n : ℕ) (b : M)
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b)) :
    Tensor0SSpace n I b →L[ℝ] Tensor0SSpace n I b :=
  ((tensor0SSpaceContinuousLinearEquiv (I := I) (M := M) n b).symm
      : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ →L[ℝ]
          Tensor0SSpace n I b).comp
    ((tangentCompCLM (I := I) (M := M) n b Φ).comp
      ((tensor0SSpaceContinuousLinearEquiv (I := I) (M := M) n b)
          : Tensor0SSpace n I b →L[ℝ]
            ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
lemma tensorSlotSubstCLM_apply (n : ℕ) (b : M)
    (Φ : Fin n → (TangentSpace I b →L[ℝ] TangentSpace I b))
    (τ : Tensor0SSpace n I b) (m : Fin n → TangentSpace I b) :
    Tensor0SSpace.eval (tensorSlotSubstCLM (I := I) n b Φ τ) m =
      Tensor0SSpace.eval τ (fun i => Φ i (m i)) := by
  classical
  unfold tensorSlotSubstCLM tangentCompCLM
  rfl

end DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]


def slotInsertEndomorphism (s : ℕ) (k : Fin s) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    Tensor0SSpace s I x →L[ℝ] Tensor0SSpace s I x :=
  tensorSlotSubstCLM (I := I) (M := M) s x
    (tangentSlotCLM (I := I) s k Λ)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma slotInsertEndomorphism_apply_natural (s : ℕ) (k : Fin s) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (A : Tensor0SSpace s I x)
    (m : Fin s → TangentSpace I x) :
    Tensor0SSpace.eval (slotInsertEndomorphism (I := I) (M := M) s k x Λ A) m =
      Tensor0SSpace.eval A (Function.update m k (Λ (m k))) := by
  unfold slotInsertEndomorphism
  rw [tensorSlotSubstCLM_apply]
  congr 1
  funext i
  by_cases h : i = k
  · subst i
    rw [tangentSlotCLM_self, Function.update_self]
  · rw [tangentSlotCLM_other (I := I) s k Λ h,
      ContinuousLinearMap.id_apply, Function.update_of_ne h]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
@[simp] lemma slotInsertEndomorphism_apply (s : ℕ) (k : Fin s) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (A : Tensor0SSpace s I x) :
    slotInsertEndomorphism (I := I) (M := M) s k x Λ A =
      Tensor0SSpace.ofModel
        ((Tensor0SSpace.toModel A).compContinuousLinearMap
          (fun i : Fin s => if i = k then tangentLinearMapToModel Λ
            else ContinuousLinearMap.id ℝ E)) := by
  apply tensor0SSpace_ext (𝕜 := ℝ) s x
  intro v
  change Tensor0SSpace.eval (slotInsertEndomorphism (I := I) (M := M) s k x Λ A) v =
    Tensor0SSpace.eval
      (Tensor0SSpace.ofModel
        ((Tensor0SSpace.toModel A).compContinuousLinearMap
          (fun i : Fin s => if i = k then tangentLinearMapToModel Λ
            else ContinuousLinearMap.id ℝ E))) v
  rw [slotInsertEndomorphism_apply_natural, Tensor0SSpace.eval_ofModel,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Tensor0SSpace.toModel_apply_model_vector, Tensor0SSpace.eval_eq]
  congr 1
  funext i
  by_cases h : i = k
  · subst i
    simp only [ite_eq_left, Function.update_self, tangentLinearMapToModel_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  · rw [ite_eq_right h, ContinuousLinearMap.id_apply, Function.update_of_ne h,
      ContinuousLinearEquiv.symm_apply_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma slotInsertEndomorphism_apply_eval (s : ℕ) (k : Fin s) (x : M)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) (A : Tensor0SSpace s I x)
    (m : Fin s → E) :
    Tensor0SSpace.toModel (slotInsertEndomorphism (I := I) (M := M) s k x Λ A) m =
      Tensor0SSpace.toModel A
        (Function.update m k (tangentLinearMapToModel Λ (m k))) := by
  rw [slotInsertEndomorphism_apply, Tensor0SSpace.toModel_ofModel]
  have hfam : (fun i : Fin s =>
      (if i = k then tangentLinearMapToModel Λ else ContinuousLinearMap.id ℝ E) (m i)) =
      Function.update m k (tangentLinearMapToModel Λ (m k)) := by
    funext i
    by_cases h : i = k
    · subst h
      simp
    · rw [ite_eq_right h, Function.update_of_ne h]
      rfl
  exact congrArg (fun t => Tensor0SSpace.toModel A t) hfam

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma slotInsertEndomorphism_add_left (s : ℕ) (k : Fin s) (x : M)
    (Λ₁ Λ₂ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    slotInsertEndomorphism (I := I) (M := M) s k x (Λ₁ + Λ₂) =
      slotInsertEndomorphism (I := I) (M := M) s k x Λ₁ +
        slotInsertEndomorphism (I := I) (M := M) s k x Λ₂ := by
  apply ContinuousLinearMap.ext
  intro A
  rw [add_apply]
  apply tensor0SSpace_ext (𝕜 := ℝ) s x
  intro v
  change Tensor0SSpace.eval (slotInsertEndomorphism (I := I) (M := M) s k x (Λ₁ + Λ₂) A) v =
    Tensor0SSpace.eval
      (slotInsertEndomorphism (I := I) (M := M) s k x Λ₁ A +
        slotInsertEndomorphism (I := I) (M := M) s k x Λ₂ A) v
  rw [slotInsertEndomorphism_apply_natural, Tensor0SSpace.eval_add,
    slotInsertEndomorphism_apply_natural, slotInsertEndomorphism_apply_natural, add_apply]
  exact ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x) A).map_update_add
    v k (Λ₁ (v k)) (Λ₂ (v k))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma slotInsertEndomorphism_smul_left (s : ℕ) (k : Fin s) (x : M) (c : ℝ)
    (Λ : TangentSpace I x →L[ℝ] TangentSpace I x) :
    slotInsertEndomorphism (I := I) (M := M) s k x (c • Λ) =
      c • slotInsertEndomorphism (I := I) (M := M) s k x Λ := by
  apply ContinuousLinearMap.ext
  intro A
  rw [smul_apply]
  apply tensor0SSpace_ext (𝕜 := ℝ) s x
  intro v
  change Tensor0SSpace.eval (slotInsertEndomorphism (I := I) (M := M) s k x (c • Λ) A) v =
    Tensor0SSpace.eval (c • slotInsertEndomorphism (I := I) (M := M) s k x Λ A) v
  rw [slotInsertEndomorphism_apply_natural, Tensor0SSpace.eval_smul,
    slotInsertEndomorphism_apply_natural, smul_apply]
  exact ((tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x) A).map_update_smul
    v k c (Λ (v k))

end DifferentialGeometry.Tensor0SBundle

end
