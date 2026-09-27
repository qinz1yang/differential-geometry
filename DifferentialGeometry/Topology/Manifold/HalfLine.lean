import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.LocalDiffeomorph

noncomputable section
open Set Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

def halfSpaceOneHomeomorph : EuclideanHalfSpace 1 ≃ₜ Ici (0 : ℝ) := by
  let T : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
    PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
  refine
    { toFun := fun t ↦ ⟨t.1 0, t.2⟩
      invFun := fun t ↦ ⟨T.symm t.1, ?_⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · change 0 ≤ t.1
    exact t.2
  · intro t
    apply Subtype.ext
    exact T.symm_apply_apply t.1
  · intro t
    apply Subtype.ext
    exact T.apply_symm_apply t.1
  · exact ((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val).subtype_mk _
  · exact (T.symm.continuous.comp continuous_subtype_val).subtype_mk _

def halfSpaceOneLift (t : ℝ) : EuclideanHalfSpace 1 :=
  (𝓡∂ 1).symm ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t)

theorem halfSpaceOneLift_eq (t : ℝ) :
    halfSpaceOneLift t = halfSpaceOneHomeomorph.symm ⟨max 0 t, le_max_left 0 t⟩ := by
  apply Subtype.ext
  apply (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).injective
  change max t 0 = max 0 t
  exact max_comm _ _

theorem contMDiffOn_halfSpaceOneLift :
    ContMDiffOn 𝓘(ℝ) (𝓡∂ 1) ∞ halfSpaceOneLift (Ici 0) := by
  let T := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
  apply (𝓡∂ 1).contMDiffOn_symm.comp T.symm.contDiff.contMDiff.contMDiffOn
  intro t ht
  rw [range_modelWithCornersEuclideanHalfSpace]
  exact ht

theorem contMDiff_halfSpaceOneCoordinate :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (fun t : EuclideanHalfSpace 1 ↦ t.1 0) :=
  (EuclideanSpace.proj 0).contDiff.contMDiff.comp (𝓡∂ 1).contMDiff

def halfSpaceOneInteriorDiffeomorph : PartialDiffeomorph 𝓘(ℝ) (𝓡∂ 1)
    ℝ (EuclideanHalfSpace 1) ∞ := by
  have htime (t : ℝ) : (halfSpaceOneLift t).1 0 = max t 0 := rfl
  refine
    { toFun := halfSpaceOneLift
      invFun := fun t ↦ t.1 0
      source := Ioi 0
      target := {t : EuclideanHalfSpace 1 | 0 < t.1 0}
      map_source' := ?_
      map_target' := fun _ ht ↦ ht
      left_inv' := ?_
      right_inv' := ?_
      open_source := isOpen_Ioi
      open_target := isOpen_lt continuous_const
        ((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val)
      contMDiffOn_toFun := contMDiffOn_halfSpaceOneLift.mono Ioi_subset_Ici_self
      contMDiffOn_invFun := contMDiff_halfSpaceOneCoordinate.contMDiffOn }
  · intro t ht
    change 0 < (halfSpaceOneLift t).1 0
    rw [htime, max_eq_left ht.le]
    exact ht
  · intro t ht
    change (halfSpaceOneLift t).1 0 = t
    rw [htime, max_eq_left ht.le]
  · intro t _
    rw [halfSpaceOneLift_eq]
    have heq : (⟨max 0 (t.1 0), le_max_left 0 (t.1 0)⟩ : Ici (0 : ℝ)) =
        halfSpaceOneHomeomorph t := Subtype.ext (max_eq_right t.2)
    rw [heq]
    exact halfSpaceOneHomeomorph.symm_apply_apply t

set_option backward.isDefEq.respectTransparency false in
theorem hasMFDerivAt_halfSpaceOneCoordinate (x : EuclideanHalfSpace 1) :
    HasMFDerivAt (𝓡∂ 1) 𝓘(ℝ) (fun t : EuclideanHalfSpace 1 ↦ t.1 0) x
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).toContinuousLinearMap := by
  let T := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
  have hh := T.toContinuousLinearMap.hasFDerivAt.hasMFDerivAt.comp x (𝓡∂ 1).hasMFDerivAt
  convert hh using 1
  · funext t
    rfl
  · exact (ContinuousLinearMap.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
theorem injective_mfderiv_scaledHalfSpaceOneProductCoordinate
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℝ E H) {σ : ℝ} (hσ : σ ≠ 0) (x : B × EuclideanHalfSpace 1) :
    Function.Injective (mfderiv (I.prod (𝓡∂ 1)) (I.prod 𝓘(ℝ))
      (fun z : B × EuclideanHalfSpace 1 ↦ (z.1, σ * z.2.1 0)) x) := by
  let T := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
  have ht : HasMFDerivAt (𝓡∂ 1) 𝓘(ℝ) (fun t : EuclideanHalfSpace 1 ↦ σ * t.1 0) x.2
      (σ • T.toContinuousLinearMap) := (hasMFDerivAt_halfSpaceOneCoordinate x.2).const_smul σ
  change Function.Injective (mfderiv (I.prod (𝓡∂ 1)) (I.prod 𝓘(ℝ))
    (Prod.map id (fun t : EuclideanHalfSpace 1 ↦ σ * t.1 0)) x)
  rw [mfderiv_prodMap mdifferentiableAt_id ht.mdifferentiableAt, mfderiv_id, ht.mfderiv]
  intro v w hvw
  apply Prod.ext
  · exact congrArg (fun p : TangentSpace I x.1 × ℝ ↦ p.1) hvw
  · apply T.injective
    have hs := congrArg (fun p : TangentSpace I x.1 × ℝ ↦ p.2) hvw
    change σ * T v.2 = σ * T w.2 at hs
    exact mul_left_cancel₀ hσ hs

end DifferentialGeometry.Topology.Manifold
