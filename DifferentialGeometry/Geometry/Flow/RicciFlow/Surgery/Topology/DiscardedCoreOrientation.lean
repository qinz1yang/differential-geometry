import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapInterior
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Bundle.Orientation.Map

noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

universe u

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem discardedCoreInclusion_positive :
    letI : ChartedSpace (EuclideanHalfSpace 3) {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} :=
      E.coreOpensCharts E.trace.discardedCoreOpen
    ∀ x : {x : E.trace.tubes.core // x ∉ E.trace.retainedCore}, (𝓡∂ 3).IsInteriorPoint x →
      ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
          (fun z : {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} => (z.val : P.Carrier)) x),
      ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel E.trace.discardedCoreInclusion x),
        Orientation.map (Fin 3)
          ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
            (fun z : {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} => (z.val : P.Carrier)) x).toLinearMap hi).symm.trans
            (LinearEquiv.ofBijective
              (mfderiv (𝓡∂ 3) ThreeModel E.trace.discardedCoreInclusion x).toLinearMap hj))
          (P.orientation.orientation x.val.val) =
            D.orientation.orientation (E.trace.discardedCoreInclusion x) := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.trace.tubes.core := E.coreCharts
  let : IsManifold (𝓡∂ 3) ∞ E.trace.tubes.core := E.coreSmooth
  let : ChartedSpace (EuclideanHalfSpace 3) {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} :=
    E.coreOpensCharts E.trace.discardedCoreOpen
  intro x hx
  let U := E.trace.discardedCoreOpen
  have hxCore : (𝓡∂ 3).IsInteriorPoint x.val :=
    (ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val (I := 𝓡∂ 3) (u := U) (x := x)).mp hx
  obtain ⟨ha, hk, hcore⟩ := E.core_positive x.val hxCore
  obtain ⟨hp, hpres⟩ := E.presentation_positive (E.trace.capping.coreInclusion x.val)
  let a : U → P.Carrier := fun z => z.val.val
  let k : U → N.Carrier := fun z => E.trace.capping.coreInclusion z.val
  have ha' : (mfderiv (𝓡∂ 3) ThreeModel a x : ThreeSpace →L[ℝ] ThreeSpace) =
      mfderiv (𝓡∂ 3) ThreeModel (Subtype.val : E.trace.tubes.core → P.Carrier) x.val := by
    change mfderiv (𝓡∂ 3) ThreeModel
      ((Subtype.val : E.trace.tubes.core → P.Carrier) ∘ (Subtype.val : U → E.trace.tubes.core)) x = _
    rw [mfderiv_comp x (E.core_induced.contMDiff.mdifferentiable (by simp) _)
      ((contMDiff_subtype_val (I := 𝓡∂ 3) (U := U) (n := ∞)).mdifferentiable (by simp) x),
      mfderiv_subtype_val]
    rfl
  have hk' : (mfderiv (𝓡∂ 3) ThreeModel k x : ThreeSpace →L[ℝ] ThreeSpace) =
      mfderiv (𝓡∂ 3) ThreeModel E.trace.capping.coreInclusion x.val := by
    change mfderiv (𝓡∂ 3) ThreeModel
      (E.trace.capping.coreInclusion ∘ (Subtype.val : U → E.trace.tubes.core)) x = _
    rw [mfderiv_comp x (E.core_inclusion_smooth.contMDiff.mdifferentiable (by simp) _)
      ((contMDiff_subtype_val (I := 𝓡∂ 3) (U := U) (n := ∞)).mdifferentiable (by simp) x),
      mfderiv_subtype_val]
    rfl
  have hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel a x) := ha' ▸ ha
  have hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel E.trace.discardedCoreInclusion x) :=
    DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt
      (𝓡∂ 3) ThreeModel E.trace.discardedCoreInclusion x
      (E.discardedCoreInclusion_isSmoothEmbedding.isImmersion.isImmersionAt x) (by simp [ThreeSpace])
  have hksmooth : ContMDiff (𝓡∂ 3) ThreeModel ∞ k :=
    E.core_inclusion_smooth.contMDiff.comp contMDiff_subtype_val
  have hcomp : (Sum.inr : D.Carrier → Q.Carrier ⊕ D.Carrier) ∘ E.trace.discardedCoreInclusion =
      E.presentation ∘ k := by
    funext z
    rw [Function.comp_apply, Function.comp_apply, E.trace.inr_discardedCoreInclusion, E.presentation_eq]
  have hd : (mfderiv (𝓡∂ 3) ThreeModel
      ((Sum.inr : D.Carrier → Q.Carrier ⊕ D.Carrier) ∘ E.trace.discardedCoreInclusion) x :
      ThreeSpace →L[ℝ] ThreeSpace) =
      mfderiv (𝓡∂ 3) ThreeModel (E.presentation ∘ k) x := by rw [hcomp]
  rw [mfderiv_comp x ((ContMDiff.inr (n := ∞)).mdifferentiable (by simp) _)
    (E.discardedCoreInclusion_isSmoothEmbedding.contMDiff.mdifferentiable (by simp) x), mfderiv_sumInr,
    mfderiv_comp x (E.presentation.contMDiff.mdifferentiable (by simp) _) (hksmooth.mdifferentiable (by simp) x),
    hk'] at hd
  let A : ThreeSpace ≃ₗ[ℝ] ThreeSpace := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) ThreeModel (Subtype.val : E.trace.tubes.core → P.Carrier) x.val).toLinearMap ha
  let B : ThreeSpace ≃ₗ[ℝ] ThreeSpace := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) ThreeModel E.trace.capping.coreInclusion x.val).toLinearMap hk
  let C : ThreeSpace ≃ₗ[ℝ] ThreeSpace := LinearEquiv.ofBijective
    (mfderiv ThreeModel ThreeModel E.presentation (E.trace.capping.coreInclusion x.val)).toLinearMap hp
  let J : ThreeSpace ≃ₗ[ℝ] ThreeSpace := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) ThreeModel E.trace.discardedCoreInclusion x).toLinearMap hj
  have hA : LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel a x).toLinearMap hi = A := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun L : ThreeSpace →L[ℝ] ThreeSpace => L v) ha'
  have hJ : J = B.trans C := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun L : ThreeSpace →L[ℝ] ThreeSpace => L v) hd
  have hcore' : Orientation.map (Fin 3) (A.symm.trans B) (P.orientation.orientation x.val.val) =
      N.orientation.orientation (E.trace.capping.coreInclusion x.val) := hcore
  have hpres' : Orientation.map (Fin 3) C (N.orientation.orientation (E.trace.capping.coreInclusion x.val)) =
      D.orientation.orientation (E.trace.discardedCoreInclusion x) := by
    have heq : E.presentation (E.trace.capping.coreInclusion x.val) = Sum.inr (E.trace.discardedCoreInclusion x) := by
      rw [E.presentation_eq]
      exact (E.trace.inr_discardedCoreInclusion x).symm
    change Orientation.map (Fin 3) C (N.orientation.orientation (E.trace.capping.coreInclusion x.val)) =
      (match E.presentation (E.trace.capping.coreInclusion x.val) with
       | Sum.inl q => Q.orientation.orientation q
       | Sum.inr d => D.orientation.orientation d) at hpres
    rw [heq] at hpres
    exact hpres
  refine ⟨hi, hj, ?_⟩
  change Orientation.map (Fin 3)
    ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel a x).toLinearMap hi).symm.trans J) _ = _
  rw [hA, hJ]
  change Orientation.map (Fin 3) ((A.symm.trans B).trans C) _ = _
  exact (DifferentialGeometry.VectorBundle.map_orientation_trans_between (A.symm.trans B) C
    (P.orientation.orientation x.val.val)).symm.trans
    ((congrArg (Orientation.map (Fin 3) C) hcore').trans hpres')

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition
