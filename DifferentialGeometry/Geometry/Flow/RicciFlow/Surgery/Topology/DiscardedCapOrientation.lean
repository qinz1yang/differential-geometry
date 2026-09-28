import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapMaps
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Bundle.Orientation.Map

noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

universe u

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem discardedCap_positive (b : E.trace.tubes.Boundary) (hb : E.trace.capDiscarded b) :
    letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
    ∀ x : ThreeBall, (𝓡∂ 3).IsInteriorPoint x →
      ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : ThreeBall → ThreeSpace) x),
      ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel (E.trace.discardedCap b hb) x),
        Orientation.map (Fin 3)
          ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
            (Subtype.val : ThreeBall → ThreeSpace) x).toLinearMap hi).symm.trans
            (LinearEquiv.ofBijective
              (mfderiv (𝓡∂ 3) ThreeModel (E.trace.discardedCap b hb) x).toLinearMap hj))
          ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
            (if b.2 then (1 : ℝˣ) else -1) • D.orientation.orientation (E.trace.discardedCap b hb x) := by
  let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
  intro x hx
  obtain ⟨hi, hk, hcap⟩ := E.cap_positive b x hx
  obtain ⟨hp, hpres⟩ := E.presentation_positive (E.trace.capping.cap b x)
  have hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel (E.trace.discardedCap b hb) x) :=
    DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt
      (𝓡∂ 3) ThreeModel (E.trace.discardedCap b hb) x
      ((E.discardedCap_isSmoothEmbedding b hb).isImmersion.isImmersionAt x)
      (by simp [ThreeSpace])
  have hcomp : (Sum.inr : D.Carrier → Q.Carrier ⊕ D.Carrier) ∘ E.trace.discardedCap b hb =
      E.presentation ∘ E.trace.capping.cap b := by
    funext y
    rw [Function.comp_apply, Function.comp_apply, E.trace.inr_discardedCap, E.presentation_eq]
  have hd : (mfderiv (𝓡∂ 3) ThreeModel
      ((Sum.inr : D.Carrier → Q.Carrier ⊕ D.Carrier) ∘ E.trace.discardedCap b hb) x :
      ThreeSpace →L[ℝ] ThreeSpace) =
      mfderiv (𝓡∂ 3) ThreeModel (E.presentation ∘ E.trace.capping.cap b) x := by rw [hcomp]
  rw [mfderiv_comp x ((ContMDiff.inr (n := ∞)).mdifferentiable (by simp) _)
    ((E.discardedCap_contMDiff b hb).mdifferentiable (by simp) x), mfderiv_sumInr,
    mfderiv_comp x (E.presentation.contMDiff.mdifferentiable (by simp) _)
      ((E.cap_smooth b).contMDiff.mdifferentiable (by simp) x)] at hd
  let A : ThreeSpace ≃ₗ[ℝ] ThreeSpace := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) ThreeModel (Subtype.val : ThreeBall → ThreeSpace) x).toLinearMap hi
  let B : ThreeSpace ≃ₗ[ℝ] ThreeSpace := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) ThreeModel (E.trace.capping.cap b) x).toLinearMap hk
  let C : ThreeSpace ≃ₗ[ℝ] ThreeSpace := LinearEquiv.ofBijective
    (mfderiv ThreeModel ThreeModel E.presentation (E.trace.capping.cap b x)).toLinearMap hp
  let J : ThreeSpace ≃ₗ[ℝ] ThreeSpace := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) ThreeModel (E.trace.discardedCap b hb) x).toLinearMap hj
  have hJ : J = B.trans C := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun L : ThreeSpace →L[ℝ] ThreeSpace => L v) hd
  have hcap' : Orientation.map (Fin 3) (A.symm.trans B)
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
      (if b.2 then (1 : ℝˣ) else -1) • N.orientation.orientation (E.trace.capping.cap b x) := hcap
  have hpres' : Orientation.map (Fin 3) C
      (N.orientation.orientation (E.trace.capping.cap b x)) =
      D.orientation.orientation (E.trace.discardedCap b hb x) := by
    have heq : E.presentation (E.trace.capping.cap b x) = Sum.inr (E.trace.discardedCap b hb x) := by
      rw [E.presentation_eq]
      exact (E.trace.inr_discardedCap b hb x).symm
    change Orientation.map (Fin 3) C
      (N.orientation.orientation (E.trace.capping.cap b x)) =
      (match E.presentation (E.trace.capping.cap b x) with
       | Sum.inl q => Q.orientation.orientation q
       | Sum.inr d => D.orientation.orientation d) at hpres
    rw [heq] at hpres
    exact hpres
  refine ⟨hi, hj, ?_⟩
  change Orientation.map (Fin 3) (A.symm.trans J) _ = _
  rw [hJ]
  change Orientation.map (Fin 3) ((A.symm.trans B).trans C) _ = _
  rw [← DifferentialGeometry.VectorBundle.map_orientation_trans_between, hcap']
  cases hside : b.2
  · simp only [Bool.false_eq_true, ite_false, Module.Ray.neg_units_smul, one_smul]
    exact (Orientation.map_neg C (N.orientation.orientation (E.trace.capping.cap b x))).trans
      (congrArg Neg.neg hpres')
  · simpa only [hside, ite_true, one_smul] using hpres'

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition
