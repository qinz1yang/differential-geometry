import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCoreOrientation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapOrientation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapInterior

noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

universe u

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)
  {Y : Type*} [TopologicalSpace Y] [ChartedSpace ThreeSpace Y] [IsManifold ThreeModel ∞ Y]
  (oY : TangentOrientationSection Y)
  [hCompact : CompactSpace {x : E.trace.tubes.core // x ∉ E.trace.retainedCore}]
  (fCore : C({x : E.trace.tubes.core // x ∉ E.trace.retainedCore}, Y))
  (fCap : (b : {b : E.trace.tubes.Boundary // E.trace.capDiscarded b}) → C(ThreeBall, Y))
  (hboundary : ∀ (b : {b : E.trace.tubes.Boundary // E.trace.capDiscarded b}) (s : Sphere 2),
    fCap b (sphereToThreeBall s) = fCore
      ⟨E.trace.tubes.coreBoundarySphere b.1 (E.trace.capping.attaching b.1 s),
        E.trace.capDiscarded_coreBoundarySphere_not_mem_retainedCore b.1 b.2 _⟩)

include hCompact in
theorem discardedDesc_preservesTangentOrientationAt_core :
    letI : ChartedSpace (EuclideanHalfSpace 3) {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} :=
      E.coreOpensCharts E.trace.discardedCoreOpen
    ∀ x : {x : E.trace.tubes.core // x ∉ E.trace.retainedCore},
      (𝓡∂ 3).IsInteriorPoint x → ContMDiffAt (𝓡∂ 3) ThreeModel ∞ fCore x →
      (∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
          (fun z : {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} => (z.val : P.Carrier)) x),
       ∃ hk : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel fCore x),
        Orientation.map (Fin 3)
          ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
            (fun z : {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} => (z.val : P.Carrier)) x).toLinearMap hi).symm.trans
            (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel fCore x).toLinearMap hk))
          (P.orientation.orientation x.val.val) = oY.orientation (fCore x)) →
      ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel
          (E.trace.discardedDesc fCore fCap hboundary) (E.trace.discardedCoreInclusion x)),
        PreservesTangentOrientationAt D.orientation oY (E.trace.discardedDesc fCore fCap hboundary)
          (E.trace.discardedCoreInclusion x) hf := by
  let : ChartedSpace (EuclideanHalfSpace 3) E.trace.tubes.core := E.coreCharts
  let : IsManifold (𝓡∂ 3) ∞ E.trace.tubes.core := E.coreSmooth
  let : ChartedSpace (EuclideanHalfSpace 3) {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} :=
    E.coreOpensCharts E.trace.discardedCoreOpen
  intro x hx hCore htarget
  obtain ⟨hi, hj, hsource⟩ := E.discardedCoreInclusion_positive x hx
  obtain ⟨hi', hk, htarget⟩ := htarget
  let f := E.trace.discardedDesc fCore fCap hboundary
  let j := E.trace.discardedCoreInclusion
  have hfAt : ContMDiffAt ThreeModel ThreeModel ∞ f (j x) :=
    E.discardedDesc_contMDiffAt_core_of_isInteriorPoint ThreeModel fCore fCap hboundary
      le_rfl x hx hCore
  have hjAt := E.discardedCoreInclusion_isSmoothEmbedding.contMDiff.contMDiffAt (x := x)
  have hcomp : (f : D.Carrier → Y) ∘ j = fCore :=
    funext (E.trace.discardedDesc_core fCore fCap hboundary)
  have hd : (mfderiv (𝓡∂ 3) ThreeModel ((f : D.Carrier → Y) ∘ j) x :
      ThreeSpace →L[ℝ] ThreeSpace) = mfderiv (𝓡∂ 3) ThreeModel fCore x := by rw [hcomp]
  rw [mfderiv_comp x (hfAt.mdifferentiableAt (by simp)) (hjAt.mdifferentiableAt (by simp))] at hd
  let A : ThreeSpace ≃ₗ[ℝ] ThreeSpace := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) ThreeModel
      (fun z : {x : E.trace.tubes.core // x ∉ E.trace.retainedCore} => (z.val : P.Carrier)) x).toLinearMap hi
  let J : ThreeSpace ≃ₗ[ℝ] ThreeSpace := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) ThreeModel j x).toLinearMap hj
  let K : ThreeSpace ≃ₗ[ℝ] ThreeSpace := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) ThreeModel fCore x).toLinearMap hk
  let L := J.symm.trans K
  have hdL : (mfderiv ThreeModel ThreeModel f (j x) : ThreeSpace →L[ℝ] ThreeSpace) =
      L.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := J.surjective v
    have hv := congrArg (fun B : ThreeSpace →L[ℝ] ThreeSpace => B w) hd
    change mfderiv ThreeModel ThreeModel f (j x) (J w) = K w at hv
    change mfderiv ThreeModel ThreeModel f (j x) (J w) = K (J.symm (J w))
    rw [J.symm_apply_apply]
    exact hv
  have hbij : Function.Bijective (mfderiv ThreeModel ThreeModel f (j x)) := by
    rw [hdL]
    exact L.bijective
  have heq : LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel f (j x)).toLinearMap hbij = L := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun B : ThreeSpace →L[ℝ] ThreeSpace => B v) hdL
  have hlin : (A.symm.trans J).trans L = A.symm.trans K := by
    apply LinearEquiv.ext
    intro v
    exact congrArg K (J.symm_apply_apply (A.symm v))
  have hsource' : Orientation.map (Fin 3) (A.symm.trans J) (P.orientation.orientation x.val.val) =
      D.orientation.orientation (j x) := hsource
  have htarget' : Orientation.map (Fin 3) (A.symm.trans K) (P.orientation.orientation x.val.val) =
      oY.orientation (fCore x) := htarget
  refine ⟨hbij, ?_⟩
  unfold PreservesTangentOrientationAt
  change Orientation.map (Fin 3)
    (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel f (j x)).toLinearMap hbij)
      (D.orientation.orientation (j x)) = oY.orientation (f (j x))
  rw [heq]
  have hor := congrArg (Orientation.map (Fin 3) L) hsource'.symm
  have hm := DifferentialGeometry.VectorBundle.map_orientation_trans_between (A.symm.trans J) L
    (P.orientation.orientation x.val.val)
  have hres := hor.trans (hm.trans ((congrArg (fun B : ThreeSpace ≃ₗ[ℝ] ThreeSpace =>
    Orientation.map (Fin 3) B (P.orientation.orientation x.val.val)) hlin).trans htarget'))
  have hvalue : f (j x) = fCore x := E.trace.discardedDesc_core fCore fCap hboundary x
  erw [hvalue]
  exact hres

include hCompact in
theorem discardedDesc_preservesTangentOrientationAt_cap (b : {b : E.trace.tubes.Boundary // E.trace.capDiscarded b}) :
    letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
    ∀ x : ThreeBall,
      (𝓡∂ 3).IsInteriorPoint x → ContMDiffAt (𝓡∂ 3) ThreeModel ∞ (fCap b) x →
      (∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : ThreeBall → ThreeSpace) x),
       ∃ hk : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel (fCap b) x),
        Orientation.map (Fin 3)
          ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
            (Subtype.val : ThreeBall → ThreeSpace) x).toLinearMap hi).symm.trans
            (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel (fCap b) x).toLinearMap hk))
          ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) = (if b.1.2 then (1 : ℝˣ) else -1) • oY.orientation (fCap b x)) →
      ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel
          (E.trace.discardedDesc fCore fCap hboundary) (E.trace.discardedCap b.1 b.2 x)),
        PreservesTangentOrientationAt D.orientation oY (E.trace.discardedDesc fCore fCap hboundary)
          (E.trace.discardedCap b.1 b.2 x) hf := by
  let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
  intro x hx hCore htarget
  obtain ⟨hi, hj, hsource⟩ := E.discardedCap_positive b.1 b.2 x hx
  obtain ⟨hi', hk, htarget⟩ := htarget
  let f := E.trace.discardedDesc fCore fCap hboundary
  let j := E.trace.discardedCap b.1 b.2
  have hfAt : ContMDiffAt ThreeModel ThreeModel ∞ f (j x) :=
    E.discardedDesc_contMDiffAt_cap_of_isInteriorPoint ThreeModel fCore fCap hboundary
      le_rfl b x hx hCore
  have hjAt := (E.discardedCap_isSmoothEmbedding b.1 b.2).contMDiff.contMDiffAt (x := x)
  have hcomp : (f : D.Carrier → Y) ∘ j = fCap b :=
    funext (E.trace.discardedDesc_cap fCore fCap hboundary b)
  have hd : (mfderiv (𝓡∂ 3) ThreeModel ((f : D.Carrier → Y) ∘ j) x :
      ThreeSpace →L[ℝ] ThreeSpace) = mfderiv (𝓡∂ 3) ThreeModel (fCap b) x := by rw [hcomp]
  rw [mfderiv_comp x (hfAt.mdifferentiableAt (by simp)) (hjAt.mdifferentiableAt (by simp))] at hd
  let A : ThreeSpace ≃ₗ[ℝ] ThreeSpace := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) ThreeModel
      (Subtype.val : ThreeBall → ThreeSpace) x).toLinearMap hi
  let J : ThreeSpace ≃ₗ[ℝ] ThreeSpace := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) ThreeModel j x).toLinearMap hj
  let K : ThreeSpace ≃ₗ[ℝ] ThreeSpace := LinearEquiv.ofBijective
    (mfderiv (𝓡∂ 3) ThreeModel (fCap b) x).toLinearMap hk
  let L := J.symm.trans K
  have hdL : (mfderiv ThreeModel ThreeModel f (j x) : ThreeSpace →L[ℝ] ThreeSpace) =
      L.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := J.surjective v
    have hv := congrArg (fun B : ThreeSpace →L[ℝ] ThreeSpace => B w) hd
    change mfderiv ThreeModel ThreeModel f (j x) (J w) = K w at hv
    change mfderiv ThreeModel ThreeModel f (j x) (J w) = K (J.symm (J w))
    rw [J.symm_apply_apply]
    exact hv
  have hbij : Function.Bijective (mfderiv ThreeModel ThreeModel f (j x)) := by
    rw [hdL]
    exact L.bijective
  have heq : LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel f (j x)).toLinearMap hbij = L := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun B : ThreeSpace →L[ℝ] ThreeSpace => B v) hdL
  have hlin : (A.symm.trans J).trans L = A.symm.trans K := by
    apply LinearEquiv.ext
    intro v
    exact congrArg K (J.symm_apply_apply (A.symm v))
  have hsource' : Orientation.map (Fin 3) (A.symm.trans J) ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
      (if b.1.2 then (1 : ℝˣ) else -1) • D.orientation.orientation (j x) := hsource
  have htarget' : Orientation.map (Fin 3) (A.symm.trans K) ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
      (if b.1.2 then (1 : ℝˣ) else -1) • oY.orientation (fCap b x) := htarget
  refine ⟨hbij, ?_⟩
  unfold PreservesTangentOrientationAt
  change Orientation.map (Fin 3)
    (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel f (j x)).toLinearMap hbij)
      (D.orientation.orientation (j x)) = oY.orientation (f (j x))
  rw [heq]
  have hor := congrArg (Orientation.map (Fin 3) L) hsource'.symm
  have hm := DifferentialGeometry.VectorBundle.map_orientation_trans_between (A.symm.trans J) L
    ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation)
  have hres := hor.trans (hm.trans ((congrArg (fun B : ThreeSpace ≃ₗ[ℝ] ThreeSpace =>
    Orientation.map (Fin 3) B ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation)) hlin).trans htarget'))
  have hvalue : f (j x) = fCap b x := E.trace.discardedDesc_cap fCore fCap hboundary b x
  erw [hvalue]
  cases hside : b.1.2
  · simp only [hside, Bool.false_eq_true, ite_false, Module.Ray.neg_units_smul, one_smul] at hres
    have hn := (Orientation.map_neg L (D.orientation.orientation (j x))).symm.trans hres
    exact neg_injective hn
  · simp only [hside, ite_true, one_smul] at hres
    exact hres

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition
