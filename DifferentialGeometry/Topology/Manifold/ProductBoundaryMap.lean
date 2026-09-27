import DifferentialGeometry.Topology.Manifold.NativeRetainedBoundary

set_option autoImplicit false
noncomputable section
open Set Function Module Manifold
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev E1 := EuclideanSpace ℝ (Fin 1)
private abbrev ER := E2 × E1
private abbrev IH := ModelProd E2 (EuclideanHalfSpace 1)
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private local instance : HasSmoothBoundary ER IH IR := productHalfSpaceBoundaryModel
private local instance : Nonempty (HasSmoothBoundary.boundaryH IR) := show Nonempty E2 from inferInstance
private local instance {M : Type*} [TopologicalSpace M] [ChartedSpace IH M]
    [IsManifold IR ∞ M] : ChartedSpace E2 (BoundaryManifold IR M) := BoundaryManifold.chartedSpace (I := IR)
private local instance {M : Type*} [TopologicalSpace M] [ChartedSpace IH M]
    [IsManifold IR ∞ M] : IsManifold (𝓡 2) ∞ (BoundaryManifold IR M) := BoundaryManifold.isManifold (I := IR)
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace IH M] [IsManifold IR ∞ M]
variable [TopologicalSpace N] [ChartedSpace IH N] [IsManifold IR ∞ N]

def productBoundaryMap (f : M → N) (hf : IsLocalDiffeomorph IR IR ∞ f) :
    BoundaryManifold IR M → BoundaryManifold IR N :=
  fun b => ⟨f b.val, ((hf b.val).isBoundaryPoint_iff (by simp)).mp b.property⟩

omit [IsManifold IR ∞ M] [IsManifold IR ∞ N] in
theorem productBoundaryMap_apply (f : M → N) (hf : IsLocalDiffeomorph IR IR ∞ f) (b : BoundaryManifold IR M) :
    (productBoundaryMap f hf b).val = f b.val := rfl

theorem productBoundaryMap_contMDiff (f : M → N) (hf : IsLocalDiffeomorph IR IR ∞ f) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (productBoundaryMap f hf) :=
  contMDiff_intoIntrinsicBoundary (productBoundaryMap f hf)
    (hf.contMDiff.comp (boundaryInclusion_contMDiff (I := IR) (M := M)))

private def sourceInclusionDerivative (b : BoundaryManifold IR M) : E2 →L[ℝ] ER :=
  mfderiv (𝓡 2) IR (boundaryInclusion IR M) b
private def targetInclusionDerivative (b : BoundaryManifold IR N) : E2 →L[ℝ] ER :=
  mfderiv (𝓡 2) IR (boundaryInclusion IR N) b
private def ambientDerivative (f : M → N) (b : BoundaryManifold IR M) : ER →L[ℝ] ER :=
  mfderiv IR IR f b.val
private def restrictedDerivative (f : M → N) (hf : IsLocalDiffeomorph IR IR ∞ f)
    (b : BoundaryManifold IR M) : E2 →L[ℝ] E2 :=
  mfderiv (𝓡 2) (𝓡 2) (productBoundaryMap f hf) b

theorem productBoundaryMap_mfderiv_chain (f : M → N) (hf : IsLocalDiffeomorph IR IR ∞ f)
    (b : BoundaryManifold IR M) :
    let DN : E2 →L[ℝ] ER := mfderiv (𝓡 2) IR (boundaryInclusion IR N) (productBoundaryMap f hf b)
    let DB : E2 →L[ℝ] E2 := mfderiv (𝓡 2) (𝓡 2) (productBoundaryMap f hf) b
    let DF : ER →L[ℝ] ER := mfderiv IR IR f b.val
    let DM : E2 →L[ℝ] ER := mfderiv (𝓡 2) IR (boundaryInclusion IR M) b
    DN.comp DB = DF.comp DM := by
  have hN := mfderiv_comp b ((boundaryInclusion_contMDiff (I := IR) (M := N)).mdifferentiableAt (by simp))
    ((productBoundaryMap_contMDiff f hf).mdifferentiableAt (by simp))
  have hM := mfderiv_comp b (hf.contMDiff.mdifferentiableAt (by simp))
    ((boundaryInclusion_contMDiff (I := IR) (M := M)).mdifferentiableAt (by simp))
  exact hN.symm.trans hM

theorem productBoundaryMap_mfderiv_bijective (f : M → N) (hf : IsLocalDiffeomorph IR IR ∞ f)
    (b : BoundaryManifold IR M) :
    Bijective (mfderiv (𝓡 2) (𝓡 2) (productBoundaryMap f hf) b) := by
  have hchain : (targetInclusionDerivative (productBoundaryMap f hf b)).comp (restrictedDerivative f hf b) =
      (ambientDerivative f b).comp (sourceInclusionDerivative b) := productBoundaryMap_mfderiv_chain f hf b
  have hsrc : Injective (sourceInclusionDerivative b) := dincl_injective (I := IR) b
  have hamb : Injective (ambientDerivative f b) := ((hf b.val).mfderivToContinuousLinearEquiv (by simp)).injective
  have hbij : Injective (restrictedDerivative f hf b) := by
    intro v w hvw
    apply hsrc
    apply hamb
    have hv := congrArg (fun D : E2 →L[ℝ] ER => D v) hchain
    have hw := congrArg (fun D : E2 →L[ℝ] ER => D w) hchain
    exact hv.symm.trans ((congrArg (targetInclusionDerivative (productBoundaryMap f hf b)) hvw).trans hw)
  exact (restrictedDerivative f hf b).toLinearMap.linearEquivOfInjective hbij rfl |>.bijective
end DifferentialGeometry.Topology.Manifold
