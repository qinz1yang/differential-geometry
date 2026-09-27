import DifferentialGeometry.Tensor.Multilinear.Bundle.Dual

noncomputable section

namespace ContinuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

def mixedMultilinearEquiv (r s : ℕ) :
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜) ≃L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F)
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) := by
  let _ : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
    DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_finiteDimensional r
  let _ : FiniteDimensional 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
    DifferentialGeometry.Tensor.Multilinear.continuousMultilinearMap_finiteDimensional r
  exact (ContinuousLinearMap.flipMultilinearEquiv 𝕜 (fun _ : Fin s => F)
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) 𝕜).trans
      (ContinuousLinearEquiv.continuousMultilinearMapCongrRight (fun _ : Fin s => F)
        (dualMultilinearEquivMultilinearOfDual 𝕜 F r).toContinuousLinearEquiv)

theorem mixedMultilinearEquiv_apply (r s : ℕ)
    (A : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜 →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F) 𝕜)
    (v : Fin s → F) (α : Fin r → F →L[𝕜] 𝕜) :
    mixedMultilinearEquiv (𝕜 := 𝕜) (F := F) r s A v α =
      A (tensorOfDualLinearForms 𝕜 F r α) v := rfl

theorem mixedMultilinearEquiv_symm_apply_tensorOfDualLinearForms (r s : ℕ)
    (A : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => F)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜))
    (v : Fin s → F) (α : Fin r → F →L[𝕜] 𝕜) :
    (mixedMultilinearEquiv (𝕜 := 𝕜) (F := F) r s).symm A
      (tensorOfDualLinearForms 𝕜 F r α) v = A v α := by
  rw [← mixedMultilinearEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]

end ContinuousMultilinearMap

namespace Bundle.continuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : B → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace 𝕜 (V x)]
  [TopologicalSpace (Bundle.TotalSpace F V)] [FiberBundle F V] [VectorBundle 𝕜 F V]

def mixedMultilinearFiberEquiv (r s : ℕ) (x : B) :
    (Bundle.continuousMultilinearMap 𝕜 r F V x →L[𝕜]
      Bundle.continuousMultilinearMap 𝕜 s F V x) ≃L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : Fin s => V x)
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => V x →L[𝕜] 𝕜) 𝕜) := by
  let _ : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  exact ((fiberContinuousLinearEquiv (F := F) (E := V) r x).arrowCongr
    (fiberContinuousLinearEquiv (F := F) (E := V) s x)).trans
      (ContinuousMultilinearMap.mixedMultilinearEquiv r s)

theorem mixedMultilinearFiberEquiv_apply (r s : ℕ) (x : B)
    (A : Bundle.continuousMultilinearMap 𝕜 r F V x →L[𝕜]
      Bundle.continuousMultilinearMap 𝕜 s F V x)
    (v : Fin s → V x) (α : Fin r → V x →L[𝕜] 𝕜) :
    mixedMultilinearFiberEquiv (𝕜 := 𝕜) (F := F) (V := V) r s x A v α =
      A (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 (V x) r α) v := rfl

theorem mixedMultilinearFiberEquiv_symm_apply_tensorOfDualLinearForms (r s : ℕ) (x : B)
    (A : ContinuousMultilinearMap 𝕜 (fun _ : Fin s => V x)
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => V x →L[𝕜] 𝕜) 𝕜))
    (v : Fin s → V x) (α : Fin r → V x →L[𝕜] 𝕜) :
    (mixedMultilinearFiberEquiv (𝕜 := 𝕜) (F := F) (V := V) r s x).symm A
        (ContinuousMultilinearMap.tensorOfDualLinearForms 𝕜 (V x) r α) v = A v α := by
  rw [← mixedMultilinearFiberEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]

end Bundle.continuousMultilinearMap
