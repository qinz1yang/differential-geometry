

import DifferentialGeometry.Tensor.Mixed.Field
import DifferentialGeometry.Tensor.Mixed.DualFiber
import DifferentialGeometry.Tensor.Mixed.Naturality
import DifferentialGeometry.Tensor.Product.Section
import DifferentialGeometry.Tensor.Product.HomEquiv

namespace DifferentialGeometry.Tensor.Mixed


noncomputable section

open DifferentialGeometry.Tensor.Multilinear
open _root_.Bundle Set ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators TensorProduct

section DualMultilinearTransition

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

set_option backward.isDefEq.respectTransparency false

local instance (r : ℕ) : FiniteDimensional 𝕜 (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F) 𝕜) :=
  continuousMultilinearMap_finiteDimensional r
local instance (r : ℕ) : FiniteDimensional 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
  continuousMultilinearMap_finiteDimensional r

local instance (r : ℕ) : NormedAddCommGroup
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
  inferInstance
local instance (r : ℕ) : NormedSpace 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :=
  inferInstance

omit [CompleteSpace 𝕜] in
theorem dualMultilinearSymmTransition {r : ℕ} (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (Φ : F ≃L[𝕜] F)
    (hΦ : Φ =
      ((trivializationAt F E x).continuousLinearEquivAt 𝕜 x
        (mem_baseSet_trivializationAt F E x)).symm.trans
        ((trivializationAt F E x₀).continuousLinearEquivAt 𝕜 x hx))
    (M : ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜) :
    (_root_.Bundle.continuousMultilinearMap.continuousLinearEquivAt
        (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := _root_.Bundle.dual 𝕜 E) r x).symm M =
      (trivializationAt
        (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
        (fun x => _root_.Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜)
          (_root_.Bundle.dual 𝕜 E) x) x₀).symmL 𝕜 x
        ((ContinuousMultilinearMap.compContinuousLinearMapL
          (𝕜 := 𝕜) (E := fun _ : Fin r => F →L[𝕜] 𝕜)
          (E₁ := fun _ : Fin r => F →L[𝕜] 𝕜) (F := 𝕜)
          (fun _ => (ContinuousLinearMap.compL 𝕜 F F 𝕜).flip
            Φ.toContinuousLinearMap)) M) := by
  apply ContinuousMultilinearMap.ext
  intro v
  have hx_dual :
      x ∈ (trivializationAt (F →L[𝕜] 𝕜) (_root_.Bundle.dual 𝕜 E) x₀).baseSet := by
    change x ∈ (trivializationAt F E x₀).baseSet ∩ Set.univ
    exact ⟨hx, trivial⟩
  rw [_root_.Bundle.continuousMultilinearMap.triv_symmL_eq_compContinuousLinearMap
    (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := _root_.Bundle.dual 𝕜 E) x₀ x hx_dual]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change M (fun i =>
      (trivializationAt (F →L[𝕜] 𝕜) (_root_.Bundle.dual 𝕜 E) x).continuousLinearMapAt
        𝕜 x (v i)) =
    ((ContinuousMultilinearMap.compContinuousLinearMapL
      (𝕜 := 𝕜) (E := fun _ : Fin r => F →L[𝕜] 𝕜)
      (E₁ := fun _ : Fin r => F →L[𝕜] 𝕜) (F := 𝕜)
      (fun _ => (ContinuousLinearMap.compL 𝕜 F F 𝕜).flip
        Φ.toContinuousLinearMap)) M)
      (fun i =>
        (trivializationAt (F →L[𝕜] 𝕜) (_root_.Bundle.dual 𝕜 E) x₀).continuousLinearMapAt
          𝕜 x (v i))
  rw [ContinuousMultilinearMap.compContinuousLinearMapL_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  apply ContinuousLinearMap.ext
  intro a
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
  have hxx : x ∈ (trivializationAt F E x).baseSet :=
    mem_baseSet_trivializationAt F E x
  have hxx_dual :
      x ∈ (trivializationAt (F →L[𝕜] 𝕜) (_root_.Bundle.dual 𝕜 E) x).baseSet :=
    mem_baseSet_trivializationAt (F →L[𝕜] 𝕜) (_root_.Bundle.dual 𝕜 E) x
  have hLHS :
      (trivializationAt (F →L[𝕜] 𝕜) (_root_.Bundle.dual 𝕜 E) x).continuousLinearMapAt
          𝕜 x (v i) a =
        (v i) (((trivializationAt F E x).continuousLinearEquivAt 𝕜 x hxx).symm a) := by
    have hdual := _root_.Bundle.continuousMultilinearMap.dualBundle_triv_symmL_eq_comp
      (𝕜 := 𝕜) (F := F) (E := E) x x hxx
      ((trivializationAt (F →L[𝕜] 𝕜) (_root_.Bundle.dual 𝕜 E) x).continuousLinearMapAt
        𝕜 x (v i))
      (((trivializationAt F E x).continuousLinearEquivAt 𝕜 x hxx).symm a)
    rw [Trivialization.symmL_continuousLinearMapAt _ hxx_dual] at hdual
    have h_symm_eq :
        ((trivializationAt F E x).continuousLinearEquivAt 𝕜 x hxx).symm a =
          (trivializationAt F E x).symmL 𝕜 x a := rfl
    rw [h_symm_eq, Trivialization.continuousLinearMapAt_symmL _ hxx] at hdual
    exact hdual.symm
  have hx_dual_x₀ :
      x ∈ (trivializationAt (F →L[𝕜] 𝕜) (_root_.Bundle.dual 𝕜 E) x₀).baseSet :=
    hx_dual
  have hRHS :
      (trivializationAt (F →L[𝕜] 𝕜) (_root_.Bundle.dual 𝕜 E) x₀).continuousLinearMapAt
          𝕜 x (v i) (Φ a) =
        (v i) (((trivializationAt F E x₀).continuousLinearEquivAt 𝕜 x hx).symm
          (Φ a)) := by
    have hdual := _root_.Bundle.continuousMultilinearMap.dualBundle_triv_symmL_eq_comp
      (𝕜 := 𝕜) (F := F) (E := E) x₀ x hx
      ((trivializationAt (F →L[𝕜] 𝕜) (_root_.Bundle.dual 𝕜 E) x₀).continuousLinearMapAt
        𝕜 x (v i))
      (((trivializationAt F E x₀).continuousLinearEquivAt 𝕜 x hx).symm (Φ a))
    rw [Trivialization.symmL_continuousLinearMapAt _ hx_dual_x₀] at hdual
    have h_symm_eq :
        ((trivializationAt F E x₀).continuousLinearEquivAt 𝕜 x hx).symm (Φ a) =
          (trivializationAt F E x₀).symmL 𝕜 x (Φ a) := rfl
    rw [h_symm_eq, Trivialization.continuousLinearMapAt_symmL _ hx] at hdual
    exact hdual.symm
  rw [hLHS]
  change _ =
    ((trivializationAt (F →L[𝕜] 𝕜) (_root_.Bundle.dual 𝕜 E) x₀).continuousLinearMapAt
      𝕜 x (v i)) (Φ a)
  rw [hRHS]
  congr 1
  rw [hΦ]
  simp only [ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply]

omit [CompleteSpace 𝕜] in
theorem dualMultilinearTrivTransition {r : ℕ} (x₀ x : B)
    (hx : x ∈ (trivializationAt F E x₀).baseSet)
    (Φ : F ≃L[𝕜] F)
    (hΦ : Φ =
      ((trivializationAt F E x).continuousLinearEquivAt 𝕜 x
        (mem_baseSet_trivializationAt F E x)).symm.trans
        ((trivializationAt F E x₀).continuousLinearEquivAt 𝕜 x hx)) :
    (((trivializationAt
            (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
            (fun x => _root_.Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜)
              (_root_.Bundle.dual 𝕜 E) x)
            x₀).continuousLinearMapAt 𝕜 x).toLinearMap ∘ₗ
        (_root_.Bundle.continuousMultilinearMap.continuousLinearEquivAt
          (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜)
            (E := _root_.Bundle.dual 𝕜 E) r x).symm.toLinearEquiv.toLinearMap) =
      (ContinuousMultilinearMap.compContinuousLinearMapL
        (𝕜 := 𝕜) (E := fun _ : Fin r => F →L[𝕜] 𝕜)
        (E₁ := fun _ : Fin r => F →L[𝕜] 𝕜) (F := 𝕜)
        (fun _ => (ContinuousLinearMap.compL 𝕜 F F 𝕜).flip
          Φ.toContinuousLinearMap)).toLinearMap := by
  apply LinearMap.ext
  intro M
  simp only [LinearMap.coe_comp, Function.comp_apply]
  have hx_dmr : x ∈ (trivializationAt
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
      (fun x => _root_.Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜)
        (_root_.Bundle.dual 𝕜 E) x) x₀).baseSet := by
    have : x ∈ (trivializationAt (F →L[𝕜] 𝕜) (_root_.Bundle.dual 𝕜 E) x₀).baseSet := by
      change x ∈ (trivializationAt F E x₀).baseSet ∩ Set.univ
      exact ⟨hx, trivial⟩
    exact this
  have key := dualMultilinearSymmTransition x₀ x hx Φ hΦ M
  change (trivializationAt
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
      (fun x => _root_.Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜)
        (_root_.Bundle.dual 𝕜 E) x) x₀).continuousLinearMapAt 𝕜 x
      ((_root_.Bundle.continuousMultilinearMap.continuousLinearEquivAt
        (𝕜 := 𝕜) (F := F →L[𝕜] 𝕜) (E := _root_.Bundle.dual 𝕜 E) r x).symm M) =
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (𝕜 := 𝕜) (E := fun _ : Fin r => F →L[𝕜] 𝕜)
      (E₁ := fun _ : Fin r => F →L[𝕜] 𝕜) (F := 𝕜)
      (fun _ => (ContinuousLinearMap.compL 𝕜 F F 𝕜).flip
        Φ.toContinuousLinearMap)) M
  rw [key]
  exact (trivializationAt
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin r => F →L[𝕜] 𝕜) 𝕜)
    (fun x => _root_.Bundle.continuousMultilinearMap 𝕜 r (F →L[𝕜] 𝕜)
      (_root_.Bundle.dual 𝕜 E) x) x₀).continuousLinearMapAt_symmL hx_dmr
    ((ContinuousMultilinearMap.compContinuousLinearMapL
      (𝕜 := 𝕜) (E := fun _ : Fin r => F →L[𝕜] 𝕜)
      (E₁ := fun _ : Fin r => F →L[𝕜] 𝕜) (F := 𝕜)
      (fun _ => (ContinuousLinearMap.compL 𝕜 F F 𝕜).flip
        Φ.toContinuousLinearMap)) M)

end DualMultilinearTransition

end

end DifferentialGeometry.Tensor.Mixed
