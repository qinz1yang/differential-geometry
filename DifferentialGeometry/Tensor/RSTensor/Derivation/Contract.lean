/-
Authors: Yuan Liao, Jack McCarthy
Modified by: Ziyang Qin
-/
import DifferentialGeometry.Tensor.RSTensor.Defs
import DifferentialGeometry.Tensor.Multilinear.Curry
import DifferentialGeometry.Tensor.Multilinear.TensorProduct
import DifferentialGeometry.Tensor.RSTensor.Coordinates.Field
import DifferentialGeometry.Tensor.Auxiliary.PredualBasis
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.LinearAlgebra.Trace


namespace DifferentialGeometry
namespace Tensor0SBundle
noncomputable section


open Bundle Set IsManifold ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

noncomputable def modelInteriorProduct (s : ℕ) (v : E) :
    Tensor0SModel (s + 1) 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E :=
  (ContinuousLinearMap.apply 𝕜
    (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => E) 𝕜) v).comp
    (continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => E) 𝕜).toContinuousLinearEquiv.toContinuousLinearMap

noncomputable def modelInteriorBilinear (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] (s : ℕ) :
    E →L[𝕜] (Tensor0SModel (s + 1) 𝕜 E →L[𝕜] Tensor0SModel s 𝕜 E) :=
  ContinuousLinearMap.flip
    (continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => E) 𝕜).toContinuousLinearEquiv.toContinuousLinearMap

omit [CompleteSpace 𝕜] in
theorem model_interior_bilinear_apply (s : ℕ) (v : E) (T : Tensor0SModel (s + 1) 𝕜 E) :
    modelInteriorBilinear 𝕜 E s v T = modelInteriorProduct s v T := rfl

noncomputable def interiorProduct (s : ℕ) (x : M)
    (v : TangentSpace I x) :
    Tensor0SSpace (s + 1) I x →L[𝕜] Tensor0SSpace s I x :=
  (tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.apply 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : Fin s => TangentSpace I x) 𝕜) v).comp
      ((continuousMultilinearCurryLeftEquiv 𝕜
        (fun _ : Fin (s + 1) => TangentSpace I x) 𝕜).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (s + 1) x).toContinuousLinearMap))

omit [CompleteSpace 𝕜] in
theorem interior_product_apply (s : ℕ) (x : M) (v : TangentSpace I x)
    (T : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    interiorProduct s x v T w = T (Fin.cons v w) := by
  rfl

noncomputable def modelTensorWithCovector (r : ℕ) (α : Tensor0SModel 1 𝕜 E) :
    Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel (r + 1) 𝕜 E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun β => Bundle.continuousMultilinearMap.modelProduct r 1 β α
      map_add' := fun β₁ β₂ => by
        ext v
        simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
          add_apply, add_mul]
      map_smul' := fun c β => by
        ext v
        simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
          smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

noncomputable def modelTensorWithCovectorFirst (r : ℕ) (α : Tensor0SModel 1 𝕜 E) :
    Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel (1 + r) 𝕜 E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun β => Bundle.continuousMultilinearMap.modelProduct 1 r α β
      map_add' := fun β₁ β₂ => by
        ext v
        simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
          add_apply, mul_add]
      map_smul' := fun c β => by
        ext v
        simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
          smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

noncomputable def modelTensorWithCovectorFirstBilinear (r : ℕ) :
    Tensor0SModel 1 𝕜 E →L[𝕜]
      (Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel (1 + r) 𝕜 E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun α =>
        LinearMap.toContinuousLinearMap
          { toFun := fun β => Bundle.continuousMultilinearMap.modelProduct 1 r α β
            map_add' := fun β₁ β₂ => by
              ext v
              simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
                add_apply, mul_add]
            map_smul' := fun c β => by
              ext v
              simp only [Bundle.continuousMultilinearMap.modelProduct_apply,
                smul_apply, smul_eq_mul, RingHom.id_apply]
              ring }
      map_add' := fun α₁ α₂ => by
        ext β v
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          Bundle.continuousMultilinearMap.modelProduct_apply,
          add_apply, add_apply, add_mul]
      map_smul' := fun c α => by
        ext β v
        simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
          Bundle.continuousMultilinearMap.modelProduct_apply,
          smul_apply, smul_apply,
          smul_eq_mul, RingHom.id_apply]
        ring }

theorem model_tensorWithCovector_first_bilinear_apply (r : ℕ)
    (α : Tensor0SModel 1 𝕜 E) (β : Tensor0SModel r 𝕜 E) :
    modelTensorWithCovectorFirstBilinear (𝕜 := 𝕜) (E := E) r α β =
      modelTensorWithCovectorFirst r α β := rfl

noncomputable def modelContractCovariantBilinear (r s : ℕ) :
    E →L[𝕜] (TensorRSModel r (s + 1) 𝕜 E →L[𝕜] TensorRSModel r s 𝕜 E) :=
  (ContinuousLinearMap.compL 𝕜
      (Tensor0SModel r 𝕜 E)
      (Tensor0SModel (s + 1) 𝕜 E)
      (Tensor0SModel s 𝕜 E)).comp
    (modelInteriorBilinear 𝕜 E s)

omit [CompleteSpace 𝕜] in
theorem model_contract_covariant_bilinear_apply (r s : ℕ) (v : E)
    (T : TensorRSModel r (s + 1) 𝕜 E) :
    modelContractCovariantBilinear (𝕜 := 𝕜) (E := E) r s v T =
      (modelInteriorProduct s v).comp T := rfl

noncomputable def modelContractContravariantFirstBilinear (r s : ℕ) :
    Tensor0SModel 1 𝕜 E →L[𝕜]
      (TensorRSModel (1 + r) s 𝕜 E →L[𝕜] TensorRSModel r s 𝕜 E) :=
  (ContinuousLinearMap.compL 𝕜
        (Tensor0SModel r 𝕜 E) (Tensor0SModel (1 + r) 𝕜 E) (Tensor0SModel s 𝕜 E)).flip.comp
    (modelTensorWithCovectorFirstBilinear (𝕜 := 𝕜) (E := E) r)

theorem model_contract_contravariant_first_bilinear_apply (r s : ℕ)
    (α : Tensor0SModel 1 𝕜 E) (T : TensorRSModel (1 + r) s 𝕜 E) :
    modelContractContravariantFirstBilinear (𝕜 := 𝕜) (E := E) r s α T =
      T.comp (modelTensorWithCovectorFirst r α) := rfl

section FieldContraction

variable (n : WithTop ℕ∞ := ⊤) [IsManifold I ω M]

noncomputable def contractTensor0SFieldFun (s : ℕ)
    (α : (x : M) → Tensor0SSpace (s + 1) I x)
    (X : (x : M) → TangentSpace I x) :
    (x : M) → Tensor0SSpace s I x :=
  fun x => interiorProduct s x (X x) (α x)

noncomputable def contractTensor0SField (s : ℕ)
    (α : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) (s + 1))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _)) :
    Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) s := by
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (s + 1)
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  refine ⟨contractTensor0SFieldFun s (fun x => α x) (fun x => X x), ?_⟩
  intro x₀
  rw [contMDiffAt_section]
  have hα := α.contMDiff x₀
  rw [contMDiffAt_section] at hα
  have hX := X.contMDiff x₀
  rw [contMDiffAt_section] at hX
  have h_combine :
      ContMDiffAt I 𝓘(𝕜, Tensor0SModel s 𝕜 E) n
        (fun x => modelInteriorBilinear 𝕜 E s
          ((trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2)
          ((trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
            (fun x => Tensor0SSpace (s + 1) I x) x₀ ⟨x, α x⟩).2)) x₀ :=
    ((contMDiffAt_const (c := modelInteriorBilinear 𝕜 E s)).clm_apply hX).clm_apply hα
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx
  ext v
  set symmL := (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x with hsymmL
  set gtilde : E := (trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2 with hgtilde
  rw [Tensor0SSpace.trivializationAt_apply (𝕜 := 𝕜) (I := I)
    (x₀ := x₀) (x := x) s]
  change interiorProduct s x (X x) (α x) (fun i => symmL (v i)) = _
  rw [interior_product_apply]
  change (α x) (Fin.cons (X x) (fun i => symmL (v i))) =
    (trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
      (fun x => Tensor0SSpace (s + 1) I x) x₀ ⟨x, α x⟩).2 (Fin.cons gtilde v)
  rw [Tensor0SSpace.trivializationAt_apply (𝕜 := 𝕜) (I := I)
    (x₀ := x₀) (x := x) (s + 1)]
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · change (X x : E) = symmL gtilde
    have h := (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hx (X x)
    have hcl : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (X x) =
      gtilde := by
      change (trivializationAt E (TangentSpace I) x₀).linearMapAt 𝕜 x (X x) = _
      rw [(trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rw [hcl] at h
    exact h.symm
  · intro j
    rfl

noncomputable def contractCovariant (r s : ℕ) (x : M)
    (v : TangentSpace I x) :
    TensorRSSpace r (s + 1) I x →L[𝕜] TensorRSSpace r s I x :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.compL 𝕜
        (Tensor0SModel r 𝕜 E)
        (Tensor0SModel (s + 1) 𝕜 E)
        (Tensor0SModel s 𝕜 E)
        (modelInteriorProduct s (tangentSpaceModelContinuousLinearEquiv (I := I) x v))).comp
      (tensorRSSpaceContinuousLinearEquiv (I := I) r (s + 1) x).toContinuousLinearMap)

noncomputable def contractContravariant (r s : ℕ) (x : M)
    (α : Tensor0SSpace 1 I x) :
    TensorRSSpace (r + 1) s I x →L[𝕜] TensorRSSpace r s I x :=
  let α_model : Tensor0SModel 1 𝕜 E := Tensor0SSpace.toModel (I := I) (M := M) α
  let embed_model : Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel (r + 1) 𝕜 E :=
    modelTensorWithCovector r α_model
  (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.compL 𝕜
        (Tensor0SModel r 𝕜 E)
        (Tensor0SModel (r + 1) 𝕜 E)
        (Tensor0SModel s 𝕜 E)).flip embed_model).comp
      (tensorRSSpaceContinuousLinearEquiv (I := I) (r + 1) s x).toContinuousLinearMap)

noncomputable def modelCovectorOfCLM :
    (E →L[𝕜] 𝕜) →L[𝕜] Tensor0SModel 1 𝕜 E :=
  (continuousMultilinearCurryFin1 𝕜 E 𝕜).symm.toContinuousLinearMap

@[simp]
theorem model_covectorOfCLM_apply (α : E →L[𝕜] 𝕜) (v : Fin 1 → E) :
    modelCovectorOfCLM (𝕜 := 𝕜) (E := E) α v = α (v 0) := by
  change ((continuousMultilinearCurryFin1 𝕜 E 𝕜).symm α) v = α (v 0)
  rfl

noncomputable def modelContractTrace (r s : ℕ) :
    TensorRSModel (1 + r) (s + 1) 𝕜 E →L[𝕜] TensorRSModel r s 𝕜 E :=
  let d := Module.finrank 𝕜 E
  let B : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 (E →L[𝕜] 𝕜) := B.cDualBasis
  ∑ i : Fin d,
    (modelContractCovariantBilinear (𝕜 := 𝕜) (E := E) r s (B i)).comp
      (modelContractContravariantFirstBilinear
        (𝕜 := 𝕜) (E := E) r (s + 1)
        (modelCovectorOfCLM (𝕜 := 𝕜) (E := E) (b i)))

theorem model_contract_trace_apply (r s : ℕ)
    (T : TensorRSModel (1 + r) (s + 1) 𝕜 E) :
    modelContractTrace (𝕜 := 𝕜) (E := E) r s T =
      ∑ i : Fin (Module.finrank 𝕜 E),
        (modelContractCovariantBilinear
          (𝕜 := 𝕜) (E := E) r s
          ((Module.finBasis 𝕜 E) i))
          ((modelContractContravariantFirstBilinear
            (𝕜 := 𝕜) (E := E) r (s + 1)
            (modelCovectorOfCLM (𝕜 := 𝕜) (E := E)
              ((Module.finBasis 𝕜 E).cDualBasis i))) T) := by
  simp [modelContractTrace]

noncomputable def contractTrace (r s : ℕ) (x : M) :
    TensorRSSpace (1 + r) (s + 1) I x →L[𝕜] TensorRSSpace r s I x :=
  (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).symm.toContinuousLinearMap.comp
    ((modelContractTrace (𝕜 := 𝕜) (E := E) r s).comp
      (tensorRSSpaceContinuousLinearEquiv (I := I) (1 + r) (s + 1) x).toContinuousLinearMap)

omit [IsManifold I ω M] in
theorem contract_trace_apply (r s : ℕ) (x : M)
    (T : TensorRSSpace (1 + r) (s + 1) I x) :
    contractTrace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x T =
      (tensorRSSpaceContinuousLinearEquiv (I := I) r s x).symm
        (modelContractTrace (𝕜 := 𝕜) (E := E) r s
          (tensorRSSpaceContinuousLinearEquiv (I := I) (1 + r) (s + 1) x T)) := by
  rfl

private theorem trace_bilinear_change_frame_coord
    (L K : E →L[𝕜] E) (hKL : ∀ z, K (L z) = z)
    (F : (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜) :
    (∑ i : Fin (Module.finrank 𝕜 E),
        F ((LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 E).coord i)).comp L)
          (K ((Module.finBasis 𝕜 E) i))) =
      ∑ i : Fin (Module.finrank 𝕜 E),
        F (LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 E).coord i))
          ((Module.finBasis 𝕜 E) i) := by
  let d := Module.finrank 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  change (∑ i : Fin d, F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)
      (K (b i))) =
    ∑ i : Fin d, F (LinearMap.toContinuousLinearMap (b.coord i)) (b i)
  have h_cov : ∀ j : Fin d,
      (∑ i : Fin d, (b.coord j (K (b i))) •
          ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)) =
        LinearMap.toContinuousLinearMap (b.coord j) := by
    intro j
    ext z
    calc
      (∑ i : Fin d, (b.coord j (K (b i))) •
          ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)) z
          = ∑ i : Fin d, b.coord j (K (b i)) * b.coord i (L z) := by
              simp [smul_eq_mul]
      _ = b.coord j (∑ i : Fin d, b.coord i (L z) • K (b i)) := by
              symm
              rw [map_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_smul]
              simp [smul_eq_mul, mul_comm]
      _ = b.coord j (K (∑ i : Fin d, b.coord i (L z) • b i)) := by
              congr 1
              symm
              rw [map_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_smul]
      _ = b.coord j (K (L z)) := by
              rw [show (∑ i : Fin d, b.coord i (L z) • b i) = L z from b.sum_repr (L z)]
      _ = b.coord j z := by rw [hKL z]
      _ = (LinearMap.toContinuousLinearMap (b.coord j)) z := rfl
  calc
    (∑ i : Fin d, F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (K (b i)))
        = ∑ i : Fin d, ∑ j : Fin d,
            (b.coord j (K (b i))) •
              F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (b j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc
            F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (K (b i))
                = F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)
                    (∑ j : Fin d, b.coord j (K (b i)) • b j) := by
                  rw [show (∑ j : Fin d, b.coord j (K (b i)) • b j) = K (b i) from
                    b.sum_repr (K (b i))]
            _ = ∑ j : Fin d, (b.coord j (K (b i))) •
                    F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (b j) := by
                  rw [map_sum]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [map_smul]
    _ = ∑ j : Fin d, ∑ i : Fin d,
            (b.coord j (K (b i))) •
              F ((LinearMap.toContinuousLinearMap (b.coord i)).comp L) (b j) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin d, F
            (∑ i : Fin d, (b.coord j (K (b i))) •
              ((LinearMap.toContinuousLinearMap (b.coord i)).comp L)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_sum]
          simp [map_smul]
    _ = ∑ j : Fin d, F (LinearMap.toContinuousLinearMap (b.coord j)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [h_cov j]

private theorem trace_bilinear_change_frame_cdual
    (L K : E →L[𝕜] E) (hKL : ∀ z, K (L z) = z)
    (F : (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜) :
    (∑ i : Fin (Module.finrank 𝕜 E),
        F (((Module.finBasis 𝕜 E).cDualBasis i).comp L)
          (K ((Module.finBasis 𝕜 E) i))) =
      ∑ i : Fin (Module.finrank 𝕜 E),
        F ((Module.finBasis 𝕜 E).cDualBasis i)
          ((Module.finBasis 𝕜 E) i) := by
  simpa [Module.Basis.cDualBasis, Module.Basis.coe_dualBasis]
    using trace_bilinear_change_frame_coord (𝕜 := 𝕜) (E := E) L K hKL F

private noncomputable def model_trace_pairing_first (r s : ℕ)
    (T : TensorRSModel (1 + r) (s + 1) 𝕜 E)
    (β : Tensor0SModel r 𝕜 E) (tail : Fin s → E) :
    (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜 :=
  let covToTensor : (E →L[𝕜] 𝕜) →L[𝕜] Tensor0SModel (1 + r) 𝕜 E :=
    ((ContinuousLinearMap.apply 𝕜 (Tensor0SModel (1 + r) 𝕜 E) β).comp
      ((modelTensorWithCovectorFirstBilinear (𝕜 := 𝕜) (E := E) r).comp
        (modelCovectorOfCLM (𝕜 := 𝕜) (E := E))))
  let covToOutput : (E →L[𝕜] 𝕜) →L[𝕜] Tensor0SModel (s + 1) 𝕜 E :=
    T.comp covToTensor
  let evalTail : Tensor0SModel s 𝕜 E →L[𝕜] 𝕜 :=
    ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin s => E) 𝕜 tail
  let curry :
      Tensor0SModel (s + 1) 𝕜 E →L[𝕜] E →L[𝕜] Tensor0SModel s 𝕜 E :=
    (continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (s + 1) => E) 𝕜).toContinuousLinearEquiv.toContinuousLinearMap
  let outputToPair : Tensor0SModel (s + 1) 𝕜 E →L[𝕜] E →L[𝕜] 𝕜 :=
    ((ContinuousLinearMap.compL 𝕜 E (Tensor0SModel s 𝕜 E) 𝕜) evalTail).comp curry
  outputToPair.comp covToOutput

private theorem model_trace_pairing_first_apply (r s : ℕ)
    (T : TensorRSModel (1 + r) (s + 1) 𝕜 E)
    (β : Tensor0SModel r 𝕜 E) (tail : Fin s → E)
    (α : E →L[𝕜] 𝕜) (X : E) :
    model_trace_pairing_first (𝕜 := 𝕜) (E := E) r s T β tail α X =
      (modelInteriorProduct s X
        (T (modelTensorWithCovectorFirst r
          (modelCovectorOfCLM (𝕜 := 𝕜) (E := E) α) β))) tail := by
  simp [model_trace_pairing_first, model_tensorWithCovector_first_bilinear_apply,
    modelInteriorProduct]

private theorem trace_bilinear_basis_coord
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx 𝕜 E)
    (F : (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜) :
    (∑ i : Idx,
        F (LinearMap.toContinuousLinearMap (basis.coord i)) (basis i)) =
      ∑ j : Fin (Module.finrank 𝕜 E),
        F (LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 E).coord j))
          ((Module.finBasis 𝕜 E) j) := by
  let d := Module.finrank 𝕜 E
  let b : Module.Basis (Fin d) 𝕜 E := Module.finBasis 𝕜 E
  change (∑ i : Idx,
      F (LinearMap.toContinuousLinearMap (basis.coord i)) (basis i)) =
    ∑ j : Fin d, F (LinearMap.toContinuousLinearMap (b.coord j)) (b j)
  have h_cov : ∀ j : Fin d,
      (∑ i : Idx, (b.coord j (basis i)) •
          LinearMap.toContinuousLinearMap (basis.coord i)) =
        LinearMap.toContinuousLinearMap (b.coord j) := by
    intro j
    ext z
    calc
      (∑ i : Idx, (b.coord j (basis i)) •
          LinearMap.toContinuousLinearMap (basis.coord i)) z
          = ∑ i : Idx, b.coord j (basis i) * basis.coord i z := by
              simp [smul_eq_mul]
      _ = b.coord j (∑ i : Idx, basis.coord i z • basis i) := by
              symm
              rw [map_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_smul]
              simp [smul_eq_mul, mul_comm]
      _ = b.coord j z := by
              rw [show (∑ i : Idx, basis.coord i z • basis i) = z from basis.sum_repr z]
      _ = (LinearMap.toContinuousLinearMap (b.coord j)) z := rfl
  calc
    (∑ i : Idx, F (LinearMap.toContinuousLinearMap (basis.coord i)) (basis i))
        = ∑ i : Idx, ∑ j : Fin d,
            (b.coord j (basis i)) •
              F (LinearMap.toContinuousLinearMap (basis.coord i)) (b j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc
            F (LinearMap.toContinuousLinearMap (basis.coord i)) (basis i)
                = F (LinearMap.toContinuousLinearMap (basis.coord i))
                    (∑ j : Fin d, b.coord j (basis i) • b j) := by
                  rw [show (∑ j : Fin d, b.coord j (basis i) • b j) = basis i from
                    b.sum_repr (basis i)]
            _ = ∑ j : Fin d, (b.coord j (basis i)) •
                    F (LinearMap.toContinuousLinearMap (basis.coord i)) (b j) := by
                  rw [map_sum]
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [map_smul]
    _ = ∑ j : Fin d, ∑ i : Idx,
            (b.coord j (basis i)) •
              F (LinearMap.toContinuousLinearMap (basis.coord i)) (b j) := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin d, F
            (∑ i : Idx, (b.coord j (basis i)) •
              LinearMap.toContinuousLinearMap (basis.coord i)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_sum]
          simp [map_smul]
    _ = ∑ j : Fin d, F (LinearMap.toContinuousLinearMap (b.coord j)) (b j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [h_cov j]

theorem model_contract_trace_apply_basis
    {Idx : Type*} [Fintype Idx]
    (basis : Module.Basis Idx 𝕜 E) (r s : ℕ)
    (T : TensorRSModel (1 + r) (s + 1) 𝕜 E)
    (β : Tensor0SModel r 𝕜 E) (tail : Fin s → E) :
    (modelContractTrace (𝕜 := 𝕜) (E := E) r s T β) tail =
      ∑ i : Idx,
        (modelInteriorProduct s (basis i)
          (T (modelTensorWithCovectorFirst r
            (modelCovectorOfCLM (𝕜 := 𝕜) (E := E)
              (LinearMap.toContinuousLinearMap (basis.coord i))) β))) tail := by
  rw [model_contract_trace_apply]
  rw [sum_apply]
  rw [sum_apply]
  symm
  calc
    (∑ i : Idx,
        (modelInteriorProduct s (basis i)
          (T (modelTensorWithCovectorFirst r
            (modelCovectorOfCLM (𝕜 := 𝕜) (E := E)
              (LinearMap.toContinuousLinearMap (basis.coord i))) β))) tail)
        = ∑ i : Idx,
            model_trace_pairing_first (𝕜 := 𝕜) (E := E) r s T β tail
              (LinearMap.toContinuousLinearMap (basis.coord i)) (basis i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [model_trace_pairing_first_apply]
    _ = ∑ j : Fin (Module.finrank 𝕜 E),
          model_trace_pairing_first (𝕜 := 𝕜) (E := E) r s T β tail
            (LinearMap.toContinuousLinearMap ((Module.finBasis 𝕜 E).coord j))
            ((Module.finBasis 𝕜 E) j) := by
          exact trace_bilinear_basis_coord (𝕜 := 𝕜) (E := E) basis
            (model_trace_pairing_first (𝕜 := 𝕜) (E := E) r s T β tail)
    _ = ∑ j : Fin (Module.finrank 𝕜 E),
          (modelContractCovariantBilinear
            (𝕜 := 𝕜) (E := E) r s
            ((Module.finBasis 𝕜 E) j))
            ((modelContractContravariantFirstBilinear
              (𝕜 := 𝕜) (E := E) r (s + 1)
              (modelCovectorOfCLM (𝕜 := 𝕜) (E := E)
                ((Module.finBasis 𝕜 E).cDualBasis j))) T) β tail := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [model_trace_pairing_first_apply]
          rw [model_contract_covariant_bilinear_apply]
          rw [model_contract_contravariant_first_bilinear_apply]
          simp [Module.Basis.cDualBasis, Module.Basis.coe_dualBasis]

noncomputable def modelCovariantChange (k : ℕ) (L : E →L[𝕜] E) :
    Tensor0SModel k 𝕜 E →L[𝕜] Tensor0SModel k 𝕜 E :=
  ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k => L)

omit [CompleteSpace 𝕜] in
@[simp]
theorem model_covariantChange_apply (k : ℕ) (L : E →L[𝕜] E)
    (T : Tensor0SModel k 𝕜 E) (v : Fin k → E) :
    modelCovariantChange (𝕜 := 𝕜) (E := E) k L T v =
      T (fun i => L (v i)) := by
  rfl

omit [CompleteSpace 𝕜] in
private theorem model_interior_product_covariantChange_apply (s : ℕ)
    (L : E →L[𝕜] E) (X : E) (U : Tensor0SModel (s + 1) 𝕜 E)
    (v : Fin s → E) :
    (modelInteriorProduct s X
      (modelCovariantChange (𝕜 := 𝕜) (E := E) (s + 1) L U)) v =
    (modelInteriorProduct s (L X) U) (fun i => L (v i)) := by
  change (modelCovariantChange (𝕜 := 𝕜) (E := E) (s + 1) L U)
      (Fin.cons X v) =
    U (Fin.cons (L X) (fun i => L (v i)))
  rw [model_covariantChange_apply]
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

private theorem model_covariantChange_tensorWithCovector_first (r : ℕ)
    (L : E →L[𝕜] E) (α : E →L[𝕜] 𝕜) (β : Tensor0SModel r 𝕜 E) :
    modelCovariantChange (𝕜 := 𝕜) (E := E) (1 + r) L
      (modelTensorWithCovectorFirst r (modelCovectorOfCLM (𝕜 := 𝕜) (E := E) α) β) =
    modelTensorWithCovectorFirst r
      (modelCovectorOfCLM (𝕜 := 𝕜) (E := E) (α.comp L))
      (modelCovariantChange (𝕜 := 𝕜) (E := E) r L β) := by
  refine ContinuousMultilinearMap.ext fun w => ?_
  change (Bundle.continuousMultilinearMap.modelProduct 1 r
      (modelCovectorOfCLM (𝕜 := 𝕜) (E := E) α) β)
      (fun i => L (w i)) =
    (Bundle.continuousMultilinearMap.modelProduct 1 r
      (modelCovectorOfCLM (𝕜 := 𝕜) (E := E) (α.comp L))
      (modelCovariantChange (𝕜 := 𝕜) (E := E) r L β)) w
  rw [Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1

theorem model_contract_trace_naturality
    (r s : ℕ) (L Linv : E →L[𝕜] E)
    (hL : L.comp Linv = ContinuousLinearMap.id 𝕜 E)
    (T : TensorRSModel (1 + r) (s + 1) 𝕜 E) :
    modelContractTrace (𝕜 := 𝕜) (E := E) r s
      ((modelCovariantChange (𝕜 := 𝕜) (E := E) (s + 1) L).comp
        (T.comp (modelCovariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv))) =
    (modelCovariantChange (𝕜 := 𝕜) (E := E) s L).comp
      ((modelContractTrace (𝕜 := 𝕜) (E := E) r s T).comp
        (modelCovariantChange (𝕜 := 𝕜) (E := E) r Linv)) := by
  ext β v
  let β' : Tensor0SModel r 𝕜 E :=
    modelCovariantChange (𝕜 := 𝕜) (E := E) r Linv β
  let tail : Fin s → E := fun i => L (v i)
  let F : (E →L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜 :=
    model_trace_pairing_first (𝕜 := 𝕜) (E := E) r s T β' tail
  have hKL : ∀ z : E, L (Linv z) = z := by
    intro z
    have h := congrArg (fun f : E →L[𝕜] E => f z) hL
    simpa [ContinuousLinearMap.comp_apply] using h
  calc
    ((modelContractTrace (𝕜 := 𝕜) (E := E) r s
        ((modelCovariantChange (𝕜 := 𝕜) (E := E) (s + 1) L).comp
          (T.comp (modelCovariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv)))) β) v
        =
      ∑ i : Fin (Module.finrank 𝕜 E),
        F (((Module.finBasis 𝕜 E).cDualBasis i).comp Linv)
          (L ((Module.finBasis 𝕜 E) i)) := by
          rw [model_contract_trace_apply]
          rw [sum_apply]
          rw [sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [model_contract_covariant_bilinear_apply]
          rw [model_contract_contravariant_first_bilinear_apply]
          change (modelInteriorProduct s ((Module.finBasis 𝕜 E) i)
              ((modelCovariantChange (𝕜 := 𝕜) (E := E) (s + 1) L)
                (T ((modelCovariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv)
                  (modelTensorWithCovectorFirst r
                    (modelCovectorOfCLM (𝕜 := 𝕜) (E := E)
                      ((Module.finBasis 𝕜 E).cDualBasis i)) β))))) v =
            F (((Module.finBasis 𝕜 E).cDualBasis i).comp Linv)
              (L ((Module.finBasis 𝕜 E) i))
          rw [model_interior_product_covariantChange_apply]
          rw [model_covariantChange_tensorWithCovector_first]
          rw [model_trace_pairing_first_apply]
    _ = ∑ i : Fin (Module.finrank 𝕜 E),
        F ((Module.finBasis 𝕜 E).cDualBasis i)
          ((Module.finBasis 𝕜 E) i) := by
          exact trace_bilinear_change_frame_cdual (𝕜 := 𝕜) (E := E)
            (L := Linv) (K := L) hKL F
    _ =
      (((modelCovariantChange (𝕜 := 𝕜) (E := E) s L).comp
        ((modelContractTrace (𝕜 := 𝕜) (E := E) r s T).comp
          (modelCovariantChange (𝕜 := 𝕜) (E := E) r Linv))) β) v := by
          change ∑ i : Fin (Module.finrank 𝕜 E),
              F ((Module.finBasis 𝕜 E).cDualBasis i)
                ((Module.finBasis 𝕜 E) i) =
            (modelCovariantChange (𝕜 := 𝕜) (E := E) s L
              ((modelContractTrace (𝕜 := 𝕜) (E := E) r s T) β')) v
          rw [model_covariantChange_apply]
          rw [model_contract_trace_apply]
          rw [sum_apply]
          rw [sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [model_trace_pairing_first_apply]
          rw [model_contract_covariant_bilinear_apply]
          rw [model_contract_contravariant_first_bilinear_apply]
          rfl

omit [IsManifold I ω M] in
theorem contract_trace_trivialization_eq
    {r s : ℕ} {x₀ x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : TensorRSSpace (1 + r) (s + 1) I x) :
    (trivializationAt (TensorRSModel r s 𝕜 E)
      (TensorRSSpace r s I) x₀
      ⟨x, contractTrace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x T⟩).2 =
    modelContractTrace (𝕜 := 𝕜) (E := E) r s
      ((trivializationAt (TensorRSModel (1 + r) (s + 1) 𝕜 E)
        (TensorRSSpace (1 + r) (s + 1) I) x₀
        ⟨x, T⟩).2) := by
  let L : E →L[𝕜] E := (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x
  let Linv : E →L[𝕜] E :=
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x
  let Tx : TensorRSModel (1 + r) (s + 1) 𝕜 E :=
    tensorRSSpaceContinuousLinearEquiv (I := I) (1 + r) (s + 1) x T
  have hL : L.comp Linv = ContinuousLinearMap.id 𝕜 E := by
    ext z
    exact (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hx z
  have h_cLMAt : ∀ (k : ℕ) (U : Tensor0SSpace k I x) (v : Fin k → E),
      (trivializationAt (Tensor0SModel k 𝕜 E)
        (Tensor0SSpace k I) x₀).continuousLinearMapAt 𝕜 x U v =
      U (fun i => L (v i)) := by
    intro k U v
    rw [Trivialization.continuousLinearMapAt_apply]
    rw [show ⇑((trivializationAt (Tensor0SModel k 𝕜 E)
        (Tensor0SSpace k I) x₀).linearMapAt 𝕜 x) =
        fun y => (trivializationAt (Tensor0SModel k 𝕜 E)
          (Tensor0SSpace k I) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rfl
  have h_symmL : ∀ (k : ℕ) (U : Tensor0SModel k 𝕜 E) (u : Fin k → E),
      ((trivializationAt (Tensor0SModel k 𝕜 E)
        (Tensor0SSpace k I) x₀).symmL 𝕜 x U) u =
        U (fun i => Linv (u i)) := by
    intro k U u
    have h_inv : ∀ z : E, L (Linv z) = z := by
      intro z
      have h := congrArg (fun f : E →L[𝕜] E => f z) hL
      simpa [ContinuousLinearMap.comp_apply] using h
    have hu : u = fun i => L (Linv (u i)) := by
      funext i
      exact (h_inv (u i)).symm
    calc
      ((trivializationAt (Tensor0SModel k 𝕜 E)
        (Tensor0SSpace k I) x₀).symmL 𝕜 x U) u
          = ((trivializationAt (Tensor0SModel k 𝕜 E)
              (Tensor0SSpace k I) x₀).symmL 𝕜 x U)
              (fun i => L (Linv (u i))) := by rw [← hu]
      _ = (trivializationAt (Tensor0SModel k 𝕜 E)
            (Tensor0SSpace k I) x₀).continuousLinearMapAt 𝕜 x
            ((trivializationAt (Tensor0SModel k 𝕜 E)
              (Tensor0SSpace k I) x₀).symmL 𝕜 x U)
            (fun i => Linv (u i)) := (h_cLMAt k _ _).symm
      _ = U (fun i => Linv (u i)) := by
            rw [(trivializationAt (Tensor0SModel k 𝕜 E)
              (Tensor0SSpace k I) x₀).continuousLinearMapAt_symmL
              (R := 𝕜) hx]
  have h_input :
      ((trivializationAt (TensorRSModel (1 + r) (s + 1) 𝕜 E)
        (TensorRSSpace (1 + r) (s + 1) I) x₀
        ⟨x, T⟩).2) =
      (modelCovariantChange (𝕜 := 𝕜) (E := E) (s + 1) L).comp
        (Tx.comp (modelCovariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
        (Tensor0SSpace (s + 1) I) x₀).continuousLinearMapAt 𝕜 x
        (T ((trivializationAt (Tensor0SModel (1 + r) 𝕜 E)
          (Tensor0SSpace (1 + r) I) x₀).symmL 𝕜 x β)) v =
      ((modelCovariantChange (𝕜 := 𝕜) (E := E) (s + 1) L)
        (Tx ((modelCovariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv) β))) v
    rw [h_cLMAt]
    rw [model_covariantChange_apply]
    have hβ :
        (trivializationAt (Tensor0SModel (1 + r) 𝕜 E)
          (Tensor0SSpace (1 + r) I) x₀).symmL 𝕜 x β =
          (modelCovariantChange (𝕜 := 𝕜) (E := E) (1 + r) Linv) β := by
      refine ContinuousMultilinearMap.ext fun u => ?_
      exact h_symmL (1 + r) β u
    rw [hβ]
    rfl
  have h_output :
      (trivializationAt (TensorRSModel r s 𝕜 E)
        (TensorRSSpace r s I) x₀
        ⟨x, contractTrace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x T⟩).2 =
      (modelCovariantChange (𝕜 := 𝕜) (E := E) s L).comp
        ((modelContractTrace (𝕜 := 𝕜) (E := E) r s Tx).comp
          (modelCovariantChange (𝕜 := 𝕜) (E := E) r Linv)) := by
    refine ContinuousLinearMap.ext fun β => ?_
    refine ContinuousMultilinearMap.ext fun v => ?_
    change (trivializationAt (Tensor0SModel s 𝕜 E)
        (Tensor0SSpace s I) x₀).continuousLinearMapAt 𝕜 x
        ((contractTrace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x T)
          ((trivializationAt (Tensor0SModel r 𝕜 E)
            (Tensor0SSpace r I) x₀).symmL 𝕜 x β)) v =
      ((modelCovariantChange (𝕜 := 𝕜) (E := E) s L)
        ((modelContractTrace (𝕜 := 𝕜) (E := E) r s Tx)
          ((modelCovariantChange (𝕜 := 𝕜) (E := E) r Linv) β))) v
    rw [h_cLMAt]
    rw [model_covariantChange_apply]
    rw [contract_trace_apply]
    have hβ :
        (trivializationAt (Tensor0SModel r 𝕜 E)
          (Tensor0SSpace r I) x₀).symmL 𝕜 x β =
          (modelCovariantChange (𝕜 := 𝕜) (E := E) r Linv) β := by
      refine ContinuousMultilinearMap.ext fun u => ?_
      exact h_symmL r β u
    rw [hβ]
    rfl
  rw [h_input, h_output]
  exact (model_contract_trace_naturality (𝕜 := 𝕜) (E := E)
    r s L Linv hL Tx).symm

noncomputable def contractCovariantFieldFun (r s : ℕ)
    (α : (x : M) → TensorRSSpace r (s + 1) I x)
    (X : (x : M) → TangentSpace I x) :
    (x : M) → TensorRSSpace r s I x :=
  fun x => contractCovariant r s x (X x) (α x)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I 1 M]
  [IsManifold I ω M] in
private theorem contMDiffAt_clm_apply₂
    {A B C : Type*}
    [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B]
    [NormedAddCommGroup C] [NormedSpace 𝕜 C]
    (L : A →L[𝕜] B →L[𝕜] C) {f : M → A} {g : M → B} {x : M}
    (hf : ContMDiffAt I 𝓘(𝕜, A) n f x)
    (hg : ContMDiffAt I 𝓘(𝕜, B) n g x) :
    ContMDiffAt I 𝓘(𝕜, C) n (fun y => L (f y) (g y)) x :=
  ((contMDiffAt_const (c := L)).clm_apply hf).clm_apply hg

private noncomputable def model_tensorWithCovector_bilinear (r : ℕ) :
    Tensor0SModel 1 𝕜 E →L[𝕜] (Tensor0SModel r 𝕜 E →L[𝕜] Tensor0SModel (r + 1) 𝕜 E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => modelTensorWithCovector r a
      map_add' := fun a₁ a₂ => by
        refine ContinuousLinearMap.ext fun β => ?_
        refine ContinuousMultilinearMap.ext fun w => ?_
        simp only [modelTensorWithCovector, LinearMap.coe_toContinuousLinearMap',
          LinearMap.coe_mk, AddHom.coe_mk, add_apply,
          Bundle.continuousMultilinearMap.modelProduct_apply,
          add_apply, mul_add]
      map_smul' := fun c a => by
        refine ContinuousLinearMap.ext fun β => ?_
        refine ContinuousMultilinearMap.ext fun w => ?_
        simp only [modelTensorWithCovector, LinearMap.coe_toContinuousLinearMap',
          LinearMap.coe_mk, AddHom.coe_mk, smul_apply,
          Bundle.continuousMultilinearMap.modelProduct_apply,
          smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

omit [CompleteSpace 𝕜] [IsManifold I ω M] in
private theorem tensor0STrivialization_continuousLinearMapAt_apply (k : ℕ) (x₀ x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : Tensor0SSpace k I x) (u : Fin k → E) :
    letI := tensor0SBundleTopology
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) k
    (trivializationAt (Tensor0SModel k 𝕜 E)
      (fun y => Tensor0SSpace k I y) x₀).continuousLinearMapAt 𝕜 x T u =
      T (fun i => (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (u i)) := by
  let := tensor0SBundleTopology
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) k
  rw [Trivialization.continuousLinearMapAt_apply]
  rw [show ⇑((trivializationAt (Tensor0SModel k 𝕜 E)
      (fun y => Tensor0SSpace k I y) x₀).linearMapAt 𝕜 x) =
      fun y => (trivializationAt (Tensor0SModel k 𝕜 E)
        (fun y => Tensor0SSpace k I y) x₀ ⟨x, y⟩).2 from
    (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
  rfl

omit [CompleteSpace 𝕜] [IsManifold I ω M] in
private theorem tensor0STrivialization_symmL_apply (k : ℕ) (x₀ x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (T : Tensor0SModel k 𝕜 E) (u : Fin k → E) :
    letI := tensor0SBundleTopology
      (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) k
    ((trivializationAt (Tensor0SModel k 𝕜 E)
      (fun y => Tensor0SSpace k I y) x₀).symmL 𝕜 x T) u =
      T (fun i => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt
        𝕜 x (u i)) := by
  let := tensor0SBundleTopology
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) k
  let sL := (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x
  have hu : u = fun i => sL
      ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (u i)) := by
    funext i
    exact ((trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hx (u i)).symm
  calc
    ((trivializationAt (Tensor0SModel k 𝕜 E)
      (fun y => Tensor0SSpace k I y) x₀).symmL 𝕜 x T) u =
        ((trivializationAt (Tensor0SModel k 𝕜 E)
          (fun y => Tensor0SSpace k I y) x₀).symmL 𝕜 x T)
          (fun i => sL
            ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt
              𝕜 x (u i))) := by rw [← hu]
    _ = (trivializationAt (Tensor0SModel k 𝕜 E)
          (fun y => Tensor0SSpace k I y) x₀).continuousLinearMapAt 𝕜 x
          ((trivializationAt (Tensor0SModel k 𝕜 E)
            (fun y => Tensor0SSpace k I y) x₀).symmL 𝕜 x T)
          (fun i => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt
            𝕜 x (u i)) := by
      exact (tensor0STrivialization_continuousLinearMapAt_apply
        (I := I) k x₀ x hx _ _).symm
    _ = T (fun i => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt
          𝕜 x (u i)) := by
      rw [(trivializationAt (Tensor0SModel k 𝕜 E)
        (fun y => Tensor0SSpace k I y) x₀).continuousLinearMapAt_symmL (R := 𝕜) hx]

noncomputable def contractCovariantField (r s : ℕ)
    (α : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r (s + 1))
    (X : ContMDiffSection I E n (TangentSpace I : M → Type _)) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s := by
  letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r (s + 1)
  letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (s + 1)
  refine ⟨contractCovariantFieldFun r s (fun x => α x) (fun x => X x), ?_⟩
  intro x₀
  rw [contMDiffAt_section]
  have hα := α.contMDiff x₀
  rw [contMDiffAt_section] at hα
  have hX := X.contMDiff x₀
  rw [contMDiffAt_section] at hX
  let biop :
      E →L[𝕜] (TensorRSModel r (s + 1) 𝕜 E →L[𝕜] TensorRSModel r s 𝕜 E) :=
    (ContinuousLinearMap.compL 𝕜
      (Tensor0SModel r 𝕜 E) (Tensor0SModel (s + 1) 𝕜 E) (Tensor0SModel s 𝕜 E)).comp
      (modelInteriorBilinear 𝕜 E s)
  have h_combine :
      ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E) n
        (fun x => biop
          ((trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2)
          ((trivializationAt (TensorRSModel r (s + 1) 𝕜 E)
            (fun x => TensorRSSpace r (s + 1) I x) x₀ ⟨x, α x⟩).2)) x₀ :=
    contMDiffAt_clm_apply₂ (I := I) (n := n) biop hX hα
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx
  refine ContinuousLinearMap.ext fun γ => ?_
  refine ContinuousMultilinearMap.ext fun w => ?_
  set sL := (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x with hsL
  set Xtilde : E := (trivializationAt E (TangentSpace I) x₀ ⟨x, X x⟩).2 with hXtilde
  set gtilde : Tensor0SSpace r I x :=
    (trivializationAt (Tensor0SModel r 𝕜 E) (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x γ
    with hgtilde
  have h_cLMAt_s : ∀ (T : Tensor0SSpace s I x) (v : Fin s → E),
      (trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).continuousLinearMapAt 𝕜 x T v =
      T (fun i => sL (v i)) := by
    intro T v
    rw [Trivialization.continuousLinearMapAt_apply]
    rw [show ⇑((trivializationAt (Tensor0SModel s 𝕜 E)
        (fun x => Tensor0SSpace s I x) x₀).linearMapAt 𝕜 x) =
        fun y => (trivializationAt (Tensor0SModel s 𝕜 E)
          (fun x => Tensor0SSpace s I x) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rfl
  have h_cLMAt_s1 : ∀ (T : Tensor0SSpace (s + 1) I x) (v : Fin (s + 1) → E),
      (trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
        (fun x => Tensor0SSpace (s + 1) I x) x₀).continuousLinearMapAt 𝕜 x T v =
      T (fun i => sL (v i)) := by
    intro T v
    rw [Trivialization.continuousLinearMapAt_apply]
    rw [show ⇑((trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
        (fun x => Tensor0SSpace (s + 1) I x) x₀).linearMapAt 𝕜 x) =
        fun y => (trivializationAt (Tensor0SModel (s + 1) 𝕜 E)
          (fun x => Tensor0SSpace (s + 1) I x) x₀ ⟨x, y⟩).2 from
      (trivializationAt _ _ x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rfl
  rw [TensorRSSpace.trivializationAt_apply (𝕜 := 𝕜) (I := I)
    (x₀ := x₀) (x := x) r s hx]
  unfold contractCovariantFieldFun contractCovariant
  simp only [ContinuousLinearMap.comp_apply]
  rw [tensorRSSpace_continuousLinearEquiv_symm_toContinuousLinearMap_apply_apply]
  simp only [ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]
  change tensorRSSpaceContinuousLinearEquiv (I := I) r (s + 1) x (α x)
      (Tensor0SSpace.toModel (I := I) (M := M) gtilde)
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x (X x))
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (sL (w i)))) = _
  rw [tensorRSSpace_continuousLinearEquiv_apply_apply]
  have hrhs :
      (((biop Xtilde)
        (trivializationAt (TensorRSModel r (s + 1) 𝕜 E)
          (fun x => TensorRSSpace r (s + 1) I x) x₀ ⟨x, α x⟩).2) γ) w =
        (trivializationAt (TensorRSModel r (s + 1) 𝕜 E)
          (fun x => TensorRSSpace r (s + 1) I x) x₀ ⟨x, α x⟩).2
          γ (Fin.cons Xtilde w) := by
    rfl
  rw [hrhs, TensorRSSpace.trivializationAt_apply (𝕜 := 𝕜) (I := I)
    (x₀ := x₀) (x := x) r (s + 1) hx]
  change ((show Tensor0SSpace r I x →L[𝕜] Tensor0SSpace (s + 1) I x from α x) gtilde)
      (Fin.cons (X x) (fun i => sL (w i))) =
    ((show Tensor0SSpace r I x →L[𝕜] Tensor0SSpace (s + 1) I x from α x) gtilde)
      (fun i => sL (@Fin.cons s (fun _ => E) Xtilde w i))
  congr 1
  funext i
  refine Fin.cases ?_ ?_ i
  · change X x = sL Xtilde
    have h := (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
      (R := 𝕜) hx (X x)
    have hcl : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt 𝕜 x (X x)
        = Xtilde := by
      change (trivializationAt E (TangentSpace I) x₀).linearMapAt 𝕜 x (X x) = _
      rw [(trivializationAt E (TangentSpace I) x₀).coe_linearMapAt_of_mem (R := 𝕜) hx]
    rw [hcl] at h
    exact h.symm
  · intro j
    rfl

noncomputable def contractContravariantFieldFun (r s : ℕ)
    (α : (x : M) → TensorRSSpace (r + 1) s I x)
    (φ : (x : M) → Tensor0SSpace 1 I x) :
    (x : M) → TensorRSSpace r s I x :=
  fun x => contractContravariant r s x (φ x) (α x)

noncomputable def contractContravariantField (r s : ℕ)
    (α : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) (r + 1) s)
    (φ : Tensor0SField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) 1) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s := by
  letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (r + 1) s
  letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) 1
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s
  letI := tensor0SBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (r + 1)
  refine ⟨contractContravariantFieldFun r s (fun x => α x) (fun x => φ x), ?_⟩
  intro x₀
  rw [contMDiffAt_section]
  have hα := α.contMDiff x₀
  rw [contMDiffAt_section] at hα
  have hφ := φ.contMDiff x₀
  rw [contMDiffAt_section] at hφ
  let biop_ctr :
      Tensor0SModel 1 𝕜 E →L[𝕜] (TensorRSModel (r + 1) s 𝕜 E →L[𝕜] TensorRSModel r s 𝕜 E) :=
    (ContinuousLinearMap.compL 𝕜
      (Tensor0SModel r 𝕜 E) (Tensor0SModel (r + 1) 𝕜 E) (Tensor0SModel s 𝕜 E)).flip.comp
      (model_tensorWithCovector_bilinear r)
  have h_combine :
      ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E) n
        (fun x => biop_ctr
          ((trivializationAt (Tensor0SModel 1 𝕜 E)
            (fun x => Tensor0SSpace 1 I x) x₀ ⟨x, φ x⟩).2)
          ((trivializationAt (TensorRSModel (r + 1) s 𝕜 E)
            (fun x => TensorRSSpace (r + 1) s I x) x₀ ⟨x, α x⟩).2)) x₀ :=
    contMDiffAt_clm_apply₂ (I := I) (n := n) biop_ctr hφ hα
  refine h_combine.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx
  refine ContinuousLinearMap.ext fun β => ?_
  refine ContinuousMultilinearMap.ext fun v => ?_
  set β_symm : Tensor0SSpace r I x :=
    (trivializationAt (Tensor0SModel r 𝕜 E) (fun x => Tensor0SSpace r I x) x₀).symmL 𝕜 x β
    with hβ_symm
  set atilde_x : Tensor0SModel 1 𝕜 E :=
    (trivializationAt (Tensor0SModel 1 𝕜 E) (fun x => Tensor0SSpace 1 I x) x₀ ⟨x, φ x⟩).2
    with hatilde_x
  rw [TensorRSSpace.trivializationAt_apply (𝕜 := 𝕜) (I := I)
    (x₀ := x₀) (x := x) r s hx]
  unfold contractContravariantFieldFun contractContravariant
  simp only [ContinuousLinearMap.comp_apply]
  rw [tensorRSSpace_continuousLinearEquiv_symm_toContinuousLinearMap_apply_apply]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply]
  change tensorRSSpaceContinuousLinearEquiv (I := I) (r + 1) s x (α x)
      (modelTensorWithCovector r (Tensor0SSpace.toModel (I := I) (M := M) (φ x))
        (Tensor0SSpace.toModel (I := I) (M := M) β_symm))
      (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
        ((trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x (v i))) = _
  rw [tensorRSSpace_continuousLinearEquiv_apply_apply]
  have hrhs :
      (((biop_ctr atilde_x)
        (trivializationAt (TensorRSModel (r + 1) s 𝕜 E)
          (fun x => TensorRSSpace (r + 1) s I x) x₀ ⟨x, α x⟩).2) β) v =
        (trivializationAt (TensorRSModel (r + 1) s 𝕜 E)
          (fun x => TensorRSSpace (r + 1) s I x) x₀ ⟨x, α x⟩).2
          (modelTensorWithCovector r atilde_x β) v := by
    rfl
  rw [hrhs, TensorRSSpace.trivializationAt_apply (𝕜 := 𝕜) (I := I)
    (x₀ := x₀) (x := x) (r + 1) s hx]
  have hinput :
      (tensor0SSpaceContinuousLinearEquiv (I := I) (M := M) (r + 1) x).symm
          (modelTensorWithCovector r (Tensor0SSpace.toModel (I := I) (M := M) (φ x))
            (Tensor0SSpace.toModel (I := I) (M := M) β_symm)) =
        (trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
          (fun x => Tensor0SSpace (r + 1) I x) x₀).symmL 𝕜 x
          (modelTensorWithCovector r atilde_x β) := by
    apply (tensor0SSpaceFiberContinuousLinearEquiv (I := I) (r + 1) x).injective
    refine ContinuousMultilinearMap.ext fun w => ?_
    rw [tensor0SSpaceFiberContinuousLinearEquiv_model_symm_apply]
    have hrhs :
        tensor0SSpaceFiberContinuousLinearEquiv (I := I) (r + 1) x
          ((trivializationAt (Tensor0SModel (r + 1) 𝕜 E)
            (fun x => Tensor0SSpace (r + 1) I x) x₀).symmL 𝕜 x
            ((modelTensorWithCovector r atilde_x) β)) w =
          ((modelTensorWithCovector r atilde_x) β)
            (fun i => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt
              𝕜 x (w i)) := by
      rw [tensor0SSpaceFiberContinuousLinearEquiv_apply_apply]
      exact tensor0STrivialization_symmL_apply (I := I) (r + 1) x₀ x hx
        ((modelTensorWithCovector r atilde_x) β) w
    refine Eq.trans ?_ hrhs.symm
    change (Bundle.continuousMultilinearMap.modelProduct r 1
        (Tensor0SSpace.toModel (I := I) (M := M) β_symm)
        (Tensor0SSpace.toModel (I := I) (M := M) (φ x)))
          (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (w i)) =
      Bundle.continuousMultilinearMap.modelProduct r 1 β atilde_x
        (fun i => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt
          𝕜 x (w i))
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    rw [Bundle.continuousMultilinearMap.modelProduct_apply]
    congr 1
    · rw [Tensor0SSpace.toModel_apply_model_vector]
      rw [hβ_symm]
      exact tensor0STrivialization_symmL_apply (I := I) r x₀ x hx β
        (w ∘ Fin.castAdd 1)
    · rw [Tensor0SSpace.toModel_apply_model_vector]
      rw [hatilde_x, Tensor0SSpace.trivializationAt_apply (𝕜 := 𝕜) (I := I)
        (x₀ := x₀) (x := x) 1]
      congr 1
      funext i
      change w (Fin.natAdd r i) =
        (trivializationAt E (TangentSpace I) x₀).symmL 𝕜 x
          ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt
            𝕜 x (w (Fin.natAdd r i)))
      exact ((trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt
        (R := 𝕜) hx (w (Fin.natAdd r i))).symm
  rw [hinput]
  congr 1

noncomputable def contractTensorRSFieldFun (r s : ℕ)
    (T : (x : M) → TensorRSSpace (1 + r) (s + 1) I x) :
    (x : M) → TensorRSSpace r s I x :=
  fun x => contractTrace r s x (T x)

noncomputable def contractTensorRSField (r s : ℕ)
    (T : TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n)
      (1 + r) (s + 1)) :
    TensorRSField (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (n := n) r s := by
  letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) (1 + r) (s + 1)
  letI := tensorRSBundleTopology (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s
  refine ⟨contractTensorRSFieldFun r s (fun x => T x), ?_⟩
  intro x₀
  rw [contMDiffAt_section]
  have hT := T.contMDiff x₀
  rw [contMDiffAt_section] at hT
  have hTrace :
      ContMDiffAt I 𝓘(𝕜, TensorRSModel r s 𝕜 E) n
        (fun x => modelContractTrace (𝕜 := 𝕜) (E := E) r s
          ((trivializationAt (TensorRSModel (1 + r) (s + 1) 𝕜 E)
            (fun x => TensorRSSpace (1 + r) (s + 1) I x) x₀ ⟨x, T x⟩).2)) x₀ :=
    (modelContractTrace (𝕜 := 𝕜) (E := E) r s).contMDiffAt.comp x₀ hT
  refine hTrace.congr_of_eventuallyEq ?_
  have hbase := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt _ _ x₀)
  filter_upwards [hbase] with x hx
  exact contract_trace_trivialization_eq
    (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M)
    (r := r) (s := s) (x₀ := x₀) (x := x) hx (T x)

end FieldContraction

end
end Tensor0SBundle
end DifferentialGeometry
