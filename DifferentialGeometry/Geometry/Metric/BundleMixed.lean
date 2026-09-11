import DifferentialGeometry.Geometry.Metric.BundleMultilinear
import DifferentialGeometry.Tensor.Mixed.Multilinear

noncomputable section

namespace ContinuousLinearMap

variable {U W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup W] [InnerProductSpace ℝ W]

private theorem hilbertSchmidtInner_smulRight_innerSL (u v : U) (w z : W) :
    hilbertSchmidtInner ((innerSL ℝ u).smulRight w) ((innerSL ℝ v).smulRight z) =
      inner ℝ u v * inner ℝ w z := by
  let b := stdOrthonormalBasis ℝ U
  rw [hilbertSchmidtInner_eq_sum b]
  simp only [smulRight_apply, innerSL_apply_apply, real_inner_smul_left, real_inner_smul_right]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  simpa only [real_inner_comm, mul_comm] using b.sum_inner_mul_inner u v

end ContinuousLinearMap

namespace Bundle

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

def mixedRiemannianMetric (r s : ℕ) :
    RiemannianMetric (fun x => Bundle.continuousMultilinearMap ℝ r F V x →L[ℝ]
      Bundle.continuousMultilinearMap ℝ s F V x) := by
  let U := Bundle.continuousMultilinearMap ℝ r F V
  let W := Bundle.continuousMultilinearMap ℝ s F V
  let _ : RiemannianBundle U := ⟨multilinearRiemannianMetric (F := F) V r⟩
  let nr : ∀ y, NormedAddCommGroup (U y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := U) y
  let _ : ∀ y, SeminormedAddCommGroup (U y) := fun y => (nr y).toSeminormedAddCommGroup
  let _ : ∀ y, InnerProductSpace ℝ (U y) := fun y => Bundle.instInnerProductSpaceReal (E := U) y
  let _ : RiemannianBundle W := ⟨multilinearRiemannianMetric (F := F) V s⟩
  let ns : ∀ y, NormedAddCommGroup (W y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := W) y
  let _ : ∀ y, SeminormedAddCommGroup (W y) := fun y => (ns y).toSeminormedAddCommGroup
  let _ : ∀ y, InnerProductSpace ℝ (W y) := fun y => Bundle.instInnerProductSpaceReal (E := W) y
  let _ : ∀ y, FiniteDimensional ℝ (U y) := fun y =>
    VectorBundle.finiteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin r => F) ℝ) U y
  exact homRiemannianMetric U W

theorem mixedRiemannianMetric_inner_smulRight (r s : ℕ) (x : B)
    (u v : Fin r → V x) (α β : Fin s → V x →L[ℝ] ℝ) :
    letI : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
    (mixedRiemannianMetric (F := F) (V := V) r s).inner x
      (((multilinearRiemannianMetric (F := F) V r).inner x
        (ContinuousMultilinearMap.tensorOfDualLinearForms ℝ (V x) r
          (fun i => innerSL ℝ (u i)))).smulRight
          (ContinuousMultilinearMap.tensorOfDualLinearForms ℝ (V x) s α))
      (((multilinearRiemannianMetric (F := F) V r).inner x
        (ContinuousMultilinearMap.tensorOfDualLinearForms ℝ (V x) r
          (fun i => innerSL ℝ (v i)))).smulRight
          (ContinuousMultilinearMap.tensorOfDualLinearForms ℝ (V x) s β)) =
      (∏ i, inner ℝ (u i) (v i)) *
        ∏ j, ContinuousLinearMap.hilbertSchmidtInner (α j) (β j) := by
  let U := Bundle.continuousMultilinearMap ℝ r F V
  let W := Bundle.continuousMultilinearMap ℝ s F V
  let _ : RiemannianBundle U := ⟨multilinearRiemannianMetric (F := F) V r⟩
  let nr : ∀ y, NormedAddCommGroup (U y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := U) y
  let _ : ∀ y, SeminormedAddCommGroup (U y) := fun y => (nr y).toSeminormedAddCommGroup
  let _ : ∀ y, InnerProductSpace ℝ (U y) := fun y => Bundle.instInnerProductSpaceReal (E := U) y
  let _ : RiemannianBundle W := ⟨multilinearRiemannianMetric (F := F) V s⟩
  let ns : ∀ y, NormedAddCommGroup (W y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := W) y
  let _ : ∀ y, SeminormedAddCommGroup (W y) := fun y => (ns y).toSeminormedAddCommGroup
  let _ : ∀ y, InnerProductSpace ℝ (W y) := fun y => Bundle.instInnerProductSpaceReal (E := W) y
  let _ : ∀ y, FiniteDimensional ℝ (U y) := fun y =>
    VectorBundle.finiteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin r => F) ℝ) U y
  let _ : FiniteDimensional ℝ (V x) := VectorBundle.finiteDimensional ℝ F V x
  change ContinuousLinearMap.hilbertSchmidtInner
    ((innerSL ℝ _).smulRight _) ((innerSL ℝ _).smulRight _) = _
  rw [ContinuousLinearMap.hilbertSchmidtInner_smulRight_innerSL]
  change (multilinearRiemannianMetric (F := F) V r).inner x _ _ *
    (multilinearRiemannianMetric (F := F) V s).inner x _ _ = _
  rw [multilinearRiemannianMetric_inner_tensorOfInnerSL,
    multilinearRiemannianMetric_inner_tensorOfDualLinearForms]
  simp only [ContinuousMultilinearMap.tensorOfDualLinearForms_apply, innerSL_apply_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact real_inner_comm _ _

theorem mixedMultilinearFiberEquiv_smulRight_tensorOfInnerSL (r s : ℕ) (x : B)
    (u : Fin r → V x) (α : Fin s → V x →L[ℝ] ℝ)
    (v : Fin s → V x) (β : Fin r → V x →L[ℝ] ℝ) :
    Bundle.continuousMultilinearMap.mixedMultilinearFiberEquiv
        (𝕜 := ℝ) (F := F) (V := V) r s x
      (((multilinearRiemannianMetric (F := F) V r).inner x
        (ContinuousMultilinearMap.tensorOfDualLinearForms ℝ (V x) r
          (fun i => innerSL ℝ (u i)))).smulRight
          (ContinuousMultilinearMap.tensorOfDualLinearForms ℝ (V x) s α)) v β =
      (∏ i, β i (u i)) * ∏ j, α j (v j) := by
  rw [Bundle.continuousMultilinearMap.mixedMultilinearFiberEquiv_apply]
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply,
    smul_eq_mul, multilinearRiemannianMetric_inner_tensorOfInnerSL,
    ContinuousMultilinearMap.tensorOfDualLinearForms_apply]

end Bundle
