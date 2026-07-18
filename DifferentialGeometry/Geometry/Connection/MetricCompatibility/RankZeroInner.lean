import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel
import DifferentialGeometry.Geometry.Metric.PointwiseInner.SlotPermutation
import DifferentialGeometry.Tensor.RSTensor.RankZero










noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]



lemma inner_nat_cast
    (g : SmoothRiemannianMetric I M) (x : M) {a b : ℕ} (h : a = b)
    (A B : ContinuousMultilinearMap ℝ (fun _ : Fin b => E) ℝ) :
    covariantTensorInnerPointwise (I := I) (M := M) a g x
        (A.domDomCongr (finCongr h.symm))
        (B.domDomCongr (finCongr h.symm)) =
      covariantTensorInnerPointwise (I := I) (M := M) b g x A B := by
  subst a
  simpa only [finCongr_refl] using
    (tensorInnerPointwise_0s_domDomCongr (I := I) (M := M) g x b
      (Equiv.refl (Fin b)) A B)



lemma lower_toRS0
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A : Tensor0SSpace s I x) :
    lowerAllUpperIndices (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (Tensor0SSpace.toRS0 A)) =
      (Tensor0SSpace.toModel A).domDomCongr
        (finCongr (Nat.zero_add s).symm) := by
  apply ContinuousMultilinearMap.ext
  intro v
  rw [lowerAllUpperIndices_apply, separableFormAt_zero]
  have hunit_model : Tensor0SSpace.toModel
      (Tensor0SSpace.ofModel (I := I) (x := x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) =
      ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ) := by
    rw [Tensor0SSpace.toModel_ofModel]
  rw [← hunit_model]
  rw [← toModel_tensorRS_apply (I := I) (M := M) 0 s x
    (Tensor0SSpace.toRS0 A)
    (Tensor0SSpace.ofModel (I := I) (x := x)
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))]
  rw [Tensor0SSpace.toRS0_apply]
  have hone : tensor0SSpace_evalScalar x
      (Tensor0SSpace.ofModel (I := I) (x := x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))) = 1 := by
    rw [Tensor0SSpace.evalScalar_apply]
    change Tensor0SSpace.toModel
      (Tensor0SSpace.ofModel (I := I) (x := x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)))
        Fin.elim0 = 1
    rw [Tensor0SSpace.toModel_ofModel]
    rfl
  rw [hone, one_smul]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  congr 1
  funext j
  congr 1
  exact (Fin.ext (by simp)).symm



lemma inner_toRS0
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (A B : Tensor0SSpace s I x) :
    tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (Tensor0SSpace.toRS0 A))
        (TensorRSSpace.toModel (Tensor0SSpace.toRS0 B)) =
      covariantTensorInnerPointwise (I := I) (M := M) s g x
        (Tensor0SSpace.toModel A) (Tensor0SSpace.toModel B) := by
  rw [show tensorInnerPointwise (I := I) (M := M) g 0 s x
      (TensorRSSpace.toModel (Tensor0SSpace.toRS0 A))
      (TensorRSSpace.toModel (Tensor0SSpace.toRS0 B)) =
        covariantTensorInnerPointwise (I := I) (M := M) (0 + s) g x
          (lowerAllUpperIndices (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (Tensor0SSpace.toRS0 A)))
          (lowerAllUpperIndices (I := I) (M := M) g 0 s x
            (TensorRSSpace.toModel (Tensor0SSpace.toRS0 B))) from rfl]
  rw [lower_toRS0 (I := I) (M := M) g s x A,
    lower_toRS0 (I := I) (M := M) g s x B]
  exact inner_nat_cast (I := I) (M := M) g x (Nat.zero_add s)
    (Tensor0SSpace.toModel A) (Tensor0SSpace.toModel B)



lemma inner_toRS0_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (A B : Tensor0SSpace 0 I x) :
    tensorInnerPointwise (I := I) (M := M) g 0 0 x
        (TensorRSSpace.toModel (Tensor0SSpace.toRS0 A))
        (TensorRSSpace.toModel (Tensor0SSpace.toRS0 B)) =
      tensor0SSpace_evalScalar x A * tensor0SSpace_evalScalar x B := by
  rw [inner_toRS0 (I := I) (M := M) g 0 x,
    tensorInnerPointwise_0s_zero_arity,
    Tensor0SSpace.evalScalar_apply, Tensor0SSpace.evalScalar_apply]
  rfl



lemma inner_toRS0_scalar
    (g : SmoothRiemannianMetric I M) (x : M) (a b : ℝ) :
    tensorInnerPointwise (I := I) (M := M) g 0 0 x
        (TensorRSSpace.toModel
          (Tensor0SSpace.toRS0 ((Tensor0SNabla.tensor0Iso I M x).symm a)))
        (TensorRSSpace.toModel
          (Tensor0SSpace.toRS0 ((Tensor0SNabla.tensor0Iso I M x).symm b))) =
      a * b := by
  rw [inner_toRS0_zero (I := I) (M := M) g x]
  change Tensor0SNabla.tensor0Iso I M x ((Tensor0SNabla.tensor0Iso I M x).symm a) *
    Tensor0SNabla.tensor0Iso I M x ((Tensor0SNabla.tensor0Iso I M x).symm b) = a * b
  rw [ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]



private theorem sum_fin_succ_fun_local {Idx : Type*} [Fintype Idx]
    {α : Type*} [AddCommMonoid α] (s : Nat)
    (F : (Fin (s + 1) → Idx) → α) :
    (∑ I0 : Fin (s + 1) → Idx, F I0) =
      ∑ i : Idx, ∑ tail : Fin s → Idx, F (Fin.cons i tail) := by
  classical
  rw [Fintype.sum_equiv
    (Fin.consEquiv (fun _ : Fin (s + 1) => Idx)).symm
    F (fun p : Idx × (Fin s → Idx) => F (Fin.cons p.1 p.2))]
  · rw [Fintype.sum_prod_type]
  · intro I0
    congr 1
    exact (Fin.cons_self_tail I0).symm



private theorem coordInner0S_zero_local {Idx : Type*} [Fintype Idx] {x : M}
    (gInv : Idx → Idx → ℝ)
    (A B : Tensor0SSpace 0 I x)
    (basis : Module.Basis Idx ℝ (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) 0 gInv A B basis =
      A Fin.elim0 * B Fin.elim0 := by
  classical
  unfold coordInner0S tensor0SComponent
  simp only [Finset.univ_unique, Finset.univ_eq_empty, Finset.prod_empty, one_mul,
    Finset.sum_singleton]
  congr <;> funext a <;> exact Fin.elim0 a



private theorem coordInner0S_succ_summand_local
    {Idx : Type*} {x : M} (s : Nat)
    (gInv : Idx → Idx → ℝ)
    (A B : Tensor0SSpace (s + 1) I x)
    (basis : Module.Basis Idx ℝ (TangentSpace I x))
    (i j : Idx) (tailI tailJ : Fin s → Idx) :
    ((∏ a : Fin (s + 1),
        gInv (((Fin.cons i tailI : Fin (s + 1) → Idx) a))
          (((Fin.cons j tailJ : Fin (s + 1) → Idx) a))) *
        A (fun a : Fin (s + 1) =>
          basis (((Fin.cons i tailI : Fin (s + 1) → Idx) a)))) *
      B (fun a : Fin (s + 1) =>
        basis (((Fin.cons j tailJ : Fin (s + 1) → Idx) a))) =
      (gInv i j * (∏ a : Fin s, gInv (tailI a) (tailJ a)) *
          ((tensor0S_curry (I := I) (𝕜 := ℝ) (M := M) s x A) (basis i))
            (fun a : Fin s => basis (tailI a))) *
        ((tensor0S_curry (I := I) (𝕜 := ℝ) (M := M) s x B) (basis j))
          (fun a : Fin s => basis (tailJ a)) := by
  rw [Fin.prod_univ_succ]
  rw [tensor0S_curry_apply_cons, tensor0S_curry_apply_cons]
  have hA :
      (fun a : Fin (s + 1) =>
          basis (((Fin.cons i tailI : Fin (s + 1) → Idx) a))) =
        Fin.cons (basis i) (fun a : Fin s => basis (tailI a)) := by
    funext a
    cases a using Fin.cases <;> simp
  have hB :
      (fun a : Fin (s + 1) =>
          basis (((Fin.cons j tailJ : Fin (s + 1) → Idx) a))) =
        Fin.cons (basis j) (fun a : Fin s => basis (tailJ a)) := by
    funext a
    cases a using Fin.cases <;> simp
  rw [hA, hB]
  simp [Fin.cons_zero, Fin.cons_succ]



set_option maxHeartbeats 800000 in
private theorem coordInner0S_succ_local
    {Idx : Type*} [Fintype Idx] {x : M} (s : Nat)
    (gInv : Idx → Idx → ℝ)
    (A B : Tensor0SSpace (s + 1) I x)
    (basis : Module.Basis Idx ℝ (TangentSpace I x)) :
    coordInner0S (I := I) (x := x) (s + 1) gInv A B basis =
      ∑ i : Idx, ∑ j : Idx,
        gInv i j *
          coordInner0S (I := I) (x := x) s gInv
            ((tensor0S_curry (I := I) (𝕜 := ℝ) (M := M) s x A) (basis i))
            ((tensor0S_curry (I := I) (𝕜 := ℝ) (M := M) s x B) (basis j))
            basis := by
  classical
  unfold coordInner0S tensor0SComponent
  rw [sum_fin_succ_fun_local s]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ tailI : Fin s → Idx,
        ∑ J0 : Fin (s + 1) → Idx,
          ((∏ a : Fin (s + 1),
              gInv (((Fin.cons i tailI : Fin (s + 1) → Idx) a)) (J0 a)) *
              A (fun a : Fin (s + 1) =>
                basis (((Fin.cons i tailI : Fin (s + 1) → Idx) a)))) *
            B (fun a : Fin (s + 1) => basis (J0 a)))
        =
        ∑ tailI : Fin s → Idx, ∑ j : Idx, ∑ tailJ : Fin s → Idx,
          ((∏ a : Fin (s + 1),
              gInv (((Fin.cons i tailI : Fin (s + 1) → Idx) a))
                (((Fin.cons j tailJ : Fin (s + 1) → Idx) a))) *
              A (fun a : Fin (s + 1) =>
                basis (((Fin.cons i tailI : Fin (s + 1) → Idx) a)))) *
            B (fun a : Fin (s + 1) =>
              basis (((Fin.cons j tailJ : Fin (s + 1) → Idx) a))) := by
          apply Finset.sum_congr rfl
          intro tailI _
          rw [sum_fin_succ_fun_local s]
    _ =
        ∑ tailI : Fin s → Idx, ∑ j : Idx, ∑ tailJ : Fin s → Idx,
          (gInv i j * (∏ a : Fin s, gInv (tailI a) (tailJ a)) *
              ((tensor0S_curry (I := I) (𝕜 := ℝ) (M := M) s x A) (basis i))
                (fun a : Fin s => basis (tailI a))) *
            ((tensor0S_curry (I := I) (𝕜 := ℝ) (M := M) s x B) (basis j))
              (fun a : Fin s => basis (tailJ a)) := by
          apply Finset.sum_congr rfl
          intro tailI _
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro tailJ _
          exact coordInner0S_succ_summand_local (I := I) s gInv A B basis i j tailI tailJ
    _ =
        ∑ j : Idx, ∑ tailI : Fin s → Idx, ∑ tailJ : Fin s → Idx,
          (gInv i j * (∏ a : Fin s, gInv (tailI a) (tailJ a)) *
              ((tensor0S_curry (I := I) (𝕜 := ℝ) (M := M) s x A) (basis i))
                (fun a : Fin s => basis (tailI a))) *
            ((tensor0S_curry (I := I) (𝕜 := ℝ) (M := M) s x B) (basis j))
              (fun a : Fin s => basis (tailJ a)) := by
          rw [Finset.sum_comm]
    _ =
        ∑ j : Idx,
          gInv i j *
            ∑ tailI : Fin s → Idx, ∑ tailJ : Fin s → Idx,
              (∏ a : Fin s, gInv (tailI a) (tailJ a)) *
                ((tensor0S_curry (I := I) (𝕜 := ℝ) (M := M) s x A) (basis i))
                  (fun a : Fin s => basis (tailI a)) *
                  ((tensor0S_curry (I := I) (𝕜 := ℝ) (M := M) s x B) (basis j))
                    (fun a : Fin s => basis (tailJ a)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro tailI _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro tailJ _
          ring



private lemma covariant_toModel_eq_coordInner0S
    (g : SmoothRiemannianMetric I M) (x : M)
    (basisT : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hb : ∀ i, basisT i = (chartModelBasis E) i) :
    ∀ (s : ℕ) (A B : Tensor0SSpace s I x),
      covariantTensorInnerPointwise (I := I) (M := M) s g x
          (Tensor0SSpace.toModel A) (Tensor0SSpace.toModel B) =
        coordInner0S (I := I) (x := x) s
          (fun i j => (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j) A B basisT := by
  intro s
  induction s with
  | zero =>
      intro A B
      rw [tensorInnerPointwise_0s_zero_arity, coordInner0S_zero_local]
      rfl
  | succ s ih =>
      intro A B
      rw [tensorInnerPointwise_0s_succ, coordInner0S_succ_local]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [← ih (tensor0S_curry (I := I) (𝕜 := ℝ) (M := M) s x A (basisT i))
            (tensor0S_curry (I := I) (𝕜 := ℝ) (M := M) s x B (basisT j))]
      rw [toModel_tensor0S_curry_eq_curryLeft, toModel_tensor0S_curry_eq_curryLeft,
        hb i, hb j]



theorem inner0S_eq_covariantTensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (A B : Tensor0SSpace s I x) :
    inner0S (I := I) g x s A B =
      covariantTensorInnerPointwise (I := I) (M := M) s g x
        (Tensor0SSpace.toModel A) (Tensor0SSpace.toModel B) := by
  classical
  set basisT : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    (chartModelBasis E) with hbasisT
  have hb : ∀ i, basisT i = (chartModelBasis E) i := fun _ => rfl
  have hgSym : ∀ i k : Fin (Module.finrank ℝ E),
      g.inner x (basisT i) (basisT k) = gramMatrixAt (I := I) (M := M) g x i k :=
    fun i k => by rw [hb i, hb k, ← gramMatrixAt_apply]
  have hinv : MetricInverseInBasis (I := I) g x basisT
      (fun i j => (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j) := by
    intro i j
    refine ⟨?_, ?_⟩
    · have h1 :
          (∑ k : Fin (Module.finrank ℝ E),
              (fun i j => (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j) i k *
                g.inner x (basisT k) (basisT j)) =
            (((gramMatrixAt (I := I) (M := M) g x)⁻¹) *
              (gramMatrixAt (I := I) (M := M) g x)) i j := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun k _ => by rw [hgSym k j])
      rw [h1, gramMatrixAt_inv_mul_self, Matrix.one_apply]
    · have hmulinv : (gramMatrixAt (I := I) (M := M) g x) *
          (gramMatrixAt (I := I) (M := M) g x)⁻¹ = 1 :=
        Matrix.mul_nonsing_inv _
          (Matrix.isUnit_iff_isUnit_det _ |>.mp
            (gramMatrixAt_isUnit (I := I) (M := M) g x))
      have h2 :
          (∑ k : Fin (Module.finrank ℝ E),
              g.inner x (basisT i) (basisT k) *
                (fun i j => (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j) k j) =
            ((gramMatrixAt (I := I) (M := M) g x) *
              (gramMatrixAt (I := I) (M := M) g x)⁻¹) i j := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun k _ => by rw [hgSym i k])
      rw [h2, hmulinv, Matrix.one_apply]
  rw [inner0S_eq_coord (I := I) g x s basisT
    (fun i j => (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j) hinv A B]
  exact (covariant_toModel_eq_coordInner0S (I := I) g x basisT hb s A B).symm



theorem normSq0S_eq_tensorInnerPointwise_toRS0
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (A : Tensor0SSpace s I x) :
    normSq0S (I := I) g x s A =
      tensorInnerPointwise (I := I) (M := M) g 0 s x
        (TensorRSSpace.toModel (Tensor0SSpace.toRS0 A))
        (TensorRSSpace.toModel (Tensor0SSpace.toRS0 A)) := by
  rw [inner_toRS0 (I := I) (M := M) g s x A A, normSq0S_eq_inner]
  exact inner0S_eq_covariantTensorInnerPointwise (I := I) g x s A A



end Connection
end Integral
end DifferentialGeometry

end
