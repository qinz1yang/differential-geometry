import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRS.Basic
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetric
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.TensorLoweringParallel
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace Tensor
namespace RSTensor

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.TensorMetricLowering DifferentialGeometry.Tensor0SNabla
    DifferentialGeometry.TensorRSNabla
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

omit [T2Space M] in
noncomputable def lowerAllSpace
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : TensorRSSpace r s I x) : Tensor0SSpace (r + s) I x :=
  Tensor0SSpace.ofModel
    (lowerAllUpperIndices (I := I) (M := M) g r s x (TensorRSSpace.toModel A))

omit [T2Space M] in
theorem lowerAllSpace_eval
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (A : TensorRSSpace r s I x) (v : Fin (r + s) → TangentSpace I x) :
    Tensor0SSpace.eval (lowerAllSpace g r s x A) v =
      TensorRSSpace.toModel A
        (separableFormAt (I := I) (M := M) g x r
          (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v (Fin.castAdd s i))))
        (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x (v (Fin.natAdd r j))) := by
  rw [Tensor0SSpace.eval_eq]
  calc
    lowerAllSpace g r s x A v =
        Tensor0SSpace.toModel (lowerAllSpace g r s x A)
          (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)) := by
      symm
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using
        (Tensor0SSpace.toModel_apply_model_vector
          (T := lowerAllSpace g r s x A)
          (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (v i)))
    _ = _ := by
      rw [lowerAllSpace, Tensor0SSpace.toModel_ofModel, lowerAllUpperIndices_apply]

omit [T2Space M] in
theorem normSqRS_eq_normSq0S_lowerAllSpace
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M) (r s : ℕ)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv : MetricInverseInBasisGen (I := I) g x basis (identityInvMetric (Idx := Idx)))
    (A : TensorRSSpace r s I x) :
    normSqRS (I := I) (g := g) (x := x) r s A =
      normSq0S (I := I) g x (r + s) (lowerAllSpace g r s x A) := by
  classical
  rw [normSqRS_identity_eq_componentL2SqRS (I := I) g x r s basis hinv A,
    normSq0S_identity_eq_sum_sq (I := I) g x (r + s) basis hinv (lowerAllSpace g r s x A)]
  unfold componentL2SqRS
  have hbij :
      (∑ slots : Fin (r + s) → Idx,
          component0S (I := I) basis (lowerAllSpace g r s x A) slots ^ 2) =
        ∑ up : Fin r → Idx, ∑ low : Fin s → Idx,
          component0S (I := I) basis (lowerAllSpace g r s x A) (Fin.append up low) ^ 2 := by
    rw [show (∑ up : Fin r → Idx, ∑ low : Fin s → Idx,
            component0S (I := I) basis (lowerAllSpace g r s x A) (Fin.append up low) ^ 2)
          = ∑ p : (Fin r → Idx) × (Fin s → Idx),
            component0S (I := I) basis (lowerAllSpace g r s x A) (Fin.append p.1 p.2) ^ 2 from
      (Fintype.sum_prod_type (fun p : (Fin r → Idx) × (Fin s → Idx) =>
        component0S (I := I) basis (lowerAllSpace g r s x A) (Fin.append p.1 p.2) ^ 2)).symm]
    refine Fintype.sum_equiv
      { toFun := fun slots => (fun i => slots (Fin.castAdd s i), fun j => slots (Fin.natAdd r j))
        invFun := fun p => Fin.append p.1 p.2
        left_inv := fun slots => by
          funext k
          refine Fin.addCases (fun i => ?_) (fun j => ?_) k
          · simp [Fin.append_left]
          · simp [Fin.append_right]
        right_inv := fun p => by
          refine Prod.ext ?_ ?_
          · funext i; simp [Fin.append_left]
          · funext j; simp [Fin.append_right] } _ _ ?_
    intro slots
    refine congrArg (fun t => component0S (I := I) basis (lowerAllSpace g r s x A) t ^ 2) ?_
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp [Fin.append_left]
    · simp [Fin.append_right]
  rw [hbij]
  refine Finset.sum_congr rfl fun up _ => Finset.sum_congr rfl fun low _ => ?_
  congr 1
  have hgram : ∀ i j : Idx, g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0 := by
    intro i j
    have hsum : (∑ k : Idx, identityInvMetric (Idx := Idx) i k * g.inner x (basis k) (basis j))
        = g.inner x (basis i) (basis j) := by
      rw [Finset.sum_eq_single i]
      · rw [identityInvMetric_apply_self, one_mul]
      · intro k _ hk
        rw [show identityInvMetric (Idx := Idx) i k = 0 from
          diagonalInvMetric_eq_zero_of_ne (Ne.symm hk), zero_mul]
      · intro hni; exact absurd (Finset.mem_univ i) hni
    rw [← hsum]; exact (hinv i j).1
  let e := tangentSpaceModelContinuousLinearEquiv (I := I) x
  have hsep : Tensor0SSpace.ofModel
      (separableFormAt (I := I) (M := M) g x r (fun i => e (basis (up i)))) =
      basisTensor0S (I := I) basis up := by
    apply ext0S_basis (I := I) basis
    intro jdx
    rw [component0S_apply, basisTensor0S_component]
    calc
      Tensor0SSpace.ofModel
          (separableFormAt (I := I) (M := M) g x r (fun i => e (basis (up i))))
          (fun a => basis (jdx a)) =
          separableFormAt (I := I) (M := M) g x r (fun i => e (basis (up i)))
            (fun a => e (basis (jdx a))) := by
        symm
        have h := Tensor0SSpace.toModel_apply_model_vector (𝕜 := ℝ) (I := I)
          (T := Tensor0SSpace.ofModel (I := I) (x := x)
            (separableFormAt (I := I) (M := M) g x r (fun i => e (basis (up i)))))
          (fun a => e (basis (jdx a)))
        rw [Tensor0SSpace.toModel_ofModel] at h
        simpa only [e, ContinuousLinearEquiv.symm_apply_apply] using h
      _ = ∏ i : Fin r, g.inner x (basis (up i)) (basis (jdx i)) := by
        rw [separableFormAt_apply]
        simp only [e, modelInnerAt_apply, ContinuousLinearEquiv.symm_apply_apply]
      _ = if up = jdx then (1 : Real) else 0 := by
        rw [Finset.prod_congr rfl (fun i _ => hgram (up i) (jdx i))]
        by_cases h : up = jdx
        · subst h; simp
        · rw [if_neg h]
          obtain ⟨i, hi⟩ := Function.ne_iff.mp h
          exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  rw [componentRS_apply_gen, component0S_apply]
  change A (basisTensor0S (I := I) basis up) (fun a => basis (low a)) =
    Tensor0SSpace.eval (lowerAllSpace g r s x A) (fun a => basis (Fin.append up low a))
  rw [lowerAllSpace_eval]
  simp only [Fin.append_left, Fin.append_right]
  have hsepModel :
      separableFormAt (I := I) (M := M) g x r (fun i => e (basis (up i))) =
        Tensor0SSpace.toModel (basisTensor0S (I := I) basis up) := by
    rw [← hsep, Tensor0SSpace.toModel_ofModel]
  rw [hsepModel, TensorRSSpace.toModel_apply_toModel]
  rw [Tensor0SSpace.toModel_apply_model_vector]
  simp only [ContinuousLinearEquiv.symm_apply_apply]

end RSTensor
end Tensor
end DifferentialGeometry
