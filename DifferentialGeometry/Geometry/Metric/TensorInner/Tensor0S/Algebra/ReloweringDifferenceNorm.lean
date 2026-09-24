import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.MetricDifference
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Algebra.ReloweringNorm
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle DifferentialGeometry.Tensor0SBundle
open _root_.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

variable [NeZero (Module.finrank Real E)]

omit [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem reLowerDefSq_le (g₁ g₂ : SmoothRiemannianMetric I M) {s : ℕ}
    (T : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (x : M) :
    normSq0S (I := I) g₁ x (s + 1)
        (reLower (I := I) g₂ g₁ T x - T x) ≤
      (Module.finrank Real E : Real) ^ (s + 3) *
        (normSq0S (I := I) g₁ x (s + 1) (T x) *
          metricDiffSq (I := I) g₁ g₂ x) := by
  classical
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g₁ x
  have hinv : MetricInverseInBasis (I := I) g₁ x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) :=
    DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g₁ basis hON
  let Hdiff : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2 :=
    metricTensorField (I := I) g₂ - metricTensorField (I := I) g₁
  let V : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1 + 2) x :=
    (Tensor0SSpace.product (T x) (Hdiff x)).domDomCongr
      (reLowerPermutationWithTwoInputs s)
  have hself : reLower (I := I) g₁ g₁ T x = T x := by
    refine ContinuousMultilinearMap.ext fun tail => ?_
    change Tensor0SSpace.eval (reLower (I := I) g₁ g₁ T x) tail =
      Tensor0SSpace.eval (T x) tail
    rw [reLower_apply (I := I) g₁ g₁ T x, sharpFlat_self]
    rw [Function.update_eq_self]
  have htrace : reLower (I := I) g₂ g₁ T x - T x =
      metricTraceFirstTwo0STensor (I := I) g₁ V := by
    rw [← hself]
    refine ContinuousMultilinearMap.ext fun tail => ?_
    change Tensor0SSpace.eval
        (reLower (I := I) g₂ g₁ T x - reLower (I := I) g₁ g₁ T x) tail =
      Tensor0SSpace.eval (metricTraceFirstTwo0STensor (I := I) g₁ V) tail
    have htraceBasis :
        Tensor0SSpace.eval (metricTraceFirstTwo0STensor (I := I) g₁ V) tail =
          metricTrace0S2InBasis (I := I) basis identityInvMetric V tail := by
      change metricTraceFirstTwo0STensor (I := I) g₁ V tail = _
      rw [metricTraceFirstTwo0STensor_apply,
        metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g₁ basis _ hinv]
    rw [Tensor0SSpace.eval_sub,
      reLower_eval (I := I) g₂ g₁ T basis _ hinv tail,
      reLower_eval (I := I) g₁ g₁ T basis _ hinv tail,
      htraceBasis]
    unfold metricTrace0S2InBasis
    change
      (∑ i, ∑ j, identityInvMetric i j *
          (Tensor0SSpace.eval (T x) (Function.update tail (Fin.last s) (basis i)) *
            g₂.inner x (basis j) (tail (Fin.last s)))) -
        (∑ i, ∑ j, identityInvMetric i j *
          (Tensor0SSpace.eval (T x) (Function.update tail (Fin.last s) (basis i)) *
            g₁.inner x (basis j) (tail (Fin.last s)))) =
      ∑ i, ∑ j, identityInvMetric i j *
        Tensor0SSpace.eval V (metricTraceInput (I := I) (basis i) (basis j) tail)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    change
      identityInvMetric i j *
          (Tensor0SSpace.eval (T x) (Function.update tail (Fin.last s) (basis i)) *
            g₂.inner x (basis j) (tail (Fin.last s))) -
        identityInvMetric i j *
          (Tensor0SSpace.eval (T x) (Function.update tail (Fin.last s) (basis i)) *
            g₁.inner x (basis j) (tail (Fin.last s))) =
      identityInvMetric i j *
        Tensor0SSpace.eval V (metricTraceInput (I := I) (basis i) (basis j) tail)
    rw [show V = (Tensor0SSpace.product (T x) (Hdiff x)).domDomCongr
      (reLowerPermutationWithTwoInputs s) from rfl,
      Tensor0SSpace.eval_domDomCongr]
    have hproduct := Tensor0SSpace.product_apply (T x) (Hdiff x)
      (metricTraceInput (I := I) (basis i) (basis j) tail ∘
        reLowerPermutationWithTwoInputs s)
    change Tensor0SSpace.eval (Tensor0SSpace.product (T x) (Hdiff x)) _ =
      Tensor0SSpace.eval (T x) _ * Tensor0SSpace.eval (Hdiff x) _ at hproduct
    rw [hproduct]
    have hfirst :
        ((metricTraceInput (I := I) (basis i) (basis j) tail ∘
          reLowerPermutationWithTwoInputs s) ∘ Fin.castAdd 2) =
            Function.update tail (Fin.last s) (basis i) := by
      funext k
      exact reLowerPermutationWithTwoInputs_first_block (I := I) (basis i) (basis j) tail k
    rw [hfirst]
    change
      _ = identityInvMetric i j *
        (T x (Function.update tail (Fin.last s) (basis i)) *
          ((metricTensorField (I := I) g₂ - metricTensorField (I := I) g₁) x)
            (fun p : Fin 2 =>
              metricTraceInput (I := I) (basis i) (basis j) tail
                (reLowerPermutationWithTwoInputs s (Fin.natAdd (s + 1) p))))
    have hsnd :
        (fun p : Fin 2 =>
          metricTraceInput (I := I) (basis i) (basis j) tail
            (reLowerPermutationWithTwoInputs s (Fin.natAdd (s + 1) p))) =
          fun p : Fin 2 => if p = 0 then basis j else tail (Fin.last s) := by
      funext p
      fin_cases p
      · simpa using reLowerPermutationWithTwoInputs_tail_zero (I := I) (basis i) (basis j) tail
      · simpa using reLowerPermutationWithTwoInputs_tail_one (I := I) (basis i) (basis j) tail
    have hHdiff :
        (metricTensorField (I := I) g₂ - metricTensorField (I := I) g₁) x =
          metricTensorField (I := I) g₂ x - metricTensorField (I := I) g₁ x := rfl
    rw [hsnd, hHdiff, Tensor0SSpace.sub_apply (I := I) 2 x,
      metricTensorField_apply, metricTensorField_apply]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [if_true, h10, if_false]
    rw [Tensor0SSpace.eval_eq]
    ring
  have hprod :
      normSq0S (I := I) g₁ x (s + 1 + 2)
          (Tensor0SSpace.product (T x) (Hdiff x)) =
        normSq0S (I := I) g₁ x (s + 1) (T x) *
          normSq0S (I := I) g₁ x 2 (Hdiff x) :=
    normSq0S_prod (I := I) g₁ x basis hinv (T x) (Hdiff x)
  have hcongr :
      normSq0S (I := I) g₁ x (s + 1 + 2) V =
        normSq0S (I := I) g₁ x (s + 1 + 2)
          (Tensor0SSpace.product (T x) (Hdiff x)) :=
    normSq0S_domDomCongr (I := I) g₁ x basis hinv (reLowerPermutationWithTwoInputs s) _
  have hH :
      normSq0S (I := I) g₁ x 2 (Hdiff x) = metricDiffSq (I := I) g₁ g₂ x := by
    rw [metricDiffSq_def]
    have heq : Hdiff x = -metricDiffAt (I := I) g₁ g₂ x := by
      dsimp [Hdiff, metricDiffAt]
      abel
    rw [heq, Tensor0SBundle.normSq0S_neg]
  rw [htrace]
  have htr := traceNormSq_le (I := I) (s := s + 1) g₁ x V
  rw [hcongr, hprod, hH] at htr
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htr


end DifferentialGeometry.PDE.RicciFlow

end
