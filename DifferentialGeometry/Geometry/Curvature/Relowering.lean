import DifferentialGeometry.Tensor.Metric.TraceDerivativeBounds
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.Algebra.ContractionLeibniz
import DifferentialGeometry.Geometry.Connection.MetricCompatibility.Tensor.Metric
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Tensor
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.Geometry.Curvature

private def lowerPerm : Fin 6 ≃ Fin 6 where
  toFun := ![2, 3, 4, 0, 1, 5]
  invFun := ![3, 4, 0, 1, 2, 5]
  left_inv := by decide
  right_inv := by decide

section Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [CompleteSpace E] [T2Space M] in
private theorem trace_orthonormal (G : SmoothRiemannianMetric I M)
    (T : Tensor0SField (I := I) (M := M) ∞ 6) (x : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I x))
    (hi : MetricInverseInBasis G x b (identityInvMetric (Idx := ι)))
    (w : Fin 4 → TangentSpace I x) :
    metricTraceFirstTwoField G T x w = ∑ i, T x (metricTraceInput (b i) (b i) w) := by
  erw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis G b (identityInvMetric (Idx := ι)) hi]
  simp only [metricTrace0S2InBasis, identityInvMetric, diagonalInvMetric,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem lower_product_eval (G g : SmoothRiemannianMetric I M)
    (x : M) (a b : TangentSpace I x) (w : Fin 4 → TangentSpace I x) :
    Tensor0SField.domDomCongr ∞ lowerPerm
      (tensor0SFieldProduct ∞
        (CovariantDerivative.rm04Section G (metricCov g) (metricCov_smooth g))
        (metricTensorField g)) x (metricTraceInput a b w) =
      G.inner x a
        (connectionRiemannCurvatureField (metricCov g)
          (CovariantDerivative.tangentConstAt (I := I) x (w 0)) (CovariantDerivative.tangentConstAt (I := I) x (w 1))
          (CovariantDerivative.tangentConstAt (I := I) x (w 2)) x) * g.inner x b (w 3) := by
  change tensor0SFieldProduct ∞
      (CovariantDerivative.rm04Section G (metricCov g) (metricCov_smooth g))
      (metricTensorField g) x (fun i => metricTraceInput a b w (lowerPerm i)) = _
  let S := CovariantDerivative.rm04Section G (metricCov g) (metricCov_smooth g)
  let V : Fin 6 → TangentSpace I x := fun i => metricTraceInput a b w (lowerPerm i)
  have he : V ∘ Fin.castAdd 2 = vec4 (w 0) (w 1) (w 2) a := by
    funext i
    fin_cases i <;> rfl
  have hs : S x (V ∘ Fin.castAdd 2) =
      G.inner x a
        (connectionRiemannCurvatureField (metricCov g)
          (CovariantDerivative.tangentConstAt (I := I) x (w 0))
          (CovariantDerivative.tangentConstAt (I := I) x (w 1))
          (CovariantDerivative.tangentConstAt (I := I) x (w 2)) x) := by
    rw [he]
    exact CovariantDerivative.rm04Section_apply_const G (metricCov g) (metricCov_smooth g) _ _ _ _
  have hm : metricTensorField g x (V ∘ Fin.natAdd 4) = g.inner x b (w 3) :=
    metricTensorField_apply g x (V ∘ Fin.natAdd 4)
  exact (tensor0SField_product_apply S (metricTensorField g) x V).trans
    (congrArg₂ (fun r s : ℝ => r * s) hs hm)

theorem exists_metricRm04_relowering :
    ∃ e : Fin 6 ≃ Fin 6, ∀ G g : SmoothRiemannianMetric I M,
      metricRm04 g = metricTraceFirstTwoField G
        (Tensor0SField.domDomCongr ∞ e
          (tensor0SFieldProduct ∞
            (CovariantDerivative.rm04Section G (metricCov g) (metricCov_smooth g))
            (metricTensorField g))) := by
  refine ⟨lowerPerm, ?_⟩
  intro G g
  apply DFunLike.ext
  intro x
  apply tensor0SSpace_ext (I := I) 4 x
  intro w
  classical
  obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis G x
  have hi : MetricInverseInBasis G x b (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) :=
    metricInverseInBasis_identity_of_orthonormal G b hb
  erw [trace_orthonormal G _ x b hi w]
  simp_rw [lower_product_eval]
  let R := connectionRiemannCurvatureField (metricCov g)
    (CovariantDerivative.tangentConstAt (I := I) x (w 0)) (CovariantDerivative.tangentConstAt (I := I) x (w 1))
    (CovariantDerivative.tangentConstAt (I := I) x (w 2)) x
  have hw : w = vec4 (w 0) (w 1) (w 2) (w 3) := by
    funext i
    fin_cases i <;> rfl
  have hleft : metricRm04 g x w = g.inner x (w 3) R := by
    rw [hw]
    exact CovariantDerivative.rm04Section_apply_const g (metricCov g) (metricCov_smooth g) _ _ _ _
  rw [hleft]
  have hrepr (i) : b.repr R i = G.inner x (b i) R := by
    rw [basis_repr_eq_sum_inv_inner G x b (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) hi R i]
    simp only [identityInvMetric, diagonalInvMetric, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [G.symm]
  calc
    g.inner x (w 3) R = g.inner x R (w 3) := g.symm x _ _
    _ = g.inner x (∑ i, b.repr R i • b i) (w 3) := by rw [b.sum_repr]
    _ = ∑ i, G.inner x (b i) R * g.inner x (b i) (w 3) := by
      rw [map_sum, sum_apply]
      simp only [map_smul, smul_apply, smul_eq_mul, hrepr]

end Manifold

section Euclidean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem exists_iterCov_metricRm04_relowering_bound_on_opens (k : ℕ) :
    ∃ C > 0, ∀ (U : Opens E) (G g : SmoothRiemannianMetric 𝓘(ℝ, E) U) (x : U),
      let S := CovariantDerivative.rm04Section G (metricCov g) (metricCov_smooth g)
      Real.sqrt (normSq0S G x (4 + k) (iterCov G 4 (metricRm04 g) k x)) ≤
        C * ∑ c ∈ Finset.range (k + 1), (k.choose c : ℝ) *
          Real.sqrt (normSq0S G x (4 + c) (iterCov G 4 S c x)) *
          Real.sqrt (normSq0S G x (2 + (k - c))
            (iterCov G 2 (metricTensorField g) (k - c) x)) := by
  obtain ⟨C, hC, htrace⟩ := exists_iter_cov_metric_trace_first_two_bound_on_opens (E := E) 4 k
  refine ⟨C, hC, ?_⟩
  intro U G g x
  dsimp only
  obtain ⟨e, he⟩ := exists_metricRm04_relowering (I := 𝓘(ℝ, E)) (M := U)
  let S := CovariantDerivative.rm04Section G (metricCov g) (metricCov_smooth g)
  let P := tensor0SFieldProduct ∞ S (metricTensorField g)
  have ht := htrace U G (Tensor0SField.domDomCongr ∞ e P) x
  rw [← he G g] at ht
  obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis G x
  have hi := metricInverseInBasis_identity_of_orthonormal G b hb
  rw [normSq0S_iterCov_domDomCongr G e P k x b hi] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left
    (iterCov_product_sqrtNormSq_le G x b hi k S (metricTensorField g)) hC.le)
end Euclidean

end DifferentialGeometry.Geometry.Curvature
