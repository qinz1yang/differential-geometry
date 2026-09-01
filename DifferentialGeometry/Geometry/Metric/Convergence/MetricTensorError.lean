import DifferentialGeometry.Geometry.Metric.Convergence.Tensor02CovariantDerivativeNorm

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem tensor_apply_bounds_of_metricTensorErrorNorm_le
    (P : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) 2)
    (g : SmoothRiemannianMetric I M) {ε : ℝ} {x : M}
    (hc0 : metricTensorErrorNorm (I := I) P g x ≤ ε)
    (v : TangentSpace I x) :
    (1 - ε) * g.inner x v v ≤ P x (fun _ => v) ∧
      P x (fun _ => v) ≤ (1 + ε) * g.inner x v v := by
  classical
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hCS := Tensor0SBundle.abs_apply_le_sqrt_normSq0S (I := I)
    g x 2 basis (fun i j => hON i j)
    (P x - Tensor0SBundle.metricTensorField (I := I) g x)
    (fun _ => v)
  have hval : (P x - Tensor0SBundle.metricTensorField (I := I) g x) (fun _ => v) =
      P x (fun _ => v) - g.inner x v v := by
    simp [Tensor0SBundle.metricTensorField_apply]
  have hnn : 0 ≤ g.inner x v v := metric_inner_self_nonneg (I := I) g x v
  have hprod : (∏ _a : Fin 2, Real.sqrt (g.inner x v v)) = g.inner x v v := by
    rw [Fin.prod_univ_two, Real.mul_self_sqrt hnn]
  have habs : |P x (fun _ => v) - g.inner x v v| ≤ ε * g.inner x v v := by
    unfold metricTensorErrorNorm at hc0
    calc
      |P x (fun _ => v) - g.inner x v v| =
          |(P x - Tensor0SBundle.metricTensorField (I := I) g x) (fun _ => v)| := by
            rw [hval]
      _ ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2
            (P x - Tensor0SBundle.metricTensorField (I := I) g x)) *
          ∏ _a : Fin 2, Real.sqrt (g.inner x v v) := hCS
      _ ≤ ε * g.inner x v v := by
        rw [hprod]
        exact mul_le_mul_of_nonneg_right hc0 hnn
  constructor <;> nlinarith [abs_le.mp habs]

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem inner_bounds_of_metricTensorErrorNorm_le
    (G g : SmoothRiemannianMetric I M) {K : Set M} {ε : ℝ}
    (hc0 : ∀ x ∈ K, metricTensorErrorNorm (I := I)
      (Tensor0SBundle.metricTensorField (I := I) G) g x ≤ ε) :
    ∀ x ∈ K, ∀ v : TangentSpace I x,
      (1 - ε) * g.inner x v v ≤ G.inner x v v ∧
        G.inner x v v ≤ (1 + ε) * g.inner x v v := by
  intro x hx v
  simpa [Tensor0SBundle.metricTensorField_apply] using
    tensor_apply_bounds_of_metricTensorErrorNorm_le (I := I)
      (Tensor0SBundle.metricTensorField (I := I) G) g (hc0 x hx) v

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem MetricUniformEquivalentOn.sqrt_normSq0S_le
    {K : Set M} {g h : SmoothRiemannianMetric I M} {C : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g h C)
    {x : M} (hx : x ∈ K) {s : ℕ}
    (A : Tensor0SBundle.Tensor0SSpace
      (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) s x) :
    Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x s A) ≤
      Real.sqrt (C ^ s) *
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x s A) :=
  Tensor0SBundle.sqrt_normSq0S_le_of_metric_equiv
    (I := I) g h x s hEq.1 (hEq.2 x hx) A

omit [SigmaCompactSpace M] in
theorem metricTensorErrorNorm_eq_metricDerivNorm_zero
    (G g : SmoothRiemannianMetric I M) (x : M) :
    metricTensorErrorNorm (I := I)
        (Tensor0SBundle.metricTensorField (I := I) G) g x =
      metricDerivNorm (I := I) 0 G g g x := by
  rfl

omit [SigmaCompactSpace M] in
theorem tensor02CovDerivNormWith_metricTensorField_eq_metricDerivNorm
    (G g : SmoothRiemannianMetric I M) (a : ℕ) (ha : 1 ≤ a) (x : M) :
    tensor02CovDerivNormWith (I := I) a
        (Tensor0SBundle.metricTensorField (I := I) G) g g x =
      metricDerivNorm (I := I) a G g g x := by
  classical
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hinv : Tensor0SBundle.MetricInverseInBasisGen (I := I) g x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g basis hON
    change Tensor0SBundle.MetricInverseInBasisGen (I := I) g x basis
      (fun i j => if i = j then (1 : Real) else 0)
    exact h
  rw [tensor02CovDerivNormWith_eq_iterCov (I := I)
      (Tensor0SBundle.metricTensorField (I := I) G) g a basis hinv,
    metricDerivNorm_eq_iterCov (I := I) G g g a basis hinv]
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  rw [iterCov_sub, show 1 + b = b + 1 by omega,
    iterCov_metric_zero g b, sub_zero]

end HCGCompactness
end DifferentialGeometry
