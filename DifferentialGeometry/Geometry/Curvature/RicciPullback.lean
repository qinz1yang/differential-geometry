import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.MetricData

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.Geometry.Curvature

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  [BoundarylessManifold I M] [BoundarylessManifold J N]

theorem riemannOp_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (x : M) (u v w : TangentSpace I x) :
    mfderiv I J Φ x (riemannOp (LeviCivita (Diffeomorph.pullbackMetricCross g Φ)) x u v w) =
      riemannOp (LeviCivita g) (Φ x) (mfderiv I J Φ x u) (mfderiv I J Φ x v)
        (mfderiv I J Φ x w) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  let e := Φ.mfderivToContinuousLinearEquiv (by decide : (∞ : WithTop ℕ∞) ≠ 0) x
  have he (z : TangentSpace I x) : e z = mfderiv I J Φ x z :=
    congrArg (fun A : TangentSpace I x →L[ℝ] TangentSpace J (Φ x) ↦ A z)
      (Φ.mfderivToContinuousLinearEquiv_coe (by decide))
  apply tangentFlatLinear_injective_gen (I := J) g (Φ x)
  ext z
  simp only [tangentFlatLinear_apply_gen]
  obtain ⟨q, rfl⟩ := e.surjective z
  rw [he]
  have h := metricRm04Standard_pullbackCross g Φ x u v w q
  rw [metricRm04StandardAt_eq_inner_riemannOp, metricRm04StandardAt_eq_inner_riemannOp,
    Diffeomorph.pullbackMetricCross_inner] at h
  exact (g.symm (Φ x) _ _).trans (h.trans (g.symm (Φ x) _ _))

theorem ricciTensor_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (x : M) (v w : TangentSpace I x) :
    ricciTensor (Diffeomorph.pullbackMetricCross g Φ) x v w =
      ricciTensor g (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w) := by
  let e := Φ.mfderivToContinuousLinearEquiv (by decide : (∞ : WithTop ℕ∞) ≠ 0) x
  have he (z : TangentSpace I x) : e z = mfderiv I J Φ x z :=
    congrArg (fun A : TangentSpace I x →L[ℝ] TangentSpace J (Φ x) ↦ A z)
      (Φ.mfderivToContinuousLinearEquiv_coe (by decide))
  let A := ricciEndo g (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w)
  have hconj : ricciEndo (Diffeomorph.pullbackMetricCross g Φ) x v w =
      e.toLinearEquiv.symm.conj A := by
    apply LinearMap.ext
    intro z
    apply e.injective
    change e (riemannOp (LeviCivita (Diffeomorph.pullbackMetricCross g Φ)) x z v w) =
      e (e.symm (A (e z)))
    rw [e.apply_symm_apply, he, he]
    exact riemannOp_pullbackMetricCross g Φ x z v w
  rw [ricciTensor_apply, ricciTensor_apply, hconj]
  exact LinearMap.trace_conj' A e.toLinearEquiv.symm

theorem ricciSharp_pullbackMetricCross
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N)
    (x : M) (v : TangentSpace I x) :
    mfderiv I J Φ x (ricciSharp (Diffeomorph.pullbackMetricCross g Φ) x v) =
      ricciSharp g (Φ x) (mfderiv I J Φ x v) := by
  let e := Φ.mfderivToContinuousLinearEquiv (by decide : (∞ : WithTop ℕ∞) ≠ 0) x
  have he (z : TangentSpace I x) : e z = mfderiv I J Φ x z :=
    congrArg (fun A : TangentSpace I x →L[ℝ] TangentSpace J (Φ x) ↦ A z)
      (Φ.mfderivToContinuousLinearEquiv_coe (by decide))
  apply tangentFlatLinear_injective_gen (I := J) g (Φ x)
  ext z
  simp only [tangentFlatLinear_apply_gen]
  obtain ⟨w, rfl⟩ := e.surjective z
  rw [he, ← Diffeomorph.pullbackMetricCross_inner, inner_ricciSharp, inner_ricciSharp]
  exact ricciTensor_pullbackMetricCross g Φ x v w

end DifferentialGeometry.Geometry.Curvature
