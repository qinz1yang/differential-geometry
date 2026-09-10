import DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.Ricci
import DifferentialGeometry.Geometry.Metric.TensorInner.Tangent.MetricData

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness

namespace Poincare.Geometry.Curvature

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

private def inclusionTangentEquiv (U : TopologicalSpace.Opens M) (x : U) :
    TangentSpace I x ≃L[ℝ] TangentSpace I (x : M) := ContinuousLinearEquiv.refl ℝ E

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M] in
private theorem inclusionTangentEquiv_apply (U : TopologicalSpace.Opens M) (x : U)
    (v : TangentSpace I x) : inclusionTangentEquiv (I := I) U x v =
      mfderiv I I (Subtype.val : U → M) x v := by
  rw [mfderiv_subtype_val]
  rfl

omit [BoundarylessManifold I M] in
private theorem restrict_inner (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (x : U) (v w : TangentSpace I x) :
    (g.restrictOpen U).inner x v w = g.inner (x : M)
      (mfderiv I I (Subtype.val : U → M) x v) (mfderiv I I (Subtype.val : U → M) x w) := by
  rw [SmoothRiemannianMetric.restrictOpen_inner, mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]

theorem riemannOp_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    (x : U) (u v w : TangentSpace I x) :
    mfderiv I I (Subtype.val : U → M) x (riemannOp (LeviCivita (g.restrictOpen U)) x u v w) =
      riemannOp (LeviCivita g) (x : M) (mfderiv I I (Subtype.val : U → M) x u)
        (mfderiv I I (Subtype.val : U → M) x v) (mfderiv I I (Subtype.val : U → M) x w) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply tangentFlatLinear_injective_gen (I := I) g (x : M)
  ext z
  simp only [tangentFlatLinear_apply_gen]
  obtain ⟨q, rfl⟩ := (inclusionTangentEquiv (I := I) U x).surjective z
  rw [inclusionTangentEquiv_apply]
  have h := metricRm04StandardAt_restrictOpen g U x u v w q
  rw [metricRm04StandardAt_eq_inner_riemannOp, metricRm04StandardAt_eq_inner_riemannOp, restrict_inner] at h
  exact (g.symm (x : M) _ _).trans (h.trans (g.symm (x : M) _ _))

theorem ricciTensor_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    (x : U) (v w : TangentSpace I x) :
    ricciTensor (g.restrictOpen U) x v w = ricciTensor g (x : M)
      (mfderiv I I (Subtype.val : U → M) x v) (mfderiv I I (Subtype.val : U → M) x w) := by
  let e := inclusionTangentEquiv (I := I) U x
  have he := inclusionTangentEquiv_apply (I := I) U x
  let A := ricciEndo g (x : M) (mfderiv I I (Subtype.val : U → M) x v)
    (mfderiv I I (Subtype.val : U → M) x w)
  have hconj : ricciEndo (g.restrictOpen U) x v w = e.toLinearEquiv.symm.conj A := by
    apply LinearMap.ext
    intro z
    apply e.injective
    change e (riemannOp (LeviCivita (g.restrictOpen U)) x z v w) = e (e.symm (A (e z)))
    rw [e.apply_symm_apply]
    change inclusionTangentEquiv U x _ = A (inclusionTangentEquiv U x z)
    rw [he, he]
    exact riemannOp_restrictOpen g U x z v w
  rw [ricciTensor_apply, ricciTensor_apply, hconj]
  exact LinearMap.trace_conj' A e.toLinearEquiv.symm

theorem ricciSharp_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    (x : U) (v : TangentSpace I x) :
    mfderiv I I (Subtype.val : U → M) x (ricciSharp (g.restrictOpen U) x v) =
      ricciSharp g (x : M) (mfderiv I I (Subtype.val : U → M) x v) := by
  apply tangentFlatLinear_injective_gen (I := I) g (x : M)
  ext z
  simp only [tangentFlatLinear_apply_gen]
  obtain ⟨w, rfl⟩ := (inclusionTangentEquiv (I := I) U x).surjective z
  rw [inclusionTangentEquiv_apply, ← restrict_inner, inner_ricciSharp, inner_ricciSharp]
  exact ricciTensor_restrictOpen g U x v w

end Poincare.Geometry.Curvature
