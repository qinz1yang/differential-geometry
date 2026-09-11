import DifferentialGeometry.Geometry.Curvature.Naturality.OpenSubtype
import DifferentialGeometry.Geometry.Operator.OrthonormalTrace
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

set_option autoImplicit false
noncomputable section
open Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Operator
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem grad_restrict_identified (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) (F : M → ℝ) (x : U)
    (hF : MDifferentiableAt I 𝓘(ℝ) F (x : M)) :
    gradFun (g.restrictOpen U) (fun y : U => F (y : M)) x = gradFun g F (x : M) := by
  apply SmoothRiemannianMetric.eq_of_inner_eq_gen g
  intro v
  change (g.restrictOpen U).inner x
    (gradFun (g.restrictOpen U) (fun y : U => F (y : M)) x) v =
      g.inner (x : M) (gradFun g F (x : M)) v
  erw [inner_gradFun, inner_gradFun]
  exact mvfderiv_restrictOpen U F x v hF

theorem gradFun_restrictOpen (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) (F : M → ℝ) (x : U)
    (hF : MDifferentiableAt I 𝓘(ℝ) F (x : M)) :
    mfderiv I I (Subtype.val : U → M) x
      (gradFun (g.restrictOpen U) (fun y : U => F (y : M)) x) = gradFun g F (x : M) := by
  rw [mfderiv_subtype_val_apply]
  exact grad_restrict_identified g U F x hF

variable [I.Boundaryless]

theorem hessFun_restrictOpen_of_contMDiff (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F)
    (x : U) (v w : TangentSpace I x) :
    hessFun (g.restrictOpen U) (fun y : U => F (y : M)) x v w =
      hessFun g F (x : M) (mfderiv I I (Subtype.val : U → M) x v)
        (mfderiv I I (Subtype.val : U → M) x w) := by
  rw [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
  have hFU : ContMDiff I 𝓘(ℝ) ∞ (fun y : U => F (y : M)) :=
    hF.comp (contMDiff_subtype_val (I := I) (U := U))
  let Y : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) :=
    ⟨fun y => gradFun g F y, gradFun_contMDiff_total g hF⟩
  have hgrad : (fun y : U => gradFun (g.restrictOpen U) (fun z : U => F (z : M)) y) =
      restrictOpenTangentField U (fun y : M => Y y) := by
    funext y
    rw [restrictOpenTangentField_apply]
    exact grad_restrict_identified g U F y (hF.mdifferentiable (by simp) (y : M))
  erw [hessFun_eq_cov_grad _ hFU, hessFun_eq_cov_grad _ hF, hgrad,
    SmoothRiemannianMetric.restrictOpen_inner]
  exact congrArg (fun a : TangentSpace I (x : M) => g.inner (x : M) a w)
    (metricCov_restrictOpen_globalSection g U Y x v)

theorem laplacian_restrictOpen (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) (F : M → ℝ) (hF : ContMDiff I 𝓘(ℝ) ∞ F) (x : U) :
    laplacian (LeviCivita (g.restrictOpen U)) (g.restrictOpen U)
      (fun y : U => F (y : M)) x = laplacian (LeviCivita g) g F (x : M) := by
  obtain ⟨B, hB⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis g (x : M)
  let BU : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) := B
  have hBU : ∀ i j, (g.restrictOpen U).inner x (BU i) (BU j) =
      if i = j then (1 : ℝ) else 0 := hB
  have hFU : ContMDiff I 𝓘(ℝ) ∞ (fun y : U => F (y : M)) :=
    hF.comp (contMDiff_subtype_val (I := I) (U := U))
  rw [laplacian_eq_sum_hessFun _ _ hFU x BU hBU,
    laplacian_eq_sum_hessFun _ _ hF (x : M) B hB]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [BU, mfderiv_subtype_val_apply] using!
    hessFun_restrictOpen_of_contMDiff g U F hF x (BU i) (BU i)

end DifferentialGeometry.Geometry.Operator
