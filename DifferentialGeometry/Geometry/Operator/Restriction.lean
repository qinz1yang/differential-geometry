import DifferentialGeometry.Geometry.Curvature.Naturality.OpenSubtype
import DifferentialGeometry.Geometry.Operator.OrthonormalTrace
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

set_option autoImplicit false
noncomputable section
open Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open Filter
open scoped Manifold ContDiff Topology
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

section

variable [BoundarylessManifold I M]

private theorem inner_cov_gradient_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    {f : M → ℝ} {x : U} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f (x : M))
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (v : TangentSpace I x) :
    (g.restrictOpen U).inner x
      (LeviCivita (g.restrictOpen U) (fun y => gradientFun (g.restrictOpen U)
        (fun z : U => f (z : M)) y) x v) (X (x : M)) =
      g.inner (x : M) (LeviCivita g (fun y => gradientFun g f y) (x : M) v) (X (x : M)) := by
  let h := g.restrictOpen U
  let Y := restrictOpenTangentSection U X
  have hcomp : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y : U => f (y : M)) x :=
    hf.comp x (contMDiff_subtype_val (I := I) (U := U)).contMDiffAt
  have hg1 := (gradientFun_contMDiffAt_one h hcomp).mdifferentiableAt (by norm_num)
  have hg2 := (gradientFun_contMDiffAt_one g hf).mdifferentiableAt (by norm_num)
  have hc1 := (LeviCivita_isMetricCompatible h).apply hg1 Y.mdifferentiableAt v
  have hc2 := (LeviCivita_isMetricCompatible g).apply hg2 X.mdifferentiableAt v
  have heq : (fun y : U => h.inner y (gradientFun h (fun z : U => f (z : M)) y) (Y y)) =ᶠ[𝓝 x]
      (fun y : U => mfderiv I 𝓘(ℝ, ℝ) f (y : M) (X (y : M))) := by
    have hfe : ∀ᶠ y in 𝓝 (x : M), MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
      ((contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by decide)).mp hf).mono
        fun _ hy => hy.mdifferentiableAt (by norm_num)
    filter_upwards [continuous_subtype_val.continuousAt.tendsto.eventually hfe] with y hy
    rw [inner_gradientFun, mvfderiv_restrictOpen U f y (Y y) hy]
    change mfderiv I 𝓘(ℝ, ℝ) f (y : M) (Y y) = _
    rw [show Y y = X (y : M) from restrictOpenTangentSection_apply U X y]
  have hdir : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => mfderiv I 𝓘(ℝ, ℝ) f y (X y)) (x : M) :=
    (mvfderiv_apply_contMDiffAt_of_section_one hf
      (X.contMDiff.contMDiffAt.of_le (by decide))).mdifferentiableAt (by norm_num)
  have hd : (mfderiv I 𝓘(ℝ, ℝ) (fun y : U => h.inner y
      (gradientFun h (fun z : U => f (z : M)) y) (Y y)) x : TangentSpace I x →L[ℝ] ℝ) =
      mfderiv I 𝓘(ℝ, ℝ) (fun y : U => mfderiv I 𝓘(ℝ, ℝ) f (y : M) (X (y : M))) x := heq.mfderiv_eq
  have hdv := congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) hd
  have hchain := mvfderiv_restrictOpen U (fun y => mfderiv I 𝓘(ℝ, ℝ) f y (X y)) x v hdir
  have hdv' := hdv.trans hchain
  have hinner : (fun y => g.inner y (gradientFun g f y) (X y)) =
      (fun y => mfderiv I 𝓘(ℝ, ℝ) f y (X y)) := by funext y; exact inner_gradientFun g f y (X y)
  rw [hinner] at hc2
  have hconn : h.inner x (gradientFun h (fun y : U => f (y : M)) x) (LeviCivita h Y x v) =
      g.inner (x : M) (gradientFun g f (x : M)) (LeviCivita g X (x : M) v) := by
    rw [inner_gradientFun, mvfderiv_restrictOpen U f x _ (hf.mdifferentiableAt (by norm_num)),
      inner_gradientFun]
    congr 1
    exact metricCov_restrictOpen_globalSection g U X x v
  rw [hconn] at hc1
  have hY : Y x = X (x : M) := restrictOpenTangentSection_apply U X x
  rw [hY] at hc1
  exact add_right_cancel (hc1.symm.trans (hdv'.trans hc2))

theorem laplacian_restrictOpen_of_contMDiffAt
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    {f : M → ℝ} {x : U} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f (x : M)) :
    laplacian (LeviCivita (g.restrictOpen U)) (g.restrictOpen U)
      (fun y : U => f (y : M)) x = laplacian (LeviCivita g) g f (x : M) := by
  have hcov : (LeviCivita (g.restrictOpen U)
      (fun y => gradientFun (g.restrictOpen U) (fun z : U => f (z : M)) y) x : E →L[ℝ] E) =
      LeviCivita g (fun y => gradientFun g f y) (x : M) := by
    ext v
    apply SmoothRiemannianMetric.eq_of_inner_eq_gen (g.restrictOpen U)
    intro w
    obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := TangentSpace I) (n := (⊤ : ℕ∞)) (x : M) w
    simpa only [hX] using! inner_cov_gradient_restrictOpen g U hf X v
  change LinearMap.trace ℝ E _ = LinearMap.trace ℝ E _
  rw [hcov]

end

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
  exact laplacian_restrictOpen_of_contMDiffAt g U (x := x)
    (hF.contMDiffAt.of_le (by decide))

end DifferentialGeometry.Geometry.Operator
