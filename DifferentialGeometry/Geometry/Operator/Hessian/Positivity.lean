import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.Hessian
import DifferentialGeometry.Geometry.Metric.LocalRealization

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private theorem abstractHessian_contMDiff_section
    (g : SmoothRiemannianMetric I M) {ρ : M → ℝ}
    (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        x (abstractHessian g ρ x)) := by
  let : CovariantDerivative.ContMDiffCovariantDerivative (LeviCivita g) ∞ :=
    { contMDiff :=
        { contMDiff := fun hσ => LeviCivita_section_contMDiffOn_univ g hσ } }
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x => abstractHessian g ρ x)
  intro Y
  apply contMDiff_continuousLinearMap_section_of_apply
    (V₂ := fun _ : M => ℝ) (φ := fun x => abstractHessian g ρ x (Y x))
  intro Z
  have hscalar : ContMDiff I 𝓘(ℝ) ∞
      (fun x : M => abstractHessian g ρ x (Y x) (Z x)) :=
    cotangentCov_double_apply_smooth (LeviCivita g)
      (cotangentCov_mvfderiv_smooth hρ) Y Z
  intro x
  rw [contMDiffAt_section]
  refine hscalar.contMDiffAt.congr_of_eventuallyEq ?_
  filter_upwards with y
  rfl

/-- A strict lower bound for the Hessian relative to the original metric is an
open condition, for any real coefficient. -/
theorem isOpen_hessFun_gt_mul_inner
    (g : SmoothRiemannianMetric I M) {ρ : M → ℝ}
    (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (c : ℝ) :
    IsOpen {x : M | ∀ v : TangentSpace I x, v ≠ 0 →
      c * g.inner x v v < hessFun g ρ x v v} := by
  let b : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    fun x => abstractHessian g ρ x - c • g.inner x
  have hb : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        x (b x)) :=
    (abstractHessian_contMDiff_section g hρ).sub_section
      (g.contMDiff.const_smul_section (a := c))
  have hval (x : M) (v w : TangentSpace I x) :
      b x v w = hessFun g ρ x v w - c * g.inner x v w := by
    change abstractHessian g ρ x v w - c * g.inner x v w = _
    rw [hessFun_eq_abstract g hρ x v w]
  have hsymm (x : M) (v w : TangentSpace I x) : b x v w = b x w v := by
    rw [hval, hval, hessFun_symm_of_boundaryless g hρ x v w, g.symm x v w]
  refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
  have hpos (v : TangentSpace I x) (hv : v ≠ 0) : 0 < b x v v := by
    rw [hval]
    exact sub_pos.mpr (hx v hv)
  obtain ⟨V, hxV, gV, hV⟩ :=
    Metric.exists_local_metric_of_bilinear_section b hb hsymm x hpos
  apply Filter.mem_of_superset (V.isOpen.mem_nhds hxV)
  intro y hy v hv
  have hp : 0 < b y v v :=
    lt_of_lt_of_eq (gV.pos ⟨y, hy⟩ v hv) (hV ⟨y, hy⟩ v v)
  rw [hval] at hp
  exact sub_pos.mp hp

end DifferentialGeometry.Geometry.Operator
