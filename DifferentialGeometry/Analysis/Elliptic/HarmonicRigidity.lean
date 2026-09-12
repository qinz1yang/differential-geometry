import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.Identities
import DifferentialGeometry.Geometry.Metric.Evaluation
import DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

omit [T2Space M] [CompactSpace M] in
theorem continuous_inner_gradFun_self
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) :
    Continuous (fun x : M => g.inner x (gradFun (I := I) g f x)
      (gradFun (I := I) g f x)) := by
  have h := DifferentialGeometry.Geometry.Metric.contMDiff_metric_inner
    (I := I) g (gradG (I := I) g f) (gradG (I := I) g f)
  refine h.continuous.congr (fun x => ?_)
  rw [grad_g_apply]

theorem integral_inner_gradFun_self_eq_zero_of_laplacian_eq_zero
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    (hf : ∀ x : M, ΔG (I := I) g f x = 0) :
    ∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  have hgreen :
      (∫ x, g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      -∫ x, f x * ΔG (I := I) g f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    exact green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
      (I := I) g (f := fun x : M => f x) (h := fun x : M => f x)
      f.contMDiff f.contMDiff (HasCompactSupport.of_compactSpace _)
  have hzero :
      ∫ x, f x * ΔG (I := I) g f x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
    have hpt : (fun x : M => f x * ΔG (I := I) g f x) = fun _ => (0 : ℝ) := by
      funext x
      rw [hf x, mul_zero]
    rw [hpt]
    simp
  rw [hgreen, hzero, neg_zero]

theorem isLocallyConstant_of_laplacian_eq_zero
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    (hf : ∀ x : M, ΔG (I := I) g f x = 0) :
    IsLocallyConstant (fun x : M => f x) := by
  classical
  have hvolpos : (riemannianVolumeMeasure (I := I) (M := M) g).IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  have hfmc : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  have hint := integral_inner_gradFun_self_eq_zero_of_laplacian_eq_zero g f hf
  have hcont := continuous_inner_gradFun_self g f
  have hnn : 0 ≤ᵐ[riemannianVolumeMeasure (I := I) (M := M) g]
      (fun x : M => g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x)) :=
    Filter.Eventually.of_forall
      (fun x => metric_inner_self_nonneg (I := I) g x _)
  have hintble : Integrable
      (fun x : M => g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hae : (fun x : M => g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x))
      =ᵐ[riemannianVolumeMeasure (I := I) (M := M) g] (fun _ : M => (0 : ℝ)) :=
    (integral_eq_zero_iff_of_nonneg_ae hnn hintble).mp hint
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq (μ := riemannianVolumeMeasure (I := I) (M := M) g)
    (U := Set.univ) (f := fun x : M => g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x))
    (g := fun _ : M => (0 : ℝ)) (by rw [MeasureTheory.Measure.restrict_univ]; exact hae) isOpen_univ
    hcont.continuousOn continuous_zero.continuousOn
  have hgradzero : ∀ x : M, gradFun (I := I) g f x = 0 := by
    intro x
    have hx : g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) = 0 :=
      heq (Set.mem_univ x)
    by_contra hne
    exact absurd hx (ne_of_gt (g.pos x _ hne))
  refine isLocallyConstant_of_mfderiv_eq_zero (f.contMDiff.mdifferentiable (by simp)) ?_
  intro x
  ext v
  rw [← inner_gradFun (I := I) g f x v, hgradzero x]
  exact congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v) (map_zero (g.inner x))

theorem exists_eq_const_of_laplacian_eq_zero [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    (hf : ∀ x : M, ΔG (I := I) g f x = 0) :
    ∃ c : ℝ, ∀ x : M, f x = c := by
  obtain ⟨c, hc⟩ := (isLocallyConstant_of_laplacian_eq_zero g f hf).exists_eq_const
  exact ⟨c, fun x => congrFun hc x⟩

end Laplacian
end Analysis
end DifferentialGeometry

end
