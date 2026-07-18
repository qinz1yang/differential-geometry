import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.Tensor0S
import DifferentialGeometry.Tensor.RSTensor.MetricCompatibility
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Tensor0SBundle

noncomputable section

open Bundle Set
open scoped BigOperators Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem contMDiffOn_tensor0SField_eval_localFrame {s : ℕ}
    (alpha : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    {Idx : Type*} [Fintype Idx]
    (frame : Idx → (x : M) → TangentSpace I x)
    {u : Set M} (hu : IsOpen u)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (m : Fin s → Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun x : M => alpha x (fun j : Fin s => frame (m j) x)) u := by
  intro x₀ hx₀
  apply ContMDiffAt.contMDiffWithinAt
  have hα_top := alpha.contMDiff x₀
  have hV_top : ∀ a : Fin s,
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (∞ : WithTop ℕ∞)
        (fun y : M =>
          (⟨y, frame (m a) y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x₀ := by
    intro a
    exact hframe.contMDiffAt hu hx₀ (m a)
  have hEval := TensorMultilinear.contMDiffAt_section_apply_gen
    (I := I) (M := M) (n := s) (x₀ := x₀)
    (T := fun y : M => alpha y) hα_top
    (v := fun a : Fin s => fun y : M => frame (m a) y)
    (hv := hV_top)
  simpa [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply] using hEval

theorem contMDiffOn_metricInner_localFrame
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx]
    (frame : Idx → (x : M) → TangentSpace I x)
    {u : Set M} (hu : IsOpen u)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (i j : Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun x : M => g.inner x (frame i x) (frame j x)) u := by
  have h := contMDiffOn_tensor0SField_eval_localFrame
    (metricTensorField (I := I) g) frame hu hframe ![i, j]
  refine h.congr (fun x _ => ?_)
  simp [metricTensorField_apply]

end

end Tensor0SBundle
