import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.Tensor0S
import DifferentialGeometry.Tensor.RSTensor.MetricCompatibility
import DifferentialGeometry.Tensor.Multilinear.BundleSmoothEval
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

theorem contMDiffWithinAt_tensor0SField_eval_localFrame {s : ℕ}
    (alpha : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    {Idx : Type*} [Fintype Idx]
    (frame : Idx → (x : M) → TangentSpace I x)
    {u : Set M} {x₀ : M} (hx₀ : x₀ ∈ u)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (m : Fin s → Idx) :
    ContMDiffWithinAt I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun x : M => alpha x (fun j : Fin s => frame (m j) x)) u x₀ := by
  have hEvalProd := TensorMultilinear.contMDiffWithinAt_section_apply_prod
    (s := u ×ˢ (Set.univ : Set ℝ)) (p₀ := (x₀, 0))
    s (fun b : M => alpha b)
    ((alpha.contMDiff.comp contMDiff_fst).contMDiffAt.contMDiffWithinAt)
    (fun (a : Fin s) (b : M) => frame (m a) b)
    (fun a => (hframe.contMDiffOn (m a) x₀ hx₀).comp (x₀, 0)
      contMDiff_fst.contMDiffAt.contMDiffWithinAt (fun p hp => hp.1))
  have hmaps : Set.MapsTo (fun x : M => (x, (0 : ℝ))) u (u ×ˢ (Set.univ : Set ℝ)) :=
    fun x hx => ⟨hx, Set.mem_univ _⟩
  have hFinal : ContMDiffWithinAt I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun x : M => Tensor0SSpace.toModel (alpha x) (fun a : Fin s => frame (m a) x)) u x₀ :=
    hEvalProd.comp x₀
      ((contMDiff_id.prodMk contMDiff_const :
          ContMDiff I (I.prod 𝓘(ℝ, ℝ)) (∞ : WithTop ℕ∞)
            (fun x : M => (x, (0 : ℝ)))).contMDiffAt.contMDiffWithinAt)
      hmaps
  simpa [Tensor0SSpace.toModel, tensor0SSpace_continuousLinearEquiv_apply] using hFinal

theorem contMDiffOn_tensor0SField_eval_localFrame_of_isLocalFrameOn {s : ℕ}
    (alpha : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    {Idx : Type*} [Fintype Idx]
    (frame : Idx → (x : M) → TangentSpace I x)
    {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (m : Fin s → Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun x : M => alpha x (fun j : Fin s => frame (m j) x)) u :=
  fun _x hx₀ =>
    contMDiffWithinAt_tensor0SField_eval_localFrame alpha frame hx₀ hframe m

theorem contMDiffOn_metricInner_localFrame_of_isLocalFrameOn
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    (g : DifferentialGeometry.SmoothRiemannianMetric I M)
    {Idx : Type*} [Fintype Idx]
    (frame : Idx → (x : M) → TangentSpace I x)
    {u : Set M}
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (i j : Idx) :
    ContMDiffOn I 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
      (fun x : M => g.inner x (frame i x) (frame j x)) u := by
  have h := contMDiffOn_tensor0SField_eval_localFrame_of_isLocalFrameOn
    (metricTensorField (I := I) g) frame hframe ![i, j]
  refine h.congr (fun x _ => ?_)
  simp [metricTensorField_apply]

end

end Tensor0SBundle
