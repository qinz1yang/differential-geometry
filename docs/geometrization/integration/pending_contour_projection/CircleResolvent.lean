import DifferentialGeometry.Analysis.Integration.Integral.Circle
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.ContinuousMap.Units

set_option autoImplicit false

noncomputable section

open Complex Metric

namespace ContinuousMap

private theorem ringInverse_apply {X A : Type*} [TopologicalSpace X]
    [NormedRing A] [CompleteSpace A] (f : C(X, A)) (hf : IsUnit f) (x : X) :
    Ring.inverse f x = Ring.inverse (f x) := by
  have hx := f.isUnit_iff_forall_isUnit.mp hf x
  have hi := congrArg (fun g : C(X, A) => g x) (Ring.inverse_mul_cancel f hf)
  change Ring.inverse f x * f x = 1 at hi
  simpa only [one_mul] using (Ring.eq_mul_inverse_iff_mul_eq _ 1 _ hx).mpr hi

end ContinuousMap

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
  [NormedRing A] [NormedAlgebra ℂ A] [NormedAlgebra 𝕜 A]
  [IsScalarTower 𝕜 ℂ A] [CompleteSpace A]

theorem contDiffOn_circleIntegral_resolvent (c : ℂ) (r : ℝ) {n : WithTop ℕ∞} :
    ContDiffOn 𝕜 n (fun a : A => ∮ z in C(c, r), resolvent a z)
      {a : A | sphere c |r| ⊆ resolventSet ℂ a} := by
  let Z : C(sphere c |r|, A) :=
    ⟨fun z => algebraMap ℂ A z, (continuous_algebraMap ℂ A).comp continuous_subtype_val⟩
  let K : A →L[𝕜] C(sphere c |r|, A) := ContinuousLinearMap.const 𝕜 _
  have hg : ContDiff 𝕜 n (fun a => Z - K a) := contDiff_const.sub K.contDiff
  have hu (a : A) (ha : sphere c |r| ⊆ resolventSet ℂ a) : IsUnit (Z - K a) := by
    apply (ContinuousMap.isUnit_iff_forall_isUnit _).mpr
    intro z
    exact ha z.property
  have hi : ContDiffOn 𝕜 n (fun a => Ring.inverse (Z - K a))
      {a : A | sphere c |r| ⊆ resolventSet ℂ a} := by
    intro a ha
    have hd := contDiffAt_ringInverse 𝕜 (n := n) (hu a ha).unit
    rw [(hu a ha).unit_spec] at hd
    exact hd.comp_contDiffWithinAt a hg.contDiffWithinAt
  have hj := ((ContinuousMap.circleIntegralCLM (E := A) c r).restrictScalars 𝕜).contDiff.comp_contDiffOn hi
  apply hj.congr
  intro a ha
  symm
  change (∫ θ : ℝ in 0..2 * Real.pi, deriv (circleMap c r) θ •
    (Ring.inverse (Z - K a)) ⟨circleMap c r θ, circleMap_mem_sphere' c r θ⟩) = _
  apply intervalIntegral.integral_congr
  intro θ _
  exact congrArg (deriv (circleMap c r) θ • ·)
    (ContinuousMap.ringInverse_apply (Z - K a) (hu a ha) _)

theorem ContDiffOn.circleIntegral_resolvent {E : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {f : E → A} {s : Set E} {n : WithTop ℕ∞}
    (hf : ContDiffOn 𝕜 n f s) (c : ℂ) (r : ℝ)
    (hs : ∀ x ∈ s, sphere c |r| ⊆ resolventSet ℂ (f x)) :
    ContDiffOn 𝕜 n (fun x => ∮ z in C(c, r), resolvent (f x) z) s :=
  (contDiffOn_circleIntegral_resolvent c r).comp hf hs
