import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

set_option autoImplicit false

noncomputable section

variable {𝕜 R E A : Type*} [NontriviallyNormedField 𝕜] [CommSemiring R]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedRing A] [NormedAlgebra 𝕜 A] [Algebra R A] [CompleteSpace A]

theorem ContDiffWithinAt.resolvent
    {f : E → A} {s : Set E} {x : E} {n : WithTop ℕ∞}
    (hf : ContDiffWithinAt 𝕜 n f s x) {μ : R} (hμ : μ ∈ resolventSet R (f x)) :
    ContDiffWithinAt 𝕜 n (fun y => resolvent (f y) μ) s x := by
  have hi := contDiffAt_ringInverse 𝕜 (n := n) hμ.unit
  rw [hμ.unit_spec] at hi
  exact hi.comp_contDiffWithinAt x (contDiffWithinAt_const.sub hf)

theorem ContDiffAt.resolvent
    {f : E → A} {x : E} {n : WithTop ℕ∞}
    (hf : ContDiffAt 𝕜 n f x) {μ : R} (hμ : μ ∈ resolventSet R (f x)) :
    ContDiffAt 𝕜 n (fun y => resolvent (f y) μ) x :=
  ContDiffWithinAt.resolvent hf hμ

theorem ContDiffOn.resolvent
    {f : E → A} {s : Set E} {n : WithTop ℕ∞} (hf : ContDiffOn 𝕜 n f s)
    {μ : R} (hμ : ∀ x ∈ s, μ ∈ resolventSet R (f x)) :
    ContDiffOn 𝕜 n (fun x => resolvent (f x) μ) s :=
  fun x hx => (hf x hx).resolvent (hμ x hx)

theorem ContDiff.resolvent
    {f : E → A} {n : WithTop ℕ∞} (hf : ContDiff 𝕜 n f)
    {μ : R} (hμ : ∀ x, μ ∈ resolventSet R (f x)) :
    ContDiff 𝕜 n (fun x => resolvent (f x) μ) :=
  contDiff_iff_contDiffAt.mpr (fun x => hf.contDiffAt.resolvent (hμ x))

theorem HasFDerivAt.resolvent
    {f : E → A} {f' : E →L[𝕜] A} {x : E} (hf : HasFDerivAt f f' x)
    {μ : R} (hμ : μ ∈ resolventSet R (f x)) :
    HasFDerivAt (fun y => resolvent (f y) μ)
      ((ContinuousLinearMap.mulLeftRight 𝕜 A (resolvent (f x) μ) (resolvent (f x) μ)).comp f') x := by
  have hi : HasFDerivAt Ring.inverse _ (algebraMap R A μ - f x) :=
    hasFDerivAt_ringInverse (𝕜 := 𝕜) hμ.unit
  have hb : HasFDerivAt (fun y => algebraMap R A μ - f y) (-f') x := by
    simpa using! (hasFDerivAt_const (algebraMap R A μ) x).sub hf
  simpa [spectrum.resolvent_eq hμ] using! hi.comp x hb

theorem DifferentiableAt.norm_fderiv_resolvent_le
    {f : E → A} {x : E} (hf : DifferentiableAt 𝕜 f x)
    {μ : R} (hμ : μ ∈ resolventSet R (f x)) :
    ‖fderiv 𝕜 (fun y => resolvent (f y) μ) x‖ ≤
      ‖resolvent (f x) μ‖ ^ 2 * ‖fderiv 𝕜 f x‖ := by
  rw [(hf.hasFDerivAt.resolvent hμ).fderiv]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact mul_le_mul_of_nonneg_right
    (by simpa only [pow_two] using (ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le 𝕜 A
      (resolvent (f x) μ) (resolvent (f x) μ))) (norm_nonneg _)
