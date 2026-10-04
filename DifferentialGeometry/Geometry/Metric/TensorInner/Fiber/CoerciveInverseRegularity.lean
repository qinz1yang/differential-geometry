import DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.CoerciveBilinearInverse
import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Finite-order regularity of the actual coercive bilinear inverse

The inverse operator uses the original bilinear form and agrees with its coercive Riesz
inverse. Regularity follows locally from inversion at the actual invertible Gram operator.
-/

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def coerciveBilinearInverse (B : E →L[ℝ] E →L[ℝ] ℝ) : (E →L[ℝ] ℝ) →L[ℝ] E :=
  (Ring.inverse (IsCoercive.gramCLM B)).comp
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem sharpCLM_eq_coerciveBilinearInverse {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : IsCoercive B) : hB.sharpCLM = coerciveBilinearInverse B := by
  ext eta
  rw [IsCoercive.sharpCLM_apply, IsCoercive.sharp_eq_inverse]
  rfl

theorem contMDiffAt_coerciveBilinearInverse
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {n : ℕ∞ω} {b : M → E →L[ℝ] E →L[ℝ] ℝ} {x : M}
    (hb : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) n b x)
    (hco : IsCoercive (b x)) :
    ContMDiffAt I 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E) n
      (fun y => coerciveBilinearInverse (b y)) x := by
  obtain ⟨u, hu⟩ := IsCoercive.gramCLM_isUnit hco
  have hinv : ContDiffAt ℝ n (Ring.inverse : (E →L[ℝ] E) → E →L[ℝ] E)
      (IsCoercive.gramCLM (b x)) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  let G : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E := IsCoercive.gramCLM
  have hgram := G.contDiff.contMDiff.contMDiffAt.comp x hb
  have hi := hinv.contMDiffAt.comp x hgram
  exact hi.clm_comp contMDiffAt_const

theorem contDiff_real_inner_inverse (n : ℕ∞ω) :
    ContDiff ℝ n (fun _point : ℝ => coerciveBilinearInverse (innerSL ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)) := by
  have hc : IsCoercive (innerSL ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) :=
    ContinuousLinearMap.isCoercive_of_posDef _ (fun v hv => by
      change 0 < (v : ℝ) * v
      exact mul_self_pos.mpr hv)
  apply contMDiff_iff_contDiff.mp
  intro x
  exact contMDiffAt_coerciveBilinearInverse (x := x) contMDiffAt_const hc

end DifferentialGeometry
