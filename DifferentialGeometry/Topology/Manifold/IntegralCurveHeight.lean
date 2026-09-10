import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set Filter Function Topology Manifold
open scoped ContDiff

namespace Poincare.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

set_option backward.isDefEq.respectTransparency false in
theorem height_eq_add_mul_time {u : M → ℝ} {v : (x : M) → TangentSpace I x} {γ : ℝ → M} {ε κ : ℝ}
    (hε : 0 < ε) (hu : MDifferentiable I 𝓘(ℝ) u)
    (hunit : ∀ x, mfderiv I 𝓘(ℝ) u x (v x) = κ)
    (hγ : IsMIntegralCurveOn γ v (Ico 0 ε)) :
    ∀ t ∈ Ico 0 ε, u (γ t) = u (γ 0) + κ * t := by
  have hd : ∀ t ∈ Ico 0 ε, HasDerivWithinAt (u ∘ γ) κ (Ico 0 ε) t := by
    intro t ht
    have hc := (hu (γ t)).hasMFDerivAt.comp_hasMFDerivWithinAt t (hγ t ht)
    rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt] at hc
    apply hc.congr_fderiv
    apply ContinuousLinearMap.ext
    intro a
    change ℝ at a
    change mfderiv I 𝓘(ℝ) u (γ t) (a • v (γ t)) = a • κ
    rw [map_smul, hunit]
  have hg : ∀ t ∈ Ico 0 ε, HasDerivWithinAt (fun s ↦ u (γ 0) + κ * s) κ (Ico 0 ε) t :=
    fun t _ ↦ by
      convert! ((hasDerivWithinAt_id t (Ico 0 ε)).const_mul κ).const_add (u (γ 0)) using 1
      simp
  have heq := (convex_Ico (0 : ℝ) ε).eqOn_of_fderivWithin_eq
    (fun t ht ↦ (hd t ht).differentiableWithinAt)
    (fun t ht ↦ (hg t ht).differentiableWithinAt)
    (uniqueDiffOn_Ico 0 ε)
    (fun {t} ht ↦ ((hd t ht).hasFDerivWithinAt.fderivWithin (uniqueDiffOn_Ico 0 ε t ht)).trans
      ((hg t ht).hasFDerivWithinAt.fderivWithin (uniqueDiffOn_Ico 0 ε t ht)).symm)
    (show (0 : ℝ) ∈ Ico 0 ε from ⟨le_rfl, hε⟩) (by simp)
  exact fun t ht ↦ heq ht

end Poincare.Topology.Manifold
