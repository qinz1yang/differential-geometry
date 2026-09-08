import DifferentialGeometry.Topology.Manifold.Path.Regularity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

noncomputable section

open Filter Set
open scoped ContDiff Manifold Topology

namespace Path

section
variable {X : Type*} [TopologicalSpace X] {x y : X}

def withSittingInstants (p : Path x y) : Path x y :=
  p.reparam
    (fun t => ⟨Real.smoothTransition (3 * t - 1),
      Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)
    (by fun_prop)
    (Subtype.ext (Real.smoothTransition.zero_of_nonpos (by norm_num)))
    (Subtype.ext (Real.smoothTransition.one_of_one_le (by norm_num)))

@[simp] theorem withSittingInstants_apply (p : Path x y) (t : unitInterval) :
    p.withSittingInstants t = p
      ⟨Real.smoothTransition (3 * t - 1),
        Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ := rfl

@[simp] theorem range_withSittingInstants (p : Path x y) :
    range p.withSittingInstants = range p := Path.range_reparam _ _ _ _

@[simp] theorem withSittingInstants_refl (x : X) :
    (Path.refl x).withSittingInstants = Path.refl x := Path.refl_reparam _ _ _

theorem extend_withSittingInstants (p : Path x y) :
    p.withSittingInstants.extend =
      p.extend ∘ fun t : ℝ => Real.smoothTransition (3 * t - 1) := by
  funext t
  by_cases ht0 : t ≤ 0
  · rw [Path.extend_of_le_zero _ ht0]
    simp only [Function.comp_apply,
      Real.smoothTransition.zero_of_nonpos (show 3 * t - 1 ≤ 0 by linarith),
      Path.extend_zero]
  by_cases ht1 : 1 ≤ t
  · rw [Path.extend_of_one_le _ ht1]
    simp only [Function.comp_apply,
      Real.smoothTransition.one_of_one_le (show 1 ≤ 3 * t - 1 by linarith),
      Path.extend_one]
  rw [Path.extend_apply _ ⟨(not_le.mp ht0).le, (not_le.mp ht1).le⟩]
  exact (p.extend_apply ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩).symm

theorem withSittingInstants_eventuallyEq_zero (p : Path x y) :
    p.withSittingInstants.extend =ᶠ[𝓝 0] fun _ : ℝ => x := by
  rw [extend_withSittingInstants]
  filter_upwards [eventually_lt_nhds (show (0 : ℝ) < 1 / 3 by norm_num)] with t ht
  simp only [Function.comp_apply,
    Real.smoothTransition.zero_of_nonpos (show 3 * t - 1 ≤ 0 by linarith),
    Path.extend_zero]

theorem withSittingInstants_eventuallyEq_one (p : Path x y) :
    p.withSittingInstants.extend =ᶠ[𝓝 1] fun _ : ℝ => y := by
  rw [extend_withSittingInstants]
  filter_upwards [eventually_gt_nhds (show (2 / 3 : ℝ) < 1 by norm_num)] with t ht
  simp only [Function.comp_apply,
    Real.smoothTransition.one_of_one_le (show 1 ≤ 3 * t - 1 by linarith),
    Path.extend_one]

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x y : M}

theorem isContMDiffWithSittingInstants_withSittingInstants {n : ℕ∞} (p : Path x y)
    (hp : ContMDiffOn 𝓘(ℝ, ℝ) I n p.extend (Icc 0 1)) :
    IsContMDiffWithSittingInstants (I := I) n p.withSittingInstants where
  contMDiff := by
    rw [extend_withSittingInstants, ← contMDiffOn_univ]
    apply hp.comp
    · rw [contMDiffOn_univ, contMDiff_iff_contDiff]
      apply ContDiff.of_le _ (show (n : ℕ∞ω) ≤ (∞ : ℕ∞ω) by exact_mod_cast (le_top : n ≤ ⊤))
      exact Real.smoothTransition.contDiff.comp
        ((contDiff_const.mul contDiff_id).sub contDiff_const)
    · intro t _
      exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  eventuallyEq_zero := p.withSittingInstants_eventuallyEq_zero
  eventuallyEq_one := p.withSittingInstants_eventuallyEq_one

end Path
