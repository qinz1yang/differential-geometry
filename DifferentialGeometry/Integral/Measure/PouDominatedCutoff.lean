import DifferentialGeometry.Integral.Measure.Glue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# POU-dominated smooth cutoff for the chart-atlas partition of unity

For each base point `α : M` of a smooth manifold modelled on a finite-dimensional
inner-product space, the canonical partition-of-unity element
`chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯` is a smooth real-valued function with
values in `[0, 1]`.

This file constructs a smooth cutoff `χ : C^∞⟮I, M; ℝ⟯` *dominated* by the POU
element: pointwise `χ x ≤ K · (chartAtlasPOU I M α) x` with `K = 4`, and `χ x = 1`
whenever `(chartAtlasPOU I M α) x ≥ 1/2`. The topological support of `χ`
remains inside that of the POU element.

## Construction

We compose the POU with a smooth real auxiliary function `φ`:

  `χ x := φ ((chartAtlasPOU I M α) x)`,

where `φ : ℝ → ℝ` is built from `Real.smoothTransition`:

  `φ t := Real.smoothTransition (4 · t - 1)`.

The function `Real.smoothTransition` is `0` on `(-∞, 0]` and `1` on `[1, ∞)`,
takes values in `[0, 1]`, and is `C^∞` everywhere. The affine reparametrisation
gives `φ t = 0` for `t ≤ 1/4` and `φ t = 1` for `t ≥ 1/2`, so:

* `φ ≥ 0` and `φ ≤ 1`, hence `0 ≤ χ ≤ 1`.
* For `t ≤ 1/4`, `φ t = 0`, so `support φ ⊆ (1/4, ∞)`, and the closure under
  composition gives `tsupport χ ⊆ tsupport (POU α)`.
* For `t ≥ 1/2`, `φ t = 1`, giving the `χ = 1` clause.
* The bound `φ t ≤ 4 · t` for all `t ≥ 0` holds because either `t ≤ 1/4`
  (so `φ t = 0`) or `t ≥ 1/4` (so `4·t ≥ 1 ≥ φ t`).

## Main result

* `chartAtlasPOU_exists_dominated_cutoff` — existence of the smooth cutoff `χ`
  with the four properties described above. The explicit constants are `K = 4`
  and `ε = 1/2`.
-/

noncomputable section

open Bundle Manifold Set Function
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- An auxiliary smooth function `ℝ → ℝ` used to build the POU-dominated cutoff.
Defined as `t ↦ Real.smoothTransition (4 * t - 1)`. It vanishes for `t ≤ 1/4`,
equals `1` for `t ≥ 1/2`, takes values in `[0, 1]`, and is dominated by `4 · t`
for `t ≥ 0`. -/
def dominatedCutoffAux (t : ℝ) : ℝ := Real.smoothTransition (4 * t - 1)

namespace dominatedCutoffAux

@[simp] theorem zero : dominatedCutoffAux 0 = 0 := by
  unfold dominatedCutoffAux
  have h : (4 : ℝ) * 0 - 1 ≤ 0 := by norm_num
  exact Real.smoothTransition.zero_of_nonpos h

theorem zero_of_le_quarter {t : ℝ} (ht : t ≤ 1/4) : dominatedCutoffAux t = 0 := by
  unfold dominatedCutoffAux
  have h : (4 : ℝ) * t - 1 ≤ 0 := by linarith
  exact Real.smoothTransition.zero_of_nonpos h

theorem one_of_half_le {t : ℝ} (ht : (1 : ℝ)/2 ≤ t) : dominatedCutoffAux t = 1 := by
  unfold dominatedCutoffAux
  have h : (1 : ℝ) ≤ 4 * t - 1 := by linarith
  exact Real.smoothTransition.one_of_one_le h

theorem nonneg (t : ℝ) : 0 ≤ dominatedCutoffAux t :=
  Real.smoothTransition.nonneg _

theorem le_one (t : ℝ) : dominatedCutoffAux t ≤ 1 :=
  Real.smoothTransition.le_one _

/-- Pointwise linear domination on the nonnegative reals:
`dominatedCutoffAux t ≤ 4 · t` for all `t ≥ 0`. -/
theorem le_four_mul {t : ℝ} (ht : 0 ≤ t) : dominatedCutoffAux t ≤ 4 * t := by
  by_cases h : t ≤ 1/4
  · rw [zero_of_le_quarter h]
    linarith
  · have h' : (1 : ℝ)/4 < t := lt_of_not_ge h
    have h1 : (1 : ℝ) < 4 * t := by linarith
    have h2 : dominatedCutoffAux t ≤ 1 := le_one t
    linarith

/-- The auxiliary function is `C^∞`. -/
theorem contDiff : ContDiff ℝ ∞ dominatedCutoffAux := by
  have h_affine : ContDiff ℝ ∞ (fun t : ℝ => 4 * t - 1) :=
    (contDiff_const.mul contDiff_id).sub contDiff_const
  have h_trans : ContDiff ℝ ∞ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := ⊤))
  exact h_trans.comp h_affine

end dominatedCutoffAux

/-- **POU-dominated smooth cutoff for `chartAtlasPOU`.**

Given a smooth manifold `M` modelled on a finite-dimensional inner-product
space, and a base point `α : M`, there exists a smooth real-valued function
`χ : C^∞⟮I, M; ℝ⟯`, a positive constant `K`, and a positive constant `ε` such
that

* `0 ≤ χ x` and `χ x ≤ K · (chartAtlasPOU I M α) x` for every `x : M`;
* `χ x = 1` whenever `(chartAtlasPOU I M α) x ≥ ε`;
* the topological support of `χ` is contained in that of `chartAtlasPOU I M α`.

The explicit constants produced are `K = 4` and `ε = 1/2`.

This is the standard "POU-dominated" cutoff used in the Hebey–Aubin construction:
unlike the thickening cutoff (which extends slightly past the POU support and
therefore admits no pointwise linear bound by the POU element), this one lives
strictly inside the POU support and is dominated by it. -/
theorem chartAtlasPOU_exists_dominated_cutoff
    [T2Space M] [SigmaCompactSpace M]
    (α : M) :
    ∃ (χ : C^∞⟮I, M; ℝ⟯) (K : ℝ) (ε : ℝ), 0 < K ∧ 0 < ε ∧
      (∀ x : M, 0 ≤ χ x ∧ χ x ≤ K * (chartAtlasPOU I M α : M → ℝ) x) ∧
      (∀ x : M, ((chartAtlasPOU I M α : M → ℝ) x ≥ ε) → χ x = 1) ∧
      tsupport (χ : M → ℝ) ⊆ tsupport (chartAtlasPOU I M α : M → ℝ) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ := chartAtlasPOU I M α with hρ_def
  have hρ_contMDiff : ContMDiff I 𝓘(ℝ, ℝ) ∞ (ρ : M → ℝ) := ρ.contMDiff
  have hχ_contMDiff : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => dominatedCutoffAux ((ρ : M → ℝ) x)) :=
    dominatedCutoffAux.contDiff.comp_contMDiff hρ_contMDiff
  refine ⟨⟨fun x => dominatedCutoffAux ((ρ : M → ℝ) x), hχ_contMDiff⟩,
          4, 1/2, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · intro x
    refine ⟨?_, ?_⟩
    · exact dominatedCutoffAux.nonneg _
    · have hρ_nonneg : 0 ≤ (ρ : M → ℝ) x := by
        exact (chartAtlasPOU I M).nonneg α x
      exact dominatedCutoffAux.le_four_mul hρ_nonneg
  · intro x hx
    exact dominatedCutoffAux.one_of_half_le hx
  · have h_zero : dominatedCutoffAux 0 = 0 := dominatedCutoffAux.zero
    have h_subset : tsupport (dominatedCutoffAux ∘ (ρ : M → ℝ)) ⊆
        tsupport (ρ : M → ℝ) :=
      tsupport_comp_subset h_zero (ρ : M → ℝ)
    exact h_subset

end Measure
end Integral
end DifferentialGeometry
