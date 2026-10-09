import DifferentialGeometry.Analysis.Integration.Measure.Parametric.FiniteIntegral
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Topology.Compactness.Compact

/-!
# Smooth dependence of interval integrals on parameters, on non-product open domains

Supplier of blueprint LC59 (`master207A.tex:23320`, the fibre integral
`Q(x, u) = c + ∫_c^u w(x, s) ds` and its rewriting `(u - c) ∫_0^1 w(x, c + t(u - c)) dt`).

The tree already proves smoothness of a parametric integral over a compact parameter set
(`DifferentialGeometry.Integral.Measure.contDiffOn_integral_subtype_of_isCompact`, every finite
order and `∞`, values in any normed space) and the variable-endpoint integral on a PRODUCT domain
`Ioo a b ×ˢ U` (`contDiffOn_intervalIntegral_param`, Thurston chapter-7 calculus). LC59 needs the
variable-endpoint integral on an open set `Ω ⊆ G × ℝ` that is not a product (the open subgraph of a
merely continuous height), so this file states:

* `intervalIntegral_eq_smul_integral_unitInterval`: `∫_c^u g = (u - c) • ∫_{[0,1]} g((u - c) t + c)`;
* `contDiffOn_intervalIntegral_unit`: `y ↦ ∫_0^1 w(y, t) dt` is `C^n` on `{y | {y} × [0,1] ⊆ Ω}`
  (tube lemma, no openness of this set is needed);
* `contDiffOn_intervalIntegral_of_segment_subset`: `(y, u) ↦ ∫_c^u w(y, s) ds` is `C^n` on every
  open `U` whose vertical segments from height `c` lie in `Ω`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

open DifferentialGeometry.Integral.Measure

variable {G V : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The interval integral over `[0, 1]` as the integral over the subtype `unitInterval`. -/
theorem intervalIntegral_zero_one_eq_integral_unitInterval (g : ℝ → V) :
    (∫ t in (0 : ℝ)..1, g t) = ∫ t : unitInterval, g t := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc,
    unitInterval.volume_def]
  exact (integral_subtype_comap measurableSet_Icc g).symm

/-- Substitution `s = (u - c) t + c` in a variable-endpoint interval integral. -/
theorem intervalIntegral_eq_smul_integral_unitInterval (g : ℝ → V) (c u : ℝ) :
    (∫ s in c..u, g s) = (u - c) • ∫ t : unitInterval, g ((u - c) * t + c) := by
  have hsub := intervalIntegral.smul_integral_comp_mul_add (a := 0) (b := 1) g (u - c) c
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at hsub
  rw [← hsub, intervalIntegral_zero_one_eq_integral_unitInterval]

/-- The affine point `(u - c) t + c`, `t ∈ [0, 1]`, lies on the segment between `c` and `u`. -/
theorem mul_add_mem_uIcc {c u t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (u - c) * t + c ∈ uIcc c u := by
  rcases le_total c u with h | h
  · rw [uIcc_of_le h]
    constructor <;> nlinarith [ht.1, ht.2]
  · rw [uIcc_of_ge h]
    constructor <;> nlinarith [ht.1, ht.2]

/-- **Parametric integral over `[0, 1]` on a non-product open domain.** If `w` is `C^n` on an
open `Ω ⊆ G × ℝ`, then `y ↦ ∫_0^1 w(y, t) dt` is `C^n` on the set of `y` whose whole vertical
segment `{y} × [0, 1]` lies in `Ω`. -/
theorem contDiffOn_intervalIntegral_unit {n : ℕ∞} {Ω : Set (G × ℝ)} (hΩ : IsOpen Ω)
    {w : G × ℝ → V} (hw : ContDiffOn ℝ n w Ω) :
    ContDiffOn ℝ n (fun y : G => ∫ t in (0 : ℝ)..1, w (y, t))
      {y | ∀ t ∈ Icc (0 : ℝ) 1, (y, t) ∈ Ω} := by
  intro y₀ hy₀
  have hsub₀ : ({y₀} : Set G) ×ˢ Icc (0 : ℝ) 1 ⊆ Ω := by
    rintro ⟨y, t⟩ ⟨hy, ht⟩
    obtain rfl : y = y₀ := hy
    exact hy₀ t ht
  obtain ⟨U, T, hU, -, hyU, hIT, hUT⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hΩ hsub₀
  have hUΩ : U ×ˢ Icc (0 : ℝ) 1 ⊆ Ω := fun q hq => hUT ⟨hq.1, hIT hq.2⟩
  have hint := contDiffOn_integral_subtype_of_isCompact n isCompact_Icc
    (volume : Measure unitInterval) hU hΩ hUΩ hw
  have hcongr : ContDiffOn ℝ n (fun y : G => ∫ t in (0 : ℝ)..1, w (y, t)) U :=
    hint.congr fun y _ => intervalIntegral_zero_one_eq_integral_unitInterval (fun t => w (y, t))
  exact (hcongr.contDiffAt (hU.mem_nhds (hyU (mem_singleton y₀)))).contDiffWithinAt

/-- **Variable-endpoint parametric interval integral on a non-product open domain.** If `w` is
`C^n` on an open `Ω ⊆ G × ℝ` and every vertical segment from height `c` to a point of the open set
`U` lies in `Ω`, then `(y, u) ↦ ∫_c^u w(y, s) ds` is `C^n` on `U`. -/
theorem contDiffOn_intervalIntegral_of_segment_subset {n : ℕ∞} {Ω : Set (G × ℝ)}
    (hΩ : IsOpen Ω) {w : G × ℝ → V} (hw : ContDiffOn ℝ n w Ω) (c : ℝ) {U : Set (G × ℝ)}
    (hU : IsOpen U) (hUΩ : ∀ p ∈ U, ∀ s ∈ uIcc c p.2, (p.1, s) ∈ Ω) :
    ContDiffOn ℝ n (fun p : G × ℝ => ∫ s in c..p.2, w (p.1, s)) U := by
  let φ : (G × ℝ) × ℝ → G × ℝ := fun q => (q.1.1, (q.1.2 - c) * q.2 + c)
  have hφ : ContDiff ℝ n φ :=
    contDiff_fst.fst.prodMk
      (((contDiff_fst.snd.sub contDiff_const).mul contDiff_snd).add contDiff_const)
  have hΩ' : IsOpen (φ ⁻¹' Ω) := hΩ.preimage hφ.continuous
  have hsub : U ×ˢ Icc (0 : ℝ) 1 ⊆ φ ⁻¹' Ω := by
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    exact hUΩ p hp _ (mul_add_mem_uIcc ht)
  have hf : ContDiffOn ℝ n (w ∘ φ) (φ ⁻¹' Ω) := hw.comp hφ.contDiffOn fun _ hq => hq
  have hint := contDiffOn_integral_subtype_of_isCompact n isCompact_Icc
    (volume : Measure unitInterval) hU hΩ' hsub hf
  have hmul := (contDiffOn_snd.sub (contDiffOn_const (c := c))).smul hint
  refine hmul.congr fun p _ => ?_
  exact intervalIntegral_eq_smul_integral_unitInterval (fun s => w (p.1, s)) c p.2

end DifferentialGeometry.Analysis
