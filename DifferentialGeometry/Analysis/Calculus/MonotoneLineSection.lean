import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# A continuous section along a monotone line (CGP03, EGP05)

Blueprint 207B, CGP03 (`lem:fibration-actual-inner-sections`, B:4004–4055), edge case: along the core
line `a ↦ j(a, z₀)` of LFR28's buffered product embedding, the tangential coordinate `η ∘ j` is
continuous and strictly increasing (`∂ₐ(η j) > 3/4`), and its endpoint values at `a = p, q` enclose
the target interval. Strict monotonicity and the intermediate value theorem give a continuous inverse
on that interval; composing with `j` produces the section `s` with `η (s a) = a`. The same argument
gives EGP05's exact edge section. Only continuity of `j` is used.

The statement is generic: `j : ℝ → X` into any topological space and a real coordinate `η : X → ℝ`.
-/

set_option autoImplicit false
open Set

namespace DifferentialGeometry.Analysis

/-- A strictly monotone continuous coordinate along a continuous line whose endpoint values
enclose `[u, v]` has a continuous section over `[u, v]` through the line. -/
theorem exists_continuousOn_section_of_strictMonoOn {X : Type*} [TopologicalSpace X]
    (j : ℝ → X) (η : X → ℝ) {p q u v : ℝ} (hpq : p ≤ q) (hj : ContinuousOn j (Icc p q))
    (hφ : ContinuousOn (η ∘ j) (Icc p q)) (hmono : StrictMonoOn (η ∘ j) (Icc p q))
    (hu : η (j p) ≤ u) (hv : v ≤ η (j q)) :
    ∃ s : ℝ → X, ContinuousOn s (Icc u v) ∧
      ∀ a ∈ Icc u v, η (s a) = a ∧ s a ∈ j '' Icc p q := by
  classical
  set φ : ℝ → ℝ := η ∘ j with hφdef
  set S : Set ℝ := Icc p q
  have hsub : Icc u v ⊆ φ '' S :=
    (Icc_subset_Icc hu hv).trans (intermediate_value_Icc hpq hφ)
  have hconn : OrdConnected (φ '' S) :=
    isPreconnected_iff_ordConnected.mp (isPreconnected_Icc.image φ hφ)
  let e : S ≃o φ '' S := StrictMonoOn.orderIso φ S hmono
  have he (x : S) : ((e x : φ '' S) : ℝ) = φ x := rfl
  have hφe (w : φ '' S) : φ (e.symm w) = w := by
    rw [← he, e.apply_symm_apply]
  let s : ℝ → X := fun a => if h : a ∈ φ '' S then j (e.symm ⟨a, h⟩) else j p
  have hs (a : ℝ) (h : a ∈ φ '' S) : s a = j (e.symm ⟨a, h⟩) := by
    simp only [s, h, dite_true]
  refine ⟨s, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have heq : (Icc u v).domRestrict s =
        j ∘ (fun a : Icc u v => ((e.symm (inclusion hsub a) : S) : ℝ)) := by
      funext a
      rw [domRestrict_apply, hs a (hsub a.property)]
      rfl
    rw [heq]
    exact hj.comp_continuous (continuous_subtype_val.comp
      (e.symm.continuous.comp (continuous_inclusion hsub))) (fun a => (e.symm _).property)
  · intro a ha
    rw [hs a (hsub ha)]
    exact ⟨hφe ⟨a, hsub ha⟩, (e.symm _ : S), (e.symm _).property, rfl⟩

/-- The same section from a positive derivative of the coordinate along the line. -/
theorem exists_continuousOn_section_of_deriv_pos {X : Type*} [TopologicalSpace X]
    (j : ℝ → X) (η : X → ℝ) {p q u v : ℝ} (hpq : p ≤ q) (hj : ContinuousOn j (Icc p q))
    (hφ : ContinuousOn (η ∘ j) (Icc p q)) (hderiv : ∀ x ∈ Ioo p q, 0 < deriv (η ∘ j) x)
    (hu : η (j p) ≤ u) (hv : v ≤ η (j q)) :
    ∃ s : ℝ → X, ContinuousOn s (Icc u v) ∧
      ∀ a ∈ Icc u v, η (s a) = a ∧ s a ∈ j '' Icc p q := by
  refine exists_continuousOn_section_of_strictMonoOn j η hpq hj hφ ?_ hu hv
  refine strictMonoOn_of_deriv_pos (convex_Icc p q) hφ ?_
  rwa [interior_Icc]

/-- CGP03's endpoint enclosure: a coordinate within `3ℓ/20` of the line parameter at
`a = ± (59/10) ℓ` encloses `[-(23/4) ℓ, (23/4) ℓ]`. -/
theorem endpoint_enclosure_of_near_identity {ℓ e lo hi : ℝ} (he : e ≤ 3 / 20 * ℓ)
    (hlo : |lo - (-(59 / 10 * ℓ))| < e) (hhi : |hi - 59 / 10 * ℓ| < e) :
    lo ≤ -(23 / 4 * ℓ) ∧ 23 / 4 * ℓ ≤ hi := by
  rw [abs_lt] at hlo hhi
  constructor <;> linarith [hlo.2, hhi.1]

end DifferentialGeometry.Analysis
