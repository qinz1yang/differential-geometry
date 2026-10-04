import DifferentialGeometry.Geometry.Comparison.ModelAngleMonotone

/-!
# Monotonicity of four-point comparison in the curvature bound

A lower curvature bound `-κ` in the four-point comparison sense implies the bound `-κ'` for every
`κ' ≥ κ ≥ 0`: each of the three model angles can only decrease
(`comparisonAngleNegCurvature_le_of_le`), so the sum stays at most `2π`.

`fourPointComparison κ s` (on a set; `s = univ` is the global form) is the only curvature-indexed
four-point predicate in the tree; the local form used by AC55,
`∀ z ∈ U, ∃ Ω, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω`, is covered by
`fourPointComparison.local_of_le`. `fourPointComparison.forall_ge` is the family form taken by
the chapter 13 kernels (LC66, LC76, LC77): `∀ K, κ ≤ K → fourPointComparison K s`.
-/

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

/-- Four-point comparison at curvature `-κ` (`κ ≥ 0`) implies it at every curvature `-κ' ≤ -κ`. -/
theorem fourPointComparison.of_le {X : Type*} [MetricSpace X] {κ κ' : ℝ} {s : Set X}
    (h : fourPointComparison κ s) (hκ : 0 ≤ κ) (hκκ' : κ ≤ κ') :
    fourPointComparison κ' s := by
  intro x hx a ha b hb c hc hax hbx hcx
  have hangle (u v : X) (hu : u ≠ x) (hv : v ≠ x) :
      comparisonAngleNegCurvature κ' (dist x u) (dist x v) (dist u v) ≤
        comparisonAngleNegCurvature κ (dist x u) (dist x v) (dist u v) :=
    comparisonAngleNegCurvature_le_of_le hκ hκκ' (dist_pos.mpr hu.symm) (dist_pos.mpr hv.symm)
  have hh := h x hx a ha b hb c hc hax hbx hcx
  linarith [hangle a b hax hbx, hangle b c hbx hcx, hangle c a hcx hax]

/-- The local form of `fourPointComparison.of_le`: open neighbourhoods carrying four-point
comparison at curvature `-κ` carry it at every curvature `-κ' ≤ -κ`. -/
theorem fourPointComparison.local_of_le {X : Type*} [MetricSpace X] {κ κ' : ℝ} {U : Set X}
    (h : ∀ z ∈ U, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω)
    (hκ : 0 ≤ κ) (hκκ' : κ ≤ κ') :
    ∀ z ∈ U, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ' Ω ∧ z ∈ Ω := by
  intro z hz
  obtain ⟨Ω, hΩ, hcomp, hzΩ⟩ := h z hz
  exact ⟨Ω, hΩ, hcomp.of_le hκ hκκ', hzΩ⟩

/-- Four-point comparison at one level `-κ` (`κ ≥ 0`) gives the whole family
`∀ K, κ ≤ K → fourPointComparison K s` assumed by the chapter 13 kernels. -/
theorem fourPointComparison.forall_ge {X : Type*} [MetricSpace X] {κ : ℝ} {s : Set X}
    (h : fourPointComparison κ s) (hκ : 0 ≤ κ) :
    ∀ K : ℝ, κ ≤ K → fourPointComparison K s :=
  fun _ hK => h.of_le hκ hK

end DifferentialGeometry.Geometry.Comparison.Toponogov
