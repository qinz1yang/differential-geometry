import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Topology.Order.Real

/-!
# A scalar comparison bound for `j'' = -k j` with `0 ≤ k ≤ Λ`

The two-dimensional transverse Jacobi bound (lane CMS-J, S-SHIFT2) reduces to the following
elementary statement. Let `j` satisfy `j(0) = 1`, `j'(0) = 0` and, at every point of `[0, ρ)` where
`j > 0`, `j'' = -k j` with `0 ≤ k ≤ Λ`. If `Λ ρ² ≤ 1`, then `1/2 ≤ j ≤ 1` on `[0, ρ)`
(`scalarJacobi_mem_Icc`).

Proof: while `j > 0`, `j'' ≤ 0` gives `j' ≤ 0` and `j ≤ 1`; then `j'' ≥ -Λ` gives `j' ≥ -Λ s` and
`j ≥ 1 - Λ s² / 2 ≥ 1/2` (`scalarJacobi_bounds_of_pos`). A first zero of `j` would be a limit of points
where `j ≥ 1/2`; continuity excludes it.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

/-- **Bounds while positive.** On `[0, T)`, if `j > 0` there and `j'' = -k j` with `0 ≤ k ≤ Λ`,
`j(0) = 1`, `j'(0) = 0`, then `1 - Λ s² / 2 ≤ j s ≤ 1`. -/
theorem scalarJacobi_bounds_of_pos {j k : ℝ → ℝ} {T Λ : ℝ} (hΛ : 0 ≤ Λ) (h0 : j 0 = 1)
    (h0' : deriv j 0 = 0)
    (hder : ∀ s ∈ Ico 0 T, HasDerivAt j (deriv j s) s ∧
      HasDerivAt (deriv j) (-(k s * j s)) s)
    (hk : ∀ s ∈ Ico 0 T, 0 ≤ k s ∧ k s ≤ Λ) (hpos : ∀ s ∈ Ico 0 T, 0 < j s) :
    ∀ s ∈ Ico 0 T, 1 - Λ * s ^ 2 / 2 ≤ j s ∧ j s ≤ 1 := by
  intro s hs
  have h0D : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, lt_of_le_of_lt hs.1 hs.2⟩
  have hD : Convex ℝ (Ico (0 : ℝ) T) := convex_Ico 0 T
  have hint : interior (Ico (0 : ℝ) T) = Ioo 0 T := interior_Ico
  have hsub : ∀ x ∈ interior (Ico (0 : ℝ) T), x ∈ Ico (0 : ℝ) T := by
    intro x hx
    rw [hint] at hx
    exact Ioo_subset_Ico_self hx
  -- `j'` is antitone
  have hj'anti : AntitoneOn (deriv j) (Ico 0 T) := by
    refine antitoneOn_of_deriv_nonpos hD
      (fun x hx => (hder x hx).2.continuousAt.continuousWithinAt)
      (fun x hx => (hder x (hsub x hx)).2.differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [(hder x (hsub x hx)).2.deriv]
    exact neg_nonpos.mpr (mul_nonneg (hk x (hsub x hx)).1 (hpos x (hsub x hx)).le)
  have hj'le : ∀ x ∈ Ico (0 : ℝ) T, deriv j x ≤ 0 := by
    intro x hx
    have h := hj'anti h0D hx hx.1
    rwa [h0'] at h
  -- `j` is antitone, so `j ≤ 1`
  have hjanti : AntitoneOn j (Ico 0 T) := by
    refine antitoneOn_of_deriv_nonpos hD
      (fun x hx => (hder x hx).1.continuousAt.continuousWithinAt)
      (fun x hx => (hder x (hsub x hx)).1.differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [(hder x (hsub x hx)).1.deriv]
    exact hj'le x (hsub x hx)
  have hjle : ∀ x ∈ Ico (0 : ℝ) T, j x ≤ 1 := by
    intro x hx
    have h := hjanti h0D hx hx.1
    rwa [h0] at h
  -- `j' + Λ s` is monotone, so `j' ≥ -Λ s`
  have hf : ∀ x ∈ Ico (0 : ℝ) T,
      HasDerivAt (fun y => deriv j y + Λ * y) (-(k x * j x) + Λ) x := by
    intro x hx
    have h := (hder x hx).2.add ((hasDerivAt_id x).const_mul Λ)
    rw [mul_one] at h
    exact h
  have hfmono : MonotoneOn (fun y => deriv j y + Λ * y) (Ico 0 T) := by
    refine monotoneOn_of_deriv_nonneg hD
      (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hf x (hsub x hx)).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    have hx' := hsub x hx
    rw [(hf x hx').deriv]
    have hk1 := (hk x hx').1
    have hk2 := (hk x hx').2
    have hj1 := hjle x hx'
    have hj0 := hpos x hx'
    have h1 : k x * j x ≤ Λ * j x := mul_le_mul_of_nonneg_right hk2 hj0.le
    have h2 : Λ * j x ≤ Λ := mul_le_of_le_one_right hΛ hj1
    linarith
  have hj'ge : ∀ x ∈ Ico (0 : ℝ) T, 0 ≤ deriv j x + Λ * x := by
    intro x hx
    have h := hfmono h0D hx hx.1
    simp only [h0', mul_zero, add_zero] at h
    exact h
  -- `j + Λ s² / 2` is monotone, so `j ≥ 1 - Λ s² / 2`
  have hF : ∀ x ∈ Ico (0 : ℝ) T,
      HasDerivAt (fun y => j y + Λ * y ^ 2 / 2) (deriv j x + Λ * x) x := by
    intro x hx
    have h := (hder x hx).1.add (((hasDerivAt_pow 2 x).const_mul Λ).div_const 2)
    convert h using 1
    ring
  have hFmono : MonotoneOn (fun y => j y + Λ * y ^ 2 / 2) (Ico 0 T) := by
    refine monotoneOn_of_deriv_nonneg hD
      (fun x hx => (hF x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hF x (hsub x hx)).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [(hF x (hsub x hx)).deriv]
    exact hj'ge x (hsub x hx)
  have hFs := hFmono h0D hs hs.1
  simp only [h0] at hFs
  refine ⟨?_, hjle s hs⟩
  have : (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [this, mul_zero, zero_div, add_zero] at hFs
  linarith

/-- **Scalar Jacobi comparison.** If `j(0) = 1`, `j'(0) = 0`, `j` is continuous on `[0, ρ)`, and at
every point of `[0, ρ)` where `j > 0` it satisfies `j'' = -k j` with `0 ≤ k ≤ Λ`, and `Λ ρ² ≤ 1`, then
`1/2 ≤ j ≤ 1` on `[0, ρ)`. -/
theorem scalarJacobi_mem_Icc {j k : ℝ → ℝ} {ρ Λ : ℝ} (hΛ : 0 ≤ Λ) (hρΛ : Λ * ρ ^ 2 ≤ 1)
    (hcont : ContinuousOn j (Ico 0 ρ)) (h0 : j 0 = 1) (h0' : deriv j 0 = 0)
    (hder : ∀ s ∈ Ico 0 ρ, 0 < j s →
      HasDerivAt j (deriv j s) s ∧ HasDerivAt (deriv j) (-(k s * j s)) s)
    (hk : ∀ s ∈ Ico 0 ρ, 0 ≤ k s ∧ k s ≤ Λ) :
    ∀ s ∈ Ico 0 ρ, 1 / 2 ≤ j s ∧ j s ≤ 1 := by
  -- bounds on any initial interval where `j` stays positive
  have hbd : ∀ T ≤ ρ, (∀ s ∈ Ico 0 T, 0 < j s) → ∀ s ∈ Ico 0 T, 1 / 2 ≤ j s ∧ j s ≤ 1 := by
    intro T hT hpos s hs
    have hsρ : ∀ x ∈ Ico (0 : ℝ) T, x ∈ Ico (0 : ℝ) ρ :=
      fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hT⟩
    have h := scalarJacobi_bounds_of_pos hΛ h0 h0'
      (fun x hx => hder x (hsρ x hx) (hpos x hx)) (fun x hx => hk x (hsρ x hx)) hpos s hs
    refine ⟨?_, h.2⟩
    have hs2 : s ^ 2 ≤ ρ ^ 2 := by
      have := hsρ s hs
      exact pow_le_pow_left₀ hs.1 this.2.le 2
    have : Λ * s ^ 2 ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hs2 hΛ) hρΛ
    linarith [h.1]
  suffices hpos : ∀ s ∈ Ico 0 ρ, 0 < j s from hbd ρ le_rfl hpos
  by_contra hneg
  push Not at hneg
  obtain ⟨s₀, hs₀, hjs₀⟩ := hneg
  set A : Set ℝ := {s | s ∈ Ico 0 ρ ∧ j s ≤ 0} with hA
  have hAne : A.Nonempty := ⟨s₀, hs₀, hjs₀⟩
  have hAbdd : BddBelow A := ⟨0, fun s hs => hs.1.1⟩
  set T := sInf A with hTdef
  have hT0 : 0 ≤ T := le_csInf hAne fun s hs => hs.1.1
  have hTs₀ : T ≤ s₀ := csInf_le hAbdd ⟨hs₀, hjs₀⟩
  have hTρ : T ∈ Ico (0 : ℝ) ρ := ⟨hT0, lt_of_le_of_lt hTs₀ hs₀.2⟩
  have hbefore : ∀ s ∈ Ico 0 T, 0 < j s := by
    intro s hs
    by_contra hle
    push Not at hle
    have hsA : s ∈ A := ⟨⟨hs.1, lt_of_lt_of_le hs.2 (le_of_lt hTρ.2)⟩, hle⟩
    exact absurd (csInf_le hAbdd hsA) (not_le.mpr hs.2)
  have hcT : ContinuousWithinAt j (Ico 0 ρ) T := hcont T hTρ
  -- `j T ≤ 0`
  have hjT : j T ≤ 0 := by
    have hcl : T ∈ closure A := csInf_mem_closure hAne hAbdd
    have : (𝓝[A] T).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
    have htend : Tendsto j (𝓝[A] T) (𝓝 (j T)) :=
      (hcT.mono fun s hs => hs.1).tendsto
    exact le_of_tendsto htend (eventually_nhdsWithin_of_forall fun s hs => hs.2)
  have hTpos : 0 < T := by
    rcases hT0.eq_or_lt with h | h
    · rw [← h, h0] at hjT
      norm_num at hjT
    · exact h
  -- `j T ≥ 1/2` from the left
  have hjT' : 1 / 2 ≤ j T := by
    have hcl : T ∈ closure (Ico 0 T) := by
      rw [closure_Ico hTpos.ne]
      exact ⟨hT0, le_rfl⟩
    have : (𝓝[Ico 0 T] T).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
    have htend : Tendsto j (𝓝[Ico 0 T] T) (𝓝 (j T)) :=
      (hcT.mono fun s hs => ⟨hs.1, lt_of_lt_of_le hs.2 hTρ.2.le⟩).tendsto
    exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall fun s hs =>
      (hbd T hTρ.2.le hbefore s hs).1)
  linarith

end DifferentialGeometry.Analysis
