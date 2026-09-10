import DifferentialGeometry.Topology.LocalDegree.Real
import DifferentialGeometry.Topology.VectorField.PartialDiffeomorphLinearization
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
open Filter Metric Set
open scoped Topology Manifold ContDiff
noncomputable section

namespace Poincare.LocalDegree

private theorem coordinate_deriv_ne_zero {n : ℕ∞ω}
    (φ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ n)
    (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ φ.source) : deriv φ x ≠ 0 := by
  have hi := Poincare.VectorField.isInvertible_mfderiv_partialDiffeomorph φ
    (ne_of_gt (zero_lt_one.trans_le hn)) hx
  have hi' : (fderiv ℝ φ x).IsInvertible := by
    simpa only [mfderiv_eq_fderiv] using! hi
  have hone := hi'.self_apply_inverse (1 : ℝ)
  rw [fderiv_eq_deriv_mul] at hone
  intro hzero
  rw [hzero, zero_mul] at hone
  exact zero_ne_one hone

private theorem real_pullback_eq_div {n : ℕ∞ω}
    (φ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ n)
    (hn : 1 ≤ n) (V : ℝ → ℝ) {x : ℝ} (hx : x ∈ φ.source) :
    _root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ V x = V (φ x) / deriv φ x := by
  have hi := Poincare.VectorField.isInvertible_mfderiv_partialDiffeomorph φ
    (ne_of_gt (zero_lt_one.trans_le hn)) hx
  have hi' : (fderiv ℝ φ x).IsInvertible := by
    simpa only [mfderiv_eq_fderiv] using! hi
  have heq := hi'.self_apply_inverse (V (φ x))
  rw [fderiv_eq_deriv_mul] at heq
  have hdiv : (fderiv ℝ φ x).inverse (V (φ x)) = V (φ x) / deriv φ x :=
    (eq_div_iff (coordinate_deriv_ne_zero φ hn hx)).mpr (by simpa only [mul_comm] using heq)
  simpa only [_root_.VectorField.mpullback_eq_pullback, _root_.VectorField.pullback] using! hdiv

theorem realIsolatedZero_mpullback_partialDiffeomorph {n : ℕ∞ω}
    (φ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ n)
    (hn : 1 ≤ n) {V : ℝ → ℝ} {x : ℝ} (hx : x ∈ φ.source)
    (hV : realIsolatedZero V (φ x)) :
    realIsolatedZero (_root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ V) x := by
  obtain ⟨R, hR⟩ := hV
  let s : Set ℝ := φ.source ∩ φ ⁻¹' closedBall (φ x) R
  have hs : s ∈ 𝓝 x :=
    inter_mem (φ.open_source.mem_nhds hx)
      ((φ.toOpenPartialHomeomorph.continuousAt hx).preimage_mem_nhds
        (closedBall_mem_nhds _ hR.pos))
  have hcomp : ContinuousOn (fun y ↦ V (φ y)) s :=
    hR.continuousOn.comp (φ.contMDiffOn.continuousOn.mono (fun _ hy ↦ hy.1)) (fun _ hy ↦ hy.2)
  have hd : ContinuousOn (deriv φ) s :=
    (φ.contMDiffOn.contDiffOn.continuousOn_deriv_of_isOpen φ.open_source hn).mono
      (fun _ hy ↦ hy.1)
  have hcont : ContinuousOn
      (_root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ V) s :=
    (hcomp.div hd (fun y hy ↦ coordinate_deriv_ne_zero φ hn hy.1)).congr
      (fun y hy ↦ real_pullback_eq_div φ hn V hy.1)
  apply realIsolatedZero_of_nhds hs hcont
  · rw [real_pullback_eq_div φ hn V hx, hR.zero, zero_div]
  · apply eventually_nhdsWithin_iff.mpr
    filter_upwards [hs] with y hy
    intro hyx
    rw [real_pullback_eq_div φ hn V hy.1]
    exact div_ne_zero (hR.nonzero _ hy.2 (fun heq ↦ hyx (φ.injOn hy.1 hx heq)))
      (coordinate_deriv_ne_zero φ hn hy.1)

private theorem positive_iff_on_preconnected {f : ℝ → ℝ} {s : Set ℝ}
    (hs : IsPreconnected s) (hc : ContinuousOn f s) (hn : ∀ y ∈ s, f y ≠ 0)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) : 0 < f a ↔ 0 < f b := by
  suffices transfer : ∀ {a b : ℝ}, a ∈ s → b ∈ s → 0 < f a → 0 < f b from
    ⟨transfer ha hb, transfer hb ha⟩
  intro a b ha hb hpos
  by_contra hnot
  obtain ⟨y, hy, hzero⟩ := hs.intermediate_value hb ha hc ⟨le_of_not_gt hnot, hpos.le⟩
  exact hn y hy hzero

private theorem degree_eq_asymmetric_endpoints {V : ℝ → ℝ} {x R l r : ℝ}
    (hV : realIsolatedZero V x) (hR : RealIsolatingRadius V x R)
    (hlmem : l ∈ closedBall x R) (hrmem : r ∈ closedBall x R) (hl : l < x) (hr : x < r) :
    realLocalDegree V x hV =
      (if 0 < V r then 1 else 0) - (if 0 < V l then 1 else 0) := by
  have hleft : Ico (x - R) x ⊆ closedBall x R := by
    intro y hy
    rw [Real.closedBall_eq_Icc]
    exact ⟨hy.1, by linarith [hy.2, hR.pos]⟩
  have hright : Ioc x (x + R) ⊆ closedBall x R := by
    intro y hy
    rw [Real.closedBall_eq_Icc]
    exact ⟨by linarith [hy.1, hR.pos], hy.2⟩
  rw [Real.closedBall_eq_Icc] at hlmem hrmem
  have hp := positive_iff_on_preconnected isPreconnected_Ioc
    (hR.continuousOn.mono hright)
    (fun y hy ↦ hR.nonzero y (hright hy) (ne_of_gt hy.1))
    (a := x + R) ⟨by linarith [hR.pos], le_rfl⟩ ⟨hr, hrmem.2⟩
  have hm := positive_iff_on_preconnected isPreconnected_Ico
    (hR.continuousOn.mono hleft)
    (fun y hy ↦ hR.nonzero y (hleft hy) (ne_of_lt hy.2))
    (a := x - R) ⟨le_rfl, by linarith [hR.pos]⟩ ⟨hlmem.1, hl⟩
  rw [realLocalDegree_eq_endpoints hV hR ⟨R, hR.pos, le_rfl⟩]
  simp only [hp, hm]

private theorem exists_coordinate_control {n : ℕ∞ω}
    (φ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ n)
    (hn : 1 ≤ n) {x R S : ℝ} (hx : x ∈ φ.source) (hR : 0 < R) (hS : 0 < S) :
    ∃ r > 0, r ≤ S ∧ ∀ y ∈ closedBall x r,
      y ∈ φ.source ∧ φ y ∈ closedBall (φ x) R ∧ (0 < deriv φ y ↔ 0 < deriv φ x) := by
  have hd : ContinuousAt (deriv φ) x :=
    (φ.contMDiffOn.contDiffOn.continuousOn_deriv_of_isOpen φ.open_source hn).continuousAt
      (φ.open_source.mem_nhds hx)
  have hsign : ∀ᶠ y in 𝓝 x, 0 < deriv φ y ↔ 0 < deriv φ x := by
    rcases lt_or_gt_of_ne (coordinate_deriv_ne_zero φ hn hx) with hneg | hpos
    · filter_upwards [hd.eventually (eventually_lt_nhds hneg)] with y hy
      exact iff_of_false (not_lt_of_gt hy) (not_lt_of_gt hneg)
    · filter_upwards [hd.eventually (eventually_gt_nhds hpos)] with y hy
      exact iff_of_true hy hpos
  have hevent : ∀ᶠ y in 𝓝 x,
      y ∈ φ.source ∧ φ y ∈ closedBall (φ x) R ∧ (0 < deriv φ y ↔ 0 < deriv φ x) := by
    filter_upwards [φ.open_source.mem_nhds hx,
      (φ.toOpenPartialHomeomorph.continuousAt hx).preimage_mem_nhds
        (closedBall_mem_nhds _ hR), hsign] with y hy hiy hdy
    exact ⟨hy, hiy, hdy⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨min S (ε / 2), lt_min hS (by positivity), min_le_left _ _, ?_⟩
  intro y hy
  exact hball (closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith)) hy)

theorem realLocalDegree_mpullback_partialDiffeomorph {n : ℕ∞ω}
    (φ : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ n)
    (hn : 1 ≤ n) {V : ℝ → ℝ} {x : ℝ} (hx : x ∈ φ.source)
    (hV : realIsolatedZero V (φ x)) :
    realLocalDegree (_root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ V) x
      (realIsolatedZero_mpullback_partialDiffeomorph φ hn hx hV) =
        realLocalDegree V (φ x) hV := by
  let P : ℝ → ℝ := _root_.VectorField.mpullback 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ V
  have hP : realIsolatedZero P x := realIsolatedZero_mpullback_partialDiffeomorph φ hn hx hV
  change realLocalDegree P x hP = realLocalDegree V (φ x) hV
  let R := hV.choose
  have hR : RealIsolatingRadius V (φ x) R := hV.choose_spec
  let S := hP.choose
  have hS : RealIsolatingRadius P x S := hP.choose_spec
  obtain ⟨r, hr, hrS, hcontrol⟩ := exists_coordinate_control φ hn hx hR.pos hS.pos
  have hPr := hS.mono hr hrS
  have hxm : x - r ∈ closedBall x r := by
    rw [Real.closedBall_eq_Icc]
    exact ⟨le_rfl, by linarith⟩
  have hxp : x + r ∈ closedBall x r := by
    rw [Real.closedBall_eq_Icc]
    exact ⟨by linarith, le_rfl⟩
  have hxc : x ∈ closedBall x r := mem_closedBall_self hr.le
  have hcφ : ContinuousOn φ (closedBall x r) :=
    φ.contMDiffOn.continuousOn.mono (fun y hy ↦ (hcontrol y hy).1)
  rcases lt_or_gt_of_ne (coordinate_deriv_ne_zero φ hn hx) with hneg | hpos
  · have hdneg : ∀ y ∈ closedBall x r, deriv φ y < 0 := by
      intro y hy
      apply lt_of_le_of_ne
      · exact le_of_not_gt (fun h ↦ not_lt_of_gt hneg ((hcontrol y hy).2.2.mp h))
      · exact coordinate_deriv_ne_zero φ hn (hcontrol y hy).1
    have hanti : StrictAntiOn φ (closedBall x r) :=
      strictAntiOn_of_deriv_neg (convex_closedBall x r) hcφ
        (fun y hy ↦ hdneg y (interior_subset hy))
    have hleft : φ (x + r) < φ x := hanti hxc hxp (by linarith)
    have hright : φ x < φ (x - r) := hanti hxm hxc (by linarith)
    have hpne : V (φ (x + r)) ≠ 0 :=
      hR.nonzero _ (hcontrol _ hxp).2.1 (ne_of_lt hleft)
    have hmne : V (φ (x - r)) ≠ 0 :=
      hR.nonzero _ (hcontrol _ hxm).2.1 (ne_of_gt hright)
    have hp : 0 < P (x + r) ↔ ¬ 0 < V (φ (x + r)) := by
      rw [show P (x + r) = V (φ (x + r)) / deriv φ (x + r) from
        real_pullback_eq_div φ hn V (hcontrol _ hxp).1,
        div_pos_iff]
      simp only [not_lt_of_gt (hdneg _ hxp), hdneg _ hxp, and_false, false_or, and_true]
      exact ⟨fun h ↦ not_lt_of_gt h, fun h ↦ lt_of_le_of_ne (le_of_not_gt h) hpne⟩
    have hm : 0 < P (x - r) ↔ ¬ 0 < V (φ (x - r)) := by
      rw [show P (x - r) = V (φ (x - r)) / deriv φ (x - r) from
        real_pullback_eq_div φ hn V (hcontrol _ hxm).1,
        div_pos_iff]
      simp only [not_lt_of_gt (hdneg _ hxm), hdneg _ hxm, and_false, false_or, and_true]
      exact ⟨fun h ↦ not_lt_of_gt h, fun h ↦ lt_of_le_of_ne (le_of_not_gt h) hmne⟩
    rw [realLocalDegree_eq_endpoints hP hPr ⟨r, hr, le_rfl⟩,
      degree_eq_asymmetric_endpoints hV hR (hcontrol _ hxp).2.1
        (hcontrol _ hxm).2.1 hleft hright]
    simp only [hp, hm]
    by_cases hpV : 0 < V (φ (x + r)) <;> by_cases hmV : 0 < V (φ (x - r)) <;>
      simp [hpV, hmV]
  · have hdpos : ∀ y ∈ closedBall x r, 0 < deriv φ y :=
      fun y hy ↦ (hcontrol y hy).2.2.mpr hpos
    have hmono : StrictMonoOn φ (closedBall x r) :=
      strictMonoOn_of_deriv_pos (convex_closedBall x r) hcφ
        (fun y hy ↦ hdpos y (interior_subset hy))
    have hleft : φ (x - r) < φ x := hmono hxm hxc (by linarith)
    have hright : φ x < φ (x + r) := hmono hxc hxp (by linarith)
    have hp : 0 < P (x + r) ↔ 0 < V (φ (x + r)) := by
      rw [show P (x + r) = V (φ (x + r)) / deriv φ (x + r) from
        real_pullback_eq_div φ hn V (hcontrol _ hxp).1]
      exact div_pos_iff_of_pos_right (hdpos _ hxp)
    have hm : 0 < P (x - r) ↔ 0 < V (φ (x - r)) := by
      rw [show P (x - r) = V (φ (x - r)) / deriv φ (x - r) from
        real_pullback_eq_div φ hn V (hcontrol _ hxm).1]
      exact div_pos_iff_of_pos_right (hdpos _ hxm)
    rw [realLocalDegree_eq_endpoints hP hPr ⟨r, hr, le_rfl⟩,
      degree_eq_asymmetric_endpoints hV hR (hcontrol _ hxm).2.1
        (hcontrol _ hxp).2.1 hleft hright]
    simp only [hp, hm]

end Poincare.LocalDegree
