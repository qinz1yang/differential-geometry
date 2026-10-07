import DifferentialGeometry.Analysis.Calculus.UpperSupport.Monotonicity
import Mathlib.Topology.Order.WithTop

/-!
# S-CH11-PORT-B1 port of `UpperSupport.WithTop` (`PortC11P`)

Source: donor `DifferentialGeometry/Analysis/Calculus/UpperSupport/WithTop.lean` of the
chapter-11 branch (ch11 HEAD a73e4bdbfd).  The donor file does not elaborate against this tree
(same lakefile, Lean v4.35.0-rc3, same Mathlib).  One elaboration-level repair:
* port line 51 (donor 37): `change (bound : WithTop ℝ) < capped t` inserted before
  `rw [← hcoe t]`
  (the goal is the beta-redex `(fun x1 x2 => capped x1 > x2) t ↑bound`, which hides `capped t`
  from `rw`).
No statement, definition or proof idea is altered.  The module `UpperSupport.WithTop` is a shim
re-exporting this file.
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology

/-- Right upper supports below a finite guard propagate that guard and force
antitonicity. The extended function is capped before taking its real value. -/
theorem WithTop.antitoneOn_of_lowerSemicontinuousOn_of_upper_support_below
    (F : ℝ → WithTop ℝ) (a b c : ℝ)
    (hF : LowerSemicontinuousOn F (Icc a b))
    (hentry : F a < (c : WithTop ℝ))
    (hsupport : ∀ t ∈ Ico a b, F t < (c : WithTop ℝ) →
      ∃ psi : ℝ → ℝ, ∃ d : ℝ,
        F t = (psi t : WithTop ℝ) ∧
        (∀ᶠ z in 𝓝[>] t, F z ≤ (psi z : WithTop ℝ)) ∧
        HasDerivAt psi d t ∧ d ≤ 0) :
    AntitoneOn F (Icc a b) ∧ ∀ t ∈ Icc a b, F t < (c : WithTop ℝ) := by
  classical
  let capped : ℝ → WithTop ℝ := fun t => min (F t) (c : WithTop ℝ)
  let G : ℝ → ℝ := fun t => (capped t).untopD 0
  have hfinite (t : ℝ) : capped t ≠ ⊤ :=
    ne_of_lt ((min_le_right (F t) (c : WithTop ℝ)).trans_lt (WithTop.coe_lt_top c))
  have hcoe (t : ℝ) : (G t : WithTop ℝ) = capped t := by
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp (hfinite t)
    dsimp only [G]
    rw [← hv, WithTop.untopD_coe]
  have hcapped : LowerSemicontinuousOn capped (Icc a b) := by
    change LowerSemicontinuousOn (fun t => F t ⊓ (c : WithTop ℝ)) (Icc a b)
    exact hF.inf lowerSemicontinuousOn_const
  have hG : LowerSemicontinuousOn G (Icc a b) := by
    intro t ht bound hbound
    have hh := hcapped t ht (bound : WithTop ℝ) (by
      change (bound : WithTop ℝ) < capped t
      rw [← hcoe t]
      exact WithTop.coe_lt_coe.mpr hbound)
    filter_upwards [hh] with z hz
    rw [← hcoe z] at hz
    exact WithTop.coe_lt_coe.mp hz
  have huncap (t : ℝ) (ht : F t < (c : WithTop ℝ)) :
      (G t : WithTop ℝ) = F t :=
    (hcoe t).trans (min_eq_left ht.le)
  have hbelow (t : ℝ) (ht : G t < c) : F t < (c : WithTop ℝ) := by
    by_contra hnot
    have hcap : capped t = (c : WithTop ℝ) := min_eq_right (le_of_not_gt hnot)
    have heq : G t = c := WithTop.coe_inj.mp ((hcoe t).trans hcap)
    exact (ne_of_lt ht) heq
  have hGa : G a < c := WithTop.coe_lt_coe.mp (by
    rw [huncap a hentry]
    exact hentry)
  have hGsupport : ∀ t ∈ Ico a b, G t < c → ∀ ε : ℝ, 0 < ε →
      ∃ psi : ℝ → ℝ, ∃ d : ℝ,
        psi t = G t ∧ G ≤ᶠ[𝓝[>] t] psi ∧ HasDerivAt psi d t ∧ d ≤ ε := by
    intro t ht htc ε hε
    have hFt := hbelow t htc
    obtain ⟨psi, d, hcontact, hupper, hderiv, hd⟩ := hsupport t ht hFt
    refine ⟨psi, d, WithTop.coe_inj.mp (hcontact.symm.trans (huncap t hFt).symm),
      ?_, hderiv, hd.trans hε.le⟩
    filter_upwards [hupper] with z hz
    apply WithTop.coe_le_coe.mp
    calc
      (G z : WithTop ℝ) = capped z := hcoe z
      _ ≤ F z := min_le_left _ _
      _ ≤ (psi z : WithTop ℝ) := hz
  have hle : ∀ t ∈ Icc a b, G t ≤ G a :=
    DifferentialGeometry.le_initial_of_lowerSemicontinuousOn_of_upper_support
      hG hGa hGsupport
  have hGlt (t : ℝ) (ht : t ∈ Icc a b) : G t < c := (hle t ht).trans_lt hGa
  have hFlt (t : ℝ) (ht : t ∈ Icc a b) : F t < (c : WithTop ℝ) :=
    hbelow t (hGlt t ht)
  have hanti : AntitoneOn G (Icc a b) := by
    intro x hx y hy hxy
    have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
    apply DifferentialGeometry.le_initial_of_lowerSemicontinuousOn_of_upper_support
      (hG.mono hsub) (hGlt x hx) ?_ y ⟨hxy, le_rfl⟩
    intro t ht htc ε hε
    exact hGsupport t ⟨hx.1.trans ht.1, ht.2.trans_le hy.2⟩ htc ε hε
  refine ⟨?_, hFlt⟩
  intro x hx y hy hxy
  rw [← huncap y (hFlt y hy), ← huncap x (hFlt x hx)]
  exact WithTop.coe_le_coe.mpr (hanti hx hy hxy)
