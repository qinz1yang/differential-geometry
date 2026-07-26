import DifferentialGeometry.Analysis.ODE.IndexForm
import DifferentialGeometry.Analysis.ODE.SecondOrderGronwall

set_option autoImplicit false

/-!
# Uniqueness for the abstract Jacobi ODE

This module extends `IndexForm.lean` with the interior zero-data uniqueness
needed by the no-conjugate-point argument.  The proof is independent of
Riemannian geometry: propagate zero data to the right by the second-order
Gronwall estimate, and to the left after reversing time.
-/

open Set

noncomputable section

namespace DifferentialGeometry.Analysis.ODE

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A homogeneous second-order system with zero initial data vanishes on its
forward interval. -/
private theorem ode2_zero
    {Y V W : ℝ → F} {C b : ℝ}
    (hC : 0 ≤ C)
    (hYcont : ContinuousOn Y (Icc 0 b))
    (hVcont : ContinuousOn V (Icc 0 b))
    (hYderiv : ∀ t ∈ Ico 0 b, HasDerivWithinAt Y (V t) (Ici t) t)
    (hVderiv : ∀ t ∈ Ico 0 b, HasDerivWithinAt V (W t) (Ici t) t)
    (hWbound : ∀ t ∈ Ico 0 b, ‖W t‖ ≤ C * ‖Y t‖)
    (hY0 : Y 0 = 0) (hV0 : V 0 = 0) :
    ∀ t ∈ Icc 0 b, Y t = 0 := by
  have hbound : ∀ t ∈ Ico 0 b, ‖W t‖ ≤ C * ‖Y t‖ + 0 := by
    intro t ht
    simpa using hWbound t ht
  have hnormY0 : ‖Y 0‖ ≤ 0 := by simp [hY0]
  have hnormV0 : ‖V 0‖ ≤ 0 := by simp [hV0]
  have hgronwall := DifferentialGeometry.norm_le_gronwall_secondOrder
    (Y := Y) (Y' := V) (Y'' := W) hC le_rfl hYcont hVcont
    hYderiv hVderiv hbound hnormY0 hnormV0
  have hzero : ∀ t : ℝ, gronwallBound 0 (max C 1) 0 t = 0 := by
    intro t
    have h := DifferentialGeometry.gronwallBound_zero_mul_eps
      (K := max C 1) (eps := (1 : ℝ)) (a := (0 : ℝ)) (x := t)
    simpa using h
  intro t ht
  have hnorm := hgronwall t ht
  rw [hzero t] at hnorm
  exact norm_le_zero_iff.mp hnorm

namespace IsJacobiSolOn

/-- If a Jacobi ODE solution has zero position and velocity at an interior
time, then both fields vanish on the whole interval. -/
theorem eq_zero_of_interior
    [CompleteSpace F]
    {R : ℝ → F →L[ℝ] F} {a b c C : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiSolOn R a b y v)
    (hc : c ∈ Ioo a b) (hC : 0 ≤ C)
    (hR : ∀ t ∈ Icc a b, ‖R t‖ ≤ C)
    (hyc : y c = 0) (hvc : v c = 0) :
    ∀ t ∈ Icc a b, y t = 0 ∧ v t = 0 := by
  let Bpos : ℝ := b - c
  let Ypos : ℝ → F := fun t => y (c + t)
  let Vpos : ℝ → F := fun t => v (c + t)
  let Wpos : ℝ → F := fun t => -(R (c + t)) (y (c + t))
  have hBpos : 0 < Bpos := by
    dsimp [Bpos]
    linarith [hc.2]
  have hmap_pos : MapsTo (fun t : ℝ => c + t) (Icc 0 Bpos) (Icc a b) := by
    intro t ht
    constructor
    · linarith [hc.1, ht.1]
    · dsimp [Bpos] at ht
      linarith [ht.2]
  have hYpos_cont : ContinuousOn Ypos (Icc 0 Bpos) := by
    exact hsol.contOn_fst.comp
      (continuous_const.add continuous_id).continuousOn hmap_pos
  have hVpos_cont : ContinuousOn Vpos (Icc 0 Bpos) := by
    exact hsol.contOn_snd.comp
      (continuous_const.add continuous_id).continuousOn hmap_pos
  have hYpos_deriv :
      ∀ t ∈ Ico 0 Bpos, HasDerivWithinAt Ypos (Vpos t) (Ici t) t := by
    intro t ht
    have hu : c + t ∈ Ioo a b := by
      constructor
      · linarith [hc.1, ht.1]
      · dsimp [Bpos] at ht
        linarith [ht.2]
    have hbase := (hsol.deriv_fst (c + t) (Ioo_subset_Icc_self hu)).hasDerivAt
      (Icc_mem_nhds hu.1 hu.2)
    have hshift : HasDerivAt (fun s : ℝ => c + s) 1 t := by
      simpa using (hasDerivAt_const t c).add (hasDerivAt_id t)
    have hcomp := hbase.scomp t hshift
    simpa only [Ypos, Vpos, Function.comp_apply, one_smul] using
      hcomp.hasDerivWithinAt
  have hVpos_deriv :
      ∀ t ∈ Ico 0 Bpos, HasDerivWithinAt Vpos (Wpos t) (Ici t) t := by
    intro t ht
    have hu : c + t ∈ Ioo a b := by
      constructor
      · linarith [hc.1, ht.1]
      · dsimp [Bpos] at ht
        linarith [ht.2]
    have hbase := (hsol.deriv_snd (c + t) (Ioo_subset_Icc_self hu)).hasDerivAt
      (Icc_mem_nhds hu.1 hu.2)
    have hshift : HasDerivAt (fun s : ℝ => c + s) 1 t := by
      simpa using (hasDerivAt_const t c).add (hasDerivAt_id t)
    have hcomp := hbase.scomp t hshift
    simpa only [Vpos, Wpos, Function.comp_apply, one_smul] using
      hcomp.hasDerivWithinAt
  have hWpos_bound : ∀ t ∈ Ico 0 Bpos, ‖Wpos t‖ ≤ C * ‖Ypos t‖ := by
    intro t ht
    have htIcc : t ∈ Icc 0 Bpos := Ico_subset_Icc_self ht
    have hu := hmap_pos htIcc
    calc
      ‖Wpos t‖ = ‖(R (c + t)) (y (c + t))‖ := by simp only [Wpos, norm_neg]
      _ ≤ ‖R (c + t)‖ * ‖y (c + t)‖ := (R (c + t)).le_opNorm _
      _ ≤ C * ‖y (c + t)‖ :=
        mul_le_mul_of_nonneg_right (hR (c + t) hu) (norm_nonneg _)
      _ = C * ‖Ypos t‖ := rfl
  have hYpos0 : Ypos 0 = 0 := by simpa [Ypos] using hyc
  have hVpos0 : Vpos 0 = 0 := by simpa [Vpos] using hvc
  have hpos_zero : ∀ t ∈ Icc 0 Bpos, Ypos t = 0 :=
    ode2_zero hC hYpos_cont hVpos_cont hYpos_deriv hVpos_deriv
      hWpos_bound hYpos0 hVpos0
  have hy_pos : ∀ t ∈ Icc c b, y t = 0 := by
    intro t ht
    have htc : t - c ∈ Icc 0 Bpos := by
      dsimp [Bpos]
      constructor <;> linarith [ht.1, ht.2]
    have hzero := hpos_zero (t - c) htc
    change y (c + (t - c)) = 0 at hzero
    have heq : c + (t - c) = t := by ring
    simpa only [heq] using hzero

  let Bneg : ℝ := c - a
  let Yneg : ℝ → F := fun t => y (c - t)
  let Vneg : ℝ → F := fun t => -v (c - t)
  let Wneg : ℝ → F := fun t => -(R (c - t)) (y (c - t))
  have hBneg : 0 < Bneg := by
    dsimp [Bneg]
    linarith [hc.1]
  have hmap_neg : MapsTo (fun t : ℝ => c - t) (Icc 0 Bneg) (Icc a b) := by
    intro t ht
    constructor
    · dsimp [Bneg] at ht
      linarith [ht.2]
    · linarith [hc.2, ht.1]
  have hYneg_cont : ContinuousOn Yneg (Icc 0 Bneg) := by
    exact hsol.contOn_fst.comp
      (continuous_const.sub continuous_id).continuousOn hmap_neg
  have hVneg_cont : ContinuousOn Vneg (Icc 0 Bneg) := by
    exact (hsol.contOn_snd.comp
      (continuous_const.sub continuous_id).continuousOn hmap_neg).neg
  have hYneg_deriv :
      ∀ t ∈ Ico 0 Bneg, HasDerivWithinAt Yneg (Vneg t) (Ici t) t := by
    intro t ht
    have hu : c - t ∈ Ioo a b := by
      constructor
      · dsimp [Bneg] at ht
        linarith [ht.2]
      · linarith [hc.2, ht.1]
    have hbase := (hsol.deriv_fst (c - t) (Ioo_subset_Icc_self hu)).hasDerivAt
      (Icc_mem_nhds hu.1 hu.2)
    have hshift : HasDerivAt (fun s : ℝ => c - s) (-1) t := by
      simpa using (hasDerivAt_const t c).sub (hasDerivAt_id t)
    have hcomp := hbase.scomp t hshift
    simpa only [Yneg, Vneg, Function.comp_apply, neg_one_smul] using
      hcomp.hasDerivWithinAt
  have hVneg_deriv :
      ∀ t ∈ Ico 0 Bneg, HasDerivWithinAt Vneg (Wneg t) (Ici t) t := by
    intro t ht
    have hu : c - t ∈ Ioo a b := by
      constructor
      · dsimp [Bneg] at ht
        linarith [ht.2]
      · linarith [hc.2, ht.1]
    have hbase := (hsol.deriv_snd (c - t) (Ioo_subset_Icc_self hu)).hasDerivAt
      (Icc_mem_nhds hu.1 hu.2)
    have hshift : HasDerivAt (fun s : ℝ => c - s) (-1) t := by
      simpa using (hasDerivAt_const t c).sub (hasDerivAt_id t)
    have hcomp := (hbase.scomp t hshift).neg
    simpa only [Vneg, Wneg, Function.comp_apply, neg_one_smul, neg_neg] using
      hcomp.hasDerivWithinAt
  have hWneg_bound : ∀ t ∈ Ico 0 Bneg, ‖Wneg t‖ ≤ C * ‖Yneg t‖ := by
    intro t ht
    have htIcc : t ∈ Icc 0 Bneg := Ico_subset_Icc_self ht
    have hu := hmap_neg htIcc
    calc
      ‖Wneg t‖ = ‖(R (c - t)) (y (c - t))‖ := by simp only [Wneg, norm_neg]
      _ ≤ ‖R (c - t)‖ * ‖y (c - t)‖ := (R (c - t)).le_opNorm _
      _ ≤ C * ‖y (c - t)‖ :=
        mul_le_mul_of_nonneg_right (hR (c - t) hu) (norm_nonneg _)
      _ = C * ‖Yneg t‖ := rfl
  have hYneg0 : Yneg 0 = 0 := by simpa [Yneg] using hyc
  have hVneg0 : Vneg 0 = 0 := by simpa [Vneg] using congrArg Neg.neg hvc
  have hneg_zero : ∀ t ∈ Icc 0 Bneg, Yneg t = 0 :=
    ode2_zero hC hYneg_cont hVneg_cont hYneg_deriv hVneg_deriv
      hWneg_bound hYneg0 hVneg0
  have hy_neg : ∀ t ∈ Icc a c, y t = 0 := by
    intro t ht
    have hct : c - t ∈ Icc 0 Bneg := by
      dsimp [Bneg]
      constructor <;> linarith [ht.1, ht.2]
    have hzero := hneg_zero (c - t) hct
    simpa only [Yneg, sub_sub_cancel] using hzero

  have hy_zero : ∀ t ∈ Icc a b, y t = 0 := by
    intro t ht
    rcases le_total t c with htc | hct
    · exact hy_neg t ⟨ht.1, htc⟩
    · exact hy_pos t ⟨hct, ht.2⟩
  have hab : a < b := hc.1.trans hc.2
  have hv_zero : ∀ t ∈ Icc a b, v t = 0 := by
    intro t ht
    have hzero_deriv : HasDerivWithinAt y 0 (Icc a b) t := by
      refine (hasDerivWithinAt_const t (Icc a b) (0 : F)).congr_of_mem ?_ ht
      intro s hs
      exact hy_zero s hs
    have hderiv_eq := (uniqueDiffOn_Icc hab t ht).eq_deriv
      (Icc a b) hzero_deriv (hsol.deriv_fst t ht)
    exact hderiv_eq.symm
  intro t ht
  exact ⟨hy_zero t ht, hv_zero t ht⟩

end IsJacobiSolOn

end DifferentialGeometry.Analysis.ODE
