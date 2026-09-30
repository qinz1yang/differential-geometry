import DifferentialGeometry.Topology.MetricSpace.OppositePrefixes

open Set

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem exists_signed_prefix_of_opposite_prefixes
    {o : X} {L E η : ℝ} (hL : 0 ≤ L) (hE : 0 ≤ E) (hη : 0 ≤ η)
    (qPlus qMinus : Icc (0 : ℝ) L → X)
    (hpLip : LipschitzWith 1 qPlus) (hmLip : LipschitzWith 1 qMinus)
    (hp0 : qPlus ⟨0, ⟨le_rfl, hL⟩⟩ = o) (hm0 : qMinus ⟨0, ⟨le_rfl, hL⟩⟩ = o)
    (hpdist : ∀ s t, s ≤ t → t.val - s.val - η ≤ dist (qPlus s) (qPlus t))
    (hmdist : ∀ s t, s ≤ t → t.val - s.val - η ≤ dist (qMinus s) (qMinus t))
    (hcross : ∀ t u, t.val + u.val - E - 2 * η ≤ dist (qPlus t) (qMinus u)) :
    ∃ Q : Icc (-L) L → X, LipschitzWith 1 Q ∧
      Q ⟨0, ⟨by linarith, hL⟩⟩ = o ∧
      (∀ t : Icc (0 : ℝ) L,
        Q ⟨t.val, ⟨by linarith [t.property.1], t.property.2⟩⟩ = qPlus t ∧
        Q ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1]⟩⟩ = qMinus t) ∧
      (∀ s t, |s.val - t.val| - E - 2 * η ≤ dist (Q s) (Q t)) ∧
      ∀ t, dist (Q t) o ≤ |t.val| := by
  let Q : Icc (-L) L → X := fun t =>
    if ht : 0 ≤ t.val then qPlus ⟨t.val, ⟨ht, t.property.2⟩⟩
    else qMinus ⟨-t.val, ⟨by linarith, by linarith [t.property.1]⟩⟩
  have hqp (t : Icc (-L) L) (ht : 0 ≤ t.val) :
      Q t = qPlus ⟨t.val, ⟨ht, t.property.2⟩⟩ := by simp only [Q, dite_eq_left ht]
  have hqm (t : Icc (-L) L) (ht : t.val ≤ 0) :
      Q t = qMinus ⟨-t.val, ⟨by linarith, by linarith [t.property.1]⟩⟩ := by
    by_cases hz : t.val = 0
    · have ht0 : t = ⟨0, ⟨by linarith, hL⟩⟩ := Subtype.ext hz
      subst t
      simp only [Q, le_refl, dite_eq_left, neg_zero, hp0, hm0]
    · have hn : ¬ 0 ≤ t.val := by intro hn; exact hz (le_antisymm ht hn)
      simp only [Q, dite_eq_right hn]
  have hrad (q : Icc (0 : ℝ) L → X) (hl : LipschitzWith 1 q)
      (hz : q ⟨0, ⟨le_rfl, hL⟩⟩ = o) (t : Icc (0 : ℝ) L) : dist (q t) o ≤ t.val := by
    have hh := hl.dist_le_mul t ⟨0, ⟨le_rfl, hL⟩⟩
    rw [hz] at hh
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq, sub_zero,
      abs_of_nonneg t.property.1] using hh
  have hbranch (q : Icc (0 : ℝ) L → X)
      (hd : ∀ s t, s ≤ t → t.val - s.val - η ≤ dist (q s) (q t))
      (s t : Icc (0 : ℝ) L) : |s.val - t.val| - η ≤ dist (q s) (q t) := by
    rcases le_total s t with hst | hts
    · rw [abs_of_nonpos (sub_nonpos.mpr (show s.val ≤ t.val from hst))]
      linarith [hd s t hst]
    · rw [abs_of_nonneg (sub_nonneg.mpr (show t.val ≤ s.val from hts)), dist_comm]
      exact hd t s hts
  have hboth (s t : Icc (-L) L) : |s.val - t.val| - E - 2 * η ≤ dist (Q s) (Q t) ∧
      dist (Q s) (Q t) ≤ |s.val - t.val| := by
    by_cases hs : 0 ≤ s.val <;> by_cases ht : 0 ≤ t.val
    · rw [hqp s hs, hqp t ht]
      have hb := hbranch qPlus hpdist ⟨s.val, ⟨hs, s.property.2⟩⟩ ⟨t.val, ⟨ht, t.property.2⟩⟩
      have hu := hpLip.dist_le_mul ⟨s.val, ⟨hs, s.property.2⟩⟩ ⟨t.val, ⟨ht, t.property.2⟩⟩
      change _ ≤ 1 * |s.val - t.val| at hu
      exact ⟨by linarith, by linarith⟩
    · have ht' : t.val ≤ 0 := (lt_of_not_ge ht).le
      rw [hqp s hs, hqm t ht', abs_of_nonneg (by linarith : 0 ≤ s.val - t.val)]
      let sp : Icc (0 : ℝ) L := ⟨s.val, ⟨hs, s.property.2⟩⟩
      let tm : Icc (0 : ℝ) L := ⟨-t.val, ⟨by linarith, by linarith [t.property.1]⟩⟩
      change _ ≤ dist (qPlus sp) (qMinus tm) ∧ _
      have hh := hcross sp tm
      have hu := dist_triangle (qPlus sp) o (qMinus tm)
      rw [dist_comm o (qMinus tm)] at hu
      have hp := hrad qPlus hpLip hp0 sp
      have hm := hrad qMinus hmLip hm0 tm
      dsimp [sp, tm] at hh hp hm
      exact ⟨by linarith, by linarith⟩
    · have hs' : s.val ≤ 0 := (lt_of_not_ge hs).le
      rw [hqm s hs', hqp t ht, abs_of_nonpos (by linarith : s.val - t.val ≤ 0), dist_comm]
      let sm : Icc (0 : ℝ) L := ⟨-s.val, ⟨by linarith, by linarith [s.property.1]⟩⟩
      let tp : Icc (0 : ℝ) L := ⟨t.val, ⟨ht, t.property.2⟩⟩
      change _ ≤ dist (qPlus tp) (qMinus sm) ∧ _
      have hh := hcross tp sm
      have hu := dist_triangle (qPlus tp) o (qMinus sm)
      rw [dist_comm o (qMinus sm)] at hu
      have hp := hrad qPlus hpLip hp0 tp
      have hm := hrad qMinus hmLip hm0 sm
      dsimp [sm, tp] at hh hp hm
      exact ⟨by linarith, by linarith⟩
    · have hs' : s.val ≤ 0 := (lt_of_not_ge hs).le
      have ht' : t.val ≤ 0 := (lt_of_not_ge ht).le
      rw [hqm s hs', hqm t ht']
      let sm : Icc (0 : ℝ) L := ⟨-s.val, ⟨by linarith, by linarith [s.property.1]⟩⟩
      let tm : Icc (0 : ℝ) L := ⟨-t.val, ⟨by linarith, by linarith [t.property.1]⟩⟩
      have hb := hbranch qMinus hmdist sm tm
      have hu := hmLip.dist_le_mul sm tm
      change dist (qMinus sm) (qMinus tm) ≤ 1 * |(-s.val) - (-t.val)| at hu
      change |(-s.val) - (-t.val)| - η ≤ dist (qMinus sm) (qMinus tm) at hb
      rw [neg_sub_neg, abs_sub_comm] at hu hb
      change _ ≤ dist (qMinus sm) (qMinus tm) ∧ _
      exact ⟨by linarith, by linarith⟩
  have hQLip : LipschitzWith 1 Q := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq] using (hboth s t).2
  have hQ0 : Q ⟨0, ⟨by linarith, hL⟩⟩ = o := (hqp _ le_rfl).trans hp0
  refine ⟨Q, hQLip, hQ0, ?_, fun s t => (hboth s t).1, ?_⟩
  · intro t
    refine ⟨hqp _ t.property.1, ?_⟩
    have hh := hqm ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1]⟩⟩
      (neg_nonpos.mpr t.property.1)
    simpa only [neg_neg] using hh
  · intro t
    have hh := hQLip.dist_le_mul t ⟨0, ⟨by linarith, hL⟩⟩
    rw [hQ0] at hh
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, Real.dist_eq, sub_zero] using hh

end Metric
