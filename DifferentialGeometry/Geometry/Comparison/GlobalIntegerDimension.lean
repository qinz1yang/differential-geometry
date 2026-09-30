import DifferentialGeometry.Geometry.Comparison.LocalIntegerDimension

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_global_integer_dimH_of_local_comparison_and_dimH
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    {n : ℕ} (hdim : dimH (univ : Set X) ≤ n)
    (hlocal : ∀ p : X, ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison 1 Ω ∧ p ∈ Ω) :
    ∃ m : ℕ, m ≤ n ∧ dimH (univ : Set X) = m ∧
      ∀ V : Set X, IsOpen V → V.Nonempty → dimH V = m := by
  classical
  rcases isEmpty_or_nonempty X with hempty | hnonempty
  · have hz (V : Set X) : dimH V = 0 :=
      Set.Subsingleton.dimH_zero (fun x _ => isEmptyElim x)
    refine ⟨0, Nat.zero_le n, by simpa only [Nat.cast_zero] using hz univ, ?_⟩
    intro V _ _
    simpa only [Nat.cast_zero] using hz V
  · let p : X := Classical.choice hnonempty
    have hlocalized (R : ℝ) (hR : 0 < R) :
        ∃ m : ℕ, m ≤ n ∧ dimH (closedBall p R) = m ∧
          ∀ V : Set X, IsOpen V → V.Nonempty → V ⊆ ball p (R / 2) → dimH V = m := by
      apply exists_local_integer_dimH_of_intrinsic_eight_comparison_and_dimH
        hcurves p hR ((dimH_mono (subset_univ _)).trans hdim)
      intro z
      exact (exists_local_fourPointComparison_intrinsicBall_iff hcurves p
        (by positivity : 0 < 8 * R) z).mpr (hlocal z.val)
    obtain ⟨m, hmn, hclosed, hopen⟩ := hlocalized 1 zero_lt_one
    have hlarge (R : ℝ) (hR : 1 ≤ R) :
        dimH (closedBall p R) = m ∧
          ∀ V : Set X, IsOpen V → V.Nonempty → V ⊆ ball p (R / 2) → dimH V = m := by
      obtain ⟨k, _, hclosedR, hopenR⟩ := hlocalized R (by linarith)
      have hballne : (ball p (1 / 4 : ℝ)).Nonempty := ⟨p, mem_ball_self (by norm_num)⟩
      have heqone := hopen (ball p (1 / 4)) isOpen_ball hballne (ball_subset_ball (by norm_num))
      have heqR := hopenR (ball p (1 / 4)) isOpen_ball hballne (ball_subset_ball (by linarith))
      have heq : (k : ENNReal) = m := heqR.symm.trans heqone
      refine ⟨hclosedR.trans heq, ?_⟩
      intro V hV hVne hsub
      exact (hopenR V hV hVne hsub).trans heq
    have hglobal : dimH (univ : Set X) = m := by
      apply le_antisymm
      · rw [← iUnion_closedBall_nat p, dimH_iUnion]
        apply iSup_le
        intro k
        by_cases hk : k = 0
        · subst k
          simpa only [Nat.cast_zero] using
            (dimH_mono (closedBall_subset_closedBall (by norm_num : (0 : ℝ) ≤ 1))).trans_eq hclosed
        · exact (hlarge k (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk)).1.le
      · rw [← hclosed]
        exact dimH_mono (subset_univ _)
    refine ⟨m, hmn, hglobal, ?_⟩
    intro V hV hVne
    obtain ⟨q, hq⟩ := hVne
    let R : ℝ := 2 * dist q p + 2
    have hR : 1 ≤ R := by dsimp [R]; linarith [dist_nonneg (x := q) (y := p)]
    have hqR : q ∈ ball p (R / 2) := by
      change dist q p < R / 2
      dsimp [R]
      linarith
    have hsmall := (hlarge R hR).2 (V ∩ ball p (R / 2)) (hV.inter isOpen_ball)
      ⟨q, hq, hqR⟩ inter_subset_right
    apply le_antisymm
    · exact (dimH_mono (subset_univ V)).trans_eq hglobal
    · rw [← hsmall]
      exact dimH_mono inter_subset_left

end DifferentialGeometry.Geometry.Comparison.Toponogov
