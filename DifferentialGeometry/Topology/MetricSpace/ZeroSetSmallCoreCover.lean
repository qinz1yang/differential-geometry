import DifferentialGeometry.Topology.MetricSpace.VariableRadiusCover

/-!
# The zero-set cover with maximal selected centers (LC64)

Blueprint `master207A.tex`, LC64 (`thm:collapse-zero-small-core-cover`, lines 23621–23673).
On a compact metric space, a radius assignment squeezed between two multiples of a positive
continuous scale admits a finite selection of centers which are maximal candidates in the sense
of LC62. Their open balls are pairwise disjoint and meet the set `Z`, the neighboring radius
and scale-ratio bounds hold on the closed ten-radius balls, the five-radius balls cover `Z`, and,
whenever every selected center satisfies the closed annular exclusion, the open tenth-radius
balls cover `Z`. The radius assignment is never changed after the selection.
-/

set_option autoImplicit false

open Set Metric

namespace Metric

variable {X : Type*} [MetricSpace X]

/-- LC64 with the maximality of the selected centers (LC62) exported, for an arbitrary
totally bounded space with a positive floor and a finite ceiling on the radii. -/
theorem exists_finite_maximal_ball_cover_of_bounded_radii
    (htot : TotallyBounded (Set.univ : Set X)) (Z : Set X) (r : X → ℝ)
    {rmin R : ℝ} (hmin : 0 < rmin) (hlower : ∀ p, rmin ≤ r p) (hupper : ∀ p, r p ≤ R) :
    ∃ I : Set X, I.Finite ∧
      (∀ i ∈ I, (ball i (r i) ∩ Z).Nonempty ∧
        ∀ q, (ball q (r q) ∩ Z).Nonempty → ball i (r i) ⊆ ball q (r q) → r q ≤ 2 * r i) ∧
      I.PairwiseDisjoint (fun i => ball i (r i)) ∧
      (∀ i ∈ I, ∀ q, dist i q ≤ 10 * r i → r q ≤ 20 * r i) ∧
      Z ⊆ ⋃ i ∈ I, ball i (5 * r i) := by
  let V : Set X := {v | (ball v (r v) ∩ Z).Nonempty ∧
    ∀ q, (ball q (r q) ∩ Z).Nonempty →
      ball v (r v) ⊆ ball q (r q) → r q ≤ 2 * r v}
  have hpos : ∀ p, 0 < r p := fun p => hmin.trans_le (hlower p)
  obtain ⟨I, hIV, hfin, hdisj, hcover⟩ := exists_finite_disjoint_ball_selection
    (htot.subset (subset_univ V)) r hmin (fun p _ => hlower p) (fun p _ => hupper p)
  refine ⟨I, hfin, fun i hi => hIV hi, hdisj, ?_, ?_⟩
  · intro i hi q hq
    exact radius_le_of_maximal_doubling_ball r Z (hIV hi).1 (hpos i) (hIV hi).2 hq
  · intro z hz
    obtain ⟨v, hvZ, hzv, hmax⟩ := exists_maximal_doubling_ball r Z hpos hupper
      (show (ball z (r z) ∩ Z).Nonempty from ⟨z, mem_ball_self (hpos z), hz⟩)
    have hzball : z ∈ ball v (r v) := by
      rcases hzv with rfl | ⟨_, hsub⟩
      · exact mem_ball_self (hpos z)
      · exact hsub (mem_ball_self (hpos z))
    obtain ⟨i, hi, _, _, _, hsub⟩ := hcover v ⟨hvZ, hmax⟩
    exact mem_iUnion₂.mpr ⟨i, hi, hsub hzball⟩

/-- **LC64.** Zero-set cover from annular exclusion. The selected centers are maximal
candidates (LC62), the selected open balls are disjoint and meet `Z`, the neighboring radius and
scale-ratio bounds hold on the closed ten-radius balls, the five-radius balls cover `Z`, and the
closed annular exclusion at every selected center gives the open tenth-radius cover. -/
theorem exists_zero_set_small_core_cover [CompactSpace X]
    (Z : Set X) (r ρ : X → ℝ) (hρ : Continuous ρ) (hρpos : ∀ p, 0 < ρ p)
    {T U : ℝ} (hT : 0 < T) (hTU : T ≤ U)
    (hlower : ∀ p, T * ρ p ≤ r p) (hupper : ∀ p, r p ≤ U * ρ p) :
    ∃ I : Set X, I.Finite ∧
      (∀ i ∈ I, (ball i (r i) ∩ Z).Nonempty ∧
        ∀ q, (ball q (r q) ∩ Z).Nonempty → ball i (r i) ⊆ ball q (r q) → r q ≤ 2 * r i) ∧
      I.PairwiseDisjoint (fun i => ball i (r i)) ∧
      (∀ i ∈ I, ∀ q, dist i q ≤ 10 * r i → r q ≤ 20 * r i ∧ T / 20 ≤ r i / ρ q) ∧
      Z ⊆ ⋃ i ∈ I, ball i (5 * r i) ∧
      ((∀ i ∈ I, ∀ z ∈ Z, ¬ (r i / 10 ≤ dist i z ∧ dist i z ≤ 10 * r i)) →
        Z ⊆ ⋃ i ∈ I, ball i (r i / 10)) := by
  classical
  by_cases hX : Nonempty X
  · obtain ⟨pmin, _, hmin⟩ := isCompact_univ.exists_isMinOn
      (Set.univ_nonempty : (Set.univ : Set X).Nonempty) hρ.continuousOn
    obtain ⟨pmax, _, hmax⟩ := isCompact_univ.exists_isMaxOn
      (Set.univ_nonempty : (Set.univ : Set X).Nonempty) hρ.continuousOn
    obtain ⟨I, hfin, hmaxI, hdisj, hlocal, hcover⟩ :=
      exists_finite_maximal_ball_cover_of_bounded_radii
        isCompact_univ.totallyBounded Z r (mul_pos hT (hρpos pmin))
        (fun p => (mul_le_mul_of_nonneg_left (hmin (mem_univ p)) hT.le).trans (hlower p))
        (fun p => (hupper p).trans
          (mul_le_mul_of_nonneg_left (hmax (mem_univ p)) (hT.le.trans hTU)))
    refine ⟨I, hfin, hmaxI, hdisj, ?_, hcover, fun hex =>
      subset_small_balls_of_annular_exclusion Z I r hcover hex⟩
    intro i hi q hq
    have hr := hlocal i hi q hq
    refine ⟨hr, (le_div_iff₀ (hρpos q)).mpr ?_⟩
    linarith [hlower q]
  · have hZ : Z = ∅ := eq_empty_iff_forall_notMem.mpr (fun x _ => hX ⟨x⟩)
    exact ⟨∅, finite_empty, by simp, by simp, by simp, by simp [hZ], fun _ => by simp [hZ]⟩

end Metric
