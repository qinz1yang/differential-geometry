import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith

noncomputable section
open scoped Topology
open Set Filter

namespace DifferentialGeometry.Topology

variable {M : Type*} [TopologicalSpace M] [CompactSpace M]

theorem exists_running_maximum_sequence_of_unbounded
    {a T theta : ℝ} (hθ : a ≤ theta) (hθT : theta < T)
    (f : ℝ × M → ℝ)
    (hcont : ContinuousOn f ((Set.Ico a T) ×ˢ (Set.univ : Set M)))
    (hunbdd : ∀ A : ℝ, ∃ t : ℝ, ∃ x : M,
      t ∈ Set.Ico a T ∧ A < f (t, x)) :
    ∃ (x : ℕ → M) (t : ℕ → ℝ),
      (∀ i, t i ∈ Set.Ioo theta T) ∧
      (∀ i, 0 < f (t i, x i)) ∧
      (∀ i s, s ∈ Set.Icc a (t i) → ∀ y : M,
        f (s, y) ≤ f (t i, x i)) ∧
      Filter.Tendsto (fun i => f (t i, x i)) Filter.atTop Filter.atTop := by
  classical
  obtain ⟨_, x0, _, _⟩ := hunbdd 0
  have hcompactθ : IsCompact (Set.Icc a theta ×ˢ (Set.univ : Set M)) :=
    isCompact_Icc.prod isCompact_univ
  have hnonemptyθ : (Set.Icc a theta ×ˢ (Set.univ : Set M)).Nonempty :=
    ⟨(a, x0), ⟨le_rfl, hθ⟩, Set.mem_univ _⟩
  obtain ⟨pθ, _, hpmax⟩ := hcompactθ.exists_isMaxOn hnonemptyθ
    (hcont.mono (fun _ hp => ⟨⟨hp.1.1, hp.1.2.trans_lt hθT⟩, hp.2⟩))
  let B : ℝ := max (f pθ) 0
  have hBnonneg : 0 ≤ B := le_max_right _ _
  have hB : ∀ s : ℝ, s ∈ Set.Icc a theta → ∀ y : M, f (s, y) ≤ B := by
    intro s hs y
    exact (hpmax ⟨hs, Set.mem_univ _⟩).trans (le_max_left _ _)
  have hraw : ∀ i : ℕ, ∃ t : ℝ, ∃ x : M,
      t ∈ Set.Ico a T ∧ B + (i : ℝ) + 1 < f (t, x) := by
    intro i
    exact hunbdd (B + (i : ℝ) + 1)
  choose rawTime rawPoint hraw_spec using hraw
  have hraw_nonneg : ∀ i, a ≤ rawTime i :=
    fun i => (hraw_spec i).1.1
  have hmax_exists : ∀ i : ℕ, ∃ tmax : ℝ, ∃ xmax : M,
      tmax ∈ Set.Icc a (rawTime i) ∧
        ∀ s : ℝ, s ∈ Set.Icc a (rawTime i) → ∀ y : M,
          f (s, y) ≤ f (tmax, xmax) := by
    intro i
    have hcompact : IsCompact (Set.Icc a (rawTime i) ×ˢ (Set.univ : Set M)) :=
      isCompact_Icc.prod isCompact_univ
    have hnonempty : (Set.Icc a (rawTime i) ×ˢ (Set.univ : Set M)).Nonempty :=
      ⟨(rawTime i, rawPoint i), ⟨hraw_nonneg i, le_rfl⟩, Set.mem_univ _⟩
    obtain ⟨p, hp, hmax⟩ := hcompact.exists_isMaxOn hnonempty
      (hcont.mono (fun _ hp => ⟨⟨hp.1.1, hp.1.2.trans_lt (hraw_spec i).1.2⟩, hp.2⟩))
    rcases p with ⟨tmax, xmax⟩
    refine ⟨tmax, xmax, hp.1, ?_⟩
    intro s hs y
    exact hmax ⟨hs, Set.mem_univ _⟩
  choose maxTime maxPoint hmax_spec using hmax_exists
  have hvalue : ∀ i : ℕ, B + (i : ℝ) + 1 < f (maxTime i, maxPoint i) := by
    intro i
    exact (hraw_spec i).2.trans_le
      ((hmax_spec i).2 (rawTime i) ⟨hraw_nonneg i, le_rfl⟩ (rawPoint i))
  have htheta_lt : ∀ i, theta < maxTime i := by
    intro i
    by_contra hnot
    have hboundmax := hB (maxTime i) ⟨(hmax_spec i).1.1, le_of_not_gt hnot⟩ (maxPoint i)
    have hrawgt := hvalue i
    have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  refine ⟨maxPoint, maxTime, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨htheta_lt i, (hmax_spec i).1.2.trans_lt (hraw_spec i).1.2⟩
  · intro i
    have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    have hv := hvalue i
    linarith
  · intro i s hs y
    exact (hmax_spec i).2 s ⟨hs.1, hs.2.trans (hmax_spec i).1.2⟩ y
  · refine tendsto_atTop.2 fun A => ?_
    obtain ⟨N, hN⟩ := exists_nat_ge A
    filter_upwards [Filter.eventually_ge_atTop N] with i hi
    have hNi : (N : ℝ) ≤ i := Nat.cast_le.mpr hi
    have hv := hvalue i
    linarith

end DifferentialGeometry.Topology
