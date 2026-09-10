import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Basic

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace Poincare.Analysis

def extendIntervalById {P : Type*} (a b : ℝ) (f : P × ℝ → ℝ) (q : P × ℝ) : ℝ :=
  if q.2 ∈ Icc a b then f q else q.2

theorem contDiffOn_extendIntervalById
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {a b ε : ℝ} {f : P × ℝ → ℝ} {S : Set P} (hε : 0 < ε)
    (hf : ContDiffOn ℝ ∞ f (S ×ˢ Icc a b))
    (hfixed : ∀ p ∈ S, ∀ y ∈ Icc a b, y ≤ a + ε ∨ b - ε ≤ y → f (p, y) = y) :
    ContDiffOn ℝ ∞ (extendIntervalById a b f) (S ×ˢ univ) := by
  intro q hq
  by_cases hqint : q.2 ∈ Ioo a b
  · have hmem : S ×ˢ Icc a b ∈ 𝓝[S ×ˢ univ] q := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds ((isOpen_Ioo.preimage continuous_snd).mem_nhds hqint)] with r hr hri
      exact ⟨hr.1, ⟨hri.1.le, hri.2.le⟩⟩
    apply ((hf q ⟨hq.1, ⟨hqint.1.le, hqint.2.le⟩⟩).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq_of_mem _ hq
    filter_upwards [hmem] with r hr
    simp only [extendIntervalById, if_pos hr.2]
  · let U : Set (P × ℝ) := {r | r.2 < a + ε ∨ b - ε < r.2}
    have hU : IsOpen U :=
      (isOpen_lt continuous_snd continuous_const).union (isOpen_lt continuous_const continuous_snd)
    have hUq : q ∈ U := by
      simp only [mem_Ioo, not_and_or, not_lt] at hqint
      rcases hqint with hqint | hqint
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    apply contDiffWithinAt_snd.congr_of_eventuallyEq_of_mem _ hq
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds hUq)] with r hr hUr
    by_cases hri : r.2 ∈ Icc a b
    · simp only [extendIntervalById, if_pos hri]
      exact hfixed r.1 hr.1 r.2 hri (hUr.imp le_of_lt le_of_lt)
    · simp only [extendIntervalById, if_neg hri]

theorem leftInverse_extendIntervalById
    {P : Type*} {a b : ℝ} {f g : P × ℝ → ℝ} {p : P}
    (hf : MapsTo (fun y ↦ f (p, y)) (Icc a b) (Icc a b))
    (hinv : ∀ y ∈ Icc a b, g (p, f (p, y)) = y) :
    Function.LeftInverse (fun y ↦ extendIntervalById a b g (p, y))
      (fun y ↦ extendIntervalById a b f (p, y)) := by
  intro y
  by_cases hy : y ∈ Icc a b
  · simp only [extendIntervalById, if_pos hy, if_pos (hf hy)]
    exact hinv y hy
  · simp only [extendIntervalById, if_neg hy]

end Poincare.Analysis
