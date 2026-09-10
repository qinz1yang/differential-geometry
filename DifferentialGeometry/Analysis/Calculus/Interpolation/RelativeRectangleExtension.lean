import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Basic

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace Poincare.Analysis

def extendRectangleById {P : Type*} (a b c d : ℝ) (f : P × ℂ → ℂ) (q : P × ℂ) : ℂ := by
  classical
  exact if q.2 ∈ Complex.reProdIm (Icc a b) (Icc c d) then f q else q.2

private theorem extendRectangleById_of_mem {P : Type*} {a b c d : ℝ}
    (f : P × ℂ → ℂ) {q : P × ℂ} (hq : q.2 ∈ Complex.reProdIm (Icc a b) (Icc c d)) :
    extendRectangleById a b c d f q = f q := if_pos hq

private theorem extendRectangleById_of_notMem {P : Type*} {a b c d : ℝ}
    (f : P × ℂ → ℂ) {q : P × ℂ} (hq : q.2 ∉ Complex.reProdIm (Icc a b) (Icc c d)) :
    extendRectangleById a b c d f q = q.2 := if_neg hq

theorem contDiffOn_extendRectangleById
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {a b c d ε : ℝ} {f : P × ℂ → ℂ} {S : Set P} (hε : 0 < ε)
    (hf : ContDiffOn ℝ ∞ f (S ×ˢ Complex.reProdIm (Icc a b) (Icc c d)))
    (hfixed : ∀ p ∈ S, ∀ z ∈ Complex.reProdIm (Icc a b) (Icc c d),
      z.re ≤ a + ε ∨ b - ε ≤ z.re ∨ z.im ≤ c + ε ∨ d - ε ≤ z.im → f (p, z) = z) :
    ContDiffOn ℝ ∞ (extendRectangleById a b c d f) (S ×ˢ univ) := by
  let Q := Complex.reProdIm (Icc a b) (Icc c d)
  have hr : Continuous (fun q : P × ℂ ↦ q.2.re) := Complex.continuous_re.comp continuous_snd
  have hi : Continuous (fun q : P × ℂ ↦ q.2.im) := Complex.continuous_im.comp continuous_snd
  intro q hq
  by_cases hqint : q.2.re ∈ Ioo a b ∧ q.2.im ∈ Ioo c d
  · have hmem : S ×ˢ Q ∈ 𝓝[S ×ˢ univ] q := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (((isOpen_Ioo.preimage hr).inter (isOpen_Ioo.preimage hi)).mem_nhds hqint)]
        with r hrS hrint
      exact ⟨hrS.1, ⟨hrint.1.1.le, hrint.1.2.le⟩, ⟨hrint.2.1.le, hrint.2.2.le⟩⟩
    have hqin : q ∈ S ×ˢ Q := ⟨hq.1, ⟨hqint.1.1.le, hqint.1.2.le⟩, ⟨hqint.2.1.le, hqint.2.2.le⟩⟩
    apply ((hf q hqin).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq_of_mem _ hq
    filter_upwards [hmem] with r hrQ
    exact extendRectangleById_of_mem f hrQ.2
  · let U : Set (P × ℂ) := {r | r.2.re < a + ε ∨ b - ε < r.2.re ∨ r.2.im < c + ε ∨ d - ε < r.2.im}
    have hU : IsOpen U := (isOpen_lt hr continuous_const).union
      ((isOpen_lt continuous_const hr).union ((isOpen_lt hi continuous_const).union
        (isOpen_lt continuous_const hi)))
    have hUq : q ∈ U := by
      simp only [mem_Ioo, not_and_or, not_lt] at hqint
      rcases hqint with (h | h) | h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inr (Or.inl (by linarith)))
      · exact Or.inr (Or.inr (Or.inr (by linarith)))
    apply contDiffWithinAt_snd.congr_of_eventuallyEq_of_mem _ hq
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds hUq)] with r hrS hrU
    by_cases hrQ : r.2 ∈ Q
    · rw [extendRectangleById_of_mem f hrQ]
      exact hfixed r.1 hrS.1 r.2 hrQ (hrU.imp le_of_lt
        (Or.imp le_of_lt (Or.imp le_of_lt le_of_lt)))
    · exact extendRectangleById_of_notMem f hrQ

theorem leftInverse_extendRectangleById
    {P : Type*} {a b c d : ℝ} {f g : P × ℂ → ℂ} {p : P}
    (hf : MapsTo (fun z ↦ f (p, z)) (Complex.reProdIm (Icc a b) (Icc c d))
      (Complex.reProdIm (Icc a b) (Icc c d)))
    (hinv : ∀ z ∈ Complex.reProdIm (Icc a b) (Icc c d), g (p, f (p, z)) = z) :
    Function.LeftInverse (fun z ↦ extendRectangleById a b c d g (p, z))
      (fun z ↦ extendRectangleById a b c d f (p, z)) := by
  intro z
  change extendRectangleById a b c d g (p, extendRectangleById a b c d f (p, z)) = z
  by_cases hz : z ∈ Complex.reProdIm (Icc a b) (Icc c d)
  · rw [extendRectangleById_of_mem f (q := (p, z)) hz,
      extendRectangleById_of_mem g (q := (p, f (p, z))) (hf hz)]
    exact hinv z hz
  · rw [extendRectangleById_of_notMem f (q := (p, z)) hz,
      extendRectangleById_of_notMem g (q := (p, z)) hz]

end Poincare.Analysis
