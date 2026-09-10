import Mathlib.Analysis.Complex.Convex

open Set

namespace Poincare.Topology

theorem isConnected_compl_openRectangle (a b c d : ℝ) :
    IsConnected {z : ℂ | z.re ≤ a ∨ b ≤ z.re ∨ z.im ≤ c ∨ d ≤ z.im} := by
  let L : Set ℂ := {z | z.re ≤ a}
  let R : Set ℂ := {z | b ≤ z.re}
  let B : Set ℂ := {z | z.im ≤ c}
  let T : Set ℂ := {z | d ≤ z.im}
  have hL : IsConnected L := (convex_halfSpace_re_le a).isConnected ⟨⟨a, 0⟩, by simp⟩
  have hR : IsConnected R := (convex_halfSpace_re_ge b).isConnected ⟨⟨b, 0⟩, by simp⟩
  have hB : IsConnected B := (convex_halfSpace_im_le c).isConnected ⟨⟨0, c⟩, by simp⟩
  have hT : IsConnected T := (convex_halfSpace_im_ge d).isConnected ⟨⟨0, d⟩, by simp⟩
  have hLB : IsConnected (L ∪ B) :=
    IsConnected.union ⟨⟨a, c⟩, by simp [L], by simp [B]⟩ hL hB
  have hRT : IsConnected (R ∪ T) :=
    IsConnected.union ⟨⟨b, d⟩, by simp [R], by simp [T]⟩ hR hT
  have hconn : IsConnected ((L ∪ B) ∪ (R ∪ T)) :=
    IsConnected.union ⟨⟨a, d⟩, Or.inl (by simp [L]), Or.inr (by simp [T])⟩ hLB hRT
  convert hconn using 1
  ext z
  change (z.re ≤ a ∨ b ≤ z.re ∨ z.im ≤ c ∨ d ≤ z.im) ↔
    ((z.re ≤ a ∨ z.im ≤ c) ∨ b ≤ z.re ∨ d ≤ z.im)
  tauto

end Poincare.Topology
