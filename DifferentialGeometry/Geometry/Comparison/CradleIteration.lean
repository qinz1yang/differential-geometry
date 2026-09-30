import DifferentialGeometry.Geometry.Comparison.CradleSideLimit

set_option autoImplicit false

open Set Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem le_modelSideNegCurvature_of_cradle_steps
    {Q : Type*} {κ ℓ D : ℝ} (hκ : 0 ≤ κ) (hℓ : 0 < ℓ) (a b α : Q → ℝ)
    (hwindow : ∀ q, modelSideNegCurvature κ (a q) (b q) (α q) < D →
      0 ≤ a q ∧ a q ≤ b q ∧ 2 * ℓ / 3 ≤ a q + b q ∧ a q + b q < ℓ)
    (hα : ∀ q, α q ∈ Icc (0 : ℝ) Real.pi)
    (hD : ∀ q, D ≤ a q + b q)
    (hstep : ∀ q, modelSideNegCurvature κ (a q) (b q) (α q) < D →
      ∃ q' c, 0 ≤ c ∧ c ≤ a q + (2 * ℓ / 3 - a q) / 3 ∧
        a q' = min c (b q - (2 * ℓ / 3 - a q) / 3) ∧
        b q' = max c (b q - (2 * ℓ / 3 - a q) / 3) ∧
        modelSideNegCurvature κ (a q') (b q') (α q') ≤
          modelSideNegCurvature κ (a q) (b q) (α q) ∧
        comparisonAngleNegCurvature κ (a q) ((2 * ℓ / 3 - a q) / 3) c ≤ α q) :
    ∀ q, D ≤ modelSideNegCurvature κ (a q) (b q) (α q) := by
  classical
  intro q
  by_contra hn
  have hbad : modelSideNegCurvature κ (a q) (b q) (α q) < D := lt_of_not_ge hn
  let B := {q : Q // modelSideNegCurvature κ (a q) (b q) (α q) < D}
  have hs : ∀ z : B, ∃ z' : B, ∃ c, 0 ≤ c ∧ c ≤ a z.val + (2 * ℓ / 3 - a z.val) / 3 ∧
      a z'.val = min c (b z.val - (2 * ℓ / 3 - a z.val) / 3) ∧
      b z'.val = max c (b z.val - (2 * ℓ / 3 - a z.val) / 3) ∧
      modelSideNegCurvature κ (a z'.val) (b z'.val) (α z'.val) ≤
        modelSideNegCurvature κ (a z.val) (b z.val) (α z.val) ∧
      comparisonAngleNegCurvature κ (a z.val) ((2 * ℓ / 3 - a z.val) / 3) c ≤ α z.val := by
    intro z
    obtain ⟨z', c, hc, hcb, ha, hb, hm, hangle⟩ := hstep z.val z.property
    exact ⟨⟨z', hm.trans_lt z.property⟩, c, hc, hcb, ha, hb, hm, hangle⟩
  choose f c hc hcb ha hb hm hangle using hs
  let u : ℕ → B := fun n => Nat.rec ⟨q, hbad⟩ (fun _ z => f z) n
  have hsucc (n : ℕ) : u (n + 1) = f (u n) := rfl
  have hmono : Antitone (fun n => modelSideNegCurvature κ
      (a (u n).val) (b (u n).val) (α (u n).val)) := by
    apply antitone_nat_of_succ_le
    intro n
    rw [hsucc]
    exact hm (u n)
  have hbound := le_modelSideNegCurvature_of_cradle_recurrence hκ hℓ
    (a := fun n => a (u n).val) (b := fun n => b (u n).val)
    (c := fun n => c (u n)) (α := fun n => α (u n).val)
    (fun n => hwindow (u n).val (u n).property)
    (fun n => ⟨hc (u n), hcb (u n)⟩)
    (fun n => by rw [hsucc]; exact ha (u n))
    (fun n => by rw [hsucc]; exact hb (u n))
    (fun n => hα (u n).val) (fun n => hangle (u n)) hmono (fun n => hD (u n).val)
  exact (not_lt_of_ge (hbound 0)) hbad

end DifferentialGeometry.Geometry.Comparison.Toponogov
