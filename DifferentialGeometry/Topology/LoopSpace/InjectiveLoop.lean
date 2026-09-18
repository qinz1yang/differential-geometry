import DifferentialGeometry.Topology.LoopSpace.BasedCircle

namespace DifferentialGeometry.Topology

open Set

variable {X : Type*} [TopologicalSpace X]

theorem injective_trans {a b c : X} {p : Path a b} {q : Path b c}
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hpq : Set.range p ∩ Set.range q ⊆ {b}) : Function.Injective (p.trans q) := by
  intro s t hst
  simp only [Path.trans_apply] at hst
  split_ifs at hst with hs ht ht
  · have h := congrArg Subtype.val (hp hst)
    simp only at h
    exact Subtype.ext (by linarith)
  · have hmem : p _ ∈ Set.range p ∩ Set.range q := ⟨⟨_, rfl⟩, ⟨_, hst.symm⟩⟩
    have hb : p _ = b := hpq hmem
    have hs1 := congrArg Subtype.val (hp (hb.trans p.target.symm))
    have ht0 := congrArg Subtype.val (hq ((hst.symm.trans hb).trans q.source.symm))
    simp only [Set.Icc.coe_one, Set.Icc.coe_zero] at hs1 ht0
    exact absurd (by linarith : (t : ℝ) ≤ 1 / 2) ht
  · have hmem : p _ ∈ Set.range p ∩ Set.range q := ⟨⟨_, rfl⟩, ⟨_, hst⟩⟩
    have hb : p _ = b := hpq hmem
    have hs1 := congrArg Subtype.val (hp (hb.trans p.target.symm))
    have ht0 := congrArg Subtype.val (hq ((hst.trans hb).trans q.source.symm))
    simp only [Set.Icc.coe_one, Set.Icc.coe_zero] at hs1 ht0
    exact absurd (by linarith : (s : ℝ) ≤ 1 / 2) hs
  · have h := congrArg Subtype.val (hq hst)
    simp only at h
    exact Subtype.ext (by linarith)

theorem pathToCircle_trans_injective {a b : X} {p : Path a b} {q : Path b a}
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hpq : Set.range p ∩ Set.range q ⊆ {a, b}) :
    Function.Injective (pathToCircle (p.trans q)) := by
  intro θ₁ θ₂ hθ
  obtain ⟨s, rfl⟩ := unitInterval_to_loopCircle_surjective θ₁
  obtain ⟨t, rfl⟩ := unitInterval_to_loopCircle_surjective θ₂
  rw [pathToCircle_coe, pathToCircle_coe] at hθ
  have hcoe : ∀ r₁ r₂ : unitInterval, (r₁ : ℝ) = (r₂ : ℝ) →
      ((r₁ : ℝ) : loopCircle) = ((r₂ : ℝ) : loopCircle) := fun _ _ h => by rw [h]
  have hends : ((0 : ℝ) : loopCircle) = ((1 : ℝ) : loopCircle) :=
    (AddCircle.coe_period (1 : ℝ)).symm
  simp only [Path.trans_apply] at hθ
  split_ifs at hθ with hs ht ht
  · exact hcoe s t (by linarith [congrArg Subtype.val (hp hθ)])
  · have hmem : p _ ∈ Set.range p ∩ Set.range q := ⟨⟨_, rfl⟩, ⟨_, hθ.symm⟩⟩
    rcases hpq hmem with hval | hval
    · have hs0 := congrArg Subtype.val (hp (hval.trans p.source.symm))
      have ht1 := congrArg Subtype.val (hq ((hθ.symm.trans hval).trans q.target.symm))
      simp only [Set.Icc.coe_one, Set.Icc.coe_zero] at hs0 ht1
      have hs' : (s : ℝ) = 0 := by linarith
      have ht' : (t : ℝ) = 1 := by linarith
      change ((s : ℝ) : loopCircle) = ((t : ℝ) : loopCircle)
      rw [hs', ht']
      exact hends
    · rw [mem_singleton_iff] at hval
      have hs1 := congrArg Subtype.val (hp (hval.trans p.target.symm))
      have ht0 := congrArg Subtype.val (hq ((hθ.symm.trans hval).trans q.source.symm))
      simp only [Set.Icc.coe_one, Set.Icc.coe_zero] at hs1 ht0
      exact absurd (by linarith : (t : ℝ) ≤ 1 / 2) ht
  · have hmem : p _ ∈ Set.range p ∩ Set.range q := ⟨⟨_, rfl⟩, ⟨_, hθ⟩⟩
    rcases hpq hmem with hval | hval
    · have ht0 := congrArg Subtype.val (hp (hval.trans p.source.symm))
      have hs1 := congrArg Subtype.val (hq ((hθ.trans hval).trans q.target.symm))
      simp only [Set.Icc.coe_one, Set.Icc.coe_zero] at hs1 ht0
      have hs' : (s : ℝ) = 1 := by linarith
      have ht' : (t : ℝ) = 0 := by linarith
      change ((s : ℝ) : loopCircle) = ((t : ℝ) : loopCircle)
      rw [hs', ht']
      exact hends.symm
    · rw [mem_singleton_iff] at hval
      have ht1 := congrArg Subtype.val (hp (hval.trans p.target.symm))
      have hs0 := congrArg Subtype.val (hq ((hθ.trans hval).trans q.source.symm))
      simp only [Set.Icc.coe_one, Set.Icc.coe_zero] at ht1 hs0
      exact absurd (by linarith : (s : ℝ) ≤ 1 / 2) hs
  · exact hcoe s t (by linarith [congrArg Subtype.val (hq hθ)])

theorem pathToCircle_surjective {x : X} (ℓ : Path x x) (hrange : Set.range ℓ = Set.univ) :
    Function.Surjective (pathToCircle ℓ) := by
  intro y
  obtain ⟨t, ht⟩ : y ∈ Set.range ℓ := hrange ▸ Set.mem_univ y
  exact ⟨((t : ℝ) : loopCircle), (pathToCircle_coe ℓ t).trans ht⟩

end DifferentialGeometry.Topology
