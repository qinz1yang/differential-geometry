import DifferentialGeometry.Topology.PiecewiseLinear.Section34SquareCylindricalCancellation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem ordered_parameters {E : Type*} [TopologicalSpace E] {N J : Set E}
    {γ : ℝ → E} (hγ : SurjOn γ (Icc 0 1) J)
    (hends : {γ 0, γ 1} ⊆ frontier N) (p : Fin 2 → E)
    (hpJ : ∀ i, p i ∈ J) (hpN : ∀ i, p i ∈ interior N) (hpne : p 0 ≠ p 1) :
    ∃ (σ : Fin 2 ≃ Fin 2) (t : Fin 2 → ℝ),
      0 < t 0 ∧ t 0 < t 1 ∧ t 1 < 1 ∧
      (∀ i, γ (t i) = p (σ i)) ∧ ({γ (t 0), γ (t 1)} : Set E) = {p 0, p 1} := by
  classical
  have hex (i : Fin 2) : ∃ s ∈ Ioo (0 : ℝ) 1, γ s = p i := by
    obtain ⟨s, hs, hsp⟩ := hγ (hpJ i)
    have hs0 : s ≠ 0 := by
      intro h
      apply Set.disjoint_left.mp disjoint_interior_frontier (hpN i)
      rw [← hsp, h]
      exact hends (by simp)
    have hs1 : s ≠ 1 := by
      intro h
      apply Set.disjoint_left.mp disjoint_interior_frontier (hpN i)
      rw [← hsp, h]
      exact hends (by simp)
    exact ⟨s, ⟨lt_of_le_of_ne hs.1 hs0.symm, lt_of_le_of_ne hs.2 hs1⟩, hsp⟩
  choose s hs hsp using hex
  have hne : s 0 ≠ s 1 := fun h => hpne ((hsp 0).symm.trans ((congrArg γ h).trans (hsp 1)))
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨Equiv.refl _, s, (hs 0).1, hlt, (hs 1).2, hsp, by rw [hsp 0, hsp 1]⟩
  · refine ⟨Equiv.swap 0 1, s ∘ Equiv.swap 0 1, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using (hs 1).1
    · simpa using hlt
    · simpa using (hs 0).2
    · intro i
      exact hsp _
    · simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right, hsp]
      exact pair_comm _ _

theorem exists_strict_square_cylindrical_cancellation_of_two_interior_crossings
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {N J L : Set (ℝ × ℝ)} (hN : IsPLBall 2 N) {γ δ : ℝ → ℝ × ℝ}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) J) (hJN : J ⊆ N)
    (hJends : J ∩ frontier N = {γ 0, γ 1})
    (hδ : IsPLHomeomorphOn δ (Icc 0 1) L) (hLN : L ⊆ N)
    (hLends : L ∩ frontier N = {δ 0, δ 1})
    (p : Fin 2 → ℝ × ℝ) (hpN : ∀ i, p i ∈ interior N) (hpne : p 0 ≠ p 1)
    (htrace : J ∩ L = {p 0, p 1})
    (e : Fin 2 → OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (ε : Fin 2 → ℝ) (hε : ∀ i, 0 < ε i)
    (hsource : ∀ i, Ioo (-ε i) (ε i) ×ˢ Ioo (-ε i) (ε i) ⊆ (e i).source)
    (hcenter : ∀ i, e i (0, 0) = p i)
    (hcurve : ∀ i, ∀ z ∈ Ioo (-ε i) (ε i) ×ˢ Ioo (-ε i) (ε i),
      e i z ∈ L ↔ z.2 = 0)
    (haxis : ∀ i, ∀ s ∈ Ioo (-ε i) (ε i), e i (0, s) ∈ J)
    {f : (ℝ × ℝ) × ℝ → E} {S X Y : Set E}
    (hf : IsCylindricalDiagram f N S) (hends : ∀ x ∈ N, f (x, 0) = f (x, 1))
    (hfront : frontier S ⊆ f '' (frontier N ×ˢ Icc (0 : ℝ) 1))
    (hX : X ∩ S = f '' (J ×ˢ Icc (0 : ℝ) 1))
    (hY : Y ∩ S = f '' (L ×ˢ Icc (0 : ℝ) 1))
    {ι : Type*} [Finite ι] {Γ : ι → Set E} (hΓ : ∀ i, IsPLSphere 1 (Γ i))
    (hΓdis : Pairwise fun i j => Disjoint (Γ i) (Γ j)) (hfull : X ∩ Y = ⋃ i, Γ i) :
    ∃ (I : Set ι) (H : E ≃ₜ E), Nat.card I < Nat.card ι ∧
      IsPLHomeomorphOn H univ univ ∧ EqOn H id Sᶜ ∧
      (∀ i : I, Disjoint S (Γ i.1)) ∧
      (∀ i : I, ∀ x ∈ Γ i.1, H =ᶠ[𝓝 x] id) ∧ H '' X ∩ Y = ⋃ i : I, Γ i.1 := by
  have hpJ (i : Fin 2) : p i ∈ J := by
    have h : p i ∈ ({p 0, p 1} : Set (ℝ × ℝ)) := by fin_cases i <;> simp
    rw [← htrace] at h
    exact h.1
  have hend : {γ 0, γ 1} ⊆ frontier N := by
    rw [← hJends]
    exact inter_subset_right
  obtain ⟨σ, t, ht0, htt, ht1, hmatch, hpair⟩ :=
    ordered_parameters hγ.bijOn.surjOn hend p hpJ hpN hpne
  exact exists_strict_square_cylindrical_cancellation_of_two_crossing_crosscuts
    hN hγ hJN hJends hδ hLN hLends t ht0 htt ht1 (htrace.trans hpair.symm)
    (e ∘ σ) (ε ∘ σ) (fun i => hε (σ i)) (fun i => hsource (σ i))
    (fun i => (hcenter (σ i)).trans (hmatch i).symm)
    (fun i => hcurve (σ i)) (fun i => haxis (σ i))
    hf hends hfront hX hY hΓ hΓdis hfull

end DifferentialGeometry.Topology.PiecewiseLinear
