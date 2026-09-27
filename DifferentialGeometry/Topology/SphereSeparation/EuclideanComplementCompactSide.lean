import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section

open Set Metric Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private theorem compact_closure_of_disjoint_sphere
    {V : Type*} [NormedAddCommGroup V] [ProperSpace V]
    {C : Set V} (hC : IsPreconnected C) {c : V} (hc : c ∈ C) {R : ℝ}
    (hcR : ‖c‖ < R) (havoid : Disjoint C (sphere (0 : V) R)) :
    IsCompact (closure C) := by
  have hbound : C ⊆ closedBall (0 : V) R := by
    intro x hx
    have hxR : ‖x‖ ≤ R := by
      by_contra h
      have hRx : R < ‖x‖ := lt_of_not_ge h
      obtain ⟨y, hyC, hyR⟩ := hC.intermediate_value hc hx continuous_norm.continuousOn
        ⟨le_of_lt hcR, le_of_lt hRx⟩
      exact (Set.disjoint_left.mp havoid) hyC (by simpa [mem_sphere_iff_norm] using hyR)
    simpa [mem_closedBall, dist_zero_right] using hxR
  exact (isBounded_closedBall.subset hbound).isCompact_closure

theorem exactly_one_compact_closure_of_two_complementary_components
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (hdim : 2 ≤ Module.finrank ℝ V)
    {S B E : Set V} (hS : IsCompact S)
    (hB : IsConnected B) (hE : IsConnected E)
    (hBopen : IsOpen B) (hEopen : IsOpen E) (hdisjoint : Disjoint B E)
    (hunion : B ∪ E = Sᶜ) :
    (IsCompact (closure B) ∧ ¬ IsCompact (closure E)) ∨
      (IsCompact (closure E) ∧ ¬ IsCompact (closure B)) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hrank : 1 < Module.rank ℝ V := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast (by omega : 1 < Module.finrank ℝ V)
  obtain ⟨b, hb⟩ := hB.nonempty
  obtain ⟨e, he⟩ := hE.nonempty
  have hcompact : IsCompact (S ∪ ({b} ∪ {e})) :=
    hS.union (isCompact_singleton.union isCompact_singleton)
  obtain ⟨R, hRpos, hR⟩ :=
    hcompact.isBounded.subset_ball_lt 0 (0 : V)
  have hbR : ‖b‖ < R := by
    simpa [mem_ball, dist_zero_right] using hR (Or.inr (Or.inl (mem_singleton b)))
  have heR : ‖e‖ < R := by
    simpa [mem_ball, dist_zero_right] using hR (Or.inr (Or.inr (mem_singleton e)))
  have hSball : S ⊆ ball (0 : V) R := by
    intro s hs
    exact hR (Or.inl hs)
  have hsphereSub : sphere (0 : V) R ⊆ B ∪ E := by
    intro x hx
    rw [hunion]
    intro hxS
    have hxlt : ‖x‖ < R := by simpa [mem_ball, dist_zero_right] using hSball hxS
    have hxeq : ‖x‖ = R := by simpa [mem_sphere_iff_norm] using hx
    linarith
  have hsome : IsCompact (closure B) ∨ IsCompact (closure E) := by
    rcases (isConnected_sphere hrank (0 : V) (le_of_lt hRpos)).isPreconnected.subset_or_subset
      hBopen hEopen hdisjoint hsphereSub with hsB | hsE
    · exact Or.inr (compact_closure_of_disjoint_sphere hE.isPreconnected he heR
        (hdisjoint.symm.mono_right hsB))
    · exact Or.inl (compact_closure_of_disjoint_sphere hB.isPreconnected hb hbR
        (hdisjoint.mono_right hsE))
  have hnotboth : ¬ (IsCompact (closure B) ∧ IsCompact (closure E)) := by
    rintro ⟨hBc, hEc⟩
    have hcover : closure B ∪ closure E ∪ S = univ := by
      apply Set.eq_univ_of_forall
      intro x
      by_cases hxS : x ∈ S
      · exact Or.inr hxS
      · have hxBE : x ∈ B ∪ E := by rw [hunion]; exact hxS
        rcases hxBE with hxB | hxE
        · exact Or.inl (Or.inl (subset_closure hxB))
        · exact Or.inl (Or.inr (subset_closure hxE))
    exact noncompact_univ V (hcover ▸ (hBc.union hEc).union hS)
  rcases hsome with hBc | hEc
  · exact Or.inl ⟨hBc, fun hEc => hnotboth ⟨hBc, hEc⟩⟩
  · exact Or.inr ⟨hEc, fun hBc => hnotboth ⟨hBc, hEc⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
