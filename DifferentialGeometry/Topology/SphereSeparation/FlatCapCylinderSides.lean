import DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.IntermediateValue

open Set Metric

namespace DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation

private theorem isConnected_signed_interval {σ b : ℝ} (hσ : σ ≠ 0) (hb : 0 < b) :
    IsConnected {t ∈ Ioo (-b) b | 0 < σ * t} := by
  rcases lt_or_gt_of_ne hσ with hs | hs
  · have he : {t ∈ Ioo (-b) b | 0 < σ * t} = Ioo (-b) 0 := by
      ext t
      have hm : 0 < σ * t ↔ t < 0 := by
        simpa only [smul_eq_mul] using (smul_pos_iff_of_neg_left hs : 0 < σ • t ↔ t < 0)
      simp only [mem_ofPred_eq, mem_Ioo, hm]
      constructor
      · tauto
      · rintro ⟨ht, ht'⟩
        exact ⟨⟨ht, lt_trans ht' hb⟩, ht'⟩
    rw [he]
    exact isConnected_Ioo (by linarith)
  · have he : {t ∈ Ioo (-b) b | 0 < σ * t} = Ioo 0 b := by
      ext t
      simp only [mem_ofPred_eq, mem_Ioo, mul_pos_iff_of_pos_left hs]
      constructor
      · tauto
      · rintro ⟨ht, ht'⟩
        exact ⟨⟨by linarith, ht'⟩, ht⟩
    rw [he]
    exact isConnected_Ioo hb

private theorem isConnected_cylinder_outer_side
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r R b σ : ℝ} (hR : 0 < R) (hb : 0 < b) (hσ : σ ≠ 0) :
    IsConnected {p ∈ ball (0 : E) R ×ˢ Ioo (-b) b | r < ‖p.1‖ ∨ σ * p.2 < 0} := by
  let N : Set (E × ℝ) := ball (0 : E) R ×ˢ {t ∈ Ioo (-b) b | σ * t < 0}
  have hN : IsConnected N := by
    apply (isConnected_ball hR).prod
    simpa only [neg_mul, neg_pos] using isConnected_signed_interval (neg_ne_zero.mpr hσ) hb
  obtain ⟨t₀, ht₀, htσ⟩ :=
    (show ({t ∈ Ioo (-b) b | σ * t < 0} : Set ℝ).Nonempty from by
      simpa only [neg_mul, neg_pos] using
        (isConnected_signed_interval (neg_ne_zero.mpr hσ) hb).nonempty)
  have hzero : (0 : E) ∈ ball (0 : E) R := mem_ball_self hR
  refine ⟨⟨(0, t₀), ⟨hzero, ht₀⟩, Or.inr htσ⟩,
    isPreconnected_of_forall (0, t₀) ?_⟩
  intro p hp
  have hNsub : N ⊆ {p ∈ ball (0 : E) R ×ˢ Ioo (-b) b |
      r < ‖p.1‖ ∨ σ * p.2 < 0} := by
    intro q hq
    exact ⟨⟨hq.1, hq.2.1⟩, Or.inr hq.2.2⟩
  by_cases houter : r < ‖p.1‖
  · let V : Set (E × ℝ) := {p.1} ×ˢ Ioo (-b) b
    have hV : IsConnected V := isConnected_singleton.prod (isConnected_Ioo (by linarith))
    refine ⟨N ∪ V, ?_, Or.inl ⟨hzero, ht₀, htσ⟩,
      Or.inr ⟨mem_singleton _, hp.1.2⟩, ?_⟩
    · rintro q (hq | hq)
      · exact hNsub hq
      · have he : q.1 = p.1 := hq.1
        exact ⟨⟨he ▸ hp.1.1, hq.2⟩, Or.inl (he ▸ houter)⟩
    · exact (IsConnected.union (show (N ∩ V).Nonempty from
        ⟨(p.1, t₀), ⟨hp.1.1, ht₀, htσ⟩, mem_singleton _, ht₀⟩) hN hV).isPreconnected
  · exact ⟨N, hNsub, ⟨hzero, ht₀, htσ⟩,
      ⟨hp.1.1, hp.1.2, hp.2.resolve_left houter⟩, hN.isPreconnected⟩

private theorem closed_side_in_flat_cap_cylinder
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    {S : Set X} (d : TwoSidedSeparation S) (Ψ : (E × ℝ) ≃ₜ X)
    {r R b σ : ℝ} (hr : 0 < r) (hR : r < R) (hb : 0 < b) (hσ : σ ≠ 0)
    (hS : ∀ p ∈ ball (0 : E) R ×ˢ Ioo (-b) b,
      Ψ p ∈ S ↔ (‖p.1‖ ≤ r ∧ p.2 = 0) ∨ (‖p.1‖ = r ∧ 0 < σ * p.2)) :
    (∀ p ∈ ball (0 : E) R ×ˢ Ioo (-b) b,
      Ψ p ∈ closure d.positiveSide ↔ ‖p.1‖ ≤ r ∧ 0 ≤ σ * p.2) ∨
    (∀ p ∈ ball (0 : E) R ×ˢ Ioo (-b) b,
      Ψ p ∈ closure d.positiveSide ↔ r ≤ ‖p.1‖ ∨ σ * p.2 ≤ 0) := by
  let C : Set (E × ℝ) := ball (0 : E) R ×ˢ Ioo (-b) b
  let A : Set (E × ℝ) := ball (0 : E) r ×ˢ {t ∈ Ioo (-b) b | 0 < σ * t}
  let B : Set (E × ℝ) := {p ∈ C | r < ‖p.1‖ ∨ σ * p.2 < 0}
  let U := Ψ '' A
  let V := Ψ '' B
  have hAC : A ⊆ C := fun _ hp => ⟨ball_subset_ball hR.le hp.1, hp.2.1⟩
  have hBC : B ⊆ C := fun _ hp => hp.1
  have hA : IsConnected A := (isConnected_ball hr).prod (isConnected_signed_interval hσ hb)
  have hB : IsConnected B := isConnected_cylinder_outer_side (hr.trans hR) hb hσ
  have hU : IsConnected U := hA.image Ψ Ψ.continuous.continuousOn
  have hV : IsConnected V := hB.image Ψ Ψ.continuous.continuousOn
  have hUS : U ⊆ Sᶜ := by
    rintro _ ⟨p, hp, rfl⟩ hs
    rcases (hS p (hAC hp)).mp hs with hs | hs
    · have := hp.2.2
      rw [hs.2, mul_zero] at this
      exact lt_irrefl _ this
    · have hn : ‖p.1‖ < r := by simpa only [mem_ball, dist_zero_right] using hp.1
      exact (ne_of_lt hn) hs.1
  have hVS : V ⊆ Sᶜ := by
    rintro _ ⟨p, hp, rfl⟩ hs
    have hs' := (hS p (hBC hp)).mp hs
    rcases hp.2 with hn | ht
    · rcases hs' with hs' | hs' <;> linarith [hs'.1]
    · rcases hs' with hs' | hs'
      · rw [hs'.2, mul_zero] at ht
        exact lt_irrefl _ ht
      · linarith [hs'.2]
  let O := Ψ '' C
  have hO : IsOpen O := Ψ.isOpenMap _ (isOpen_ball.prod isOpen_Ioo)
  have hSO : (S ∩ O).Nonempty := by
    have hp : ((0 : E), (0 : ℝ)) ∈ C := ⟨mem_ball_self (hr.trans hR), by linarith, hb⟩
    exact ⟨Ψ (0, 0), (hS _ hp).mpr (Or.inl ⟨by simpa using hr.le, rfl⟩), _, hp, rfl⟩
  have hcover : O ⊆ (U ∪ S) ∪ V := by
    rintro _ ⟨p, hp, rfl⟩
    by_cases hout : r < ‖p.1‖ ∨ σ * p.2 < 0
    · exact Or.inr ⟨p, ⟨hp, hout⟩, rfl⟩
    · push Not at hout
      rcases lt_or_eq_of_le hout.1 with hn | hn
      · rcases eq_or_lt_of_le hout.2 with ht | ht
        · have hz : p.2 = 0 := (mul_eq_zero.mp ht.symm).resolve_left hσ
          exact Or.inl (Or.inr ((hS _ hp).mpr (Or.inl ⟨hn.le, hz⟩)))
        · exact Or.inl (Or.inl ⟨p,
            ⟨by simpa only [mem_ball, dist_zero_right] using hn, hp.2, ht⟩, rfl⟩)
      · rcases eq_or_lt_of_le hout.2 with ht | ht
        · have hz : p.2 = 0 := (mul_eq_zero.mp ht.symm).resolve_left hσ
          exact Or.inl (Or.inr ((hS _ hp).mpr (Or.inl ⟨hn.le, hz⟩)))
        · exact Or.inl (Or.inr ((hS _ hp).mpr (Or.inr ⟨hn, ht⟩)))
  have hcl : closure d.positiveSide = d.positiveSide ∪ S := by
    exact (closure_eq_self_union_frontier d.positiveSide).trans
      (congrArg (d.positiveSide ∪ ·) d.frontier_positiveSide)
  have hnotcl (x : X) (hx : x ∈ d.negativeSide) : x ∉ closure d.positiveSide := by
    rw [hcl]
    rintro (h | h)
    · exact d.disjoint.le_bot ⟨h, hx⟩
    · exact d.negativeSide_subset_compl hx h
  rcases (d.neighborhood_halves_opposite_of_inter_nonempty hU hV hUS hVS hO hSO hcover).or
    with h | h
  · left
    intro p hp
    constructor
    · intro hc
      by_contra hn
      have hn' : r < ‖p.1‖ ∨ σ * p.2 < 0 := by
        rcases not_and_or.mp hn with hn | hn
        · exact Or.inl (lt_of_not_ge hn)
        · exact Or.inr (lt_of_not_ge hn)
      exact hnotcl _ (h.2 ⟨p, ⟨hp, hn'⟩, rfl⟩) hc
    · rintro ⟨hn, ht⟩
      rcases eq_or_lt_of_le ht with ht | ht
      · rw [hcl]
        have hz : p.2 = 0 := (mul_eq_zero.mp ht.symm).resolve_left hσ
        exact Or.inr ((hS _ hp).mpr (Or.inl ⟨hn, hz⟩))
      · rcases lt_or_eq_of_le hn with hn | hn
        · exact subset_closure (h.1 ⟨p,
            ⟨by simpa only [mem_ball, dist_zero_right] using hn, hp.2, ht⟩, rfl⟩)
        · rw [hcl]
          exact Or.inr ((hS _ hp).mpr (Or.inr ⟨hn, ht⟩))
  · right
    intro p hp
    constructor
    · intro hc
      by_contra hn
      push Not at hn
      exact hnotcl _ (h.1 ⟨p,
        ⟨by simpa only [mem_ball, dist_zero_right] using hn.1, hp.2, hn.2⟩, rfl⟩) hc
    · intro hn
      by_cases hout : r < ‖p.1‖ ∨ σ * p.2 < 0
      · exact subset_closure (h.2 ⟨p, ⟨hp, hout⟩, rfl⟩)
      · push Not at hout
        rw [hcl]
        apply Or.inr
        apply (hS _ hp).mpr
        rcases eq_or_lt_of_le hout.2 with ht | ht
        · exact Or.inl ⟨hout.1, (mul_eq_zero.mp ht.symm).resolve_left hσ⟩
        · exact Or.inr ⟨le_antisymm hout.1 (hn.resolve_right (not_le_of_gt ht)), ht⟩

theorem closed_sides_in_flat_cap_cylinder
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    {S : Set X} (d : TwoSidedSeparation S) (Ψ : (E × ℝ) ≃ₜ X)
    {r R b σ : ℝ} (hr : 0 < r) (hR : r < R) (hb : 0 < b) (hσ : σ ≠ 0)
    (hS : ∀ p ∈ ball (0 : E) R ×ˢ Ioo (-b) b,
      Ψ p ∈ S ↔ (‖p.1‖ ≤ r ∧ p.2 = 0) ∨ (‖p.1‖ = r ∧ 0 < σ * p.2)) :
    ((∀ p ∈ ball (0 : E) R ×ˢ Ioo (-b) b,
      Ψ p ∈ closure d.positiveSide ↔ ‖p.1‖ ≤ r ∧ 0 ≤ σ * p.2) ∧
      (∀ p ∈ ball (0 : E) R ×ˢ Ioo (-b) b,
        Ψ p ∈ closure d.negativeSide ↔ r ≤ ‖p.1‖ ∨ σ * p.2 ≤ 0)) ∨
    ((∀ p ∈ ball (0 : E) R ×ˢ Ioo (-b) b,
      Ψ p ∈ closure d.positiveSide ↔ r ≤ ‖p.1‖ ∨ σ * p.2 ≤ 0) ∧
      (∀ p ∈ ball (0 : E) R ×ˢ Ioo (-b) b,
        Ψ p ∈ closure d.negativeSide ↔ ‖p.1‖ ≤ r ∧ 0 ≤ σ * p.2)) := by
  have hclp : closure d.positiveSide = d.positiveSide ∪ S := by
    exact (closure_eq_self_union_frontier d.positiveSide).trans
      (congrArg (d.positiveSide ∪ ·) d.frontier_positiveSide)
  have hcln : closure d.negativeSide = d.negativeSide ∪ S := by
    exact (closure_eq_self_union_frontier d.negativeSide).trans
      (congrArg (d.negativeSide ∪ ·) d.frontier_negativeSide)
  have hc (x : X) : x ∈ closure d.negativeSide ↔ x ∈ S ∨ x ∉ closure d.positiveSide := by
    rw [hcln, hclp]
    constructor
    · rintro (hx | hx)
      · right
        rintro (hy | hy)
        · exact d.disjoint.le_bot ⟨hy, hx⟩
        · exact d.negativeSide_subset_compl hx hy
      · exact Or.inl hx
    · rintro (hx | hx)
      · exact Or.inr hx
      · have hS' : x ∈ Sᶜ := fun hs => hx (Or.inr hs)
        have hsplit : x ∈ d.positiveSide ∪ d.negativeSide := by
          rwa [d.union_eq_compl]
        exact Or.inl (hsplit.resolve_left fun hp => hx (Or.inl hp))
  have hboundary (p : E × ℝ) (hp : p ∈ ball (0 : E) R ×ˢ Ioo (-b) b) :
      Ψ p ∈ S ↔ (‖p.1‖ ≤ r ∧ 0 ≤ σ * p.2) ∧ (r ≤ ‖p.1‖ ∨ σ * p.2 ≤ 0) := by
    rw [hS p hp]
    constructor
    · rintro (⟨hn, ht⟩ | ⟨hn, ht⟩)
      · rw [ht, mul_zero]
        exact ⟨⟨hn, le_rfl⟩, Or.inr le_rfl⟩
      · exact ⟨⟨hn.le, ht.le⟩, Or.inl hn.ge⟩
    · rintro ⟨⟨hn, ht⟩, h⟩
      rcases eq_or_lt_of_le ht with ht | ht
      · exact Or.inl ⟨hn, (mul_eq_zero.mp ht.symm).resolve_left hσ⟩
      · exact Or.inr ⟨le_antisymm hn (h.resolve_right (not_le_of_gt ht)), ht⟩
  have hcover (p : E × ℝ) :
      (‖p.1‖ ≤ r ∧ 0 ≤ σ * p.2) ∨ (r ≤ ‖p.1‖ ∨ σ * p.2 ≤ 0) := by
    by_cases hn : ‖p.1‖ ≤ r
    · by_cases ht : 0 ≤ σ * p.2
      · exact Or.inl ⟨hn, ht⟩
      · exact Or.inr (Or.inr (le_of_not_ge ht))
    · exact Or.inr (Or.inl (le_of_not_ge hn))
  rcases closed_side_in_flat_cap_cylinder d Ψ hr hR hb hσ hS with h | h
  · left
    refine ⟨h, ?_⟩
    intro p hp
    rw [hc, hboundary p hp, h p hp]
    have := hcover p
    tauto
  · right
    refine ⟨h, ?_⟩
    intro p hp
    rw [hc, hboundary p hp, h p hp]
    have := hcover p
    tauto

theorem closed_positiveSide_in_flat_cap_cylinder_of_disjoint_or_subset
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] [TopologicalSpace X]
    {S₀ S₁ : Set X} (d₀ : TwoSidedSeparation S₀) (d₁ : TwoSidedSeparation S₁)
    (Ψ : (E × ℝ) ≃ₜ X) {r R b σ : ℝ} (hr : 0 < r) (hR : r < R)
    (hb : 0 < b) (hσ : σ ≠ 0)
    (hS₀ : ∀ p ∈ ball (0 : E) R ×ˢ Ioo (-b) b,
      Ψ p ∈ S₀ ↔ (‖p.1‖ ≤ r ∧ p.2 = 0) ∨ (‖p.1‖ = r ∧ 0 < σ * p.2))
    (hS₁ : ∀ p ∈ ball (0 : E) R ×ˢ Ioo (-b) b,
      Ψ p ∈ S₁ ↔ (‖p.1‖ ≤ r ∧ p.2 = 0) ∨ (‖p.1‖ = r ∧ 0 < -σ * p.2))
    (hrel : Disjoint d₀.positiveSide d₁.positiveSide ∨ d₀.positiveSide ⊆ d₁.positiveSide) :
    ∀ p ∈ ball (0 : E) R ×ˢ Ioo (-b) b,
      Ψ p ∈ closure d₀.positiveSide ↔ ‖p.1‖ ≤ r ∧ 0 ≤ σ * p.2 := by
  rcases d₀.closed_sides_in_flat_cap_cylinder Ψ hr hR hb hσ hS₀ with h₀ | h₀
  · exact h₀.1
  have hcl₀ := h₀.1
  obtain ⟨t, ht, hσt⟩ : ∃ t ∈ Ioo (-b) b, 0 < σ * t := by
    rcases lt_or_gt_of_ne hσ with hs | hs
    · refine ⟨-b / 2, ⟨by linarith, by linarith⟩, ?_⟩
      exact mul_pos_of_neg_of_neg hs (by linarith)
    · exact ⟨b / 2, ⟨by linarith, by linarith⟩, mul_pos hs (half_pos hb)⟩
  have htne : t ≠ 0 := by intro hh; rw [hh, mul_zero] at hσt; exact lt_irrefl _ hσt
  obtain ⟨x, hx'⟩ := (NormedSpace.sphere_nonempty (E := E) (x := 0)
    (r := (r + R) / 2)).mpr (by linarith)
  have hx : ‖x‖ = (r + R) / 2 := mem_sphere_zero_iff_norm.mp hx'
  have hxlo : r < ‖x‖ := by rw [hx]; linarith
  have hxhi : ‖x‖ < R := by rw [hx]; linarith
  have hxW : (x, (0 : ℝ)) ∈ ball (0 : E) R ×ˢ Ioo (-b) b :=
    ⟨mem_ball_zero_iff.mpr hxhi, neg_neg_of_pos hb, hb⟩
  have hyW : ((0 : E), -t) ∈ ball (0 : E) R ×ˢ Ioo (-b) b :=
    ⟨mem_ball_self (hr.trans hR), by constructor <;> linarith [ht.1, ht.2]⟩
  have hxS₀ : Ψ (x, 0) ∉ S₀ := by
    rw [hS₀ _ hxW]
    rintro (⟨hn, _⟩ | ⟨hn, _⟩) <;> linarith
  have hxS₁ : Ψ (x, 0) ∉ S₁ := by
    rw [hS₁ _ hxW]
    rintro (⟨hn, _⟩ | ⟨hn, _⟩) <;> linarith
  have hyS₀ : Ψ (0, -t) ∉ S₀ := by
    rw [hS₀ _ hyW]
    rintro (⟨_, ht'⟩ | ⟨hn, _⟩)
    · exact htne (neg_eq_zero.mp ht')
    · simp only [norm_zero] at hn
      linarith
  have hyS₁ : Ψ (0, -t) ∉ S₁ := by
    rw [hS₁ _ hyW]
    rintro (⟨_, ht'⟩ | ⟨hn, _⟩)
    · exact htne (neg_eq_zero.mp ht')
    · simp only [norm_zero] at hn
      linarith
  have hmem₀ {z : X} (hz : z ∈ closure d₀.positiveSide) (hnot : z ∉ S₀) :
      z ∈ d₀.positiveSide := by
    rw [closure_eq_self_union_frontier, d₀.frontier_positiveSide] at hz
    exact hz.resolve_right hnot
  have hmem₁ {z : X} (hz : z ∈ closure d₁.positiveSide) (hnot : z ∉ S₁) :
      z ∈ d₁.positiveSide := by
    rw [closure_eq_self_union_frontier, d₁.frontier_positiveSide] at hz
    exact hz.resolve_right hnot
  have hx₀ : Ψ (x, 0) ∈ d₀.positiveSide :=
    hmem₀ ((hcl₀ _ hxW).mpr (Or.inl hxlo.le)) hxS₀
  have hy₀ : Ψ (0, -t) ∈ d₀.positiveSide :=
    hmem₀ ((hcl₀ _ hyW).mpr (Or.inr (by dsimp; nlinarith))) hyS₀
  rcases d₁.closed_sides_in_flat_cap_cylinder Ψ hr hR hb (neg_ne_zero.mpr hσ) hS₁ with h₁ | h₁
  · have hxnot : Ψ (x, 0) ∉ closure d₁.positiveSide := by
      rw [h₁.1 _ hxW]
      exact fun hh => not_le_of_gt hxlo hh.1
    have hy₁ : Ψ (0, -t) ∈ d₁.positiveSide := by
      apply hmem₁ _ hyS₁
      apply (h₁.1 _ hyW).mpr
      exact ⟨by simpa only [norm_zero] using hr.le, by dsimp; nlinarith⟩
    rcases hrel with hrel | hrel
    · exact False.elim (hrel.le_bot ⟨hy₀, hy₁⟩)
    · exact False.elim (hxnot (subset_closure (hrel hx₀)))
  · have hx₁ : Ψ (x, 0) ∈ d₁.positiveSide :=
      hmem₁ ((h₁.1 _ hxW).mpr (Or.inl hxlo.le)) hxS₁
    have hynot : Ψ (0, -t) ∉ closure d₁.positiveSide := by
      rw [h₁.1 _ hyW]
      simp only [norm_zero]
      rintro (hn | ht') <;> nlinarith
    rcases hrel with hrel | hrel
    · exact False.elim (hrel.le_bot ⟨hx₀, hx₁⟩)
    · exact False.elim (hynot (subset_closure (hrel hy₀)))

end DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation
