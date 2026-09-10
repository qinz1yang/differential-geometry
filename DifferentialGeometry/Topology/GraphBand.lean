import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

noncomputable section
open Set

namespace Poincare.Topology

variable {N : Type*} [TopologicalSpace N]

def graphBandHomeomorph (a b : N → ℝ) (ha : Continuous a) (hb : Continuous b)
    (hab : ∀ p, a p < b p) : N × ℝ ≃ₜ N × ℝ where
  toEquiv := Equiv.prodCongrRight (fun p ↦
    (affineHomeomorph (b p - a p) (a p) (ne_of_gt (sub_pos.mpr (hab p)))).toEquiv)
  continuous_toFun := continuous_fst.prodMk
    ((((hb.sub ha).comp continuous_fst).mul continuous_snd).add (ha.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk
    ((continuous_snd.sub (ha.comp continuous_fst)).div
      ((hb.sub ha).comp continuous_fst)
      (fun x ↦ ne_of_gt (sub_pos.mpr (hab x.1))))

@[simp] theorem graphBandHomeomorph_apply (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p < b p) (x : N × ℝ) :
    graphBandHomeomorph a b ha hb hab x = (x.1, a x.1 + (b x.1 - a x.1) * x.2) :=
  Prod.ext rfl (add_comm _ _)

@[simp] theorem graphBandHomeomorph_symm_apply (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p < b p) (x : N × ℝ) :
    (graphBandHomeomorph a b ha hb hab).symm x =
      (x.1, (x.2 - a x.1) / (b x.1 - a x.1)) := rfl

private theorem image_closed_strip (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p < b p) :
    graphBandHomeomorph a b ha hb hab '' ((univ : Set N) ×ˢ Icc (0 : ℝ) 1) =
      {x : N × ℝ | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1} := by
  rw [(graphBandHomeomorph a b ha hb hab).image_eq_preimage_symm]
  ext ⟨p, t⟩
  change (True ∧ 0 ≤ (t - a p) / (b p - a p) ∧
    (t - a p) / (b p - a p) ≤ 1) ↔ a p ≤ t ∧ t ≤ b p
  rw [true_and, le_div_iff₀ (sub_pos.mpr (hab p)), zero_mul,
    div_le_one (sub_pos.mpr (hab p))]
  constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith only [h₀, h₁]

private theorem image_open_strip (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p < b p) :
    graphBandHomeomorph a b ha hb hab '' ((univ : Set N) ×ˢ Ioo (0 : ℝ) 1) =
      {x : N × ℝ | a x.1 < x.2 ∧ x.2 < b x.1} := by
  rw [(graphBandHomeomorph a b ha hb hab).image_eq_preimage_symm]
  ext ⟨p, t⟩
  change (True ∧ 0 < (t - a p) / (b p - a p) ∧
    (t - a p) / (b p - a p) < 1) ↔ a p < t ∧ t < b p
  rw [true_and, lt_div_iff₀ (sub_pos.mpr (hab p)), zero_mul,
    div_lt_one (sub_pos.mpr (hab p))]
  constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith only [h₀, h₁]

theorem interior_graphBand (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p < b p) :
    interior {x : N × ℝ | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1} =
      {x : N × ℝ | a x.1 < x.2 ∧ x.2 < b x.1} := by
  rw [← image_closed_strip a b ha hb hab,
    ← (graphBandHomeomorph a b ha hb hab).image_interior]
  simpa only [interior_prod_eq, interior_univ, interior_Icc] using
    image_open_strip a b ha hb hab

theorem closure_openGraphBand (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p < b p) :
    closure {x : N × ℝ | a x.1 < x.2 ∧ x.2 < b x.1} =
      {x : N × ℝ | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1} := by
  rw [← image_open_strip a b ha hb hab,
    ← (graphBandHomeomorph a b ha hb hab).image_closure]
  simpa only [closure_prod_eq, closure_univ, closure_Ioo zero_ne_one] using
    image_closed_strip a b ha hb hab

theorem frontier_graphBand (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p < b p) :
    frontier {x : N × ℝ | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1} =
      range (fun p ↦ (p, a p)) ∪ range (fun p ↦ (p, b p)) := by
  rw [← image_closed_strip a b ha hb hab,
    ← (graphBandHomeomorph a b ha hb hab).image_frontier,
    frontier_univ_prod_eq, frontier_Icc zero_le_one]
  ext y
  constructor
  · rintro ⟨⟨p, t⟩, ⟨_, ht⟩, rfl⟩
    rcases ht with rfl | ht
    · exact Or.inl ⟨p, by simp⟩
    · have ht1 : t = 1 := ht
      subst t
      exact Or.inr ⟨p, by simp⟩
  · rintro (⟨p, rfl⟩ | ⟨p, rfl⟩)
    · exact ⟨(p, 0), ⟨mem_univ _, by simp⟩, by simp⟩
    · exact ⟨(p, 1), ⟨mem_univ _, by simp⟩, by simp⟩

theorem isCompact_graphBand [CompactSpace N] (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p < b p) :
    IsCompact {x : N × ℝ | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1} := by
  rw [← image_closed_strip a b ha hb hab]
  exact (isCompact_univ.prod isCompact_Icc).image
    (graphBandHomeomorph a b ha hb hab).continuous

theorem isPreconnected_openGraphBand [PreconnectedSpace N] (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p < b p) :
    IsPreconnected {x : N × ℝ | a x.1 < x.2 ∧ x.2 < b x.1} := by
  rw [← image_open_strip a b ha hb hab]
  exact (isPreconnected_univ.prod isPreconnected_Ioo).image _
    (graphBandHomeomorph a b ha hb hab).continuous.continuousOn

theorem isPreconnected_graphBand [PreconnectedSpace N] (a b : N → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hab : ∀ p, a p < b p) :
    IsPreconnected {x : N × ℝ | a x.1 ≤ x.2 ∧ x.2 ≤ b x.1} := by
  rw [← closure_openGraphBand a b ha hb hab]
  exact (isPreconnected_openGraphBand a b ha hb hab).closure

end Poincare.Topology
