import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section
open Set Topology

namespace DifferentialGeometry.Topology.Ehresmann

variable {M : Type*} [TopologicalSpace M]

abbrev IntervalCompletionSpace (u : M → ℝ) (a b : ℝ) :=
  {q : M × ℝ // q.2 = u q.1 ∨ (u q.1 = a ∧ q.2 ≤ a) ∨ (u q.1 = b ∧ b ≤ q.2)}

def intervalCompletionInclusion (u : M → ℝ) (a b : ℝ) (x : M) : IntervalCompletionSpace u a b :=
  ⟨(x, u x), Or.inl rfl⟩

def intervalCompletionHeight (u : M → ℝ) (a b : ℝ) : IntervalCompletionSpace u a b → ℝ :=
  fun q ↦ q.1.2

def intervalCompletionReflect (u : M → ℝ) (a b : ℝ) :
    IntervalCompletionSpace u a b ≃ₜ IntervalCompletionSpace (fun x ↦ -u x) (-b) (-a) := by
  let f : IntervalCompletionSpace u a b → IntervalCompletionSpace (fun x ↦ -u x) (-b) (-a) :=
    fun q ↦ ⟨(q.1.1, -q.1.2), by
      rcases q.2 with h | ⟨hu, ht⟩ | ⟨hu, ht⟩
      · exact Or.inl (congrArg Neg.neg h)
      · exact Or.inr (Or.inr ⟨congrArg Neg.neg hu, neg_le_neg ht⟩)
      · exact Or.inr (Or.inl ⟨congrArg Neg.neg hu, neg_le_neg ht⟩)⟩
  let g : IntervalCompletionSpace (fun x ↦ -u x) (-b) (-a) → IntervalCompletionSpace u a b :=
    fun q ↦ ⟨(q.1.1, -q.1.2), by
      rcases q.2 with h | ⟨hu, ht⟩ | ⟨hu, ht⟩
      · exact Or.inl (by simpa only [neg_neg] using congrArg Neg.neg h)
      · exact Or.inr (Or.inr ⟨neg_injective hu, by simpa only [neg_neg] using neg_le_neg ht⟩)
      · exact Or.inr (Or.inl ⟨neg_injective hu, by simpa only [neg_neg] using neg_le_neg ht⟩)⟩
  refine ⟨⟨f, g, (fun q ↦ Subtype.ext (Prod.ext rfl (neg_neg _))),
    (fun q ↦ Subtype.ext (Prod.ext rfl (neg_neg _)))⟩, ?_, ?_⟩
  · exact ((continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_snd.comp continuous_subtype_val).neg).subtype_mk _
  · exact ((continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_snd.comp continuous_subtype_val).neg).subtype_mk _

theorem isClosedEmbedding_intervalCompletionInclusion [CompactSpace M] [T2Space M]
    {u : M → ℝ} (hu : Continuous u) (a b : ℝ) :
    IsClosedEmbedding (intervalCompletionInclusion u a b) := by
  have hc : Continuous (intervalCompletionInclusion u a b) :=
    (continuous_id.prodMk hu).subtype_mk _
  apply hc.isClosedEmbedding
  intro x y hxy
  exact congrArg (fun q : IntervalCompletionSpace u a b ↦ q.1.1) hxy

omit [TopologicalSpace M] in
theorem preimage_Icc_intervalCompletionHeight {u : M → ℝ} {a b : ℝ}
    (hbound : ∀ x, u x ∈ Icc a b) :
    intervalCompletionHeight u a b ⁻¹' Icc a b = range (intervalCompletionInclusion u a b) := by
  ext q
  constructor
  · intro hq
    have heq : q.1.2 = u q.1.1 := by
      rcases q.2 with h | ⟨hu, ht⟩ | ⟨hu, ht⟩
      · exact h
      · exact (le_antisymm ht hq.1).trans hu.symm
      · exact (le_antisymm hq.2 ht).trans hu.symm
    exact ⟨q.1.1, Subtype.ext (Prod.ext rfl heq.symm)⟩
  · rintro ⟨x, rfl⟩
    exact hbound x

set_option backward.isDefEq.respectTransparency false in
theorem isCompact_preimage_Icc_intervalCompletionHeight [CompactSpace M]
    {u : M → ℝ} (hu : Continuous u) (a b r s : ℝ) :
    IsCompact (intervalCompletionHeight u a b ⁻¹' Icc r s) := by
  have hclosed : IsClosed {q : M × ℝ |
      q.2 = u q.1 ∨ (u q.1 = a ∧ q.2 ≤ a) ∨ (u q.1 = b ∧ b ≤ q.2)} :=
    (isClosed_eq continuous_snd (hu.comp continuous_fst)).union
      (((isClosed_eq (hu.comp continuous_fst) continuous_const).inter
        (isClosed_le continuous_snd continuous_const)).union
      ((isClosed_eq (hu.comp continuous_fst) continuous_const).inter
        (isClosed_le continuous_const continuous_snd)))
  have hemb : IsClosedEmbedding (Subtype.val : IntervalCompletionSpace u a b → M × ℝ) :=
    hclosed.isClosedEmbedding_subtypeVal
  have hh := hemb.isCompact_preimage (isCompact_univ.prod (isCompact_Icc : IsCompact (Icc r s)))
  have heq : (Subtype.val : IntervalCompletionSpace u a b → M × ℝ) ⁻¹' (univ ×ˢ Icc r s) =
      intervalCompletionHeight u a b ⁻¹' Icc r s := by
    ext q
    exact and_iff_right (mem_univ q.1.1)
  rwa [heq] at hh

end DifferentialGeometry.Topology.Ehresmann
