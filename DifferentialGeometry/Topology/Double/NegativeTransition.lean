import DifferentialGeometry.Topology.Double.PositiveTransition
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology TopologicalSpace
open scoped ContDiff Topology
namespace Poincare.Topology
variable {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℝ E H)
  (B : Set M) {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace G] [ChartedSpace G B] (J : ModelWithCorners ℝ F G)
  (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
  (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
  {a : ℝ} (c : C(B × Icc (0 : ℝ) a, M))
  (hheight : ∀ q, r (c q) = q.2.val)
  (hsmall : ∀ x, r x ≤ a → x ∈ range c) (hc : IsEmbedding c) (ha : 0 < a) (b : B)


def doubleNegativeStrip : Opens (B × ℝ) :=
  ⟨{q | 0 < -q.2 ∧ -q.2 < a},
    (isOpen_lt continuous_const continuous_snd.neg).inter
      (isOpen_lt continuous_snd.neg continuous_const)⟩


theorem source_doubleSeam_negative_transition :
    ((doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).trans
      (doubleNegativePatch B r hr hn).symm).source = {q | 0 < -q.2 ∧ -q.2 < a} := by
  ext q
  change (q ∈ (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).source ∧
    doubleHeight B r hr (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q) < 0) ↔ _
  rw [doubleSeamPatch_source]
  constructor
  · rintro ⟨hq, ht⟩
    rw [doubleHeight_seamPatch B r hr hz hn c hheight hsmall hc ha b hq] at ht
    exact ⟨neg_pos.mpr ht, (neg_le_abs q.2).trans_lt hq⟩
  · intro hq
    have ht : q.2 < 0 := neg_pos.mp hq.1
    have hqa : |q.2| < a := by rw [abs_of_neg ht]; exact hq.2
    exact ⟨hqa, by rw [doubleHeight_seamPatch B r hr hz hn c hheight hsmall hc ha b hqa]; exact ht⟩


theorem source_doubleNegative_seam_transition :
    ((doubleNegativePatch B r hr hn).trans
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm).source =
        {x | 0 < r x ∧ r x < a} := by
  ext x
  change (0 < r x ∧ doubleNegative B x ∈
    (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).target) ↔ _
  rw [doubleSeamPatch_target]
  change (0 < r x ∧ |-r x| < a) ↔ _
  rw [abs_neg, abs_of_nonneg (hn x)]
  rfl


theorem contMDiffOn_doubleSeam_negative_transition
    (d : Diffeomorph (J.prod 𝓘(ℝ, ℝ)) I (doublePositiveStrip B (a := a)) (doublePositiveBand r (a := a)) ∞)
    (hd : ∀ q, (d q).val = c (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.le⟩)) :
    ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) I ∞
      ((doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).trans
        (doubleNegativePatch B r hr hn).symm)
      ((doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).trans
        (doubleNegativePatch B r hr hn).symm).source := by
  rw [source_doubleSeam_negative_transition]
  apply Poincare.Manifold.contMDiffOn_of_contMDiff_open_restrict (doubleNegativeStrip B (a := a))
  let f : doubleNegativeStrip B (a := a) → doublePositiveStrip B (a := a) :=
    fun q => ⟨(q.val.1, -q.val.2), q.property⟩
  have hf : ContMDiff (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff (doublePositiveStrip B (a := a)) f).mp
    have hneg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => -t) := contDiff_neg.contMDiff
    exact (contMDiff_fst.comp contMDiff_subtype_val).prodMk
      (hneg.comp (contMDiff_snd.comp contMDiff_subtype_val))
  apply (contMDiff_subtype_val.comp (d.contMDiff.comp hf)).congr
  intro q
  change doubleFold B (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q.val) = (d (f q)).val
  rw [doubleSeamPatch_of_neg B r hr hz hn c hheight hsmall hc ha b
    (by rw [abs_of_neg (neg_pos.mp q.property.1)]; exact q.property.2) (neg_pos.mp q.property.1)]
  exact (hd (f q)).symm


theorem contMDiffOn_doubleNegative_seam_transition
    (d : Diffeomorph (J.prod 𝓘(ℝ, ℝ)) I (doublePositiveStrip B (a := a)) (doublePositiveBand r (a := a)) ∞)
    (hd : ∀ q, (d q).val = c (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.le⟩)) :
    ContMDiffOn I (J.prod 𝓘(ℝ, ℝ)) ∞
      ((doubleNegativePatch B r hr hn).trans
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm)
      ((doubleNegativePatch B r hr hn).trans
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm).source := by
  rw [source_doubleNegative_seam_transition]
  apply Poincare.Manifold.contMDiffOn_of_contMDiff_open_restrict (doublePositiveBand r (a := a))
  have hfirst := contMDiff_fst.comp (contMDiff_subtype_val.comp d.symm.contMDiff)
  have hneg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => -t) := contDiff_neg.contMDiff
  have hsecond := hneg.comp (contMDiff_snd.comp (contMDiff_subtype_val.comp d.symm.contMDiff))
  apply (hfirst.prodMk hsecond).congr
  intro x
  let q := d.symm x
  let p : B × ℝ := (q.val.1, -q.val.2)
  let s := doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b
  have hp : |p.2| < a := by
    change |-q.val.2| < a
    rw [abs_neg, abs_of_pos q.property.1]
    exact q.property.2
  have heq : s p = doubleNegative B x.val := by
    rw [doubleSeamPatch_of_neg B r hr hz hn c hheight hsmall hc ha b hp (neg_neg_of_pos q.property.1)]
    have hpair : (p.1, (⟨-p.2, (neg_pos.mpr (neg_neg_of_pos q.property.1)).le,
        (neg_le_abs p.2).trans hp.le⟩ : Icc (0 : ℝ) a)) =
        (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.le⟩) := by
      exact Prod.ext rfl (Subtype.ext (neg_neg q.val.2))
    rw [hpair, ← hd q]
    exact congrArg (fun y => doubleNegative B y.val) (d.apply_symm_apply x)
  change s.symm (doubleNegative B x.val) = p
  rw [← heq]
  apply s.left_inv
  rw [doubleSeamPatch_source]
  exact hp

end Poincare.Topology
