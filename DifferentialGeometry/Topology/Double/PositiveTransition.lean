import DifferentialGeometry.Topology.Double.InteriorPatches
import DifferentialGeometry.Topology.Double.SeamPatch
import DifferentialGeometry.Topology.Manifold.ContMDiff.DomainOpenSubtype
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.PositiveCoordinates

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


def doublePositiveStrip : Opens (B × ℝ) :=
  ⟨{q | 0 < q.2 ∧ q.2 < a},
    (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)⟩


def doublePositiveBand : Opens M :=
  ⟨{x | 0 < r x ∧ r x < a},
    (isOpen_lt continuous_const r.continuous).inter (isOpen_lt r.continuous continuous_const)⟩


theorem source_doubleSeam_positive_transition :
    ((doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).trans
      (doublePositivePatch B r hr hn).symm).source = {q | 0 < q.2 ∧ q.2 < a} := by
  ext q
  change (q ∈ (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).source ∧
    0 < doubleHeight B r hr (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q)) ↔ _
  rw [doubleSeamPatch_source]
  constructor
  · rintro ⟨hq, ht⟩
    rw [doubleHeight_seamPatch B r hr hz hn c hheight hsmall hc ha b hq] at ht
    exact ⟨ht, (le_abs_self q.2).trans_lt hq⟩
  · intro hq
    have hqa : |q.2| < a := by rw [abs_of_pos hq.1]; exact hq.2
    exact ⟨hqa, by rw [doubleHeight_seamPatch B r hr hz hn c hheight hsmall hc ha b hqa]; exact hq.1⟩


theorem source_doublePositive_seam_transition :
    ((doublePositivePatch B r hr hn).trans
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm).source =
        {x | 0 < r x ∧ r x < a} := by
  ext x
  change (0 < r x ∧ doublePositive B x ∈
    (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).target) ↔ _
  rw [doubleSeamPatch_target]
  change (0 < r x ∧ |r x| < a) ↔ _
  rw [abs_of_nonneg (hn x)]
  rfl


theorem contMDiffOn_doubleSeam_positive_transition
    (d : Diffeomorph (J.prod 𝓘(ℝ, ℝ)) I (doublePositiveStrip B (a := a)) (doublePositiveBand r (a := a)) ∞)
    (hd : ∀ q, (d q).val = c (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.le⟩)) :
    ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) I ∞
      ((doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).trans
        (doublePositivePatch B r hr hn).symm)
      ((doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).trans
        (doublePositivePatch B r hr hn).symm).source := by
  rw [source_doubleSeam_positive_transition]
  apply Poincare.Manifold.contMDiffOn_of_contMDiff_open_restrict (doublePositiveStrip B (a := a))
  apply (contMDiff_subtype_val.comp d.contMDiff).congr
  intro q
  change doubleFold B (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b q.val) = (d q).val
  rw [doubleSeamPatch_of_nonneg B r hr hz hn c hheight hsmall hc ha b
    (by rw [abs_of_pos q.property.1]; exact q.property.2) q.property.1.le]
  exact (hd q).symm


theorem contMDiffOn_doublePositive_seam_transition
    (d : Diffeomorph (J.prod 𝓘(ℝ, ℝ)) I (doublePositiveStrip B (a := a)) (doublePositiveBand r (a := a)) ∞)
    (hd : ∀ q, (d q).val = c (q.val.1, ⟨q.val.2, q.property.1.le, q.property.2.le⟩)) :
    ContMDiffOn I (J.prod 𝓘(ℝ, ℝ)) ∞
      ((doublePositivePatch B r hr hn).trans
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm)
      ((doublePositivePatch B r hr hn).trans
        (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b).symm).source := by
  rw [source_doublePositive_seam_transition]
  apply Poincare.Manifold.contMDiffOn_of_contMDiff_open_restrict (doublePositiveBand r (a := a))
  apply (contMDiff_subtype_val.comp d.symm.contMDiff).congr
  intro x
  let q := d.symm x
  let s := doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b
  have hq : |q.val.2| < a := by rw [abs_of_pos q.property.1]; exact q.property.2
  have heq : s q.val = doublePositive B x.val := by
    rw [doubleSeamPatch_of_nonneg B r hr hz hn c hheight hsmall hc ha b hq q.property.1.le]
    rw [← hd q]
    exact congrArg (fun y => doublePositive B y.val) (d.apply_symm_apply x)
  change s.symm (doublePositive B x.val) = q.val
  rw [← heq]
  apply s.left_inv
  rw [doubleSeamPatch_source]
  exact hq

end Poincare.Topology
