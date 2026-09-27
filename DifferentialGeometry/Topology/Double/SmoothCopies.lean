import DifferentialGeometry.Topology.Double.SeamPatch
import DifferentialGeometry.Topology.Manifold.ContMDiff.DomainOpenSubtype
import Mathlib.Geometry.Manifold.Instances.Icc

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology TopologicalSpace
open scoped ContDiff Topology
namespace DifferentialGeometry.Topology

theorem contMDiff_double_copies_of_collar
    {M E H F G : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H)
    (B : Set M) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] [ChartedSpace G B] (J : ModelWithCorners ℝ F G)
    [ChartedSpace E (Double B)]
    (r : C(M, ℝ)) (hr : ∀ b : B, r b.val = 0)
    (hz : ∀ x, r x = 0 → x ∈ B) (hn : ∀ x, 0 ≤ r x)
    {a : ℝ} [Fact ((0 : ℝ) < a)]
    (c : C(B × Icc (0 : ℝ) a, M)) (hheight : ∀ q, r (c q) = q.2.val)
    (hsmall : ∀ x, r x ≤ a → x ∈ range c) (hc : IsEmbedding c) (ha : 0 < a)
    (Y : Opens M) (hY : (Y : Set M) = {x | r x < a})
    (d : Diffeomorph (J.prod (𝓡∂ 1)) I
      (⟨{q : B × Icc (0 : ℝ) a | q.2.val < a},
        isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩ :
          Opens (B × Icc (0 : ℝ) a)) Y ∞)
    (hd : ∀ q, (d q).val = c q.val)
    (hp : ContMDiffOn I 𝓘(ℝ, E) ∞ (doublePositive B) {x | 0 < r x})
    (hm : ContMDiffOn I 𝓘(ℝ, E) ∞ (doubleNegative B) {x | 0 < r x})
    (hs : ∀ b : B, ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b) {q | |q.2| < a}) :
    ContMDiff I 𝓘(ℝ, E) ∞ (doublePositive B) ∧
      ContMDiff I 𝓘(ℝ, E) ∞ (doubleNegative B) := by
  let g : Y → B × ℝ := fun y => ((d.symm y).val.1, (d.symm y).val.2.val)
  have hg : ContMDiff I (J.prod 𝓘(ℝ, ℝ)) ∞ g :=
    (contMDiff_fst.comp (contMDiff_subtype_val.comp d.symm.contMDiff)).prodMk
      (contMDiff_subtypeVal_Icc.comp (contMDiff_snd.comp
        (contMDiff_subtype_val.comp d.symm.contMDiff)))
  have hgpos (y : Y) : 0 ≤ (g y).2 := (d.symm y).val.2.property.1
  have hgsmall (y : Y) : |(g y).2| < a := by
    rw [abs_of_nonneg (hgpos y)]
    exact (d.symm y).property
  have hcg (y : Y) : c ((g y).1, ⟨(g y).2, hgpos y, (le_abs_self _).trans (hgsmall y).le⟩) = y.val := by
    change c (d.symm y).val = y.val
    rw [← hd, d.apply_symm_apply]
  have hplus : ContMDiffOn I 𝓘(ℝ, E) ∞ (doublePositive B) Y := by
    apply DifferentialGeometry.Manifold.contMDiffOn_of_contMDiff_open_restrict Y
    intro y
    let b := (g y).1
    have hcomp : ContMDiff I 𝓘(ℝ, E) ∞
        (fun z : Y => doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b (g z)) :=
      contMDiffOn_univ.mp ((hs b).comp hg.contMDiffOn (fun z _ => hgsmall z))
    have heq (z : Y) : doublePositive B z.val =
        doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b (g z) := by
      rw [doubleSeamPatch_of_nonneg B r hr hz hn c hheight hsmall hc ha b (hgsmall z) (hgpos z), hcg]
    exact (hcomp.congr heq).contMDiffAt
  let g' : Y → B × ℝ := fun y => ((g y).1, -(g y).2)
  have hneg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => -t) := contDiff_neg.contMDiff
  have hg' : ContMDiff I (J.prod 𝓘(ℝ, ℝ)) ∞ g' :=
    (contMDiff_fst.comp hg).prodMk (hneg.comp (contMDiff_snd.comp hg))
  have hg'small (y : Y) : |(g' y).2| < a := by simpa only [g', abs_neg] using hgsmall y
  have hminus : ContMDiffOn I 𝓘(ℝ, E) ∞ (doubleNegative B) Y := by
    apply DifferentialGeometry.Manifold.contMDiffOn_of_contMDiff_open_restrict Y
    intro y
    let b := (g y).1
    have hcomp : ContMDiff I 𝓘(ℝ, E) ∞
        (fun z : Y => doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b (g' z)) :=
      contMDiffOn_univ.mp ((hs b).comp hg'.contMDiffOn (fun z _ => hg'small z))
    have heq (z : Y) : doubleNegative B z.val =
        doubleSeamPatch B r hr hz hn c hheight hsmall hc ha b (g' z) := by
      rw [doubleSeamPatch_of_nonpos B r hr hz hn c hheight hsmall hc ha b (hg'small z)
        (neg_nonpos.mpr (hgpos z))]
      apply congrArg (doubleNegative B)
      have hpair : ((g' z).1, (⟨-(g' z).2, neg_nonneg.mpr (neg_nonpos.mpr (hgpos z)),
          (neg_le_abs (g' z).2).trans (hg'small z).le⟩ : Icc (0 : ℝ) a)) =
          ((g z).1, ⟨(g z).2, hgpos z, (le_abs_self _).trans (hgsmall z).le⟩) := by
        have ht : -(g' z).2 = (g z).2 := neg_neg _
        exact Prod.ext rfl (Subtype.ext ht)
      rw [hpair, hcg]
    exact (hcomp.congr heq).contMDiffAt
  constructor <;> intro x
  · by_cases hx : 0 < r x
    · exact hp.contMDiffAt ((isOpen_lt continuous_const r.continuous).mem_nhds hx)
    · have hxY : x ∈ Y := by
        change x ∈ (Y : Set M)
        rw [hY]
        exact (le_of_not_gt hx).trans_lt ha
      exact hplus.contMDiffAt (Y.isOpen.mem_nhds hxY)
  · by_cases hx : 0 < r x
    · exact hm.contMDiffAt ((isOpen_lt continuous_const r.continuous).mem_nhds hx)
    · have hxY : x ∈ Y := by
        change x ∈ (Y : Set M)
        rw [hY]
        exact (le_of_not_gt hx).trans_lt ha
      exact hminus.contMDiffAt (Y.isOpen.mem_nhds hxY)

end DifferentialGeometry.Topology
