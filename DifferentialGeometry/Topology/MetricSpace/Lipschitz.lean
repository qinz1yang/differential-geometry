import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

open Set Filter
open scoped Topology

section

variable {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

theorem LocallyLipschitzOn.comp {f : Y → Z} {g : X → Y} {s : Set X} {t : Set Y}
    (hf : LocallyLipschitzOn t f) (hg : LocallyLipschitzOn s g) (hm : MapsTo g s t) :
    LocallyLipschitzOn s (f ∘ g) := by
  intro x hx
  obtain ⟨K, U, hU, hfU⟩ := hf (hm hx)
  obtain ⟨L, V, hV, hgV⟩ := hg hx
  refine ⟨K * L, V ∩ g ⁻¹' U, inter_mem hV ((hg.continuousOn x hx).tendsto_nhdsWithin hm hU), ?_⟩
  exact hfU.comp (hgV.mono inter_subset_left) (mapsTo_preimage g U |>.mono_left inter_subset_right)

theorem LocallyLipschitzOn.prodMk {f : X → Y} {g : X → Z} {s : Set X}
    (hf : LocallyLipschitzOn s f) (hg : LocallyLipschitzOn s g) :
    LocallyLipschitzOn s (fun x => (f x, g x)) :=
  locallyLipschitzOn_iff_restrict.mpr (hf.restrict.prodMk hg.restrict)

end

theorem locallyLipschitz_of_lipschitzOn_closedBall
    {X Y : Type*} [PseudoMetricSpace X] [PseudoEMetricSpace Y] {f : X → Y} (p : X)
    (hf : ∀ R : ℝ, 0 ≤ R → ∃ K, LipschitzOnWith K f (Metric.closedBall p R)) :
    LocallyLipschitz f := by
  intro x
  obtain ⟨K, hK⟩ := hf (dist x p + 1) (by positivity)
  exact ⟨K, Metric.closedBall p (dist x p + 1),
    Metric.closedBall_mem_nhds_of_mem (by linarith : dist x p < dist x p + 1), hK⟩

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y] [Zero Y]

open scoped NNReal in
open Metric in
theorem LocallyLipschitzOn.exists_lipschitzWith_of_hasCompactSupport
    {f : X → Y} {Ω : Set X} (hf : LocallyLipschitzOn Ω f)
    (hΩ : IsOpen Ω) (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Ω) :
    ∃ C : ℝ≥0, LipschitzWith C f := by
  classical
  have hlocal (x : tsupport f) : ∃ C : ℝ≥0, ∃ U : Set X,
      IsOpen U ∧ x.1 ∈ U ∧ LipschitzOnWith C f U := by
    obtain ⟨C, U, hU, hC⟩ := hf (hfs x.2)
    rw [hΩ.nhdsWithin_eq (hfs x.2)] at hU
    obtain ⟨W, hWU, hW, hxW⟩ := _root_.mem_nhds_iff.mp hU
    exact ⟨C, W, hW, hxW, hC.mono hWU⟩
  choose C U hU hxU hC using hlocal
  obtain ⟨s, hs⟩ := hfc.isCompact.elim_finite_subcover U hU
    (fun x hx => mem_iUnion_of_mem ⟨x, hx⟩ (hxU ⟨x, hx⟩))
  have hcover : tsupport f ⊆ ⋃ i : s, U i.1 := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion_of_mem ⟨i, hi⟩ hxi
  obtain ⟨δ, hδ, hδU⟩ := lebesgue_number_lemma_of_metric hfc.isCompact
    (fun i : s => hU i.1) hcover
  obtain ⟨B, hB⟩ := hfc.isCompact.bddAbove_image
    (continuous_dist.comp_continuousOn
      ((hf.continuousOn.mono hfs).prodMk continuousOn_const))
  let B' : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  let D : ℝ≥0 := ⟨2 * (B' : ℝ) / δ, div_nonneg (by positivity) hδ.le⟩
  let K := s.sup C
  have hbound (x : X) : dist (f x) 0 ≤ (B' : ℝ) := by
    by_cases hx : x ∈ tsupport f
    · exact (hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx, dist_self]
      exact B'.coe_nonneg
  have hone (x y : X) (hx : x ∈ tsupport f) :
      dist (f x) (f y) ≤ ((K + D : ℝ≥0) : ℝ) * dist x y := by
    by_cases hdist : dist x y < δ
    · obtain ⟨i, hi⟩ := hδU x hx
      have hnear := (hC i.1).dist_le_mul x (hi (mem_ball_self hδ))
        y (hi (by simpa only [mem_ball, dist_comm] using hdist))
      have hle : C i.1 ≤ K + D := (Finset.le_sup i.2).trans (le_add_of_nonneg_right (show 0 ≤ D from zero_le))
      exact hnear.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hle) dist_nonneg)
    · have hdist' : δ ≤ dist x y := le_of_not_gt hdist
      calc
        dist (f x) (f y) ≤ dist (f x) 0 + dist (f y) 0 := dist_triangle_right _ _ _
        _ ≤ 2 * (B' : ℝ) := by linarith [hbound x, hbound y]
        _ = (D : ℝ) * δ := by dsimp [D]; exact (div_mul_cancel₀ _ hδ.ne').symm
        _ ≤ (D : ℝ) * dist x y := mul_le_mul_of_nonneg_left hdist' D.coe_nonneg
        _ ≤ ((K + D : ℝ≥0) : ℝ) * dist x y :=
          mul_le_mul_of_nonneg_right (by simp) dist_nonneg
  refine ⟨K + D, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact hone x y hx
  · by_cases hy : y ∈ tsupport f
    · simpa only [dist_comm] using hone y x hy
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy, dist_self]
      positivity
