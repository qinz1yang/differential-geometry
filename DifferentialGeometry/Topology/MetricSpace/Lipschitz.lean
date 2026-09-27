import DifferentialGeometry.Topology.LocallyLipschitzOperations
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

open Set Filter
open scoped Topology

section

variable {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

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

open scoped ENNReal NNReal in
theorem lipschitzWith_truncateToReal_edist {X : Type*} [PseudoEMetricSpace X]
    (K : ℝ≥0) (R : ℝ≥0∞) (hR : R ≠ ⊤) (o : X) :
    LipschitzWith K (fun x => ENNReal.truncateToReal R ((K : ℝ≥0∞) * edist o x)) := by
  by_cases hK : K = 0
  · subst K
    simpa only [ENNReal.coe_zero, zero_mul] using
      (LipschitzWith.const (ENNReal.truncateToReal R 0) :
        LipschitzWith 0 (fun _ : X => ENNReal.truncateToReal R 0))
  intro x y
  by_cases hxy : edist x y = ⊤
  · rw [hxy, ENNReal.mul_top (by exact_mod_cast hK)]
    exact le_top
  have hfin (z : X) : min R ((K : ℝ≥0∞) * edist o z) ≠ ⊤ :=
    ne_top_of_le_ne_top hR (min_le_left _ _)
  have hstep (z w : X) (hzw : edist z w ≠ ⊤) :
      ENNReal.truncateToReal R ((K : ℝ≥0∞) * edist o z) ≤
        ENNReal.truncateToReal R ((K : ℝ≥0∞) * edist o w) + (K : ℝ) * (edist z w).toReal := by
    have hm : min R ((K : ℝ≥0∞) * edist o z) ≤
        min R ((K : ℝ≥0∞) * edist o w) + (K : ℝ≥0∞) * edist z w := by
      rcases le_total R ((K : ℝ≥0∞) * edist o w) with hw | hw
      · rw [min_eq_left hw]
        exact (min_le_left _ _).trans le_self_add
      · rw [min_eq_right hw]
        calc
          _ ≤ (K : ℝ≥0∞) * edist o z := min_le_right _ _
          _ ≤ (K : ℝ≥0∞) * (edist o w + edist w z) :=
            mul_le_mul_right (edist_triangle o w z) _
          _ = _ := by rw [mul_add, edist_comm w z]
    have hf : (K : ℝ≥0∞) * edist z w ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hzw
    have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin w, hf⟩) hm
    rwa [ENNReal.toReal_add (hfin w) hf, ENNReal.toReal_mul, ENNReal.coe_toReal] at ht
  have hreal : dist (ENNReal.truncateToReal R ((K : ℝ≥0∞) * edist o x))
      (ENNReal.truncateToReal R ((K : ℝ≥0∞) * edist o y)) ≤ (K : ℝ) * (edist x y).toReal := by
    rw [Real.dist_eq, abs_sub_le_iff]
    have h₁ := hstep x y hxy
    have h₂ := hstep y x (by rwa [edist_comm])
    rw [edist_comm y x] at h₂
    constructor <;> linarith
  rw [edist_dist]
  have hr := ENNReal.ofReal_le_ofReal hreal
  rwa [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_toReal hxy] at hr
