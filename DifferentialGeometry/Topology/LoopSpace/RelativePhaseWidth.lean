import DifferentialGeometry.Topology.LoopSpace.CircleMetric
import DifferentialGeometry.Analysis.Calculus.Interpolation.RadialLipschitzPasting

noncomputable section

open Set Metric
open DifferentialGeometry.Topology
open scoped NNReal ENNReal

namespace DifferentialGeometry.Geometry

private theorem displacement_eq_zero_of_dist_lt
    {ρ : ℝ → ℝ} {δ : loopCircle → ℝ}
    (hδ : ∀ t : ℝ, δ (t : loopCircle) = ρ t - t)
    {s ε : ℝ} (hlocal : ∀ t : ℝ, |t - s| < ε → ρ t = t)
    {θ : loopCircle} (hθ : dist θ (s : loopCircle) < ε) : δ θ = 0 := by
  obtain ⟨d, hd, hn⟩ := loopCircle_exists_minimal_lift (θ - (s : loopCircle))
  have hsd : ((s + d : ℝ) : loopCircle) = θ := by
    rw [AddCircle.coe_add, hd]
    abel
  have habs : |s + d - s| < ε := by
    simpa only [add_sub_cancel_left, hn, ← dist_eq_norm] using hθ
  rw [← hsd, hδ, hlocal (s + d) habs, sub_self]

/-- A Lipschitz radial width suffices: no differentiability at the origin is
used by the bi-Lipschitz area change of variables. -/
theorem exists_relative_phase_radius
    {ρ : ℝ → ℝ} {δ : loopCircle → ℝ}
    (hδ : ∀ t : ℝ, δ (t : loopCircle) = ρ t - t)
    {s ε : ℝ} (hε : 0 < ε)
    (hlocal : ∀ t : ℝ, |t - s| < ε → ρ t = t) :
    ∃ R : loopCircle → ℝ, (∃ K : ℝ≥0, LipschitzWith K R) ∧
      (∀ θ, 1 / 2 ≤ R θ ∧ R θ ≤ 1) ∧
      (∀ θ, 2 * (1 - R θ) * δ θ = δ θ) ∧
      (∀ t : ℝ, |t - s| < ε / 4 → R (t : loopCircle) = 1) := by
  let K : ℝ≥0 := ⟨4 / ε, by positivity⟩
  let f : loopCircle → ℝ := fun θ => (4 / ε) * dist θ (s : loopCircle) - 1
  have hf : LipschitzWith K f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (f x) (f y) ≤ (4 / ε) * dist x y
    have hd := abs_dist_sub_le x y (s : loopCircle)
    have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ 4 / ε by positivity)
    simpa only [f, Real.dist_eq, sub_sub_sub_cancel_right, ← mul_sub,
      abs_mul, abs_of_nonneg (show 0 ≤ 4 / ε by positivity), K, NNReal.coe_mk] using hh
  let c : loopCircle → ℝ := fun θ => max 0 (min (f θ) 1)
  have hc : LipschitzWith K c := (hf.min_const 1).const_max 0
  have hc0 (θ : loopCircle) : 0 ≤ c θ := le_max_left _ _
  have hc1 (θ : loopCircle) : c θ ≤ 1 := max_le (by norm_num) (min_le_right _ _)
  let R : loopCircle → ℝ := fun θ => 1 - (1 / 2 : ℝ) * c θ
  have hR : LipschitzWith K R := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have he : dist (R x) (R y) = (1 / 2 : ℝ) * dist (c x) (c y) := by
      rw [Real.dist_eq, Real.dist_eq]
      dsimp only [R]
      rw [sub_sub_sub_cancel_left, ← mul_sub, abs_mul]
      norm_num
      rw [abs_sub_comm]
    rw [he]
    exact (mul_le_of_le_one_left dist_nonneg (by norm_num)).trans (hc.dist_le_mul x y)
  refine ⟨R, ⟨K, hR⟩, ?_, ?_, ?_⟩
  · intro θ
    dsimp only [R]
    constructor <;> linarith [hc0 θ, hc1 θ]
  · intro θ
    by_cases hd : δ θ = 0
    · simp [hd]
    · have heps : ε ≤ dist θ (s : loopCircle) := le_of_not_gt (fun h =>
        hd (displacement_eq_zero_of_dist_lt hδ hlocal h))
      have hfone : 1 ≤ f θ := by
        dsimp only [f]
        have hmul : 4 ≤ (4 / ε) * dist θ (s : loopCircle) := by
          calc
            4 = (4 / ε) * ε := by field_simp
            _ ≤ _ := mul_le_mul_of_nonneg_left heps (by positivity)
        linarith
      have hcθ : c θ = 1 := by simp only [c, min_eq_right hfone]; norm_num
      simp only [R, hcθ]
      ring
  · intro t ht
    have hd0 : dist (t : loopCircle) (s : loopCircle) ≤ |t - s| := by
      simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using
        loopCircle_projection_lipschitz.dist_le_mul t s
    have hd : dist (t : loopCircle) (s : loopCircle) < ε / 4 := hd0.trans_lt ht
    have hfneg : f (t : loopCircle) ≤ 0 := by
      dsimp only [f]
      have hm := mul_lt_mul_of_pos_left hd (show 0 < 4 / ε by positivity)
      have he : (4 / ε) * (ε / 4) = 1 := by field_simp
      rw [he] at hm
      linarith
    have hcθ : c (t : loopCircle) = 0 := by
      dsimp only [c]
      exact max_eq_left ((min_le_left _ _).trans hfneg)
    simp [R, hcθ]

end DifferentialGeometry.Geometry

namespace DifferentialGeometry.Analysis

/-- Pasting across a continuous scalar level preserves a common Lipschitz
constant on a convex source. The level set need not be a round circle. -/
theorem lipschitzOnWith_of_scalar_pieces
    {V Q : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [PseudoEMetricSpace Q]
    {f : V → Q} {S : Set V} {a : V → ℝ} {r : ℝ} {K : ℝ≥0}
    (hS : Convex ℝ S) (ha : Continuous a)
    (hin : LipschitzOnWith K f (S ∩ {z | a z ≤ r}))
    (hout : LipschitzOnWith K f (S ∩ {z | r ≤ a z})) :
    LipschitzOnWith K f S := by
  have hcross (x : V) (hxS : x ∈ S) (hx : a x ≤ r)
      (y : V) (hyS : y ∈ S) (hy : r ≤ a y) :
      edist (f x) (f y) ≤ (K : ℝ≥0∞) * edist x y := by
    let b : ℝ → ℝ := fun t => a (AffineMap.lineMap x y t)
    have hb : Continuous b := ha.comp AffineMap.lineMap_continuous
    have hr : r ∈ Icc (b 0) (b 1) := by simpa [b] using And.intro hx hy
    obtain ⟨t, ht, htr⟩ := intermediate_value_Icc (zero_le_one : (0 : ℝ) ≤ 1)
      hb.continuousOn hr
    let z := AffineMap.lineMap x y t
    have hz : z ∈ segment ℝ x y := lineMap_mem_segment ℝ x y ht
    have hzr : a z = r := htr
    have hzS := hS.segment_subset hxS hyS hz
    calc
      _ ≤ edist (f x) (f z) + edist (f z) (f y) := edist_triangle _ _ _
      _ ≤ (K : ℝ≥0∞) * edist x z + (K : ℝ≥0∞) * edist z y := add_le_add
        (hin ⟨hxS, hx⟩ ⟨hzS, hzr.le⟩) (hout ⟨hzS, hzr.ge⟩ ⟨hyS, hy⟩)
      _ = _ := by rw [← mul_add, edist_add_edist_of_mem_segment hz]
  intro x hx y hy
  by_cases hxr : a x ≤ r
  · by_cases hyr : a y ≤ r
    · exact hin ⟨hx, hxr⟩ ⟨hy, hyr⟩
    · exact hcross x hx hxr y hy (le_of_not_ge hyr)
  · by_cases hyr : a y ≤ r
    · simpa only [edist_comm] using hcross y hy hyr x hx (le_of_not_ge hxr)
    · exact hout ⟨hx, le_of_not_ge hxr⟩ ⟨hy, le_of_not_ge hyr⟩

end DifferentialGeometry.Analysis
