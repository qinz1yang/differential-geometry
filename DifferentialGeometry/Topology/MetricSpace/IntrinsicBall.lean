import DifferentialGeometry.Topology.MetricSpace.IntrinsicEDist
import DifferentialGeometry.Topology.MetricSpace.VariationIsometry

set_option autoImplicit false

open Set Metric
open scoped ENNReal NNReal

namespace Metric

theorem intrinsicEDist_subtype_le_curve_variation
    {X : Type*} [MetricSpace X] {U : Set X} {a b : U} {c : unitInterval → X}
    (hc : Continuous c) (hc0 : c 0 = (a : X)) (hc1 : c 1 = (b : X))
    (hmem : ∀ t, c t ∈ U) : intrinsicEDist a b ≤ eVariationOn c univ := by
  let c' : unitInterval → U := fun t => ⟨c t, hmem t⟩
  have hc' : Continuous c' := hc.subtype_mk hmem
  have h0 : c' 0 = a := Subtype.ext hc0
  have h1 : c' 1 = b := Subtype.ext hc1
  have hvar : eVariationOn c' univ = eVariationOn c univ :=
    eVariationOn.eq_of_edist_eq (fun _ _ _ _ => rfl)
  exact (intrinsicEDist_le_curve_variation hc' h0 h1).trans_eq hvar

theorem intrinsicEDist_lt_top_on_ball_of_arbitrarily_short_curves
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {L : ℝ} (hL : 0 < L) (a b : ball o L) : intrinsicEDist a b < ⊤ := by
  let p : ball o L := ⟨o, by simpa only [mem_ball, dist_self] using hL⟩
  have hcenter (y : ball o L) : intrinsicEDist p y < ⊤ := by
    have hy : dist o (y : X) < L := by simpa only [mem_ball, dist_comm] using y.property
    let ε := (L - dist o (y : X)) / 2
    have hε : 0 < ε := by dsimp only [ε]; linarith
    obtain ⟨c, hc, hc0, hc1, hlen⟩ := hcurves o y ε hε
    have hlenL : eVariationOn c univ < ENNReal.ofReal L :=
      hlen.trans ((ENNReal.ofReal_lt_ofReal_iff hL).mpr (by dsimp only [ε]; linarith))
    have hmem (t : unitInterval) : c t ∈ ball o L := by
      have he := eVariationOn.edist_le c (mem_univ (0 : unitInterval)) (mem_univ t)
      rw [hc0, edist_dist] at he
      have hd := (ENNReal.ofReal_lt_ofReal_iff hL).mp (he.trans_lt hlenL)
      simpa only [mem_ball, dist_comm] using hd
    exact (intrinsicEDist_subtype_le_curve_variation (a := p) (b := y) hc hc0 hc1 hmem).trans_lt
      (hlenL.trans ENNReal.ofReal_lt_top)
  have hpa := hcenter a
  have hpb := hcenter b
  rw [intrinsicEDist_comm p a] at hpa
  exact (intrinsicEDist_triangle a p b).trans_lt (ENNReal.add_lt_top.mpr ⟨hpa, hpb⟩)

theorem intrinsicEDist_eq_edist_on_inner_closedBall
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    {o x : X} {L h : ℝ} (hh : 0 < h) (hmargin : dist x o + 4 * h < L)
    {a b : ball o L} (ha : (a : X) ∈ closedBall x h) (hb : (b : X) ∈ closedBall x h) :
    intrinsicEDist a b = edist (a : X) (b : X) := by
  apply le_antisymm _ (edist_le_intrinsicEDist a b)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hfin
  let η := min (ε : ℝ) (h / 2)
  have hη : 0 < η := lt_min hε (half_pos hh)
  obtain ⟨c, hc, hc0, hc1, hlen⟩ := hcurves a b η hη
  have ha' : dist (a : X) x ≤ h := ha
  have hb' : dist (b : X) x ≤ h := hb
  have hab : dist (a : X) (b : X) ≤ 2 * h := by
    have ht := dist_triangle (a : X) x (b : X)
    rw [dist_comm x (b : X)] at ht
    linarith
  have hmem (t : unitInterval) : c t ∈ ball o L := by
    have he := eVariationOn.edist_le c (mem_univ (0 : unitInterval)) (mem_univ t)
    rw [hc0, edist_dist] at he
    have hd := (ENNReal.ofReal_lt_ofReal_iff (add_pos_of_nonneg_of_pos dist_nonneg hη)).mp
      (he.trans_lt hlen)
    have hca := dist_triangle (c t) (a : X) x
    rw [dist_comm (c t) (a : X)] at hca
    have hco := dist_triangle (c t) x o
    have hηh : η ≤ h / 2 := min_le_right _ _
    change dist (c t) o < L
    linarith
  have hlen' : eVariationOn c univ ≤ ENNReal.ofReal (dist (a : X) (b : X) + (ε : ℝ)) :=
    hlen.le.trans (ENNReal.ofReal_le_ofReal (by
      have he : η ≤ (ε : ℝ) := min_le_left _ _
      linarith))
  have ht := (intrinsicEDist_subtype_le_curve_variation (a := a) (b := b) hc hc0 hc1 hmem).trans hlen'
  change intrinsicEDist a b ≤ edist (a : X) (b : X) + (ε : ℝ≥0∞)
  simpa only [ENNReal.ofReal_add dist_nonneg ε.coe_nonneg, ← edist_dist,
    ENNReal.ofReal_coe_nnreal] using ht

end Metric
