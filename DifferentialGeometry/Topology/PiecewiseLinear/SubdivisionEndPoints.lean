/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DualCells
import DifferentialGeometry.Topology.SimplicialComplex.EdgeGraph

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem exists_pair_mem_faces_of_forall_add_smul_mem_space
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hdim : ∀ s ∈ L.faces, s.card ≤ 2)
    {v d : E} (hv : {v} ∈ L.faces) (hd : d ≠ 0) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hray : ∀ t ∈ Ioc 0 t₀, v + t • d ∈ L.space) :
    ∃ x t, x ≠ v ∧ ({v, x} : Finset E) ∈ L.faces ∧ 0 < t ∧ t ≤ t₀ ∧
      v + t • d ∈ convexHull ℝ (({v, x} : Finset E) : Set E) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp (closedStar_mem_nhdsWithin L v)
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have htpos : 0 < min t₀ (r / (2 * ‖d‖)) := lt_min ht₀ (by positivity)
  have htle : min t₀ (r / (2 * ‖d‖)) ≤ t₀ := min_le_left _ _
  have hdist : v + min t₀ (r / (2 * ‖d‖)) • d ∈ Metric.ball v r := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg htpos.le]
    calc min t₀ (r / (2 * ‖d‖)) * ‖d‖ ≤ r / (2 * ‖d‖) * ‖d‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hdpos.le
      _ = r / 2 := by rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hdpos.ne']
      _ < r := half_lt_self hr
  obtain ⟨σ, ⟨hσ, hvσ⟩, hpσ⟩ := mem_iUnion₂.mp (hball ⟨hdist, hray _ ⟨htpos, htle⟩⟩)
  have hvσ' : v ∈ σ := mem_of_mem_convexHull_of_singleton_mem L hv hσ hvσ
  have hσne : ∃ x ∈ σ, x ≠ v := by
    by_contra hcon
    have hσv : σ = {v} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hvσ', fun y hy => by_contra fun hyv => hcon ⟨y, hy, hyv⟩⟩
    rw [hσv, Finset.coe_singleton, convexHull_singleton, mem_singleton_iff,
      add_eq_left] at hpσ
    rcases smul_eq_zero.mp hpσ with h | h
    · exact htpos.ne' h
    · exact hd h
  obtain ⟨x, hxσ, hxv⟩ := hσne
  have hσeq : ({v, x} : Finset E) = σ := Finset.eq_of_subset_of_card_le
    (Finset.insert_subset_iff.mpr ⟨hvσ', Finset.singleton_subset_iff.mpr hxσ⟩)
    (by rw [Finset.card_pair (Ne.symm hxv)]; exact hdim σ hσ)
  refine ⟨x, _, hxv, hσeq ▸ hσ, htpos, htle, ?_⟩
  rw [hσeq]
  exact hpσ

open Classical in
theorem IsSubdivision.edgeGraph_neighborSet_ncard_ne_one {L L' : Geometry.SimplicialComplex ℝ E}
    [Finite L'.faces] (h : IsSubdivision L' L)
    (hdim : ∀ s ∈ L.faces, s.card ≤ 2)
    (hend : ∀ v : L.vertices, ((SimplicialComplex.edgeGraph L).neighborSet v).ncard ≠ 1)
    (v : L'.vertices) : ((SimplicialComplex.edgeGraph L').neighborSet v).ncard ≠ 1 := by
  have hdim' : ∀ s ∈ L'.faces, s.card ≤ 2 := fun s hs => h.card_le hdim hs
  rw [SimplicialComplex.ncard_neighborSet_edgeGraph]
  intro h1
  obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp h1
  have hwS : w ∈ {w : E | w ≠ (v : E) ∧ {(v : E), w} ∈ L'.faces} := by
    rw [hw]
    exact mem_singleton w
  obtain ⟨hwv, hvw⟩ := hwS
  suffices hsecond : ∃ x, x ≠ (v : E) ∧ {(v : E), x} ∈ L'.faces ∧ x ≠ w by
    obtain ⟨x, hxv, hvx, hxw⟩ := hsecond
    have hx : x ∈ ({w} : Set E) := by
      rw [← hw]
      exact ⟨hxv, hvx⟩
    exact hxw hx
  obtain ⟨s, hs, hvws⟩ := h.exists_face_subset hvw
  have hvs : (v : E) ∈ convexHull ℝ (s : Set E) :=
    hvws (subset_convexHull ℝ _ (by simp))
  have hws : w ∈ convexHull ℝ (s : Set E) := hvws (subset_convexHull ℝ _ (by simp))
  have hs2 : s.card = 2 := by
    by_contra hne
    have hs1 : s.card = 1 := by
      have := Finset.card_pos.mpr (L.nonempty_of_mem_faces hs)
      have := hdim s hs
      omega
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs1
    rw [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] at hvs hws
    exact hwv (hws.trans hvs.symm)
  have hspace : ∀ y ∈ convexHull ℝ (s : Set E), y ∈ L'.space := fun y hy => by
    rw [h.space_eq]
    exact L.convexHull_subset_space hs hy
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs2
  by_cases hvab : (v : E) ∈ ({a, b} : Finset E)
  · obtain ⟨b', hb'v, hseq⟩ : ∃ b', b' ≠ (v : E) ∧ ({a, b} : Finset E) = {(v : E), b'} := by
      rcases Finset.mem_insert.mp hvab with hva | hvb
      · exact ⟨b, fun hb => hab (hva.symm.trans hb.symm), by rw [hva]⟩
      · refine ⟨a, fun ha => hab (ha.trans (Finset.mem_singleton.mp hvb)), ?_⟩
        rw [Finset.mem_singleton.mp hvb, Finset.pair_comm]
    rw [hseq] at hs hvws hspace
    have hvL : {(v : E)} ∈ L.faces :=
      L.down_closed hs (by simp) (Finset.singleton_nonempty _)
    have hdeg : {u : E | u ≠ (v : E) ∧ {(v : E), u} ∈ L.faces}.ncard ≠ 1 := by
      have hdeg₀ := hend ⟨(v : E), hvL⟩
      rwa [SimplicialComplex.ncard_neighborSet_edgeGraph] at hdeg₀
    have hb'mem : b' ∈ {u : E | u ≠ (v : E) ∧ {(v : E), u} ∈ L.faces} := ⟨hb'v, hs⟩
    obtain ⟨c, ⟨hcv, hvc⟩, hcb'⟩ :
        ∃ c ∈ {u : E | u ≠ (v : E) ∧ {(v : E), u} ∈ L.faces}, c ≠ b' := by
      by_contra hcon
      apply hdeg
      rw [Set.eq_singleton_iff_unique_mem.mpr ⟨hb'mem, fun c hc =>
        by_contra fun hcb => hcon ⟨c, hc, hcb⟩⟩, Set.ncard_singleton]
    have hray : ∀ t ∈ Ioc (0 : ℝ) 1, (v : E) + t • (c - v) ∈ L'.space := by
      intro t ht
      rw [h.space_eq]
      refine L.convexHull_subset_space hvc ?_
      rw [Finset.coe_pair, convexHull_pair]
      exact ⟨1 - t, t, by linarith [ht.2], ht.1.le, by ring, by module⟩
    obtain ⟨x, t, hxv, hvx, htpos, htle, hpx⟩ :=
      exists_pair_mem_faces_of_forall_add_smul_mem_space hdim' v.2 (sub_ne_zero.mpr hcv)
        one_pos hray
    refine ⟨x, hxv, hvx, fun hxw => ?_⟩
    rw [hxw] at hpx
    have hpc : (v : E) + t • (c - v) ∈ convexHull ℝ (({(v : E), c} : Finset E) : Set E) := by
      rw [Finset.coe_pair, convexHull_pair]
      exact ⟨1 - t, t, by linarith, htpos.le, by ring, by module⟩
    have hmeet := L.inter_subset_convexHull hs hvc ⟨hvws hpx, hpc⟩
    have hsub : ((({(v : E), b'} : Finset E) : Set E) ∩ (({(v : E), c} : Finset E) : Set E)) ⊆
        {(v : E)} := by
      rintro y ⟨hy1, hy2⟩
      simp only [Finset.coe_pair, mem_insert_iff, mem_singleton_iff] at hy1 hy2
      rcases hy1 with hy1 | hy1
      · exact hy1
      · rcases hy2 with hy2 | hy2
        · exact hy2
        · exact absurd (hy1.symm.trans hy2) (Ne.symm hcb')
    have hpv := convexHull_mono hsub hmeet
    rw [convexHull_singleton, mem_singleton_iff, add_eq_left] at hpv
    rcases smul_eq_zero.mp hpv with h0 | h0
    · exact htpos.ne' h0
    · exact hcv (sub_eq_zero.mp h0)
  · have hva : (v : E) ≠ a := fun h' => hvab (by rw [h']; exact Finset.mem_insert_self a {b})
    have hvb : (v : E) ≠ b := fun h' =>
      hvab (by rw [h']; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
    rw [Finset.coe_pair, convexHull_pair] at hvs hws
    obtain ⟨α, β, hα, hβ, hαβ, hvdef⟩ := hvs
    obtain ⟨γ, δ, hγ, hδ, hγδ, hwdef⟩ := hws
    have hαpos : 0 < α := by
      rcases hα.eq_or_lt with h0 | h0
      · exfalso
        apply hvb
        rw [← hvdef, ← h0, show β = 1 by linarith, zero_smul, zero_add, one_smul]
      · exact h0
    have hβpos : 0 < β := by
      rcases hβ.eq_or_lt with h0 | h0
      · exfalso
        apply hva
        rw [← hvdef, ← h0, show α = 1 by linarith, zero_smul, add_zero, one_smul]
      · exact h0
    have hray : ∀ t ∈ Ioc 0 (min α β), (v : E) + t • ((v : E) - w) ∈ L'.space := by
      intro t ht
      apply hspace
      rw [Finset.coe_pair, convexHull_pair]
      have htα : t ≤ α := ht.2.trans (min_le_left _ _)
      have htβ : t ≤ β := ht.2.trans (min_le_right _ _)
      have htγ : t * γ ≤ t := by
        have := mul_le_mul_of_nonneg_left (show γ ≤ 1 by linarith) ht.1.le
        linarith
      have htδ : t * δ ≤ t := by
        have := mul_le_mul_of_nonneg_left (show δ ≤ 1 by linarith) ht.1.le
        linarith
      refine ⟨α + t * (α - γ), β + t * (β - δ), by nlinarith [ht.1], by nlinarith [ht.1],
        by linear_combination (1 + t) * hαβ - t * hγδ, ?_⟩
      rw [← hvdef, ← hwdef]
      module
    obtain ⟨x, t, hxv, hvx, htpos, -, hpx⟩ :=
      exists_pair_mem_faces_of_forall_add_smul_mem_space hdim' v.2
        (sub_ne_zero.mpr (Ne.symm hwv)) (lt_min hαpos hβpos) hray
    refine ⟨x, hxv, hvx, fun hxw => ?_⟩
    rw [hxw, Finset.coe_pair, convexHull_pair] at hpx
    obtain ⟨μ, ν, hμ, hν, hμν, heq⟩ := hpx
    have hkey : (ν + t) • (w - (v : E)) = 0 := by
      have hμ' : μ = 1 - ν := by linarith
      rw [hμ'] at heq
      calc (ν + t) • (w - (v : E)) = ((1 - ν) • (v : E) + ν • w) - ((v : E) + t • ((v : E) - w)) :=
            by module
        _ = 0 := sub_eq_zero.mpr heq
    rcases smul_eq_zero.mp hkey with h0 | h0
    · linarith
    · exact hwv (sub_eq_zero.mp h0)

open Classical in
theorem IsSubdivision.exists_mem_faces_card_eq_two {L L' : Geometry.SimplicialComplex ℝ E}
    [Finite L'.faces] (h : IsSubdivision L' L) (hdim : ∀ s ∈ L.faces, s.card ≤ 2)
    (hedge : ∃ e ∈ L.faces, e.card = 2) : ∃ e ∈ L'.faces, e.card = 2 := by
  have hdim' : ∀ s ∈ L'.faces, s.card ≤ 2 := fun s hs => h.card_le hdim hs
  obtain ⟨e, he, he2⟩ := hedge
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he2
  have haL' : a ∈ L'.space := by
    rw [h.space_eq]
    exact L.convexHull_subset_space he (subset_convexHull ℝ _ (by simp))
  obtain ⟨σ, hσ, haσ⟩ := L'.mem_space_iff.mp haL'
  by_cases hσ2 : σ.card = 2
  · exact ⟨σ, hσ, hσ2⟩
  have hσ1 : σ.card = 1 := by
    have := Finset.card_pos.mpr (L'.nonempty_of_mem_faces hσ)
    have := hdim' σ hσ
    omega
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hσ1
  rw [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] at haσ
  rw [← haσ] at hσ
  have hray : ∀ t ∈ Ioc (0 : ℝ) 1, a + t • (b - a) ∈ L'.space := by
    intro t ht
    rw [h.space_eq]
    refine L.convexHull_subset_space he ?_
    rw [Finset.coe_pair, convexHull_pair]
    exact ⟨1 - t, t, by linarith [ht.2], ht.1.le, by ring, by module⟩
  obtain ⟨y, t, hya, hay, -⟩ := exists_pair_mem_faces_of_forall_add_smul_mem_space hdim' hσ
    (sub_ne_zero.mpr (Ne.symm hab)) one_pos hray
  exact ⟨{a, y}, hay, Finset.card_pair (Ne.symm hya)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
