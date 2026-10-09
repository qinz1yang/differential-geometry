import DifferentialGeometry.Topology.MetricSpace.HopfRinow
import DifferentialGeometry.Topology.MetricSpace.CompactMinimizingCurve

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Metric

variable {X : Type*} [MetricSpace X]

private theorem complete_closed_subset {S T : Set X} (hS : IsComplete S)
    (hT : IsClosed T) (hTS : T ⊆ S) : IsComplete T := by
  intro f hf hfT
  obtain ⟨x, _, hx⟩ := hS f hf (hfT.trans (Filter.principal_mono.mpr hTS))
  exact ⟨x, isClosed_iff_clusterPt.mp hT x (hf.1.mono (le_inf hx hfT)), hx⟩

theorem isComplete_closedBall_of_add_dist_le {o p : X} {L r : ℝ}
    (hcomplete : IsComplete (closedBall o L)) (hbuffer : dist p o + r ≤ L) :
    IsComplete (closedBall p r) := by
  apply complete_closed_subset hcomplete isClosed_closedBall
  intro x hx
  exact (dist_triangle x p o).trans (by linarith [mem_closedBall.mp hx])

private theorem compact_nhds_of_locallyCompact_open {U : Set X}
    [LocallyCompactSpace U] (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    ∃ V : Set X, IsCompact V ∧ V ∈ 𝓝 x := by
  obtain ⟨V, hV, hVn⟩ := exists_compact_mem_nhds (⟨x, hx⟩ : U)
  exact ⟨Subtype.val '' V, hV.image continuous_subtype_val,
    hU.isOpenMap_subtype_val.image_mem_nhds hVn⟩

private theorem compact_neighborhood_of_locallyCompact_open {U K : Set X}
    [LocallyCompactSpace U] (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ V : Set X, IsCompact V ∧ K ⊆ interior V := by
  classical
  have hpoint (x : X) (hx : x ∈ K) :=
    compact_nhds_of_locallyCompact_open hU (hKU hx)
  choose! V hVc hVn using hpoint
  obtain ⟨s, hsK, hs⟩ := hK.elim_nhds_subcover_nhdsSet hVn
  exact ⟨⋃ x ∈ s, V x, s.isCompact_biUnion (fun x hx => hVc x (hsK x hx)),
    subset_interior_iff_mem_nhdsSet.mpr hs⟩

private theorem enlarge_compact_ball_in_open_ball
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {L r : ℝ} [LocallyCompactSpace (ball p L)]
    (hr : 0 ≤ r) (hrL : r < L) (hcompact : IsCompact (closedBall p r)) :
    ∃ δ : ℝ, 0 < δ ∧ r + δ < L ∧ IsCompact (closedBall p (r + δ)) := by
  obtain ⟨V, hV, hKV⟩ := compact_neighborhood_of_locallyCompact_open
    isOpen_ball hcompact (closedBall_subset_ball hrL)
  obtain ⟨η, hη, hthick⟩ := hcompact.exists_cthickening_subset_open isOpen_interior hKV
  let δ := min (η / 3) ((L - r) / 2)
  have hδ : 0 < δ := lt_min (by positivity) (by linarith)
  have hδη : δ ≤ η / 3 := min_le_left _ _
  have hδL : δ ≤ (L - r) / 2 := min_le_right _ _
  refine ⟨δ, hδ, by linarith, hV.of_isClosed_subset isClosed_closedBall ?_⟩
  intro y hy
  obtain ⟨z, hz, hyz⟩ := exists_radial_trimming_of_arbitrarily_short_curves
    hcurves p y hr hδ.le (by positivity : 0 < η / 3) hy
  apply interior_subset (hthick (thickening_subset_cthickening η (closedBall p r) ?_))
  exact mem_thickening_iff.mpr ⟨z, hz, by linarith⟩

theorem isCompact_closedBall_of_complete_buffer
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {L : ℝ} (hL : 0 < L) [LocallyCompactSpace (ball p L)]
    (hcomplete : IsComplete (closedBall p L)) {r : ℝ} (hrL : r < L) :
    IsCompact (closedBall p r) := by
  obtain ⟨V, hV, hVn⟩ := compact_nhds_of_locallyCompact_open isOpen_ball
    (mem_ball_self hL : p ∈ ball p L)
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hVn
  let r₀ := min (ε / 2) (L / 2)
  have hr₀ : 0 < r₀ := lt_min (by positivity) (by positivity)
  have hr₀L : r₀ < L := (min_le_right _ _).trans_lt (by linarith)
  have hcompact₀ : IsCompact (closedBall p r₀) :=
    hV.of_isClosed_subset isClosed_closedBall
      ((closedBall_subset_ball ((min_le_left _ _).trans_lt (by linarith))).trans hεV)
  let S : Set ℝ := {s | 0 < s ∧ s < L ∧ IsCompact (closedBall p s)}
  have hS : S.Nonempty := ⟨r₀, hr₀, hr₀L, hcompact₀⟩
  have hbounded : BddAbove S := ⟨L, fun s hs => hs.2.1.le⟩
  have hsup : 0 < sSup S := hr₀.trans_le (le_csSup hbounded ⟨hr₀, hr₀L, hcompact₀⟩)
  have hLsup : L ≤ sSup S := by
    by_contra h
    have hsupL : sSup S < L := lt_of_not_ge h
    have hcompact : IsCompact (closedBall p (sSup S)) := by
      apply isCompact_iff_totallyBounded_isComplete.mpr
      refine ⟨?_, complete_closed_subset hcomplete isClosed_closedBall
        (closedBall_subset_closedBall hsupL.le)⟩
      rw [totallyBounded_iff]
      intro ε hε
      obtain ⟨s, hs, hnear⟩ := exists_lt_of_lt_csSup hS
        (by linarith : sSup S - ε / 4 < sSup S)
      have hssup : s ≤ sSup S := le_csSup hbounded hs
      obtain ⟨T, hTfinite, hTcover⟩ := totallyBounded_iff.mp hs.2.2.totallyBounded
        (ε / 2) (half_pos hε)
      refine ⟨T, hTfinite, fun y hy => ?_⟩
      obtain ⟨z, hz, hyz⟩ := exists_radial_trimming_of_arbitrarily_short_curves
        hcurves p y hs.1.le (sub_nonneg.mpr hssup) (by positivity : 0 < ε / 4)
        (by simpa only [add_sub_cancel] using (show dist y p ≤ sSup S from hy))
      obtain ⟨w, hwT, hzw⟩ := mem_iUnion₂.mp (hTcover hz)
      refine mem_iUnion₂.mpr ⟨w, hwT, ?_⟩
      change dist y w < ε
      change dist z w < ε / 2 at hzw
      linarith [dist_triangle y z w]
    obtain ⟨δ, hδ, hlargeL, hlarge⟩ :=
      enlarge_compact_ball_in_open_ball hcurves p hsup.le hsupL hcompact
    have hle := le_csSup hbounded
      (show sSup S + δ ∈ S from ⟨by linarith, hlargeL, hlarge⟩)
    linarith
  obtain ⟨s, hs, hrs⟩ := exists_lt_of_lt_csSup hS (hrL.trans_le hLsup)
  exact hs.2.2.of_isClosed_subset isClosed_closedBall (closedBall_subset_closedBall hrs.le)

theorem isCompact_closedBall_of_locallyCompact_ball [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {L : ℝ} (hL : 0 < L) [LocallyCompactSpace (ball p L)]
    {r : ℝ} (hrL : r < L) : IsCompact (closedBall p r) :=
  isCompact_closedBall_of_complete_buffer hcurves p hL isClosed_closedBall.isComplete hrL

private theorem curve_dist_center_bound {a b p : X} {ε : ℝ} (hε : 0 < ε)
    (c : unitInterval → X) (ha : c 0 = a) (hb : c 1 = b)
    (hlen : eVariationOn c univ < ENNReal.ofReal (dist a b + ε)) (t : unitInterval) :
    2 * dist (c t) p < dist a p + dist b p + dist a b + ε := by
  have hbound := (edist_add_edist_le_eVariationOn c t).trans_lt hlen
  rw [ha, hb, edist_dist, edist_dist,
    ← ENNReal.ofReal_add dist_nonneg dist_nonneg] at hbound
  have hreal := (ENNReal.ofReal_lt_ofReal_iff
    (add_pos_of_nonneg_of_pos dist_nonneg hε)).mp hbound
  have h₁ := dist_triangle (c t) a p
  have h₂ := dist_triangle (c t) b p
  rw [dist_comm (c t) a] at h₁
  linarith

theorem dist_center_le_of_metric_segment {a b p : X} (f : unitInterval → X)
    (hf0 : f 0 = a) (hf1 : f 1 = b)
    (hf : ∀ s t, dist (f s) (f t) = dist a b * dist s t) (t : unitInterval) :
    dist (f t) p ≤ (dist a p + dist b p + dist a b) / 2 := by
  have h₁ := hf 0 t
  have h₂ := hf t 1
  rw [hf0] at h₁
  rw [hf1] at h₂
  change dist a (f t) = dist a b * |0 - (t : ℝ)| at h₁
  change dist (f t) b = dist a b * |(t : ℝ) - 1| at h₂
  rw [zero_sub, abs_neg, abs_of_nonneg t.property.1] at h₁
  rw [abs_of_nonpos (sub_nonpos.mpr t.property.2)] at h₂
  have h₃ := dist_triangle (f t) a p
  have h₄ := dist_triangle (f t) b p
  rw [dist_comm (f t) a] at h₃
  nlinarith

theorem exists_metric_segment_in_closedBall_of_complete_buffer
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {L r : ℝ} [LocallyCompactSpace (ball p L)]
    (hcomplete : IsComplete (closedBall p L)) (hrL : 2 * r < L)
    {a b : X} (ha : a ∈ closedBall p r) (hb : b ∈ closedBall p r) :
    ∃ f : unitInterval → X, Continuous f ∧ f 0 = a ∧ f 1 = b ∧
      (∀ t, f t ∈ closedBall p (2 * r)) ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  have ha' : dist a p ≤ r := ha
  have hb' : dist b p ≤ r := hb
  have hr : 0 ≤ r := dist_nonneg.trans ha'
  have hL : 0 < L := by linarith
  have hab : dist a b ≤ 2 * r := by
    have h := dist_triangle a p b
    rw [dist_comm p b] at h
    linarith
  let R := (2 * r + L) / 2
  have hR : 2 * r < R := by dsimp [R]; linarith
  have hRL : R < L := by dsimp [R]; linarith
  have hK := isCompact_closedBall_of_complete_buffer hcurves p hL hcomplete hRL
  have hshort : ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        (∀ t, c t ∈ closedBall p R) ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε) := by
    intro ε hε
    let η := min ε (R - 2 * r)
    have hη : 0 < η := lt_min hε (by linarith)
    obtain ⟨c, hc, hc0, hc1, hlen⟩ := hcurves a b η hη
    refine ⟨c, hc, hc0, hc1, ?_, hlen.trans_le ?_⟩
    · intro t
      have hbound := curve_dist_center_bound (p := p) hη c hc0 hc1 hlen t
      have hηR : η ≤ R - 2 * r := min_le_right _ _
      change dist (c t) p ≤ R
      linarith
    · apply ENNReal.ofReal_le_ofReal
      have hηε : η ≤ ε := min_le_left _ _
      linarith
  obtain ⟨f, hf, hf0, hf1, _, hdist⟩ :=
    exists_metric_segment_of_compact_arbitrarily_short_curves hK hshort
  refine ⟨f, hf, hf0, hf1, ?_, hdist⟩
  intro t
  have hbound := dist_center_le_of_metric_segment (p := p) f hf0 hf1 hdist t
  change dist (f t) p ≤ 2 * r
  linarith

theorem exists_metric_segment_in_closedBall_of_locallyCompact_ball [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {L r : ℝ} [LocallyCompactSpace (ball p L)] (hrL : 2 * r < L)
    {a b : X} (ha : a ∈ closedBall p r) (hb : b ∈ closedBall p r) :
    ∃ f : unitInterval → X, Continuous f ∧ f 0 = a ∧ f 1 = b ∧
      (∀ t, f t ∈ closedBall p (2 * r)) ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t :=
  exists_metric_segment_in_closedBall_of_complete_buffer hcurves p
    isClosed_closedBall.isComplete hrL ha hb

theorem exists_metric_segment_in_ball_of_complete_buffer [LocallyCompactSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {r : ℝ} (hr : 0 < r) (hcomplete : IsComplete (closedBall p (3 * r)))
    {a b : X} (ha : a ∈ ball p r) (hb : b ∈ ball p r) :
    ∃ f : unitInterval → X, Continuous f ∧ f 0 = a ∧ f 1 = b ∧
      (∀ t, f t ∈ ball p (2 * r)) ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  let : LocallyCompactSpace (ball p (3 * r)) := isOpen_ball.locallyCompactSpace
  obtain ⟨f, hf, hf0, hf1, _, hdist⟩ :=
    exists_metric_segment_in_closedBall_of_complete_buffer hcurves p hcomplete
      (by linarith) (mem_closedBall.mpr (mem_ball.mp ha).le)
      (mem_closedBall.mpr (mem_ball.mp hb).le)
  refine ⟨f, hf, hf0, hf1, ?_, hdist⟩
  intro t
  have hbound := dist_center_le_of_metric_segment (p := p) f hf0 hf1 hdist t
  have ha' : dist a p < r := ha
  have hb' : dist b p < r := hb
  have htri := dist_triangle a p b
  rw [dist_comm p b] at htri
  change dist (f t) p < 2 * r
  linarith

theorem exists_metric_segment_in_ball_of_recentered_complete_buffer [LocallyCompactSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    {o p : X} {L r : ℝ} (hr : 0 < r) (hcomplete : IsComplete (closedBall o L))
    (hbuffer : dist p o + 3 * r ≤ L)
    {a b : X} (ha : a ∈ ball p r) (hb : b ∈ ball p r) :
    ∃ f : unitInterval → X, Continuous f ∧ f 0 = a ∧ f 1 = b ∧
      (∀ t, f t ∈ ball p (2 * r)) ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t :=
  exists_metric_segment_in_ball_of_complete_buffer hcurves p hr
    (isComplete_closedBall_of_add_dist_le hcomplete hbuffer) ha hb

end Metric
