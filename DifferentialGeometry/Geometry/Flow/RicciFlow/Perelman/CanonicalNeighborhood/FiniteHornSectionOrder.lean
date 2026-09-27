import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRadialNeighborhood

set_option autoImplicit false
noncomputable section
open Filter Manifold Set
open DifferentialGeometry.Geometry.Curvature
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]

local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩
local instance : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
  (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank
    (by simp [ThreeSpace] : 1 < Module.finrank ℝ ThreeSpace)) (0 : ThreeSpace)
    (by norm_num : (0 : ℝ) ≤ 1))

private theorem height_map (T : GlobalNeckTube W) (p : Sphere 2)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) : T.height (T.map (p, q)) = q := by
  change (T.map.invFun (T.map (p, q))).2 = q
  rw [T.map.left_inv' (by rw [T.source_eq]; exact ⟨mem_univ _, hq⟩)]

private theorem isConnected_upper_side (T : GlobalNeckTube W)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) : IsConnected {x : W | q ≤ T.height x} := by
  have himage : T.map '' (univ ×ˢ Ico q 1) = {x : W | q ≤ T.height x} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change q ≤ T.height (T.map (y.1, y.2))
      rw [height_map T y.1 ⟨hq.1.trans_le hy.2.1, hy.2.2⟩]
      exact hy.2.1
    · intro hx
      refine ⟨T.map.symm x, ⟨mem_univ _, hx, (T.height_mem x).2⟩, ?_⟩
      exact T.map.right_inv' (by rw [T.target_eq]; trivial)
  rw [← himage]
  apply ((_root_.isConnected_univ : IsConnected (univ : Set (Sphere 2))).prod
    (isConnected_Ico hq.2)).image
  apply T.map.contMDiffOn_toFun.continuousOn.mono
  intro y hy
  rw [T.source_eq]
  exact ⟨hy.1, hq.1.trans_le hy.2.1, hy.2.2⟩

private theorem not_isCompact_upper_half (T : GlobalNeckTube W) :
    ¬ IsCompact {x : W | (1 / 2 : ℝ) ≤ T.height x} := by
  classical
  intro hcompact
  let p : Sphere 2 := Classical.choice inferInstance
  have hne : ({x : W | (1 / 2 : ℝ) ≤ T.height x} : Set W).Nonempty := by
    refine ⟨T.map (p, 1 / 2), ?_⟩
    change (1 / 2 : ℝ) ≤ T.height (T.map (p, 1 / 2))
    rw [height_map T p (by norm_num)]
  obtain ⟨x, _hx, hmax⟩ := hcompact.exists_isMaxOn hne T.continuous_height.continuousOn
  let q : ℝ := (T.height x + 1) / 2
  have hq : q ∈ Ioo (0 : ℝ) 1 := by
    have h := T.height_mem x
    dsimp [q]
    constructor <;> linarith [h.1, h.2]
  have hy : (1 / 2 : ℝ) ≤ T.height (T.map (p, q)) := by
    rw [height_map T p hq]
    have h := (T.height_mem x).1
    dsimp [q]
    linarith
  have hle : T.height (T.map (p, q)) ≤ T.height x := hmax hy
  rw [height_map T p hq] at hle
  have h := (T.height_mem x).2
  dsimp [q] at hle
  linarith

variable [IsManifold I3 ∞ W]

theorem GlobalNeckCrossSection.outer_side_of_center_in_subend
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    {F : PartialDiffeomorph IC I3 Cylinder W ∞}
    (G : GlobalNeckCrossSection F H.subend H.axial.point H.axial.length)
    (i : ℕ) (hcenter : ∀ p : Sphere 2, F (p, 0) ∈ H.subend i) :
    ∀ x : W, x ∉ H.subend i → (1 / 2 : ℝ) < G.tube.height x := by
  let S : Set W := {x | H.cut_height i ≤ H.tube.height x}
  have hS : IsConnected S := isConnected_upper_side H.tube (H.cut_height_mem i)
  have hne (x : W) (hx : x ∈ S) : G.tube.height x ≠ (1 / 2 : ℝ) := by
    intro heq
    obtain ⟨y, hy, hyx⟩ := (G.tube.mem_sectionSet_iff (by norm_num) x).mpr heq
    have hyq : y.2 = (1 / 2 : ℝ) := hy.2
    have hp : F (y.1, 0) = x := by
      rw [← G.center_eq, ← hyq]
      exact hyx
    have hbelow := hcenter y.1
    rw [hp, H.subend_eq i] at hbelow
    change H.tube.height x < H.cut_height i at hbelow
    change H.cut_height i ≤ H.tube.height x at hx
    exact (not_lt_of_ge hx) hbelow
  rcases hS.isPreconnected.mapsTo_Ioi_or_Iio G.tube.continuous_height.continuousOn hne with
    houter | hinner
  · intro x hx
    apply houter
    change H.cut_height i ≤ H.tube.height x
    simpa only [H.subend_eq i, mem_ofPred_eq, not_lt] using hx
  · obtain ⟨j, hj⟩ := G.deep_side
    have hcompact : IsCompact {x : W | (1 / 2 : ℝ) ≤ G.tube.height x} := by
      apply (H.tube.isCompact_slab (H.cut_height_mem j).1 (H.cut_height_mem i).2).of_isClosed_subset
        (isClosed_le continuous_const G.tube.continuous_height)
      intro x hx
      have hxj : H.cut_height j ≤ H.tube.height x := by
        apply le_of_not_gt
        intro hlt
        have hmem : x ∈ H.subend j := by rwa [H.subend_eq j]
        exact (not_lt_of_ge hx) (hj x hmem)
      have hxi : H.tube.height x < H.cut_height i := by
        apply lt_of_not_ge
        intro hge
        have hnegative : G.tube.height x < (1 / 2 : ℝ) := hinner hge
        exact (not_lt_of_ge (show (1 / 2 : ℝ) ≤ G.tube.height x from hx)) hnegative
      refine ⟨H.tube.map.symm x, ⟨mem_univ _, hxj, hxi.le⟩, ?_⟩
      exact H.tube.map.right_inv' (by rw [H.tube.target_eq]; trivial)
    exact (not_isCompact_upper_half G.tube hcompact).elim

theorem finiteHorn_exists_inner_collar
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) (x y : W)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ (w : W) (C : CylinderReference) (F : PartialDiffeomorph IC I3 Cylinder W ∞)
      (p : Sphere 2) (G : GlobalNeckCrossSection F H.subend H.axial.point H.axial.length),
      F (p, 0) = w ∧ univ ×ˢ Icc (-H.collar_depth) H.collar_depth ⊆ F.source ∧
      ∃ hQ : 0 < metricScalarAt g w,
        Nonempty (MetricComparisonOn (fun _ => C.metric 0)
          (fun _ => scaleMetric (metricScalarAt g w) hQ g) F
          (univ ×ˢ Icc (-H.collar_depth) H.collar_depth) {0}
          (⌈H.neck_precision⁻¹⌉₊) H.neck_precision) ∧
        (∀ q : Sphere 2, dist (F (q, 0) : UniformSpace.Completion W) H.endpoint < eta) ∧
        (1 / 2 : ℝ) < G.tube.height x ∧ (1 / 2 : ℝ) < G.tube.height y := by
  have hheight : 0 < min (H.tube.height x) (H.tube.height y) :=
    lt_min (H.tube.height_mem x).1 (H.tube.height_mem y).1
  obtain ⟨i, hi⟩ := ((tendsto_order.1 H.cut_height_zero).2 _ hheight).exists
  have hxi : x ∉ H.subend i := by
    rw [H.subend_eq i, mem_ofPred_eq, not_lt]
    exact (hi.trans_le (min_le_left _ _)).le
  have hyi : y ∉ H.subend i := by
    rw [H.subend_eq i, mem_ofPred_eq, not_lt]
    exact (hi.trans_le (min_le_right _ _)).le
  obtain ⟨delta, hdelta, hball⟩ := finiteHorn_ball_subset_subend g H i
  let e : ℝ := min eta delta
  have he : 0 < e := lt_min heta hdelta
  obtain ⟨D, hD, hshortcuts⟩ := exists_uniform_transverse_shortcuts (M := W)
  obtain ⟨j, hj⟩ := H.cylindrical_tail
  obtain ⟨k, hk⟩ := finiteHorn_subend_radial_small g H (half_pos he)
  obtain ⟨l, hl⟩ := H.curvature_diverges ((2 * D / e) ^ 2 + 1)
  have hmono : Antitone H.subend := antitone_nat_of_succ_le H.nested
  obtain ⟨w, hw⟩ := (H.connected_subend (max j (max k l))).nonempty
  have hwj := hmono (le_max_left j (max k l)) hw
  have hwk := hmono ((le_max_left k l).trans (le_max_right j (max k l))) hw
  have hwl := hmono ((le_max_right k l).trans (le_max_right j (max k l))) hw
  obtain ⟨C, F, p, hcenter, ⟨G⟩, hsource, hQ, ⟨cmp⟩⟩ := hj w hwj
  have hlarge := hl w hwl
  have hsqrt : 2 * D / e < Real.sqrt (metricScalarAt g w) := by
    have hsq := Real.sq_sqrt hQ.le
    have hnonneg : 0 ≤ 2 * D / e := by positivity
    nlinarith [Real.sqrt_nonneg (metricScalarAt g w)]
  have hshort : D / Real.sqrt (metricScalarAt g w) < e / 2 := by
    apply (div_lt_iff₀ (Real.sqrt_pos.mpr hQ)).mpr
    have hmul := (div_lt_iff₀ he).mp hsqrt
    nlinarith
  have hlevel : ∀ q : Sphere 2, (q, (0 : ℝ)) ∈
      (univ ×ˢ Icc (-H.collar_depth) H.collar_depth : Set Cylinder) := by
    intro q
    exact ⟨mem_univ _, by constructor <;> linarith [H.collar_depth_pos]⟩
  have hcentral (q : Sphere 2) :
      dist (F (q, 0) : UniformSpace.Completion W) H.endpoint < e := by
    obtain ⟨gamma, hstart, hend, hsmooth, _hmem, hlength⟩ :=
      hshortcuts C (fun _ => C.metric 0)
        (fun _ => scaleMetric (metricScalarAt g w) hQ g) F
        (univ ×ˢ Icc (-H.collar_depth) H.collar_depth) {0}
        (⌈H.neck_precision⁻¹⌉₊) H.neck_precision 0 cmp rfl H.neck_precision_pos.le
        (by linarith [H.neck_precision_small]) (by simp) hsource hlevel q p
    have hdist := (edistOf_le_metricPathELength (scaleMetric (metricScalarAt g w) hQ g)
      (by norm_num : (0 : ℝ) ≤ 1) hsmooth).trans hlength
    rw [hstart, hend, hcenter, edistOf_scale, H.edist_eq_ofReal_dist,
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hdist
    have hreal := (ENNReal.ofReal_le_ofReal_iff hD.le).mp hdist
    have hnear : dist (F (q, 0)) w < e / 2 := by
      apply lt_of_le_of_lt _ hshort
      apply (le_div_iff₀ (Real.sqrt_pos.mpr hQ)).mpr
      nlinarith
    have hwnear := hk w hwk
    have htri := dist_triangle (F (q, 0) : UniformSpace.Completion W)
      (w : UniformSpace.Completion W) H.endpoint
    rw [UniformSpace.Completion.dist_eq] at htri
    linarith
  have hinside (q : Sphere 2) : F (q, 0) ∈ H.subend i :=
    hball _ ((hcentral q).trans_le (min_le_right _ _))
  refine ⟨w, C, F, p, G, hcenter, hsource, hQ, ⟨cmp⟩, ?_, ?_, ?_⟩
  · intro q
    exact (hcentral q).trans_le (min_le_left _ _)
  · exact G.outer_side_of_center_in_subend g H i hinside x hxi
  · exact G.outer_side_of_center_in_subend g H i hinside y hyi

theorem GlobalNeckCrossSection.endRay_meets_center
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    {F : PartialDiffeomorph IC I3 Cylinder W ∞}
    (G : GlobalNeckCrossSection F H.subend H.axial.point H.axial.length)
    (a : EndRay H.endpoint) (houter : (1 / 2 : ℝ) < G.tube.height (a.point a.length)) :
    ∃ s ∈ Ioc (0 : ℝ) a.length, ∃ p : Sphere 2, F (p, 0) = a.point s := by
  obtain ⟨j, hj⟩ := G.deep_side
  obtain ⟨delta, hdelta, hball⟩ := finiteHorn_ball_subset_subend g H j
  let s₀ : ℝ := min delta a.length / 2
  have hs₀ : 0 < s₀ := half_pos (lt_min hdelta a.length_pos)
  have hslen : s₀ ≤ a.length := by
    have h := min_le_right delta a.length
    dsimp [s₀]
    linarith [a.length_pos]
  have hsdelta : s₀ < delta := by
    have h := min_le_left delta a.length
    dsimp [s₀]
    linarith
  have hstart : G.tube.height (a.point s₀) < (1 / 2 : ℝ) := by
    apply hj
    apply hball
    rw [a.radial s₀ ⟨hs₀, hslen⟩]
    exact hsdelta
  have hLip : LipschitzOnWith 1 a.point (Ioc (0 : ℝ) a.length) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    simpa only [a.minimizing s hs t ht, NNReal.coe_one, one_mul, Real.dist_eq] using
      (le_rfl : |s - t| ≤ |s - t|)
  have hcont : ContinuousOn (G.tube.height ∘ a.point) (Icc s₀ a.length) :=
    G.tube.continuous_height.comp_continuousOn
      (hLip.continuousOn.mono (fun s hs => ⟨hs₀.trans_le hs.1, hs.2⟩))
  obtain ⟨s, hs, hheight⟩ := intermediate_value_Icc hslen hcont ⟨hstart.le, houter.le⟩
  change G.tube.height (a.point s) = (1 / 2 : ℝ) at hheight
  obtain ⟨y, hy, hys⟩ := (G.tube.mem_sectionSet_iff (by norm_num) (a.point s)).mpr hheight
  have hyq : y.2 = (1 / 2 : ℝ) := hy.2
  refine ⟨s, ⟨hs₀.trans_le hs.1, hs.2⟩, y.1, ?_⟩
  rw [← G.center_eq, ← hyq]
  exact hys

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
