import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructureReduction

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

omit [SigmaCompactSpace W] in
noncomputable def subendRadialLevel (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (R : ℝ) : ℕ :=
  sInf {j : ℕ | H.subend j ⊆ {x : W | dist (x : UniformSpace.Completion W) H.endpoint < R}}

omit [SigmaCompactSpace W] in
theorem subend_subset_ball_subendRadialLevel (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) {R : ℝ} (hR : 0 < R) :
    H.subend (subendRadialLevel g H R) ⊆
      {x : W | dist (x : UniformSpace.Completion W) H.endpoint < R} :=
  Nat.sInf_mem (s := {j : ℕ | H.subend j ⊆
    {x : W | dist (x : UniformSpace.Completion W) H.endpoint < R}})
    (by
      obtain ⟨j, hj⟩ := finiteHorn_subend_radial_small g H hR
      exact ⟨j, hj⟩)

omit [SigmaCompactSpace W] in
theorem subendRadialLevel_le (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) {R : ℝ}
    {j : ℕ} (h : H.subend j ⊆
      {x : W | dist (x : UniformSpace.Completion W) H.endpoint < R}) :
    subendRadialLevel g H R ≤ j :=
  Nat.sInf_le h

omit [SigmaCompactSpace W] in
theorem subendRadialLevel_mono (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) {R R' : ℝ}
    (hR : 0 < R) (hRR' : R ≤ R') : subendRadialLevel g H R' ≤ subendRadialLevel g H R := by
  refine subendRadialLevel_le g H ?_
  refine Set.Subset.trans (subend_subset_ball_subendRadialLevel g H hR) ?_
  intro x hx
  exact lt_of_lt_of_le hx hRR'

omit [SigmaCompactSpace W] in
theorem eventually_lt_subendRadialLevel (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (d : ℕ → ℝ) (hd : ∀ i, 0 < d i) (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    {e : ℝ} (he : 0 < e) (J : ℕ) :
    ∀ᶠ i in Filter.atTop, J < subendRadialLevel g H ((1 + e) * d i) := by
  obtain ⟨dJ, hdJ, hdJL, htail⟩ := H.cofinal_axial J
  have hlim : Filter.Tendsto (fun i => (1 + e) * d i) Filter.atTop (nhds 0) := by
    simpa using hzero.const_mul (1 + e)
  filter_upwards [hlim.eventually (eventually_lt_nhds hdJ)] with i hi
  by_contra hcon
  have hle : subendRadialLevel g H ((1 + e) * d i) ≤ J := not_lt.mp hcon
  have hmem : H.axial.point dJ ∈ H.subend J := htail dJ ⟨hdJ, le_rfl⟩
  have hmono : Antitone H.subend := antitone_nat_of_succ_le H.nested
  have hspec := subend_subset_ball_subendRadialLevel g H (R := (1 + e) * d i)
    (mul_pos (by linarith) (hd i)) (hmono hle hmem)
  change dist ((H.axial.point dJ : W) : UniformSpace.Completion W) H.endpoint <
    (1 + e) * d i at hspec
  rw [H.axial.radial dJ ⟨hdJ, hdJL⟩] at hspec
  linarith

omit [SigmaCompactSpace W] in
theorem endChartSectionSubendCapture_iff_exists_tipSide_subendCover
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) :
    EndChartSectionSubendCapture g H ray d ↔
      ∀ e : ℝ, 0 < e → e < 1 / 10 → ∀ᶠ i in Filter.atTop, ∃ j : ℕ,
        H.subend j ⊆
          {x : W | dist (x : UniformSpace.Completion W) H.endpoint < (1 + e) * d i} ∧
        ∀ (hx : ray.point (d i) ∈ H.subend (tailIndex g H)), ∀ x : W,
          (endChart g H (ray.point (d i)) hx).cross.tube.height x ≤ 1 / 2 →
            x ∈ H.subend j := by
  constructor
  · intro h e he he10
    filter_upwards [h e he he10] with i hi
    obtain ⟨j, hball, hsec⟩ := hi
    refine ⟨j, hball, fun hx x hxle => ?_⟩
    by_contra hnot
    exact absurd (GlobalNeckCrossSection.outer_side_of_center_in_subend g H
      (endChart g H (ray.point (d i)) hx).cross j (fun p => hsec hx p) x hnot)
      (not_lt.mpr hxle)
  · intro h e he he10
    filter_upwards [h e he he10] with i hi
    obtain ⟨j, hball, htip⟩ := hi
    refine ⟨j, hball, fun hx p => ?_⟩
    have hmemsec : (endChart g H (ray.point (d i)) hx).F (p, 0) ∈
        (endChart g H (ray.point (d i)) hx).cross.tube.sectionSet (1 / 2) := by
      rw [← GlobalNeckTube.range_sectionMap
        (endChart g H (ray.point (d i)) hx).cross.tube (1 / 2)]
      exact ⟨p, (endChart g H (ray.point (d i)) hx).cross.center_eq p⟩
    have hheight := (GlobalNeckTube.mem_sectionSet_iff
      (endChart g H (ray.point (d i)) hx).cross.tube (by norm_num) _).mp hmemsec
    exact htip hx _ hheight.le

omit [SigmaCompactSpace W] in
theorem subendRadialNesting_iff_radialLevelCover {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (d : ℕ → ℝ) (hd : ∀ i, 0 < d i) :
    SubendRadialNesting g H d ↔
      ∀ e : ℝ, 0 < e → e < 1 / 10 → ∀ᶠ i in Filter.atTop,
        {x : W | dist (x : UniformSpace.Completion W) H.endpoint < (1 + e / 2) * d i} ⊆
          H.subend (subendRadialLevel g H ((1 + e) * d i)) := by
  constructor
  · intro h e he he10
    filter_upwards [h e he he10] with i hi
    obtain ⟨j, hsub, hout⟩ := hi
    exact Set.Subset.trans hsub
      ((antitone_nat_of_succ_le H.nested) (subendRadialLevel_le g H hout))
  · intro h e he he10
    filter_upwards [h e he he10] with i hi
    exact ⟨subendRadialLevel g H ((1 + e) * d i), hi,
      subend_subset_ball_subendRadialLevel g H (mul_pos (by linarith) (hd i))⟩

omit [SigmaCompactSpace W] in
theorem endChartSectionSubendCapture_of_radialLevelCover
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hcover : ∀ e : ℝ, 0 < e → e < 1 / 10 → ∀ᶠ i in Filter.atTop,
      {x : W | dist (x : UniformSpace.Completion W) H.endpoint < (1 + e / 2) * d i} ⊆
        H.subend (subendRadialLevel g H ((1 + e) * d i))) :
    EndChartSectionSubendCapture g H ray d := by
  intro e he he10
  have hT : 0 < transverseShortcutConstant W := transverseShortcutConstant_pos W
  filter_upwards [hcover e he he10,
    hlarge.eventually_ge_atTop (max 1 ((4 * transverseShortcutConstant W / e) ^ 2 + 1))]
    with i hcov hbig
  have hdpos : 0 < d i := (hd i).1
  refine ⟨subendRadialLevel g H ((1 + e) * d i),
    subend_subset_ball_subendRadialLevel g H (mul_pos (by linarith) hdpos), ?_⟩
  intro hx p
  set E := endChart g H (ray.point (d i)) hx with hE
  refine hcov ?_
  have hs_pos : 0 < metricScalarAt g (ray.point (d i)) := by
    have hone : 1 ≤ metricScalarAt g (ray.point (d i)) * d i ^ 2 :=
      le_trans (le_max_left _ _) hbig
    nlinarith [hone, sq_nonneg (d i), sq_pos_of_pos hdpos]
  have hspread : transverseShortcutConstant W /
      Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) < e / 4 := by
    have hpos : 0 < 4 * transverseShortcutConstant W / e := div_pos (by linarith) he
    have hlt : 4 * transverseShortcutConstant W / e <
        Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) := by
      rw [Real.lt_sqrt hpos.le]
      have h2 : (4 * transverseShortcutConstant W / e) ^ 2 + 1 ≤
          metricScalarAt g (ray.point (d i)) * d i ^ 2 :=
        le_trans (le_max_right _ _) hbig
      linarith
    have hdiv := div_lt_div_of_pos_left hT hpos hlt
    have heq : transverseShortcutConstant W / (4 * transverseShortcutConstant W / e) =
        e / 4 := by
      field_simp
    rwa [heq] at hdiv
  have hdiam : transverseShortcutConstant W / Real.sqrt (metricScalarAt g (ray.point (d i))) <
      d i * (e / 4) := by
    have hsqrt : Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) =
        Real.sqrt (metricScalarAt g (ray.point (d i))) * d i := by
      rw [Real.sqrt_mul hs_pos.le, Real.sqrt_sq hdpos.le]
    rw [hsqrt] at hspread
    have hsplit : transverseShortcutConstant W /
        Real.sqrt (metricScalarAt g (ray.point (d i))) =
        d i * (transverseShortcutConstant W /
          (Real.sqrt (metricScalarAt g (ray.point (d i))) * d i)) := by
      field_simp
    rw [hsplit]
    exact mul_lt_mul_of_pos_left hspread hdpos
  have hsec : E.F (p, 0) ∈ E.cross.tube.sectionSet (1 / 2) := by
    rw [← GlobalNeckTube.range_sectionMap E.cross.tube (1 / 2)]
    exact ⟨p, E.cross.center_eq p⟩
  have hbound := EndChart.section_diameter_le E _ hsec
  have htri := dist_triangle ((E.F (p, 0)) : UniformSpace.Completion W)
    ((ray.point (d i)) : UniformSpace.Completion W) H.endpoint
  rw [UniformSpace.Completion.dist_eq, dist_comm (E.F (p, 0)) (ray.point (d i)),
    ray.radial (d i) (hd i)] at htri
  have hdist : dist (ray.point (d i)) (E.F (p, 0)) < d i * (e / 4) :=
    lt_of_le_of_lt hbound hdiam
  have hrew : d i * (e / 4) + d i = (1 + e / 4) * d i := by ring
  have hstrict : dist ((E.F (p, 0)) : UniformSpace.Completion W) H.endpoint <
      (1 + e / 4) * d i := by
    rw [← hrew]
    linarith
  exact lt_trans hstrict (mul_lt_mul_of_pos_right (by linarith) hdpos)

theorem finite_horn_barriers_of_radialLevelCover {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (endData : EndGeometry H) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hcover : ∀ e : ℝ, 0 < e → e < 1 / 10 → ∀ᶠ i in Filter.atTop,
      {x : W | dist (x : UniformSpace.Completion W) H.endpoint < (1 + e / 2) * d i} ⊆
        H.subend (subendRadialLevel g H ((1 + e) * d i))) :
    Nonempty (HornBarriers H ray d) :=
  finite_horn_barriers_of_endChartSectionSubendCapture H endData ray d hd hzero hlarge
    (endChartSectionSubendCapture_of_radialLevelCover H ray d hd hlarge hcover)

theorem ball_subset_subendRadialLevel_of_endChartSectionSubendCapture
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (h : EndChartSectionSubendCapture g H ray d) :
    ∀ e : ℝ, 0 < e → e < 1 / 10 → ∀ᶠ i in Filter.atTop,
      {x : W | dist (x : UniformSpace.Completion W) H.endpoint < (1 - e / 2) * d i} ⊆
        H.subend (subendRadialLevel g H ((1 + e / 2) * d i)) := by
  intro e he he10
  have he2 : 0 < e / 2 := half_pos he
  have he210 : e / 2 < 1 / 10 := by linarith
  filter_upwards [h (e / 2) he2 he210,
    endChart_height_lt_half_of_dist_lt H ray d hd hzero hlarge (e / 2) he2 he210,
    eventually_mem_tail g H ray d hd hzero] with i hcap hinner hgood
  obtain ⟨j, hball, hsec⟩ := hcap
  have hle : subendRadialLevel g H ((1 + e / 2) * d i) ≤ j := subendRadialLevel_le g H hball
  have htip : ∀ x : W, (endChart g H (ray.point (d i)) hgood).cross.tube.height x ≤ 1 / 2 →
      x ∈ H.subend j := by
    intro x hxle
    by_contra hnot
    exact absurd (GlobalNeckCrossSection.outer_side_of_center_in_subend g H
      (endChart g H (ray.point (d i)) hgood).cross j (fun p => hsec hgood p) x hnot)
      (not_lt.mpr hxle)
  refine Set.Subset.trans ?_ ((antitone_nat_of_succ_le H.nested) hle)
  intro x hx
  exact htip x (hinner hgood (endChart g H (ray.point (d i)) hgood) x hx).le

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
