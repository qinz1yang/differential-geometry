import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBarriersNeckEndScale

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] RealizedFiniteHorn.metric_space RealizedFiniteHorn.charted
  RealizedFiniteHorn.smooth RealizedFiniteHorn.sigmaCompact

def BoundedAtDistanceShell (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, BoundedAtDistance X

theorem finite_horn_construction_of_boundedAtDistanceShell {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi)
    (h : BoundedAtDistanceShell.{u} kappa sigma Phi) :
    ∃ alphaMax collarMin : ℝ, 0 < alphaMax ∧ alphaMax < 1 / 11 ∧ 0 < collarMin ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaMax → ∀ collar : ℝ, collarMin ≤ collar →
        ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            FiniteControlledRadius X → ∃ H : RealizedFiniteHorn X.toFlowSequence,
              H.horn.neck_precision = alpha ∧ collar ≤ H.horn.collar_depth := by
  let _ := hkappa
  let _ := hsigma
  let _ := hPhi
  obtain ⟨e₀, he₀, hb⟩ := h
  refine ⟨1 / 20, 1, by norm_num, by norm_num, by norm_num, ?_⟩
  intro alpha ha halp collar hcollar
  exact ⟨e₀, he₀, fun eps heps hle X hrad =>
    False.elim (finiteControlledRadius_false_of_boundedAtDistance X (hb eps heps hle X) hrad)⟩

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

def SubendRadialNesting (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (d : ℕ → ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → e < 1 / 10 → ∀ᶠ i in Filter.atTop, ∃ j : ℕ,
    {x : W | dist (x : UniformSpace.Completion W) H.endpoint < (1 + e / 2) * d i} ⊆ H.subend j ∧
    H.subend j ⊆ {x : W | dist (x : UniformSpace.Completion W) H.endpoint < (1 + e) * d i}

def HornRadialOuterPosition (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → e < 1 / 10 → ∀ᶠ i in Filter.atTop,
    ∀ x : W, (1 + e) * d i < dist (x : UniformSpace.Completion W) H.endpoint →
      (1 / 2 : ℝ) < (neckTube g H ray d i).height x

private theorem radial_spread_lt_half {L eta s e : ℝ} (hL : 0 < L) (heta : 0 < eta)
    (h : (2 * L / eta) ^ 2 < s * e) : L / Real.sqrt (s * e) < eta / 2 := by
  have hpos : 0 < 2 * L / eta := by positivity
  have hlt : 2 * L / eta < Real.sqrt (s * e) := by
    rw [Real.lt_sqrt hpos.le]
    exact h
  have hdiv := div_lt_div_of_pos_left hL hpos hlt
  have heq : L / (2 * L / eta) = eta / 2 := by field_simp
  simpa only [heq] using hdiv

private theorem div_sqrt_lt_mul {L eta s d : ℝ} (hs : 0 < s) (hd : 0 < d)
    (h : L / Real.sqrt (s * d ^ 2) < eta) : L / Real.sqrt s < d * eta := by
  have hsqrt : Real.sqrt (s * d ^ 2) = Real.sqrt s * d := by
    rw [Real.sqrt_mul hs.le, Real.sqrt_sq hd.le]
  rw [hsqrt] at h
  calc L / Real.sqrt s = d * (L / (Real.sqrt s * d)) := by field_simp
    _ < d * eta := mul_lt_mul_of_pos_left h hd

omit [SigmaCompactSpace W] in
theorem subend_contains_ball {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (d : ℕ → ℝ) (hzero : Filter.Tendsto d Filter.atTop (nhds 0)) (e : ℝ) :
    ∀ᶠ i in Filter.atTop, ∃ j : ℕ,
      {x : W | dist (x : UniformSpace.Completion W) H.endpoint < (1 - e) * d i} ⊆ H.subend j := by
  obtain ⟨delta, hdelta, hball⟩ := finiteHorn_ball_subset_subend g H 0
  have hlim : Filter.Tendsto (fun i => (1 - e) * d i) Filter.atTop (nhds 0) := by
    simpa using hzero.const_mul (1 - e)
  filter_upwards [hlim.eventually (eventually_lt_nhds hdelta)] with i hi
  exact ⟨0, fun x hx => hball x (lt_trans hx hi)⟩

omit [SigmaCompactSpace W] in
theorem subend_inside_ball {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (d : ℕ → ℝ) {e : ℝ} (he : 0 < e) (i : ℕ) (hdi : 0 < d i) :
    ∃ j : ℕ, H.subend j ⊆
      {x : W | dist (x : UniformSpace.Completion W) H.endpoint < (1 + e) * d i} := by
  obtain ⟨j, hj⟩ := finiteHorn_subend_radial_small g H
    (eta := (1 + e) * d i) (mul_pos (by linarith only [he]) hdi)
  exact ⟨j, fun x hx => hj x hx⟩

omit [SigmaCompactSpace W] in
theorem subendRadialNesting_of_neckEndScaleWindow {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hscale : NeckEndScaleWindow g H ray d) : SubendRadialNesting g H d :=
  hscale.2

omit [SigmaCompactSpace W] in
theorem subendRadialNesting_of_neckEndScale {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hscale : NeckEndScale g H ray d) : SubendRadialNesting g H d :=
  subendRadialNesting_of_neckEndScaleWindow H ray d
    (neckEndScaleWindow_of_neckEndScale g H ray d hscale)

theorem hornRadialPosition_iff_hornRadialOuterPosition {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop) :
    HornRadialPosition g H ray d ↔ HornRadialOuterPosition g H ray d := by
  classical
  constructor
  · intro h e he he10
    filter_upwards [h e he he10] with i hi
    exact hi.2
  · intro h e he he10
    filter_upwards [endChart_height_lt_half_of_dist_lt H ray d hd hzero hlarge e he he10,
      eventually_mem_tail g H ray d hd hzero, h e he he10] with i htip hgood houter
    refine ⟨?_, ?_⟩
    · intro x hx
      have htube : neckTube g H ray d i = (endChart g H (ray.point (d i)) hgood).cross.tube := by
        rw [neckTube, dif_pos hgood]
      rw [htube]
      exact htip hgood (endChart g H (ray.point (d i)) hgood) x hx
    · intro x hx
      exact houter x hx

omit [SigmaCompactSpace W] in
theorem hornRadialOuterPosition_of_subendRadialNesting {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hnest : SubendRadialNesting g H d) : HornRadialOuterPosition g H ray d := by
  classical
  intro e he he10
  filter_upwards [hnest e he he10, eventually_mem_tail g H ray d hd hzero,
    hlarge.eventually_ge_atTop (max 1 ((2 * transverseShortcutConstant W / e) ^ 2 + 1))]
    with i hnest_i hgood hbig
  obtain ⟨j1, hsub1, hsup1⟩ := hnest_i
  set E := endChart g H (ray.point (d i)) hgood with hE
  have htube : neckTube g H ray d i = E.cross.tube := by rw [neckTube, dif_pos hgood]
  have hdpos : 0 < d i := (hd i).1
  have hsmul : 1 ≤ metricScalarAt g (ray.point (d i)) * d i ^ 2 :=
    le_trans (le_max_left _ _) hbig
  have hs_pos : 0 < metricScalarAt g (ray.point (d i)) := by
    nlinarith [hsmul, sq_nonneg (d i), sq_pos_of_pos hdpos]
  have hspread : transverseShortcutConstant W /
      Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) < e / 2 := by
    refine radial_spread_lt_half (transverseShortcutConstant_pos W) he ?_
    have h2 : (2 * transverseShortcutConstant W / e) ^ 2 + 1 ≤
        metricScalarAt g (ray.point (d i)) * d i ^ 2 := le_trans (le_max_right _ _) hbig
    linarith
  have hcenter_ball : ∀ q : Sphere 2,
      dist (E.F (q, 0) : UniformSpace.Completion W) H.endpoint < (1 + e / 2) * d i := by
    intro q
    have hdiam := endChart_section_diameter_le g H (ray.point (d i)) hgood (E.F (q, 0))
      (by
        rw [← GlobalNeckTube.range_sectionMap E.cross.tube (1 / 2),
          show (fun r : Sphere 2 => E.cross.tube.map (r, 1 / 2)) =
            (fun r : Sphere 2 => E.F (r, 0)) from funext E.cross.center_eq]
        exact ⟨q, rfl⟩)
    have hle : transverseShortcutConstant W /
        Real.sqrt (metricScalarAt g (ray.point (d i))) < d i * (e / 2) :=
      div_sqrt_lt_mul hs_pos hdpos hspread
    have hlt : dist (ray.point (d i)) (E.F (q, 0)) < (e / 2) * d i := by
      rw [mul_comm (e / 2) (d i)]
      exact lt_of_le_of_lt hdiam hle
    calc dist (E.F (q, 0) : UniformSpace.Completion W) H.endpoint
        ≤ dist (E.F (q, 0) : UniformSpace.Completion W)
            (ray.point (d i) : UniformSpace.Completion W) +
          dist (ray.point (d i) : UniformSpace.Completion W) H.endpoint := dist_triangle _ _ _
      _ = dist (ray.point (d i)) (E.F (q, 0)) + d i := by
            rw [UniformSpace.Completion.dist_eq, dist_comm (E.F (q, 0)) (ray.point (d i)),
              ray.radial (d i) (hd i)]
      _ < (e / 2) * d i + d i := by linarith
      _ = (1 + e / 2) * d i := by ring
  have hcenter_sub1 : ∀ q : Sphere 2, E.F (q, 0) ∈ H.subend j1 :=
    fun q => hsub1 (hcenter_ball q)
  intro x hx
  have hout : x ∉ H.subend j1 := by
    intro hmem
    have h' : dist (x : UniformSpace.Completion W) H.endpoint < (1 + e) * d i := hsup1 hmem
    linarith
  have houter := GlobalNeckCrossSection.outer_side_of_center_in_subend g H E.cross j1
    hcenter_sub1 x hout
  rwa [htube]

theorem hornRadialPosition_of_subendRadialNesting {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hnest : SubendRadialNesting g H d) : HornRadialPosition g H ray d :=
  (hornRadialPosition_iff_hornRadialOuterPosition H ray d hd hzero hlarge).mpr
    (hornRadialOuterPosition_of_subendRadialNesting H ray d hd hzero hlarge hnest)

theorem finite_horn_barriers_of_subendRadialNesting {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hnest : SubendRadialNesting g H d) : Nonempty (HornBarriers H ray d) :=
  nonempty_hornBarriers_of_hornRadialPosition g H ray d hd hzero
    (hornRadialPosition_of_subendRadialNesting H ray d hd hzero hlarge hnest)

theorem finite_horn_barriers_of_hornRadialOuterPosition {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hout : HornRadialOuterPosition g H ray d) : Nonempty (HornBarriers H ray d) :=
  nonempty_hornBarriers_of_hornRadialPosition g H ray d hd hzero
    ((hornRadialPosition_iff_hornRadialOuterPosition H ray d hd hzero hlarge).mpr hout)

omit [SigmaCompactSpace W] in
theorem not_unrestricted_subend_radial_nesting {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (d : ℕ → ℝ) (hd : ∀ i, 0 < d i)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0)) :
    ¬ (∀ a b : ℝ, -1 < a → a < b → b < 1 / 10 → ∀ᶠ i in Filter.atTop, ∃ j : ℕ,
      {x : W | dist (x : UniformSpace.Completion W) H.endpoint < (1 - a) * d i} ⊆ H.subend j ∧
      H.subend j ⊆ {x : W | dist (x : UniformSpace.Completion W) H.endpoint < (1 + b) * d i}) := by
  intro hnest
  have hspec : ∀ᶠ i in Filter.atTop, ∃ j : ℕ,
      {x : W | dist (x : UniformSpace.Completion W) H.endpoint < (1 - (-0.9)) * d i} ⊆ H.subend j ∧
      H.subend j ⊆ {x : W | dist (x : UniformSpace.Completion W) H.endpoint < (1 + 0.05) * d i} :=
    hnest (-0.9) 0.05 (by norm_num) (by norm_num) (by norm_num)
  have hlim : Filter.Tendsto (fun i => 1.2 * d i) Filter.atTop (nhds 0) := by
    simpa using hzero.const_mul (1.2 : ℝ)
  have hsmall : ∀ᶠ i in Filter.atTop, 1.2 * d i < H.axial.length :=
    hlim.eventually (eventually_lt_nhds H.axial.length_pos)
  obtain ⟨i, hsi, hi⟩ := (hspec.and hsmall).exists
  obtain ⟨j, hsub, hsup⟩ := hsi
  have hmem : 1.2 * d i ∈ Set.Ioc 0 H.axial.length := ⟨by linarith [hd i], hi.le⟩
  have hrad := H.axial.radial (1.2 * d i) hmem
  have hx1 : dist (H.axial.point (1.2 * d i) : UniformSpace.Completion W) H.endpoint <
      (1 - (-0.9)) * d i := by
    rw [hrad, show (1 - (-0.9)) * d i = 1.9 * d i by norm_num]
    linarith [hd i]
  have hx2 : dist (H.axial.point (1.2 * d i) : UniformSpace.Completion W) H.endpoint <
      (1 + 0.05) * d i := hsup (hsub hx1)
  rw [hrad, show (1 + 0.05) * d i = 1.05 * d i by norm_num] at hx2
  linarith [hd i]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
