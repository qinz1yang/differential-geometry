import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBarriersRadialNesting
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornRadialNeighborhood

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal

universe u

def RadialLevelCalibration {X : Type*} [PseudoMetricSpace X] (level : ℕ → Set X) (endpoint : X)
    (rho : ℕ → ℝ) : Prop :=
  (∀ i, 0 < rho i) ∧
    (∀ i, ∀ x : X, dist x endpoint < rho i → x ∈ level i) ∧
    (∀ i, ∀ x ∈ level i, dist x endpoint ≤ rho i) ∧
    (∀ e : ℝ, 0 < e → e < 1 / 10 → ∀ᶠ i in Filter.atTop, ∃ j : ℕ,
      (1 + e / 2) * rho i ≤ rho j ∧ rho j < (1 + e) * rho i)

theorem radialNesting_of_radialLevelCalibration {X : Type*} [PseudoMetricSpace X]
    {level : ℕ → Set X} {endpoint : X} {rho : ℕ → ℝ}
    (h : RadialLevelCalibration level endpoint rho) :
    ∀ e : ℝ, 0 < e → e < 1 / 10 → ∀ᶠ i in Filter.atTop, ∃ j : ℕ,
      {x : X | dist x endpoint < (1 + e / 2) * rho i} ⊆ level j ∧
        level j ⊆ {x : X | dist x endpoint < (1 + e) * rho i} := by
  obtain ⟨_, hinner, houter, hdense⟩ := h
  intro e he he10
  filter_upwards [hdense e he he10] with i hi
  obtain ⟨j, hlo, hhi⟩ := hi
  exact ⟨j, fun x hx => hinner j x (lt_of_lt_of_le hx hlo),
    fun x hx => lt_of_le_of_lt (houter j x hx) hhi⟩

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]

def SubendRadialLevelCalibration (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (rho : ℕ → ℝ) : Prop :=
  RadialLevelCalibration (fun i => (fun x : W => (x : UniformSpace.Completion W)) '' H.subend i)
    H.endpoint rho

theorem subendRadialNesting_of_subendRadialLevelCalibration {g : SmoothRiemannianMetric I3 W}
    {H : FiniteHorn g} {rho : ℕ → ℝ} (h : SubendRadialLevelCalibration g H rho) :
    SubendRadialNesting g H rho := by
  intro e he he10
  filter_upwards [radialNesting_of_radialLevelCalibration h e he he10] with i hi
  obtain ⟨j, hsub, hsup⟩ := hi
  exact ⟨j, fun x hx => by
      obtain ⟨y, hy, hyx⟩ := hsub hx
      rw [UniformSpace.Completion.coe_inj.mp hyx] at hy
      exact hy,
    fun x hx => hsup ⟨x, hx, rfl⟩⟩

theorem tendsto_zero_of_subendRadialLevelCalibration {g : SmoothRiemannianMetric I3 W}
    {H : FiniteHorn g} {rho : ℕ → ℝ} (h : SubendRadialLevelCalibration g H rho) :
    Filter.Tendsto rho Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  have hbase : 0 < min eps H.axial.length / 2 :=
    half_pos (lt_min heps H.axial.length_pos)
  obtain ⟨j, hj⟩ := finiteHorn_subend_radial_small g H
    (eta := min eps H.axial.length / 2) hbase
  refine ⟨j, fun k hk => ?_⟩
  have hmono : H.subend k ⊆ H.subend j := antitone_nat_of_succ_le H.nested hk
  have hbound : rho k ≤ min eps H.axial.length / 2 := by
    by_contra hcon
    have hgt : min eps H.axial.length / 2 < rho k := lt_of_not_ge hcon
    have hltL : min eps H.axial.length / 2 < H.axial.length := by
      have := min_le_right eps H.axial.length
      linarith [H.axial.length_pos]
    obtain ⟨s, hs1, hs2⟩ := exists_between (lt_min hgt hltL)
    have hmem : s ∈ Set.Ioc (0 : ℝ) H.axial.length :=
      ⟨by linarith, (hs2.trans_le (min_le_right _ _)).le⟩
    have hin : H.axial.point s ∈ H.subend k := by
      have himg := h.2.1 k (H.axial.point s : UniformSpace.Completion W) (by
        rw [H.axial.radial s hmem]
        exact lt_of_lt_of_le hs2 (min_le_left _ _))
      obtain ⟨y, hy, hyx⟩ := himg
      rwa [UniformSpace.Completion.coe_inj.mp hyx] at hy
    have hsmall : dist (H.axial.point s : UniformSpace.Completion W) H.endpoint <
        min eps H.axial.length / 2 := hj (H.axial.point s) (hmono hin)
    rw [H.axial.radial s hmem] at hsmall
    linarith
  have hpos : 0 < rho k := h.1 k
  rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
  have hle : min eps H.axial.length / 2 ≤ eps / 2 := by
    have := min_le_left eps H.axial.length
    linarith
  linarith

def raySubendScale (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (i : ℕ) : ℝ :=
  sSup {R : ℝ | R ≤ ray.length ∧
    ∀ x : W, dist (x : UniformSpace.Completion W) H.endpoint < R → x ∈ H.subend i}

private theorem bddAbove_raySubendScale (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (i : ℕ) :
    BddAbove {R : ℝ | R ≤ ray.length ∧
      ∀ x : W, dist (x : UniformSpace.Completion W) H.endpoint < R → x ∈ H.subend i} :=
  ⟨ray.length, fun _ hR => hR.1⟩

private theorem exists_pos_mem_raySubendScale (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (i : ℕ) :
    ∃ R ∈ {R : ℝ | R ≤ ray.length ∧
      ∀ x : W, dist (x : UniformSpace.Completion W) H.endpoint < R →
        x ∈ H.subend i}, 0 < R := by
  obtain ⟨delta, hdelta, hball⟩ := finiteHorn_ball_subset_subend g H i
  refine ⟨min delta ray.length / 2, ⟨?_, ?_⟩, half_pos (lt_min hdelta ray.length_pos)⟩
  · have := min_le_right delta ray.length
    linarith [ray.length_pos]
  · intro x hx
    exact hball x (lt_of_lt_of_le hx (by
      have := min_le_left delta ray.length
      linarith))

private theorem nonempty_raySubendScale (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (i : ℕ) :
    {R : ℝ | R ≤ ray.length ∧
      ∀ x : W, dist (x : UniformSpace.Completion W) H.endpoint < R →
        x ∈ H.subend i}.Nonempty :=
  (exists_pos_mem_raySubendScale g H ray i).imp (fun _ hR => hR.1)

private theorem subend_nonempty (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (i : ℕ) : (H.subend i).Nonempty := by
  obtain ⟨delta, hdelta, hball⟩ := finiteHorn_ball_subset_subend g H i
  have hmem : min delta ray.length / 2 ∈ Set.Ioc (0 : ℝ) ray.length := by
    refine ⟨half_pos (lt_min hdelta ray.length_pos), ?_⟩
    have := min_le_right delta ray.length
    linarith [ray.length_pos]
  refine ⟨ray.point (min delta ray.length / 2), hball _ ?_⟩
  rw [ray.radial _ hmem]
  have := min_le_left delta ray.length
  linarith

theorem raySubendScale_pos (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (i : ℕ) : 0 < raySubendScale g H ray i := by
  obtain ⟨R, hR, hRpos⟩ := exists_pos_mem_raySubendScale g H ray i
  exact lt_of_lt_of_le hRpos (le_csSup (bddAbove_raySubendScale g H ray i) hR)

theorem raySubendScale_le_length (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (i : ℕ) : raySubendScale g H ray i ≤ ray.length :=
  csSup_le (nonempty_raySubendScale g H ray i) (fun _ hR => hR.1)

theorem mem_subend_of_lt_raySubendScale (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (i : ℕ) {x : W}
    (hx : dist (x : UniformSpace.Completion W) H.endpoint < raySubendScale g H ray i) :
    x ∈ H.subend i := by
  obtain ⟨R, hR, hxR⟩ := (lt_csSup_iff (bddAbove_raySubendScale g H ray i)
    (nonempty_raySubendScale g H ray i)).mp hx
  exact hR.2 x hxR

theorem raySubendScale_le_of_subend_subset_ball (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (i : ℕ) {R : ℝ}
    (hsub : H.subend i ⊆ {x : W | dist (x : UniformSpace.Completion W) H.endpoint < R}) :
    raySubendScale g H ray i ≤ R := by
  refine csSup_le (nonempty_raySubendScale g H ray i) (fun R' hR' => ?_)
  by_contra hcon
  have hlt : R < R' := lt_of_not_ge hcon
  have hRpos : 0 < R := by
    obtain ⟨x, hx⟩ := subend_nonempty g H ray i
    have hthis : dist (x : UniformSpace.Completion W) H.endpoint < R := hsub hx
    have hd0 : 0 ≤ dist (x : UniformSpace.Completion W) H.endpoint := dist_nonneg
    linarith
  by_cases hcase : R < ray.length
  · obtain ⟨s, hs1, hs2⟩ := exists_between (lt_min hlt hcase)
    have hmem : s ∈ Set.Ioc (0 : ℝ) ray.length :=
      ⟨by linarith, (hs2.trans_le (min_le_right _ _)).le⟩
    have hin : ray.point s ∈ H.subend i :=
      hR'.2 _ (by
        rw [ray.radial s hmem]
        exact lt_of_lt_of_le hs2 (min_le_left _ _))
    have hthis : dist (ray.point s : UniformSpace.Completion W) H.endpoint < R := hsub hin
    rw [ray.radial s hmem] at hthis
    linarith
  · linarith [hR'.1, not_lt.mp hcase]

theorem tendsto_raySubendScale_zero (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) :
    Filter.Tendsto (fun i => raySubendScale g H ray i) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨j, hj⟩ := finiteHorn_subend_radial_small g H (half_pos heps)
  refine ⟨j, fun k hk => ?_⟩
  have hmono : H.subend k ⊆ H.subend j := antitone_nat_of_succ_le H.nested hk
  have hle : raySubendScale g H ray k ≤ eps / 2 :=
    raySubendScale_le_of_subend_subset_ball g H ray k (fun x hx => hj x (hmono hx))
  have hpos := raySubendScale_pos g H ray k
  rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
  linarith

theorem exists_raySubendScale_of_subendRadialNesting {g : SmoothRiemannianMetric I3 W}
    {H : FiniteHorn g} {ray : EndRay H.endpoint} {d : ℕ → ℝ}
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length) (hnest : SubendRadialNesting g H d) :
    ∀ e : ℝ, 0 < e → e < 1 / 10 → ∀ᶠ i in Filter.atTop, ∃ j : ℕ,
      d i ≤ raySubendScale g H ray j ∧ raySubendScale g H ray j ≤ (1 + e) * d i := by
  intro e he he10
  filter_upwards [hnest e he he10] with i hi
  obtain ⟨j, hsub, hsup⟩ := hi
  refine ⟨j, ?_, raySubendScale_le_of_subend_subset_ball g H ray j hsup⟩
  have hRmem : min ((1 + e / 2) * d i) ray.length ∈ {R : ℝ | R ≤ ray.length ∧
      ∀ x : W, dist (x : UniformSpace.Completion W) H.endpoint < R → x ∈ H.subend j} :=
    ⟨min_le_right _ _, fun x hx => hsub (lt_of_lt_of_le hx (min_le_left _ _))⟩
  have hle : min ((1 + e / 2) * d i) ray.length ≤ raySubendScale g H ray j :=
    le_csSup (bddAbove_raySubendScale g H ray j) hRmem
  have hdi : 0 < d i := (hd i).1
  have hdle : d i ≤ ray.length := (hd i).2
  have h1 : d i ≤ (1 + e / 2) * d i := by nlinarith
  have h2 : d i ≤ min ((1 + e / 2) * d i) ray.length := le_min h1 hdle
  linarith

variable [SigmaCompactSpace W] in
theorem finite_horn_barriers_of_subendRadialLevelCalibration {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (rho : ℕ → ℝ)
    (hd : ∀ i, rho i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto rho Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (rho i)) * rho i ^ 2)
      Filter.atTop Filter.atTop)
    (h : SubendRadialLevelCalibration g H rho) : Nonempty (HornBarriers H ray rho) :=
  finite_horn_barriers_of_subendRadialNesting H ray rho hd hzero hlarge
    (subendRadialNesting_of_subendRadialLevelCalibration h)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
