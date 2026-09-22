import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RadialLevelCalibration

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal

universe u

def RadialLevelDensity (rho : ℕ → ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → e < 1 / 10 → ∀ᶠ i in Filter.atTop, ∃ j : ℕ,
    (1 + e / 2) * rho i ≤ rho j ∧ rho j < (1 + e) * rho i

theorem radialLevelDensity_of_ratio_tendsto_one {rho : ℕ → ℝ} (hpos : ∀ i, 0 < rho i)
    (hanti : Antitone rho) (hzero : Filter.Tendsto rho Filter.atTop (nhds 0))
    (hratio : Filter.Tendsto (fun j : ℕ => rho j / rho (j + 1)) Filter.atTop (nhds 1)) :
    RadialLevelDensity rho := by
  intro e he _
  classical
  have hstep : (1 : ℝ) < 1 + e / (2 + e) := by
    have : 0 < e / (2 + e) := by positivity
    linarith
  obtain ⟨J, hJ⟩ : ∃ J : ℕ,
      ∀ j : ℕ, J ≤ j → rho j / rho (j + 1) < 1 + e / (2 + e) := by
    simpa only [Filter.eventually_atTop] using hratio.eventually (eventually_lt_nhds hstep)
  have hJpos : 0 < rho J := hpos J
  have hbnd : 0 < rho J / (1 + e / 2) := div_pos hJpos (by linarith)
  filter_upwards [hzero.eventually (eventually_lt_nhds hbnd)] with i hi
  have hclo : 0 < (1 + e / 2) * rho i := mul_pos (by linarith) (hpos i)
  have hex : ∃ j : ℕ, rho j < (1 + e / 2) * rho i :=
    (hzero.eventually (eventually_lt_nhds hclo)).exists
  set k := Nat.find hex with hk
  have hspec : rho k < (1 + e / 2) * rho i := Nat.find_spec hex
  have hmin : ∀ j : ℕ, j < k → (1 + e / 2) * rho i ≤ rho j :=
    fun j hj => not_lt.mp (Nat.find_min hex (by rwa [hk] at hj))
  have hlt : (1 + e / 2) * rho i < rho J := by
    have h := (lt_div_iff₀ (by linarith : (0 : ℝ) < 1 + e / 2)).mp hi
    rwa [mul_comm] at h
  have hJk : J < k := by
    by_contra hcon
    have hle : rho J ≤ rho k := hanti (not_lt.mp hcon)
    linarith
  have hkpos : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le J) hJk
  refine ⟨k - 1, hmin (k - 1) (Nat.sub_one_lt hkpos.ne'), ?_⟩
  have hJn : J ≤ k - 1 := Nat.le_sub_one_of_lt hJk
  have hratio := hJ (k - 1) hJn
  rw [Nat.sub_add_cancel hkpos] at hratio
  have hprod : rho (k - 1) < (1 + e / (2 + e)) * rho k :=
    (div_lt_iff₀ (hpos k)).mp hratio
  have hmono : (1 + e / (2 + e)) * rho k < (1 + e / (2 + e)) * ((1 + e / 2) * rho i) :=
    mul_lt_mul_of_pos_left hspec (by linarith)
  have hcombine : (1 + e / (2 + e)) * (1 + e / 2) = 1 + e := by
    field_simp
    ring
  calc rho (k - 1) < (1 + e / (2 + e)) * rho k := hprod
    _ < (1 + e / (2 + e)) * ((1 + e / 2) * rho i) := hmono
    _ = ((1 + e / (2 + e)) * (1 + e / 2)) * rho i := by ring
    _ = (1 + e) * rho i := by rw [hcombine]

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]

def SubendRadialLevelInner (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (rho : ℕ → ℝ) : Prop :=
  (∀ i, 0 < rho i) ∧
    ∀ i, ∀ x : W, dist (x : UniformSpace.Completion W) H.endpoint < rho i → x ∈ H.subend i

def SubendRadialLevelSharpness (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (rho : ℕ → ℝ) : Prop :=
  ∀ i, H.subend i ⊆ {x : W | dist (x : UniformSpace.Completion W) H.endpoint ≤ rho i}

theorem not_subendRadialLevelCalibration {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (rho : ℕ → ℝ) : ¬ SubendRadialLevelCalibration g H rho := by
  intro h
  obtain ⟨x, _, hx⟩ := h.2.1 0 H.endpoint (by simpa using h.1 0)
  exact H.endpoint_missing x hx

theorem subendRadialLevelInner_of_subendRadialLevelCalibration {g : SmoothRiemannianMetric I3 W}
    {H : FiniteHorn g} {rho : ℕ → ℝ} (h : SubendRadialLevelCalibration g H rho) :
    SubendRadialLevelInner g H rho := by
  refine ⟨h.1, fun i x hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ := h.2.1 i (x : UniformSpace.Completion W) hx
  rwa [UniformSpace.Completion.coe_inj.mp hyx] at hy

theorem subendRadialLevelSharpness_of_subendRadialLevelCalibration {g : SmoothRiemannianMetric I3 W}
    {H : FiniteHorn g} {rho : ℕ → ℝ} (h : SubendRadialLevelCalibration g H rho) :
    SubendRadialLevelSharpness g H rho :=
  fun i x hx => h.2.2.1 i (x : UniformSpace.Completion W) ⟨x, hx, rfl⟩

theorem radialLevelDensity_of_subendRadialLevelCalibration {g : SmoothRiemannianMetric I3 W}
    {H : FiniteHorn g} {rho : ℕ → ℝ} (h : SubendRadialLevelCalibration g H rho) :
    RadialLevelDensity rho :=
  h.2.2.2

theorem exists_subendRadialLevelInner (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) :
    ∃ rho : ℕ → ℝ, SubendRadialLevelInner g H rho := by
  classical
  choose rho hrho hball using fun i => finiteHorn_ball_subset_subend g H i
  exact ⟨rho, hrho, hball⟩

theorem subendRadialNesting_of_inner_sharpness_density {g : SmoothRiemannianMetric I3 W}
    {H : FiniteHorn g} {rho : ℕ → ℝ} (hinner : SubendRadialLevelInner g H rho)
    (hsharp : SubendRadialLevelSharpness g H rho) (hdense : RadialLevelDensity rho) :
    SubendRadialNesting g H rho := by
  intro e he he10
  filter_upwards [hdense e he he10] with i hi
  obtain ⟨j, hlo, hhi⟩ := hi
  exact ⟨j, fun x hx => hinner.2 j x (lt_of_lt_of_le hx hlo),
    fun x hx => lt_of_le_of_lt (hsharp j hx) hhi⟩

theorem subendRadialLevelInner_raySubendScale (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) : SubendRadialLevelInner g H (raySubendScale g H ray) :=
  ⟨fun i => raySubendScale_pos g H ray i,
    fun i _ hx => mem_subend_of_lt_raySubendScale g H ray i hx⟩

theorem raySubendScale_mem_Ioc (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (i : ℕ) :
    raySubendScale g H ray i ∈ Set.Ioc 0 ray.length :=
  ⟨raySubendScale_pos g H ray i, raySubendScale_le_length g H ray i⟩

private theorem bddAbove_raySubendScaleSet (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (i : ℕ) :
    BddAbove {R : ℝ | R ≤ ray.length ∧
      ∀ x : W, dist (x : UniformSpace.Completion W) H.endpoint < R → x ∈ H.subend i} :=
  ⟨ray.length, fun _ hR => hR.1⟩

private theorem nonempty_raySubendScaleSet (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (i : ℕ) :
    ({R : ℝ | R ≤ ray.length ∧
      ∀ x : W, dist (x : UniformSpace.Completion W) H.endpoint < R →
        x ∈ H.subend i} : Set ℝ).Nonempty := by
  obtain ⟨delta, hdelta, hball⟩ := finiteHorn_ball_subset_subend g H i
  have hle : min delta ray.length / 2 ≤ ray.length := by
    have := min_le_right delta ray.length
    linarith [ray.length_pos]
  have hball' : ∀ x : W, dist (x : UniformSpace.Completion W) H.endpoint <
      min delta ray.length / 2 → x ∈ H.subend i := by
    intro x hx
    refine hball x (lt_of_lt_of_le hx ?_)
    have := min_le_left delta ray.length
    linarith
  exact ⟨min delta ray.length / 2, hle, hball'⟩

theorem antitone_raySubendScale (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) : Antitone (fun i => raySubendScale g H ray i) := by
  intro i j hij
  refine csSup_le (nonempty_raySubendScaleSet g H ray j) (fun R hR => ?_)
  have hmono : H.subend j ⊆ H.subend i := antitone_nat_of_succ_le H.nested hij
  exact le_csSup (bddAbove_raySubendScaleSet g H ray i)
    ⟨hR.1, fun x hx => hmono (hR.2 x hx)⟩

theorem radialLevelDensity_raySubendScale_of_ratio_tendsto_one {g : SmoothRiemannianMetric I3 W}
    {H : FiniteHorn g} {ray : EndRay H.endpoint}
    (hratio : Filter.Tendsto (fun j : ℕ =>
      raySubendScale g H ray j / raySubendScale g H ray (j + 1)) Filter.atTop (nhds 1)) :
    RadialLevelDensity (raySubendScale g H ray) :=
  radialLevelDensity_of_ratio_tendsto_one (fun i => raySubendScale_pos g H ray i)
    (antitone_raySubendScale g H ray) (tendsto_raySubendScale_zero g H ray) hratio

theorem rayLength_le_of_subendRadialLevelSharpness {g : SmoothRiemannianMetric I3 W}
    {H : FiniteHorn g} {rho : ℕ → ℝ} (h : SubendRadialLevelSharpness g H rho) :
    ∀ i, ∀ a : EndRay H.endpoint, a.point a.length ∈ H.subend i → a.length ≤ rho i := by
  intro i a ha
  have hthis : dist (a.point a.length : UniformSpace.Completion W) H.endpoint ≤ rho i := h i ha
  rwa [a.radial a.length ⟨a.length_pos, le_rfl⟩] at hthis

theorem subendRadialLevelSharpness_of_forall_rayLength_le {g : SmoothRiemannianMetric I3 W}
    {H : FiniteHorn g} {rho : ℕ → ℝ} {i₀ : ℕ}
    (hrays : ∀ i, i₀ ≤ i → ∀ x ∈ H.subend i,
      ∃ a : EndRay H.endpoint, a.point a.length = x)
    (hlen : ∀ i, i₀ ≤ i → ∀ a : EndRay H.endpoint, a.point a.length ∈ H.subend i →
      a.length ≤ rho i) :
    ∀ i, i₀ ≤ i → H.subend i ⊆
      {x : W | dist (x : UniformSpace.Completion W) H.endpoint ≤ rho i} := by
  intro i hi x hx
  obtain ⟨a, ha⟩ := hrays i hi x hx
  have hle : a.length ≤ rho i := hlen i hi a (by rwa [ha])
  have hthis : dist (a.point a.length : UniformSpace.Completion W) H.endpoint ≤ rho i := by
    rwa [a.radial a.length ⟨a.length_pos, le_rfl⟩]
  change dist (x : UniformSpace.Completion W) H.endpoint ≤ rho i
  rwa [← ha]

theorem exists_hrays_of_endGeometry {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g)
    (endData : EndGeometry H) :
    ∃ i₀, ∀ i, i₀ ≤ i → ∀ x ∈ H.subend i,
      ∃ a : EndRay H.endpoint, a.point a.length = x := by
  obtain ⟨i₀, hi₀⟩ := endData.rays
  exact ⟨i₀, fun i hi x hx => hi₀ x (antitone_nat_of_succ_le H.nested hi hx)⟩

theorem subend_subset_closedBall_iff_forall_rayLength_le {g : SmoothRiemannianMetric I3 W}
    {H : FiniteHorn g} {i : ℕ} {r : ℝ}
    (hrays : ∀ x ∈ H.subend i, ∃ a : EndRay H.endpoint, a.point a.length = x) :
    H.subend i ⊆ {x : W | dist (x : UniformSpace.Completion W) H.endpoint ≤ r} ↔
      ∀ a : EndRay H.endpoint, a.point a.length ∈ H.subend i → a.length ≤ r := by
  constructor
  · intro h a ha
    have hthis : dist (a.point a.length : UniformSpace.Completion W) H.endpoint ≤ r := h ha
    rwa [a.radial a.length ⟨a.length_pos, le_rfl⟩] at hthis
  · intro h x hx
    obtain ⟨a, ha⟩ := hrays x hx
    have hle : a.length ≤ r := h a (by rwa [ha])
    have hthis : dist (a.point a.length : UniformSpace.Completion W) H.endpoint ≤ r := by
      rwa [a.radial a.length ⟨a.length_pos, le_rfl⟩]
    change dist (x : UniformSpace.Completion W) H.endpoint ≤ r
    rwa [← ha]

variable [SigmaCompactSpace W] in
theorem finite_horn_barriers_of_inner_sharpness_density {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (rho : ℕ → ℝ)
    (hd : ∀ i, rho i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto rho Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (rho i)) * rho i ^ 2)
      Filter.atTop Filter.atTop)
    (hinner : SubendRadialLevelInner g H rho) (hsharp : SubendRadialLevelSharpness g H rho)
    (hdense : RadialLevelDensity rho) : Nonempty (HornBarriers H ray rho) :=
  finite_horn_barriers_of_subendRadialNesting H ray rho hd hzero hlarge
    (subendRadialNesting_of_inner_sharpness_density hinner hsharp hdense)

variable [SigmaCompactSpace W] in
theorem finite_horn_barriers_of_raySubendScale_sharpness_density
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (raySubendScale g H ray i)) *
      raySubendScale g H ray i ^ 2) Filter.atTop Filter.atTop)
    (hsharp : SubendRadialLevelSharpness g H (raySubendScale g H ray))
    (hdense : RadialLevelDensity (raySubendScale g H ray)) :
    Nonempty (HornBarriers H ray (raySubendScale g H ray)) :=
  finite_horn_barriers_of_inner_sharpness_density H ray _ (raySubendScale_mem_Ioc g H ray)
    (tendsto_raySubendScale_zero g H ray) hlarge
    (subendRadialLevelInner_raySubendScale g H ray) hsharp hdense

variable [SigmaCompactSpace W] in
theorem finite_horn_barriers_of_raySubendScale_sharpness_ratio
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (raySubendScale g H ray i)) *
      raySubendScale g H ray i ^ 2) Filter.atTop Filter.atTop)
    (hsharp : SubendRadialLevelSharpness g H (raySubendScale g H ray))
    (hratio : Filter.Tendsto (fun j : ℕ =>
      raySubendScale g H ray j / raySubendScale g H ray (j + 1)) Filter.atTop (nhds 1)) :
    Nonempty (HornBarriers H ray (raySubendScale g H ray)) :=
  finite_horn_barriers_of_raySubendScale_sharpness_density H ray hlarge hsharp
    (radialLevelDensity_raySubendScale_of_ratio_tendsto_one hratio)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
