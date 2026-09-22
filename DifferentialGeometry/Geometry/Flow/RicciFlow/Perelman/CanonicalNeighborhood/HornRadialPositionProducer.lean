import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBarriersRadialNesting
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.RadialLevelCalibration

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal

universe u

def RadialScaleWindowCover (rho : ℕ → ℝ) (e : ℝ) : Prop :=
  ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a < a₀ →
    ∃ j : ℕ, a ≤ rho j ∧ rho j < (1 + e) * a

def RadialScaleCover (rho : ℕ → ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → e < 1 / 10 → RadialScaleWindowCover rho e

theorem radialScaleWindowCover_mono {rho : ℕ → ℝ} {e e' : ℝ} (hee : e ≤ e')
    (h : RadialScaleWindowCover rho e) : RadialScaleWindowCover rho e' := by
  obtain ⟨a₀, ha₀, hcov⟩ := h
  refine ⟨a₀, ha₀, fun a ha ha' => ?_⟩
  obtain ⟨j, hlo, hhi⟩ := hcov a ha ha'
  exact ⟨j, hlo, lt_of_lt_of_le hhi (mul_le_mul_of_nonneg_right (by linarith) ha.le)⟩

theorem radialScaleCover_of_one_div_nat :
    RadialScaleCover (fun j : ℕ => 1 / ((j : ℝ) + 1)) := by
  intro e he he10
  have h1e : (0 : ℝ) < 1 + e := by linarith
  refine ⟨e / (1 + e), by positivity, fun a ha ha' => ?_⟩
  have ha_le_one : a ≤ 1 := by
    have hlt : e / (1 + e) < 1 := by
      rw [div_lt_one h1e]
      linarith
    linarith
  set m : ℕ := Nat.floor (1 / a) with hmdef
  have hm1 : 1 ≤ m := by
    rw [hmdef, Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ 1 / a)]
    push_cast
    exact (one_le_div ha).mpr ha_le_one
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hmle : (m : ℝ) ≤ 1 / a := by
    rw [hmdef]
    exact Nat.floor_le (by positivity)
  have hmlt : 1 / a < (m : ℝ) + 1 := by
    rw [hmdef]
    exact Nat.lt_floor_add_one _
  have hcast : (((m - 1 : ℕ) : ℝ) + 1) = (m : ℝ) := by
    have h : (((m - 1 : ℕ) : ℝ)) = (m : ℝ) - 1 :=
      Nat.cast_pred (Nat.lt_of_lt_of_le Nat.zero_lt_one hm1)
    linarith
  refine ⟨m - 1, ?_, ?_⟩
  · change a ≤ 1 / (((m - 1 : ℕ) : ℝ) + 1)
    rw [hcast, le_div_iff₀ hmpos]
    have h := (le_div_iff₀ ha).mp hmle
    nlinarith [h]
  · change 1 / (((m - 1 : ℕ) : ℝ) + 1) < (1 + e) * a
    rw [hcast, div_lt_iff₀ hmpos]
    have h := (div_lt_iff₀ ha).mp hmlt
    have hkey : 1 ≤ (1 + e) * (1 - a) := by
      have h2 : 1 / (1 + e) ≤ 1 - a := by
        rw [div_le_iff₀ h1e]
        have h3 := (lt_div_iff₀ h1e).mp ha'
        nlinarith [h3]
      have h3 := mul_le_mul_of_nonneg_left h2 h1e.le
      have hone : (1 + e) * (1 / (1 + e)) = 1 := by field_simp
      linarith [h3, hone]
    nlinarith [h, hkey, ha]

theorem not_radialScaleWindowCover_of_sparseLevels {e : ℝ} (he : 0 < e) (he8 : 1 + e < 8) :
    ¬ RadialScaleWindowCover (fun j : ℕ => (1 / 8 : ℝ) ^ j) e := by
  rintro ⟨a₀, ha₀, hcov⟩
  have hlim : Filter.Tendsto (fun k : ℕ => (1 / 8 : ℝ) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev : ∀ᶠ k : ℕ in Filter.atTop, (1 / 8 : ℝ) ^ k < (1 + e) * a₀ :=
    hlim.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < (1 + e) * a₀))
  obtain ⟨k, hk⟩ := hev.exists
  have he' : (0 : ℝ) < 1 + e := by linarith
  set a : ℝ := (1 / 8 : ℝ) ^ k / (1 + e) with hadef
  have ha_pos : 0 < a := by
    rw [hadef]
    positivity
  have ha_lt : a < a₀ := by
    rw [hadef, div_lt_iff₀ he']
    linarith
  obtain ⟨j, hlo, hhi⟩ := hcov a ha_pos ha_lt
  have hjk : j ≤ k := by
    by_contra hcon
    have hkj : k + 1 ≤ j := by omega
    have hmono : (1 / 8 : ℝ) ^ j ≤ (1 / 8 : ℝ) ^ (k + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hkj
    have hlt : (1 / 8 : ℝ) ^ (k + 1) < (1 / 8 : ℝ) ^ k / (1 + e) := by
      rw [pow_succ, lt_div_iff₀ he']
      have hp : (0 : ℝ) < (1 / 8 : ℝ) ^ k := pow_pos (by norm_num) k
      nlinarith [hp, he8]
    rw [← hadef] at hlt
    linarith
  have hle : (1 / 8 : ℝ) ^ k ≤ (1 / 8 : ℝ) ^ j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hjk
  have hcontr : (1 / 8 : ℝ) ^ j < (1 / 8 : ℝ) ^ k := by
    have h := hhi
    rw [hadef, mul_div_cancel₀ _ (ne_of_gt he')] at h
    exact h
  linarith

theorem not_radialScaleCover_of_sparseLevels :
    ¬ RadialScaleCover (fun j : ℕ => (1 / 8 : ℝ) ^ j) :=
  fun h => not_radialScaleWindowCover_of_sparseLevels (e := 1 / 20) (by norm_num) (by norm_num)
    (h (1 / 20) (by norm_num) (by norm_num))

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

def SubendRadialScaleCover (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) : Prop :=
  ∀ e : ℝ, 0 < e → e < 1 / 10 → ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ a : ℝ, 0 < a → a < a₀ → ∃ j : ℕ,
      {x : W | dist (x : UniformSpace.Completion W) H.endpoint < a} ⊆ H.subend j ∧
      H.subend j ⊆ {x : W | dist (x : UniformSpace.Completion W) H.endpoint < (1 + e) * a}

omit [SigmaCompactSpace W] in
theorem subendRadialScaleCover_of_calibratedLevels {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (rho : ℕ → ℝ)
    (hinner : ∀ j : ℕ, ∀ x : W,
      dist (x : UniformSpace.Completion W) H.endpoint < rho j → x ∈ H.subend j)
    (houter : ∀ j : ℕ, H.subend j ⊆
      {x : W | dist (x : UniformSpace.Completion W) H.endpoint < rho j})
    (hcover : RadialScaleCover rho) : SubendRadialScaleCover g H := by
  intro e he he10
  obtain ⟨a₀, ha₀, hcov⟩ := hcover e he he10
  refine ⟨a₀, ha₀, fun a ha ha' => ?_⟩
  obtain ⟨j, hlo, hhi⟩ := hcov a ha ha'
  exact ⟨j, fun x hx => hinner j x (lt_of_lt_of_le hx hlo),
    fun x hx => lt_trans (houter j hx) hhi⟩

omit [SigmaCompactSpace W] in
theorem subendRadialNesting_of_subendRadialScaleCover {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (d : ℕ → ℝ) (hd : ∀ i : ℕ, 0 < d i)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0)) (h : SubendRadialScaleCover g H) :
    SubendRadialNesting g H d := by
  intro e he he10
  have h2 : 0 < e / 2 := by linarith
  have hden : (0 : ℝ) < 1 + e / 2 := by linarith
  have he' : 0 < e / 2 / (1 + e / 2) := div_pos h2 hden
  have he10' : e / 2 / (1 + e / 2) < 1 / 10 := by
    have hlt : e / 2 / (1 + e / 2) < e / 2 := by
      rw [div_lt_iff₀ hden]
      nlinarith [h2]
    linarith
  obtain ⟨a₀, ha₀, hcov⟩ := h (e / 2 / (1 + e / 2)) he' he10'
  have hratio : (0 : ℝ) < 1 + e / 2 := hden
  filter_upwards [hzero.eventually
    (eventually_lt_nhds (div_pos ha₀ hratio))] with i hi
  have hscale : 0 < (1 + e / 2) * d i := mul_pos (by linarith) (hd i)
  have hsmall : (1 + e / 2) * d i < a₀ := by
    have h := (lt_div_iff₀ hratio).mp hi
    nlinarith [h]
  obtain ⟨j, hlo, hhi⟩ := hcov ((1 + e / 2) * d i) hscale hsmall
  refine ⟨j, hlo, fun x hx => ?_⟩
  have hprod : (1 + e / 2 / (1 + e / 2)) * ((1 + e / 2) * d i) = (1 + e) * d i := by
    field_simp
    ring
  have h := hhi hx
  rwa [hprod] at h

omit [SigmaCompactSpace W] in
theorem subendRadialNesting_raySubendScale_of_subendRadialScaleCover
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (h : SubendRadialScaleCover g H) :
    SubendRadialNesting g H (raySubendScale g H ray) :=
  subendRadialNesting_of_subendRadialScaleCover H _
    (fun i => raySubendScale_pos g H ray i) (tendsto_raySubendScale_zero g H ray) h

omit [SigmaCompactSpace W] in
theorem hornRadialOuterPosition_of_subendRadialScaleCover {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (h : SubendRadialScaleCover g H) : HornRadialOuterPosition g H ray d :=
  hornRadialOuterPosition_of_subendRadialNesting H ray d hd hzero hlarge
    (subendRadialNesting_of_subendRadialScaleCover H d (fun i => (hd i).1) hzero h)

theorem hornRadialPosition_of_subendRadialScaleCover {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (h : SubendRadialScaleCover g H) : HornRadialPosition g H ray d :=
  hornRadialPosition_of_subendRadialNesting H ray d hd hzero hlarge
    (subendRadialNesting_of_subendRadialScaleCover H d (fun i => (hd i).1) hzero h)

theorem nonempty_hornBarriers_of_subendRadialScaleCover {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (h : SubendRadialScaleCover g H) : Nonempty (HornBarriers H ray d) :=
  finite_horn_barriers_of_subendRadialNesting H ray d hd hzero hlarge
    (subendRadialNesting_of_subendRadialScaleCover H d (fun i => (hd i).1) hzero h)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
