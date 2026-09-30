import DifferentialGeometry.Geometry.Metric.RadialConeIdentities
import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Choose

set_option autoImplicit false

namespace GC.MetricGeometry

open Set Filter Metric
open scoped Topology NNReal

universe u v
variable {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
variable {Y : Type v} [MetricSpace Y] [ProperSpace Y]
variable {o : ∀ i, X i} {p : Y} {R ε : ℕ → ℝ}

theorem nonempty_radialConeData_of_pointed_approximations
    (f : ∀ i, PointedBallApprox (o i) p (R i) (ε i))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (H : ∀ i, RadialConeData (o i)) : Nonempty (RadialConeData p) := by
  classical
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  let z (i : ℕ) (y : Y) : BallCarrier (o i) (R i) :=
    if h : ∃ x : BallCarrier (o i) (R i), dist y ((f i).toFun x) < ε i then h.choose
    else ⟨o i, by simpa using ((f i).error_pos.trans (f i).error_lt_radius).le⟩
  have hεone : ∀ᶠ i in atTop, ε i ≤ 1 :=
    hε.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  have hz (y : Y) : ∀ᶠ i in atTop, dist y ((f i).toFun (z i y)) < ε i := by
    filter_upwards [hR.eventually (eventually_ge_atTop (dist y p + 1)), hεone] with i hi he
    have hex := (f i).coverage y (by linarith)
    simpa only [z, dite_eq_left hex] using hex.choose_spec
  have hzconv (y : Y) : Tendsto (fun i => (f i).toFun (z i y)) atTop (𝓝 y) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) _ hε
    exact (hz y).mono (fun i hi => by simpa only [dist_comm] using hi.le)
  have hzd (x y : Y) :
      Tendsto (fun i => dist (z i x).val (z i y).val) atTop (𝓝 (dist x y)) := by
    have hd : Tendsto (fun i => dist (dist ((f i).toFun (z i x)) ((f i).toFun (z i y)))
        (dist (z i x).val (z i y).val)) atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) _ hε
      exact Eventually.of_forall (fun i => by
        simpa only [Real.dist_eq] using ((f i).distortion (z i x) (z i y)).le)
    exact ((hzconv x).dist (hzconv y)).congr_dist hd
  have hzr (y : Y) :
      Tendsto (fun i => dist (o i) (z i y).val) atTop (𝓝 (dist p y)) := by
    have hd : Tendsto (fun i => dist (dist p ((f i).toFun (z i y)))
        (dist (o i) (z i y).val)) atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) _ hε
      exact Eventually.of_forall (fun i => by
        simpa only [Real.dist_eq, dist_comm p, dist_comm (o i)] using ((f i).radial_error (z i y)).le)
    exact (tendsto_const_nhds.dist (hzconv y)).congr_dist hd
  have hzbound (y : Y) : ∀ᶠ i in atTop, dist (o i) (z i y).val ≤ dist p y + 2 :=
    (hzr y).eventually (eventually_le_nhds (by linarith : dist p y < dist p y + 2))
  let g (i : ℕ) (t : ℝ≥0) (y : Y) : Y :=
    if hx : dist ((H i).map t (z i y).val) (o i) ≤ R i then
      (f i).toFun ⟨(H i).map t (z i y).val, hx⟩ else p
  have hdom (t : ℝ≥0) (y : Y) :
      ∀ᶠ i in atTop, dist ((H i).map t (z i y).val) (o i) ≤ R i := by
    filter_upwards [hzbound y, hR.eventually (eventually_ge_atTop ((t : ℝ) * (dist p y + 2)))]
      with i hi hRi
    rw [dist_comm, (H i).dist_apex]
    exact (mul_le_mul_of_nonneg_left hi t.coe_nonneg).trans hRi
  have hg (i : ℕ) (t : ℝ≥0) (y : Y)
      (hx : dist ((H i).map t (z i y).val) (o i) ≤ R i) :
      g i t y = (f i).toFun ⟨(H i).map t (z i y).val, hx⟩ := by
    simp only [g, dite_eq_left hx]
  have hcompact (t : ℝ≥0) (y : Y) :
      ∃ w ∈ closedBall p ((t : ℝ) * (dist p y + 2) + 1),
        Tendsto (fun i => g i t y) U (𝓝 w) := by
    apply (isCompact_closedBall p ((t : ℝ) * (dist p y + 2) + 1)).ultrafilter_le_nhds
      (Ultrafilter.map (fun i => g i t y) U)
    apply le_principal_iff.mpr
    change ∀ᶠ i in (U : Filter ℕ), g i t y ∈ closedBall p ((t : ℝ) * (dist p y + 2) + 1)
    apply hU
    filter_upwards [hdom t y, hzbound y, hεone] with i hi hiz hie
    rw [hg i t y hi]
    have hr := (f i).radial_upper ⟨(H i).map t (z i y).val, hi⟩
    rw [dist_comm ((H i).map t (z i y).val), (H i).dist_apex] at hr
    have hm := mul_le_mul_of_nonneg_left hiz t.coe_nonneg
    change dist ((f i).toFun ⟨(H i).map t (z i y).val, hi⟩) p ≤ _
    linarith
  choose G hGball hGconv using hcompact
  refine ⟨⟨G, ?_, ?_, ?_⟩⟩
  · intro y
    have hz0 (i : ℕ) : g i 0 y = p := by
      have hpos : dist ((H i).map 0 (z i y).val) (o i) ≤ R i := by
        rw [(H i).map_zero, dist_self]
        exact ((f i).error_pos.trans (f i).error_lt_radius).le
      rw [hg i 0 y hpos]
      simpa only [(H i).map_zero] using (f i).basepoint
    have hh : Tendsto (fun i => g i 0 y) U (𝓝 p) := by
      simpa only [hz0] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => p) U (𝓝 p))
    exact tendsto_nhds_unique (hGconv 0 y) hh
  · intro y
    have hz1 (i : ℕ) : g i 1 y = (f i).toFun (z i y) := by
      have hpos : dist ((H i).map 1 (z i y).val) (o i) ≤ R i := by
        rw [(H i).map_one]
        exact (z i y).property
      rw [hg i 1 y hpos]
      simp only [(H i).map_one]
    have hh : Tendsto (fun i => g i 1 y) U (𝓝 y) := by
      simpa only [hz1] using (hzconv y).mono_left hU
    exact tendsto_nhds_unique (hGconv 1 y) hh
  · intro s t x y
    have hd : Tendsto (fun i => dist (dist (g i s x) (g i t y))
        (dist ((H i).map s (z i x).val) ((H i).map t (z i y).val))) U (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) _ (hε.mono_left hU)
      apply hU
      filter_upwards [hdom s x, hdom t y] with i hix hiy
      rw [hg i s x hix, hg i t y hiy]
      simpa only [Real.dist_eq] using
        ((f i).distortion ⟨(H i).map s (z i x).val, hix⟩ ⟨(H i).map t (z i y).val, hiy⟩).le
    have hl := (((hGconv s x).dist (hGconv t y)).congr_dist hd).pow 2
    have hrx := (hzr x).mono_left hU
    have hry := (hzr y).mono_left hU
    have hxy := (hzd x y).mono_left hU
    have hk : Tendsto (fun i => radialConeKernel (o i) (z i x).val (z i y).val)
        U (𝓝 (radialConeKernel p x y)) := by
      exact ((hrx.pow 2).add (hry.pow 2) |>.sub (hxy.pow 2)).div_const 2
    have hr := ((hrx.pow 2).const_mul ((s : ℝ) ^ 2)).add
      ((hry.pow 2).const_mul ((t : ℝ) ^ 2)) |>.sub (hk.const_mul (2 * (s : ℝ) * (t : ℝ)))
    apply tendsto_nhds_unique hl
    convert hr using 1
    funext i
    exact (H i).dist_sq s t (z i x).val (z i y).val

theorem PointedGHConverges.nonempty_radialConeData
    (h : PointedGHConverges o p) (H : ∀ i, RadialConeData (o i)) :
    Nonempty (RadialConeData p) := by
  classical
  let r : ℕ → ℝ := fun i => (i : ℝ) + 1
  let e : ℕ → ℝ := fun i => (1 / ((i : ℝ) + 1)) / 100
  have hr : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hepos (i : ℕ) : 0 < e i := by dsimp [e]; positivity
  have her (i : ℕ) : e i < r i := by
    have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
    have hh : 1 / ((i : ℝ) + 1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    dsimp [e, r]
    linarith
  have hezero : Tendsto e atTop (𝓝 0) := by
    simpa only [zero_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 100
  obtain ⟨β, _, hf⟩ := extraction_forall_of_eventually
    (fun i => h.eventually_approx (hepos i) (her i))
  exact nonempty_radialConeData_of_pointed_approximations
    (fun i => Classical.choice (hf i)) hr hezero (fun i => H (β i))

end GC.MetricGeometry
