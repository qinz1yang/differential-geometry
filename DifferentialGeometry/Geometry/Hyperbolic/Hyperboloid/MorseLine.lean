import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.QuasiGeodesicBoundary
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.KleinGeodesic
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.AsymptoticRays
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

open scoped Topology

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem tendsto_dist_of_quasi_geodesic (q : ℝ → Hyperboloid E) {L C : ℝ}
    (hL : 1 ≤ L)
    (hquasi : ∀ s t : ℝ, L⁻¹ * dist s t - C ≤ dist (q s) (q t) ∧
      dist (q s) (q t) ≤ L * dist s t + C) :
    Filter.Tendsto (fun t => dist (q 0) (q t)) Filter.atTop Filter.atTop := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [Filter.eventually_ge_atTop (max 0 (L * (b + C)))] with t ht
  have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
  have hmul := mul_le_mul_of_nonneg_left ((le_max_right _ _).trans ht) (inv_pos.mpr hLp).le
  rw [← mul_assoc, inv_mul_cancel₀ hLp.ne', one_mul] at hmul
  have hlo := (hquasi 0 t).1
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg ht0] at hlo
  linarith

private theorem quasi_geodesic_endpoints_ne [FiniteDimensional ℝ E]
    (q : ℝ → Hyperboloid E) {L C : ℝ} (hL : 1 ≤ L) (hC : 0 ≤ C) (hq : Continuous q)
    (hquasi : ∀ s t : ℝ, L⁻¹ * dist s t - C ≤ dist (q s) (q t) ∧
      dist (q s) (q t) ≤ L * dist s t + C)
    (ξminus ξplus : Metric.sphere (0 : E) 1)
    (hminus : Filter.Tendsto (fun t => (kleinHomeomorph (q t) : E)) Filter.atBot (𝓝 (ξminus : E)))
    (hplus : Filter.Tendsto (fun t => (kleinHomeomorph (q t) : E)) Filter.atTop (𝓝 (ξplus : E))) :
    ξminus ≠ ξplus := by
  let R := C + 1 + Real.log (4 * L ^ 2)
  let D := (2 * L ^ 2 + 1) * R + (L ^ 2 + 1) * C + 1
  let B := L ^ 2 * D + (L ^ 2 + 1) * C
  let K := 2 * (B + 1)
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hLsq : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
  have hlog : 0 ≤ Real.log (4 * L ^ 2) := Real.log_nonneg (by nlinarith)
  have hK : 0 ≤ K := by
    dsimp only [K, B, D, R]
    positivity
  obtain ⟨v, hv, ho, hnear⟩ := exists_geodesicLine_close_of_quasi_geodesic q hL hC
    hq.continuousOn (fun s _ t _ => hquasi s t)
  change ∀ t ∈ Set.Ici (0 : ℝ),
    dist (q t) (geodesicLine (q 0) v hv ho (dist (q 0) (q t))) ≤ K at hnear
  let qn : ℝ → Hyperboloid E := fun t => q (-t)
  have hqn : Continuous qn := hq.comp continuous_neg
  have hqnquasi : ∀ s t : ℝ, L⁻¹ * dist s t - C ≤ dist (qn s) (qn t) ∧
      dist (qn s) (qn t) ≤ L * dist s t + C := by
    intro s t
    simpa only [qn, dist_neg_neg] using hquasi (-s) (-t)
  obtain ⟨w, hw, how, hnear'⟩ := exists_geodesicLine_close_of_quasi_geodesic qn hL hC
    hqn.continuousOn (fun s _ t _ => hqnquasi s t)
  have hqn0 : qn 0 = q 0 := by simp only [qn, neg_zero]
  have how' : lorentzForm E ((q 0).time, (q 0).space) w = 0 := by simpa only [hqn0] using how
  have hnearN : ∀ t ∈ Set.Ici (0 : ℝ),
      dist (qn t) (geodesicLine (q 0) w hw how' (dist (q 0) (qn t))) ≤ K := by
    simpa only [hqn0] using hnear'
  have hrad := tendsto_dist_of_quasi_geodesic q hL hquasi
  have hradN : Filter.Tendsto (fun t => dist (q 0) (qn t)) Filter.atTop Filter.atTop := by
    simpa only [hqn0] using tendsto_dist_of_quasi_geodesic qn hL hqnquasi
  have hlim : Filter.Tendsto (fun t => (kleinHomeomorph (q t) : E)) Filter.atTop
      (𝓝 (((q 0).time + v.1)⁻¹ • ((q 0).space + v.2))) := by
    apply tendsto_kleinHomeomorph_of_dist_bounded
      (x := fun t => geodesicLine (q 0) v hv ho (dist (q 0) (q t)))
      (ξ := ⟨((q 0).time + v.1)⁻¹ • ((q 0).space + v.2), by
        simpa only [Metric.mem_sphere, dist_zero_right] using norm_geodesicLine_forward_endpoint (q 0) v hv ho⟩)
      (C := K)
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
      exact (dist_comm _ _).le.trans (hnear t ht)
    · exact (tendsto_kleinHomeomorph_geodesicLine_atTop (q 0) v hv ho).comp hrad
  have hlimN : Filter.Tendsto (fun t => (kleinHomeomorph (qn t) : E)) Filter.atTop
      (𝓝 (((q 0).time + w.1)⁻¹ • ((q 0).space + w.2))) := by
    apply tendsto_kleinHomeomorph_of_dist_bounded
      (x := fun t => geodesicLine (q 0) w hw how' (dist (q 0) (qn t)))
      (ξ := ⟨((q 0).time + w.1)⁻¹ • ((q 0).space + w.2), by
        simpa only [Metric.mem_sphere, dist_zero_right] using norm_geodesicLine_forward_endpoint (q 0) w hw how'⟩)
      (C := K)
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
      exact (dist_comm _ _).le.trans (hnearN t ht)
    · exact (tendsto_kleinHomeomorph_geodesicLine_atTop (q 0) w hw how').comp hradN
  have heplus := tendsto_nhds_unique hlim hplus
  have heminus := tendsto_nhds_unique hlimN (hminus.comp Filter.tendsto_neg_atTop_atBot)
  intro heq
  have he : ((q 0).time + v.1)⁻¹ • ((q 0).space + v.2) =
      ((q 0).time + w.1)⁻¹ • ((q 0).space + w.2) :=
    heplus.trans ((congrArg Subtype.val heq).symm.trans heminus.symm)
  let t := L * (2 * K + C + 1)
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  obtain ⟨s, hs, hrs⟩ := intermediate_value_Ici
    ((continuous_const.dist hqn).continuousOn) hradN
    (show dist (q 0) (q t) ∈ Set.Ici (dist (q 0) (qn 0)) by rw [hqn0, dist_self]; exact dist_nonneg)
  change dist (q 0) (qn s) = dist (q 0) (q t) at hrs
  have hline : geodesicLine (q 0) v hv ho (dist (q 0) (q t)) =
      geodesicLine (q 0) w hw how' (dist (q 0) (q t)) :=
    dist_eq_zero.mp (le_antisymm
      ((dist_geodesicLine_le_of_forward_endpoint_eq (q 0) (q 0) v w hv ho hw how' he
        dist_nonneg).trans_eq (dist_self _)) dist_nonneg)
  have hclose : dist (q t) (qn s) ≤ 2 * K := by
    have hn := hnearN s hs
    rw [hrs] at hn
    calc
      dist (q t) (qn s) ≤ dist (q t) (geodesicLine (q 0) v hv ho (dist (q 0) (q t))) +
          dist (geodesicLine (q 0) v hv ho (dist (q 0) (q t))) (qn s) := dist_triangle _ _ _
      _ ≤ K + K := add_le_add (hnear t ht) (by simpa only [hline, dist_comm] using hn)
      _ = 2 * K := by ring
  have hlo := (hquasi t (-s)).1
  have hst : 0 ≤ t + s := add_nonneg ht hs
  rw [Real.dist_eq, sub_neg_eq_add, abs_of_nonneg hst] at hlo
  have hprod : L⁻¹ * t = 2 * K + C + 1 := by
    dsimp only [t]
    rw [← mul_assoc, inv_mul_cancel₀ hLp.ne', one_mul]
  have hbound := mul_nonneg (inv_pos.mpr hLp).le hs
  change dist (q t) (q (-s)) ≤ 2 * K at hclose
  nlinarith

private theorem exists_mem_line_dist_le [FiniteDimensional ℝ E]
    (q : ℝ → Hyperboloid E) (c : ℝ → Hyperboloid E)
    (ξminus ξplus : Metric.sphere (0 : E) 1) (B : ℝ) (hB : 0 ≤ B)
    (hminus : Filter.Tendsto (fun t => (kleinHomeomorph (q t) : E)) Filter.atBot (𝓝 (ξminus : E)))
    (hplus : Filter.Tendsto (fun t => (kleinHomeomorph (q t) : E)) Filter.atTop (𝓝 (ξplus : E)))
    (hchord : (fun z : Hyperboloid E => (kleinHomeomorph z : E)) '' Set.range c =
      openSegment ℝ (ξminus : E) (ξplus : E))
    (hseg : ∀ n : ℕ, Metric.hausdorffEDist (q '' Set.Icc (-(n : ℝ)) n)
      {z | dist (q (-(n : ℝ))) z + dist z (q n) = dist (q (-(n : ℝ))) (q n)} ≤
        ENNReal.ofReal B) (t : ℝ) :
    ∃ s : ℝ, dist (q t) (c s) ≤ B + 1 := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt |t|
  let T : ℕ → ℝ := fun n => (n + N : ℕ)
  have hT : Filter.Tendsto T Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ))
      (fun n => by dsimp [T]; exact_mod_cast Nat.le_add_right n N) tendsto_natCast_atTop_atTop
  have hleft := hminus.comp (Filter.tendsto_neg_atTop_atBot.comp hT)
  have hright := hplus.comp hT
  have hqt (n : ℕ) : q t ∈ q '' Set.Icc (-(T n)) (T n) := by
    refine ⟨t, ?_, rfl⟩
    have hbound : |t| ≤ T n := by
      dsimp [T]
      exact hN.le.trans (by exact_mod_cast Nat.le_add_left N n)
    exact ⟨(abs_le.mp hbound).1, (abs_le.mp hbound).2⟩
  have hw (n : ℕ) : ∃ z : Hyperboloid E,
      z ∈ {z | dist (q (-(T n))) z + dist z (q (T n)) = dist (q (-(T n))) (q (T n))} ∧
      dist (q t) z < B + 1 := by
    have hlt := (hseg (n + N)).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hB).mpr (by linarith : B < B + 1))
    obtain ⟨z, hz, hd⟩ := Metric.exists_edist_lt_of_hausdorffEDist_lt (hqt n) hlt
    exact ⟨z, hz, edist_lt_ofReal.mp hd⟩
  choose z hz hdist using hw
  have hcoeff (n : ℕ) : ∃ a ∈ Set.Icc (0 : ℝ) 1,
      (1 - a) • (kleinHomeomorph (q (-(T n))) : E) +
        a • (kleinHomeomorph (q (T n)) : E) = (kleinHomeomorph (z n) : E) := by
    have hmem : (kleinHomeomorph (z n) : E) ∈
        segment ℝ (kleinHomeomorph (q (-(T n))) : E) (kleinHomeomorph (q (T n)) : E) := by
      rw [← kleinHomeomorph_image_metric_segment]
      exact ⟨z n, hz n, rfl⟩
    simpa only [segment_eq_image, Set.mem_image] using hmem
  choose a ha heq using hcoeff
  have hcompact := (isCompact_closedBall (q t) (B + 1)).prod (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))
  obtain ⟨p, hp, φ, hφ, hlim⟩ := hcompact.tendsto_subseq (x := fun n => (z n, a n)) (by
    intro n
    exact ⟨by simpa only [Metric.mem_closedBall, dist_comm] using (hdist n).le, ha n⟩)
  have hzlim : Filter.Tendsto (fun n => z (φ n)) Filter.atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hlim
  have halim : Filter.Tendsto (fun n => a (φ n)) Filter.atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hlim
  have hkz := (continuous_subtype_val.comp (kleinHomeomorph (E := E)).continuous).continuousAt.tendsto.comp hzlim
  have hcomb := (((tendsto_const_nhds (x := (1 : ℝ))).sub halim).smul (hleft.comp hφ.tendsto_atTop)).add
    (halim.smul (hright.comp hφ.tendsto_atTop))
  have hlimit : (1 - p.2) • (ξminus : E) + p.2 • (ξplus : E) = (kleinHomeomorph p.1 : E) :=
    tendsto_nhds_unique (hcomb.congr' (Filter.Eventually.of_forall fun n => heq (φ n))) hkz
  have hmember : (kleinHomeomorph p.1 : E) ∈ segment ℝ (ξminus : E) (ξplus : E) := by
    rw [segment_eq_image]
    exact ⟨p.2, hp.2, hlimit⟩
  have hkball : ‖(kleinHomeomorph p.1 : E)‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using (kleinHomeomorph p.1).property
  have hend (ξ : Metric.sphere (0 : E) 1) : (ξ : E) ≠ (kleinHomeomorph p.1 : E) := by
    intro he
    have hn : ‖(ξ : E)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using ξ.property
    rw [← he, hn] at hkball
    exact (lt_irrefl _ hkball)
  have hopen := mem_openSegment_of_ne_left_right (hend ξminus) (hend ξplus) hmember
  rw [← hchord] at hopen
  obtain ⟨y, ⟨s, rfl⟩, he⟩ := hopen
  have he' : c s = p.1 := (kleinHomeomorph (E := E)).injective (Subtype.ext he)
  refine ⟨s, ?_⟩
  rw [he', dist_comm]
  exact hp.1

private theorem exists_quasi_geodesic_dist_le
    (q : ℝ → Hyperboloid E) (c : ℝ → Hyperboloid E)
    (ξminus ξplus : Metric.sphere (0 : E) 1) (L C B : ℝ) (hL : 1 ≤ L) (hB : 0 ≤ B)
    (hq : Continuous q)
    (hquasi : ∀ s t : ℝ, L⁻¹ * dist s t - C ≤ dist (q s) (q t) ∧
      dist (q s) (q t) ≤ L * dist s t + C)
    (hminus : Filter.Tendsto (fun t => (kleinHomeomorph (q t) : E)) Filter.atBot (𝓝 (ξminus : E)))
    (hplus : Filter.Tendsto (fun t => (kleinHomeomorph (q t) : E)) Filter.atTop (𝓝 (ξplus : E)))
    (hchord : (fun z : Hyperboloid E => (kleinHomeomorph z : E)) '' Set.range c =
      openSegment ℝ (ξminus : E) (ξplus : E))
    (hseg : ∀ n : ℕ, Metric.hausdorffEDist (q '' Set.Icc (-(n : ℝ)) n)
      {z | dist (q (-(n : ℝ))) z + dist z (q n) = dist (q (-(n : ℝ))) (q n)} ≤
        ENNReal.ofReal B) (s : ℝ) :
    ∃ t : ℝ, dist (c s) (q t) ≤ B + 1 := by
  classical
  have hpoint : (kleinHomeomorph (c s) : E) ∈ openSegment ℝ (ξminus : E) (ξplus : E) := by
    rw [← hchord]
    exact ⟨c s, ⟨s, rfl⟩, rfl⟩
  rw [openSegment_eq_image] at hpoint
  obtain ⟨a, ha, hea⟩ := hpoint
  let k (n : ℕ) : E := (1 - a) • (kleinHomeomorph (q (-(n : ℝ))) : E) +
    a • (kleinHomeomorph (q n) : E)
  have hk (n : ℕ) : k n ∈ Metric.ball (0 : E) 1 :=
    (convex_ball (0 : E) 1) (kleinHomeomorph (q (-(n : ℝ)))).property
      (kleinHomeomorph (q n)).property (sub_nonneg.mpr ha.2.le) ha.1.le (sub_add_cancel 1 a)
  let z (n : ℕ) : Hyperboloid E := kleinHomeomorph.symm ⟨k n, hk n⟩
  have hzK (n : ℕ) : (kleinHomeomorph (z n) : E) = k n :=
    congrArg Subtype.val ((kleinHomeomorph (E := E)).apply_symm_apply ⟨k n, hk n⟩)
  have hleft := hminus.comp (Filter.tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hright := hplus.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hkLim : Filter.Tendsto k Filter.atTop (𝓝 (kleinHomeomorph (c s) : E)) := by
    rw [← hea]
    exact ((tendsto_const_nhds.smul hleft).add (tendsto_const_nhds.smul hright))
  have hzLim : Filter.Tendsto z Filter.atTop (𝓝 (c s)) := by
    have hs := ((kleinHomeomorph (E := E)).symm.continuous.continuousAt.tendsto).comp
      ((tendsto_subtype_rng (f := fun n => (⟨k n, hk n⟩ : Metric.ball (0 : E) 1))
        (x := kleinHomeomorph (c s))).mpr hkLim)
    simpa only [Homeomorph.symm_apply_apply, Function.comp_def, z] using hs
  have hzseg (n : ℕ) : z n ∈
      {z | dist (q (-(n : ℝ))) z + dist z (q n) = dist (q (-(n : ℝ))) (q n)} := by
    have hkmem : k n ∈ segment ℝ (kleinHomeomorph (q (-(n : ℝ))) : E)
        (kleinHomeomorph (q n) : E) := by
      rw [segment_eq_image]
      exact ⟨a, ⟨ha.1.le, ha.2.le⟩, rfl⟩
    rw [← kleinHomeomorph_image_metric_segment] at hkmem
    obtain ⟨w, hw, he⟩ := hkmem
    have hwz : w = z n := (kleinHomeomorph (E := E)).injective
      (Subtype.ext (he.trans (hzK n).symm))
    exact hwz ▸ hw
  have hw (n : ℕ) : ∃ t ∈ Set.Icc (-(n : ℝ)) n, dist (z n) (q t) < B + 1 := by
    have hlt := (hseg n).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hB).mpr (by linarith : B < B + 1))
    rw [Metric.hausdorffEDist_comm] at hlt
    obtain ⟨w, ⟨t, ht, rfl⟩, hd⟩ := Metric.exists_edist_lt_of_hausdorffEDist_lt (hzseg n) hlt
    exact ⟨t, ht, edist_lt_ofReal.mp hd⟩
  choose t ht hdist using hw
  let P := L * (dist (q 0) (c s) + 1 + (B + 1) + C)
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hevent : ∀ᶠ n in Filter.atTop, t n ∈ Set.Icc (-P) P := by
    have hdLim : Filter.Tendsto (fun n => dist (z n) (c s)) Filter.atTop (𝓝 0) := by
      simpa only [dist_self] using hzLim.dist (tendsto_const_nhds (x := c s))
    filter_upwards [hdLim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn
    have hupper : dist (q 0) (q (t n)) ≤ dist (q 0) (c s) + 1 + (B + 1) := by
      calc
        dist (q 0) (q (t n)) ≤ dist (q 0) (c s) + dist (c s) (q (t n)) := dist_triangle _ _ _
        _ ≤ dist (q 0) (c s) + (dist (c s) (z n) + dist (z n) (q (t n))) :=
          add_le_add le_rfl (dist_triangle (c s) (z n) (q (t n)))
        _ ≤ dist (q 0) (c s) + 1 + (B + 1) := by rw [dist_comm (c s) (z n)]; linarith [hdist n]
    have hlo := (hquasi 0 (t n)).1
    rw [Real.dist_eq, zero_sub, abs_neg] at hlo
    have hmul := mul_le_mul_of_nonneg_left
      (show L⁻¹ * |t n| ≤ dist (q 0) (c s) + 1 + (B + 1) + C by linarith) hLp.le
    rw [← mul_assoc, mul_inv_cancel₀ hLp.ne', one_mul] at hmul
    exact abs_le.mp hmul
  obtain ⟨u, hu, φ, hφ, hlim⟩ := (isCompact_Icc : IsCompact (Set.Icc (-P) P)).tendsto_subseq'
    hevent.frequently
  refine ⟨u, ?_⟩
  apply le_of_tendsto ((hzLim.comp hφ.tendsto_atTop).dist (hq.continuousAt.tendsto.comp hlim))
  exact Filter.Eventually.of_forall fun n => (hdist (φ n)).le


theorem morse_lemma_line [FiniteDimensional ℝ E] (L C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (q : ℝ → Hyperboloid E), Continuous q →
      (∀ s t : ℝ, L⁻¹ * dist s t - C ≤ dist (q s) (q t) ∧
        dist (q s) (q t) ≤ L * dist s t + C) →
      ∃ (ξminus ξplus : Metric.sphere (0 : E) 1), ξminus ≠ ξplus ∧
        Filter.Tendsto (fun t => (kleinHomeomorph (q t) : E)) Filter.atBot (𝓝 (ξminus : E)) ∧
        Filter.Tendsto (fun t => (kleinHomeomorph (q t) : E)) Filter.atTop (𝓝 (ξplus : E)) ∧
        ∃ (x : Hyperboloid E) (v : ℝ × E) (hv : lorentzForm E v v = 1)
          (ho : lorentzForm E (x.time, x.space) v = 0),
          (x.time - v.1)⁻¹ • (x.space - v.2) = (ξminus : E) ∧
          (x.time + v.1)⁻¹ • (x.space + v.2) = (ξplus : E) ∧
          Metric.hausdorffEDist (Set.range q) (Set.range (geodesicLine x v hv ho)) ≤
            ENNReal.ofReal R := by
  let R₀ := C + 1 + Real.log (4 * L ^ 2)
  let D := (2 * L ^ 2 + 1) * R₀ + (L ^ 2 + 1) * C + 1
  let B := L ^ 2 * D + (L ^ 2 + 1) * C
  have hLsq : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
  have hlog : 0 ≤ Real.log (4 * L ^ 2) := Real.log_nonneg (by nlinarith)
  have hB : 0 ≤ B := by dsimp only [B, D, R₀]; positivity
  refine ⟨B + 1, by positivity, ?_⟩
  intro q hq hquasi
  obtain ⟨ξplus, hplus, _⟩ := exists_unique_tendsto_kleinHomeomorph_of_quasi_geodesic
    q hL hC hq.continuousOn (fun s _ t _ => hquasi s t)
  have hqn : Continuous (fun t : ℝ => q (-t)) := hq.comp continuous_neg
  have hqnquasi : ∀ s t : ℝ, L⁻¹ * dist s t - C ≤ dist (q (-s)) (q (-t)) ∧
      dist (q (-s)) (q (-t)) ≤ L * dist s t + C := by
    intro s t
    simpa only [dist_neg_neg] using hquasi (-s) (-t)
  obtain ⟨ξminus, hminusN, _⟩ := exists_unique_tendsto_kleinHomeomorph_of_quasi_geodesic
    (fun t => q (-t)) hL hC hqn.continuousOn (fun s _ t _ => hqnquasi s t)
  have hminus : Filter.Tendsto (fun t => (kleinHomeomorph (q t) : E)) Filter.atBot (𝓝 (ξminus : E)) := by
    simpa only [Function.comp_def, neg_neg] using hminusN.comp Filter.tendsto_neg_atBot_atTop
  have hne := quasi_geodesic_endpoints_ne q hL hC hq hquasi ξminus ξplus hminus hplus
  obtain ⟨x, v, hv, ho, hback, hforward, hchord⟩ :=
    exists_geodesicLine_with_endpoints ξminus ξplus hne
  have hseg (n : ℕ) : Metric.hausdorffEDist (q '' Set.Icc (-(n : ℝ)) n)
      {z | dist (q (-(n : ℝ))) z + dist z (q n) = dist (q (-(n : ℝ))) (q n)} ≤
        ENNReal.ofReal B :=
    morse_lemma L C hL hC (-(n : ℝ)) n (by linarith [Nat.cast_nonneg (α := ℝ) n]) q hq.continuousOn
      (fun s _ t _ => hquasi s t)
  refine ⟨ξminus, ξplus, hne, hminus, hplus, x, v, hv, ho, hback, hforward, ?_⟩
  apply Metric.hausdorffEDist_le_of_mem_edist
  · rintro _ ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := exists_mem_line_dist_le q (geodesicLine x v hv ho)
      ξminus ξplus B hB hminus hplus hchord hseg t
    refine ⟨geodesicLine x v hv ho s, ⟨s, rfl⟩, ?_⟩
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal hs
  · rintro _ ⟨s, rfl⟩
    obtain ⟨t, ht⟩ := exists_quasi_geodesic_dist_le q (geodesicLine x v hv ho)
      ξminus ξplus L C B hL hB hq hquasi hminus hplus hchord hseg s
    refine ⟨q t, ⟨t, rfl⟩, ?_⟩
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal ht

end DifferentialGeometry.Hyperboloid
