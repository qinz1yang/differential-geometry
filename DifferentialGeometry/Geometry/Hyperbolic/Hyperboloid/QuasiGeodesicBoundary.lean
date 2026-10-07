import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.GeodesicBoundary
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.GeodesicSegment
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.KleinConvergence
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Morse
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Proper
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Sequences

noncomputable section

open scoped Topology

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def originGeodesicLine (u : Metric.sphere (0 : E) 1) : ℝ → Hyperboloid E :=
  geodesicLine origin (0, (u : E))
    (by simp only [lorentzForm_apply, zero_mul, sub_zero, real_inner_self_eq_norm_sq,
      ← dist_zero_right, Metric.mem_sphere.mp u.property, one_pow])
    (by simp [lorentzForm_apply])

private theorem originGeodesicLine_zero (u : Metric.sphere (0 : E) 1) :
    originGeodesicLine u 0 = origin := geodesicLine_zero ..

private theorem originGeodesicLine_isometry (u : Metric.sphere (0 : E) 1) :
    Isometry (originGeodesicLine u) := isometry_geodesicLine _ _ _ _

private theorem continuous_originGeodesicLine (t : ℝ) :
    Continuous (fun u : Metric.sphere (0 : E) 1 => originGeodesicLine u t) := by
  have heq : (fun u : Metric.sphere (0 : E) 1 => originGeodesicLine u t) =
      ofSpace ∘ (fun u : Metric.sphere (0 : E) 1 => Real.sinh t • (u : E)) := by
    funext u
    apply ext
    simp only [originGeodesicLine, geodesicLine_space, origin_space, smul_zero,
      zero_add, Function.comp_apply, space_ofSpace]
  rw [heq]
  exact continuous_ofSpace.comp (continuous_const.smul continuous_subtype_val)

private theorem exists_originGeodesicLine {y : Hyperboloid E} (hy : origin ≠ y) :
    ∃ u : Metric.sphere (0 : E) 1, originGeodesicLine u (dist origin y) = y := by
  have hs : y.space ≠ 0 := by
    intro h
    apply hy
    apply ext
    exact h.symm
  let u : Metric.sphere (0 : E) 1 := ⟨NormedSpace.normalize y.space, by
    simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hs⟩
  refine ⟨u, ?_⟩
  apply ext
  simp only [originGeodesicLine, geodesicLine_space, origin_space, smul_zero, zero_add,
    sinh_dist_origin]
  exact NormedSpace.norm_smul_normalize y.space

private theorem dist_originGeodesicLine_radial_le (u : Metric.sphere (0 : E) 1)
    (x : Hyperboloid E) {s B : ℝ} (hs : 0 ≤ s) (hx : dist x (originGeodesicLine u s) ≤ B) :
    dist x (originGeodesicLine u (dist origin x)) ≤ 2 * B := by
  have hdist : dist origin (originGeodesicLine u s) = s := by
    rw [← originGeodesicLine_zero u, (originGeodesicLine_isometry u).dist_eq,
      Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hs]
  have hrad : dist (originGeodesicLine u s) (originGeodesicLine u (dist origin x)) ≤
      dist x (originGeodesicLine u s) := by
    rw [(originGeodesicLine_isometry u).dist_eq]
    simpa only [hdist, dist_comm (originGeodesicLine u s) x] using
      dist_dist_dist_le_right origin (originGeodesicLine u s) x
  calc
    dist x (originGeodesicLine u (dist origin x)) ≤
        dist x (originGeodesicLine u s) +
          dist (originGeodesicLine u s) (originGeodesicLine u (dist origin x)) := dist_triangle ..
    _ ≤ B + B := add_le_add hx (hrad.trans hx)
    _ = 2 * B := by ring

private theorem exists_originGeodesicLine_close_of_quasi_geodesic
    [FiniteDimensional ℝ E] (q : ℝ → Hyperboloid E) {L C : ℝ}
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hq : ContinuousOn q (Set.Ici 0)) (hq0 : q 0 = origin)
    (hquasi : ∀ s ∈ Set.Ici (0 : ℝ), ∀ t ∈ Set.Ici (0 : ℝ),
      L⁻¹ * dist s t - C ≤ dist (q s) (q t) ∧ dist (q s) (q t) ≤ L * dist s t + C) :
    let R := C + 1 + Real.log (4 * L ^ 2)
    let D := (2 * L ^ 2 + 1) * R + (L ^ 2 + 1) * C + 1
    let B := L ^ 2 * D + (L ^ 2 + 1) * C
    ∃ ξ : Metric.sphere (0 : E) 1, ∀ t ∈ Set.Ici (0 : ℝ),
      dist (q t) (originGeodesicLine ξ (dist origin (q t))) ≤ 2 * (B + 1) := by
  classical
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨N, hN⟩ := exists_nat_gt (L * (C + 1))
  let T : ℕ → ℝ := fun n => (n + N : ℕ)
  have hT0 (n : ℕ) : 0 ≤ T n := Nat.cast_nonneg _
  have hT : Filter.Tendsto T Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ))
      (fun n => by dsimp [T]; exact_mod_cast Nat.le_add_right n N)
      tendsto_natCast_atTop_atTop
  have hne (n : ℕ) : origin ≠ q (T n) := by
    have hbound : L * (C + 1) < T n := by
      dsimp [T]
      push_cast
      linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
    have hmul := mul_lt_mul_of_pos_left hbound (inv_pos.mpr hLp)
    rw [← mul_assoc, inv_mul_cancel₀ hLp.ne', one_mul] at hmul
    have hlo := (hquasi 0 (by simp) (T n) (hT0 n)).1
    rw [hq0, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (hT0 n)] at hlo
    apply dist_pos.mp
    linarith
  choose u hu using fun n => exists_originGeodesicLine (hne n)
  obtain ⟨ξ, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq u
  let R := C + 1 + Real.log (4 * L ^ 2)
  let D := (2 * L ^ 2 + 1) * R + (L ^ 2 + 1) * C + 1
  let A := L ^ 2 * D + (L ^ 2 + 1) * C
  have hlog : 0 ≤ Real.log (4 * L ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg (L - 1)])
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hnear (t : ℝ) (ht : 0 ≤ t) :
      dist (q t) (originGeodesicLine ξ (dist origin (q t))) ≤ 2 * (A + 1) := by
    have hlimline := (continuous_originGeodesicLine (dist origin (q t))).continuousAt.tendsto.comp hlim
    apply le_of_tendsto (tendsto_const_nhds.dist hlimline)
    filter_upwards [(hT.comp hφ.tendsto_atTop).eventually (Filter.eventually_ge_atTop t)] with n hn
    have hseg := morse_lemma L C hL hC 0 (T (φ n)) (hT0 (φ n)) q
      (hq.mono fun s hs => hs.1)
      (fun s hs t ht => hquasi s hs.1 t ht.1)
    change Metric.hausdorffEDist (q '' Set.Icc 0 (T (φ n)))
      {z | dist (q 0) z + dist z (q (T (φ n))) = dist (q 0) (q (T (φ n)))} ≤
        ENNReal.ofReal A at hseg
    have hlt : Metric.hausdorffEDist (q '' Set.Icc 0 (T (φ n)))
        {z | dist (q 0) z + dist z (q (T (φ n))) = dist (q 0) (q (T (φ n)))} <
          ENNReal.ofReal (A + 1) :=
      hseg.trans_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hA).mpr (by linarith))
    have hqt : q t ∈ q '' Set.Icc 0 (T (φ n)) := ⟨t, ⟨ht, hn⟩, rfl⟩
    obtain ⟨z, hz, hqz⟩ := Metric.exists_edist_lt_of_hausdorffEDist_lt hqt hlt
    have hzline : z ∈ originGeodesicLine (u (φ n)) '' Set.Icc 0 (dist origin (q (T (φ n)))) := by
      have hsegment := metric_segment_eq_image_geodesicLine origin (0, (u (φ n) : E))
        (by simp only [lorentzForm_apply, zero_mul, sub_zero, real_inner_self_eq_norm_sq,
          ← dist_zero_right, Metric.mem_sphere.mp (u (φ n)).property, one_pow])
        (by simp [lorentzForm_apply]) 0 (dist origin (q (T (φ n)))) dist_nonneg
      change {w | dist (originGeodesicLine (u (φ n)) 0) w +
          dist w (originGeodesicLine (u (φ n)) (dist origin (q (T (φ n))))) =
            dist (originGeodesicLine (u (φ n)) 0)
              (originGeodesicLine (u (φ n)) (dist origin (q (T (φ n)))))} =
        originGeodesicLine (u (φ n)) '' Set.Icc 0 (dist origin (q (T (φ n)))) at hsegment
      rw [originGeodesicLine_zero, hu] at hsegment
      rw [← hsegment]
      simpa only [hq0] using hz
    obtain ⟨s, hs, rfl⟩ := hzline
    exact dist_originGeodesicLine_radial_le (u (φ n)) (q t) hs.1 (edist_lt_ofReal.mp hqz).le
  exact ⟨ξ, hnear⟩

theorem exists_geodesicLine_close_of_quasi_geodesic
    [FiniteDimensional ℝ E] (q : ℝ → Hyperboloid E) {L C : ℝ}
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hq : ContinuousOn q (Set.Ici 0))
    (hquasi : ∀ s ∈ Set.Ici (0 : ℝ), ∀ t ∈ Set.Ici (0 : ℝ),
      L⁻¹ * dist s t - C ≤ dist (q s) (q t) ∧ dist (q s) (q t) ≤ L * dist s t + C) :
    let R := C + 1 + Real.log (4 * L ^ 2)
    let D := (2 * L ^ 2 + 1) * R + (L ^ 2 + 1) * C + 1
    let B := L ^ 2 * D + (L ^ 2 + 1) * C
    ∃ (v : ℝ × E) (hv : lorentzForm E v v = 1)
      (ho : lorentzForm E ((q 0).time, (q 0).space) v = 0),
      ∀ t ∈ Set.Ici (0 : ℝ),
        dist (q t) (geodesicLine (q 0) v hv ho (dist (q 0) (q t))) ≤ 2 * (B + 1) := by
  let e := boost (q 0)
  have he0 : e origin = q 0 := boost_origin _
  obtain ⟨ξ, hξ⟩ := exists_originGeodesicLine_close_of_quasi_geodesic
    (fun t => e.symm (q t)) hL hC (e.symm.continuous.comp_continuousOn hq)
    (by simpa only [e, boost_origin] using (boost (q 0)).symm_apply_apply origin)
    (by simpa only [e.symm.dist_eq] using hquasi)
  have hξnorm : ‖(ξ : E)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using ξ.property
  have hw : lorentzForm E (0, (ξ : E)) (0, (ξ : E)) = 1 := by
    simp [lorentzForm_apply, hξnorm]
  have hwo : lorentzForm E ((origin : Hyperboloid E).time, origin.space) (0, (ξ : E)) = 0 := by
    simp [lorentzForm_apply]
  let v := lorentzExtension e (0, (ξ : E))
  have hv : lorentzForm E v v = 1 := by
    rw [(lorentzExtension e).map_app]
    exact hw
  have ho : lorentzForm E ((q 0).time, (q 0).space) v = 0 := by
    rw [← he0, ← lorentzExtension_apply e origin, (lorentzExtension e).map_app]
    exact hwo
  have hline (r : ℝ) : e (originGeodesicLine ξ r) = geodesicLine (q 0) v hv ho r := by
    simpa only [originGeodesicLine, he0] using
      isometryEquiv_geodesicLine e origin (0, (ξ : E)) hw hwo r
  refine ⟨v, hv, ho, ?_⟩
  intro t ht
  have h := hξ t ht
  have hd : dist origin (e.symm (q t)) = dist (q 0) (q t) := by
    rw [← e.dist_eq, he0, e.apply_symm_apply]
  rw [hd] at h
  rw [← e.dist_eq, e.apply_symm_apply, hline] at h
  exact h

theorem exists_unique_tendsto_kleinHomeomorph_of_quasi_geodesic
    [FiniteDimensional ℝ E] (q : ℝ → Hyperboloid E) {L C : ℝ}
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hq : ContinuousOn q (Set.Ici 0))
    (hquasi : ∀ s ∈ Set.Ici (0 : ℝ), ∀ t ∈ Set.Ici (0 : ℝ),
      L⁻¹ * dist s t - C ≤ dist (q s) (q t) ∧ dist (q s) (q t) ≤ L * dist s t + C) :
    ∃! ξ : Metric.sphere (0 : E) 1,
      Filter.Tendsto (fun t => (kleinHomeomorph (q t) : E)) Filter.atTop (𝓝 (ξ : E)) := by
  obtain ⟨v, hv, ho, hnear⟩ := exists_geodesicLine_close_of_quasi_geodesic q hL hC hq hquasi
  let ξ : Metric.sphere (0 : E) 1 :=
    ⟨((q 0).time + v.1)⁻¹ • ((q 0).space + v.2), by
      simpa only [Metric.mem_sphere, dist_zero_right] using
        norm_geodesicLine_forward_endpoint (q 0) v hv ho⟩
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hradial : Filter.Tendsto (fun t => dist (q 0) (q t)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [Filter.eventually_ge_atTop (max 0 (L * (b + C)))] with t ht
    have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
    have hmul := mul_le_mul_of_nonneg_left ((le_max_right _ _).trans ht) (inv_pos.mpr hLp).le
    rw [← mul_assoc, inv_mul_cancel₀ hLp.ne', one_mul] at hmul
    have hlo := (hquasi 0 (by simp) t ht0).1
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg ht0] at hlo
    linarith
  let R := C + 1 + Real.log (4 * L ^ 2)
  let D := (2 * L ^ 2 + 1) * R + (L ^ 2 + 1) * C + 1
  let B := L ^ 2 * D + (L ^ 2 + 1) * C
  have hfinal : Filter.Tendsto (fun t => (kleinHomeomorph (q t) : E)) Filter.atTop (𝓝 (ξ : E)) := by
    apply tendsto_kleinHomeomorph_of_dist_bounded
      (x := fun t => geodesicLine (q 0) v hv ho (dist (q 0) (q t))) (C := 2 * (B + 1))
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
      simpa only [dist_comm] using hnear t ht
    · exact (tendsto_kleinHomeomorph_geodesicLine_atTop (q 0) v hv ho).comp hradial
  refine ⟨ξ, hfinal, ?_⟩
  intro η hη
  apply Subtype.ext
  exact tendsto_nhds_unique hη hfinal

end DifferentialGeometry.Hyperboloid
