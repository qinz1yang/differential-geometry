import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.GeodesicSegment
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Projection
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem continuous_lineProjection (e : E) (he : ‖e‖ = 1) :
    Continuous (lineProjection e he) := by
  have hd : Continuous (fun x : Hyperboloid E =>
      Real.sqrt (1 + ‖x.space - inner ℝ x.space e • e‖ ^ 2)) :=
    (continuous_const.add
      ((continuous_space.sub ((continuous_space.inner continuous_const).smul continuous_const)).norm.pow 2)).sqrt
  have hn (x : Hyperboloid E) :
      Real.sqrt (1 + ‖x.space - inner ℝ x.space e • e‖ ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr (by positivity)).ne'
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def, Pi.div_apply, Pi.smul_apply', lineProjection_time, lineProjection_space] using
    (continuous_time.div hd hn).prodMk
      (((continuous_space.inner continuous_const).div hd hn).smul continuous_const)

private theorem exists_excursion_interval (h : ℝ → ℝ) {a b t R : ℝ}
    (hh : ContinuousOn h (Set.Icc a b)) (ht : t ∈ Set.Icc a b)
    (ha : h a = 0) (hb : h b = 0) (hR : 0 < R) (hRt : R < h t) :
    ∃ u v : ℝ, u ∈ Set.Icc a t ∧ v ∈ Set.Icc t b ∧ h u = R ∧ h v = R ∧
      ∀ s ∈ Set.Icc u v, R ≤ h s := by
  have hleft : ContinuousOn h (Set.Icc a t) :=
    hh.mono (Set.Icc_subset_Icc le_rfl ht.2)
  have hright : ContinuousOn h (Set.Icc t b) :=
    hh.mono (Set.Icc_subset_Icc ht.1 le_rfl)
  have hnleft : (Set.Icc a t ∩ h ⁻¹' {R}).Nonempty := by
    obtain ⟨u, hu, heq⟩ := intermediate_value_Icc ht.1 hleft
      (show R ∈ Set.Icc (h a) (h t) by rw [ha]; exact ⟨hR.le, hRt.le⟩)
    exact ⟨u, hu, heq⟩
  have hnright : (Set.Icc t b ∩ h ⁻¹' {R}).Nonempty := by
    obtain ⟨v, hv, heq⟩ := intermediate_value_Icc' ht.2 hright
      (show R ∈ Set.Icc (h b) (h t) by rw [hb]; exact ⟨hR.le, hRt.le⟩)
    exact ⟨v, hv, heq⟩
  have hcleft : IsCompact (Set.Icc a t ∩ h ⁻¹' {R}) :=
    isCompact_Icc.of_isClosed_subset
      (hleft.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) Set.inter_subset_left
  have hcright : IsCompact (Set.Icc t b ∩ h ⁻¹' {R}) :=
    isCompact_Icc.of_isClosed_subset
      (hright.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) Set.inter_subset_left
  obtain ⟨u, hu⟩ := hcleft.exists_isGreatest hnleft
  obtain ⟨v, hv⟩ := hcright.exists_isLeast hnright
  have huR : h u = R := hu.1.2
  have hvR : h v = R := hv.1.2
  refine ⟨u, v, hu.1.1, hv.1.1, huR, hvR, ?_⟩
  intro s hs
  by_contra hnot
  have hsR : h s < R := lt_of_not_ge hnot
  rcases le_total s t with hst | hts
  · have hc : ContinuousOn h (Set.Icc s t) :=
      hh.mono (Set.Icc_subset_Icc (hu.1.1.1.trans hs.1) ht.2)
    obtain ⟨w, hw, hwR⟩ := intermediate_value_Icc hst hc ⟨hsR.le, hRt.le⟩
    have hwu : w ≤ u := hu.2 ⟨⟨(hu.1.1.1.trans hs.1).trans hw.1, hw.2⟩, hwR⟩
    have hsu : s = u := le_antisymm (hw.1.trans hwu) hs.1
    rw [hsu, huR] at hsR
    exact (lt_irrefl R) hsR
  · have hc : ContinuousOn h (Set.Icc t s) :=
      hh.mono (Set.Icc_subset_Icc ht.1 (hs.2.trans hv.1.1.2))
    obtain ⟨w, hw, hwR⟩ := intermediate_value_Icc' hts hc ⟨hsR.le, hRt.le⟩
    have hvw : v ≤ w := hv.2 ⟨⟨hw.1, hw.2.trans (hs.2.trans hv.1.1.2)⟩, hwR⟩
    have hsv : s = v := le_antisymm hs.2 (hvw.trans hw.2)
    rw [hsv, hvR] at hsR
    exact (lt_irrefl R) hsR

private theorem projection_step_le (e : E) (he : ‖e‖ = 1) (L C : ℝ) (hL : 1 ≤ L)
    (x y : Hyperboloid E)
    (hx : C + 1 + Real.log (4 * L ^ 2) ≤ dist x (lineProjection e he x))
    (hy : C + 1 + Real.log (4 * L ^ 2) ≤ dist y (lineProjection e he y))
    (hxy : dist x y ≤ 2 * C + 1) :
    dist (lineProjection e he x) (lineProjection e he y) ≤ 1 / (2 * L ^ 2) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have harg : (dist x y - dist x (lineProjection e he x) -
      dist y (lineProjection e he y)) / 2 ≤ -Real.log (4 * L ^ 2) := by
    linarith
  refine (dist_lineProjection_le_two_mul_exp e he x y).trans ?_
  calc
    _ ≤ 2 * Real.exp (-Real.log (4 * L ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num)
    _ = 2 / (4 * L ^ 2) := by
      rw [Real.exp_neg, Real.exp_log (by positivity), div_eq_mul_inv]
    _ = 1 / (2 * L ^ 2) := by
      field_simp
      ring

private theorem projection_endpoints_le (e : E) (he : ‖e‖ = 1) (L C : ℝ)
    (hL : 1 ≤ L) (hC : 0 ≤ C) (a b : ℝ) (hab : a ≤ b) (q : ℝ → Hyperboloid E)
    (hupper : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      dist (q s) (q t) ≤ L * dist s t + C)
    (hheight : ∀ s ∈ Set.Icc a b,
      C + 1 + Real.log (4 * L ^ 2) ≤ dist (q s) (lineProjection e he (q s))) :
    dist (lineProjection e he (q a)) (lineProjection e he (q b)) ≤
      (b - a) / (2 * L) + 1 / (2 * L ^ 2) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp only [sub_self, zero_div, zero_add, dist_self]
    positivity
  have hCpos : 0 < C + 1 := by linarith
  let n : ℕ := ⌈(b - a) * L / (C + 1)⌉₊
  have hnpos : 0 < n := Nat.ceil_pos.mpr (by positivity)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hnlow : (b - a) * L / (C + 1) ≤ (n : ℝ) := Nat.le_ceil _
  have hnhigh : (n : ℝ) ≤ (b - a) * L + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ (b - a) * L / (C + 1))).le.trans
      (add_le_add (div_le_self (mul_nonneg (sub_nonneg.mpr hab.le) hLpos.le) (by linarith : 1 ≤ C + 1)) le_rfl)
  let δ : ℝ := (b - a) / n
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hnδ : (n : ℝ) * δ = b - a := by
    dsimp [δ]
    field_simp
  have hstep : L * δ ≤ C + 1 := by
    apply (mul_le_mul_iff_left₀ hnreal).mp
    calc
      (L * δ) * (n : ℝ) = ((n : ℝ) * δ) * L := by ring
      _ = (b - a) * L := by rw [hnδ]
      _ ≤ (n : ℝ) * (C + 1) := (div_le_iff₀ hCpos).mp hnlow
      _ = (C + 1) * (n : ℝ) := mul_comm _ _
  let s (i : ℕ) : ℝ := a + i * δ
  have hs (i : ℕ) (hi : i ≤ n) : s i ∈ Set.Icc a b := by
    have hireal : (i : ℝ) ≤ n := by exact_mod_cast hi
    have hiδ := mul_le_mul_of_nonneg_right hireal hδ
    have hi0 : 0 ≤ (i : ℝ) * δ := mul_nonneg (Nat.cast_nonneg i) hδ
    dsimp [s]
    constructor <;> linarith
  have hs0 : s 0 = a := by simp [s]
  have hsn : s n = b := by dsimp [s]; linarith [hnδ]
  have hdist (i : ℕ) : dist (s i) (s (i + 1)) = δ := by
    rw [Real.dist_eq, show s i - s (i + 1) = -δ by dsimp [s]; push_cast; ring,
      abs_neg, abs_of_nonneg hδ]
  have hbound (i : ℕ) (hi : i < n) :
      dist (lineProjection e he (q (s i))) (lineProjection e he (q (s (i + 1)))) ≤
        1 / (2 * L ^ 2) := by
    apply projection_step_le e he L C hL
    · exact hheight _ (hs i hi.le)
    · exact hheight _ (hs (i + 1) hi)
    · have h := hupper _ (hs i hi.le) _ (hs (i + 1) hi)
      rw [hdist] at h
      linarith
  have hpoly := dist_le_range_sum_of_dist_le
    (f := fun i => lineProjection e he (q (s i))) n
    (d := fun _ => 1 / (2 * L ^ 2)) (fun {i} hi => hbound i hi)
  rw [hs0, hsn] at hpoly
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hpoly
  refine hpoly.trans ?_
  calc
    (n : ℝ) * (1 / (2 * L ^ 2)) ≤ ((b - a) * L + 1) * (1 / (2 * L ^ 2)) :=
      mul_le_mul_of_nonneg_right hnhigh (by positivity)
    _ = (b - a) / (2 * L) + 1 / (2 * L ^ 2) := by
      field_simp

theorem dist_lineProjection_le_of_quasi_geodesic
    (e : E) (he : ‖e‖ = 1) (L C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (a b : ℝ) (q : ℝ → Hyperboloid E) (hq : ContinuousOn q (Set.Icc a b))
    (hquasi : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      L⁻¹ * dist s t - C ≤ dist (q s) (q t) ∧
        dist (q s) (q t) ≤ L * dist s t + C)
    (ha : q a ∈ Set.range (geodesicLine origin (0, e)
      (by simp [lorentzForm_apply, he]) (by simp [lorentzForm_apply])))
    (hb : q b ∈ Set.range (geodesicLine origin (0, e)
      (by simp [lorentzForm_apply, he]) (by simp [lorentzForm_apply])))
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    dist (q t) (lineProjection e he (q t)) ≤
      (2 * L ^ 2 + 1) * (C + 1 + Real.log (4 * L ^ 2)) + (L ^ 2 + 1) * C + 1 := by
  let R := C + 1 + Real.log (4 * L ^ 2)
  let D := (2 * L ^ 2 + 1) * R + (L ^ 2 + 1) * C + 1
  let κ := 1 / (2 * L ^ 2)
  let h (s : ℝ) := dist (q s) (lineProjection e he (q s))
  change h t ≤ D
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLsq : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
  have hlog : 0 ≤ Real.log (4 * L ^ 2) := Real.log_nonneg (by nlinarith)
  have hRpos : 0 < R := by dsimp [R]; linarith
  have hRD : R ≤ D := by
    dsimp [D]
    nlinarith [mul_nonneg (sq_nonneg L) hRpos.le, mul_nonneg (sq_nonneg L) hC]
  by_cases hsmall : h t ≤ R
  · exact hsmall.trans hRD
  have hcont : ContinuousOn h (Set.Icc a b) :=
    continuous_dist.comp_continuousOn
      (hq.prodMk ((continuous_lineProjection e he).comp_continuousOn hq))
  have ha0 : h a = 0 := by
    have hp := eq_lineProjection_of_dist_le e he (q a) (q a) ha
      (by rw [dist_self]; exact dist_nonneg)
    change dist (q a) (lineProjection e he (q a)) = 0
    rw [← hp, dist_self]
  have hb0 : h b = 0 := by
    have hp := eq_lineProjection_of_dist_le e he (q b) (q b) hb
      (by rw [dist_self]; exact dist_nonneg)
    change dist (q b) (lineProjection e he (q b)) = 0
    rw [← hp, dist_self]
  obtain ⟨u, v, hu, hv, huR, hvR, hheight⟩ :=
    exists_excursion_interval h hcont ht ha0 hb0 hRpos (lt_of_not_ge hsmall)
  have huv : u ≤ v := hu.2.trans hv.1
  have hIu : u ∈ Set.Icc a b := ⟨hu.1, hu.2.trans ht.2⟩
  have hIv : v ∈ Set.Icc a b := ⟨ht.1.trans hv.1, hv.2⟩
  have hupper : ∀ s ∈ Set.Icc u v, ∀ w ∈ Set.Icc u v,
      dist (q s) (q w) ≤ L * dist s w + C := by
    intro s hs w hw
    exact (hquasi s ⟨hu.1.trans hs.1, hs.2.trans hv.2⟩
      w ⟨hu.1.trans hw.1, hw.2.trans hv.2⟩).2
  have hproj := projection_endpoints_le e he L C hL hC u v huv q hupper hheight
  let τ := v - u
  have hlower : τ / L - C ≤ dist (q u) (q v) := by
    have h0 := (hquasi u hIu v hIv).1
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr huv)] at h0
    simpa only [τ, div_eq_mul_inv, mul_comm] using h0
  have htriangle : dist (q u) (q v) ≤
      2 * R + dist (lineProjection e he (q u)) (lineProjection e he (q v)) := by
    calc
      _ ≤ dist (q u) (lineProjection e he (q u)) +
          dist (lineProjection e he (q u)) (q v) := dist_triangle _ _ _
      _ ≤ dist (q u) (lineProjection e he (q u)) +
          (dist (lineProjection e he (q u)) (lineProjection e he (q v)) +
            dist (lineProjection e he (q v)) (q v)) :=
        add_le_add le_rfl (dist_triangle _ _ _)
      _ = _ := by
        change h u + (_ + dist (lineProjection e he (q v)) (q v)) = _
        rw [huR, dist_comm (lineProjection e he (q v)) (q v)]
        change R + (_ + h v) = _
        rw [hvR]
        ring
  have hlength : τ ≤ 2 * L * (2 * R + C + κ) := by
    have hupp : dist (q u) (q v) ≤ 2 * R + τ / (2 * L) + κ := by
      change dist (lineProjection e he (q u)) (lineProjection e he (q v)) ≤
        τ / (2 * L) + κ at hproj
      linarith only [htriangle, hproj]
    have hm := mul_le_mul_of_nonneg_right (hlower.trans hupp) hLpos.le
    have hcancel : (τ / L) * L = τ := div_mul_cancel₀ τ hLpos.ne'
    have hhalf : (τ / (2 * L)) * L = τ / 2 := by field_simp
    nlinarith only [hm, hcancel, hhalf]
  have hclose : ∃ s ∈ Set.Icc a b, h s = R ∧ dist t s ≤ τ / 2 := by
    by_cases hmid : t ≤ (u + v) / 2
    · refine ⟨u, hIu, huR, ?_⟩
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hu.2)]
      dsimp [τ]
      linarith
    · refine ⟨v, hIv, hvR, ?_⟩
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hv.1)]
      dsimp [τ]
      linarith
  obtain ⟨s, hs, hsR, hstime⟩ := hclose
  have hnear : h t ≤ R + L * (τ / 2) + C := by
    have hmin := dist_lineProjection_le e he (q t) (lineProjection e he (q s))
      (lineProjection_mem_range e he (q s))
    have htri := dist_triangle (q t) (q s) (lineProjection e he (q s))
    have hupper := (hquasi t ht s hs).2
    have hmul := mul_le_mul_of_nonneg_left hstime hLpos.le
    change dist (q s) (lineProjection e he (q s)) = R at hsR
    change dist (q t) (lineProjection e he (q t)) ≤ _
    linarith only [hmin, htri, hupper, hmul, hsR]
  have hκ : L ^ 2 * κ = 1 / 2 := by dsimp [κ]; field_simp
  calc
    h t ≤ R + L * (τ / 2) + C := hnear
    _ ≤ R + L * (L * (2 * R + C + κ)) + C := by
      have hh : τ / 2 ≤ L * (2 * R + C + κ) := by linarith only [hlength]
      have hm := mul_le_mul_of_nonneg_left hh hLpos.le
      linarith only [hm]
    _ ≤ D := by dsimp [D]; nlinarith only [hκ]

private theorem hausdorffEDist_axis_segment_le
    (e : E) (he : ‖e‖ = 1) (L C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (a b : ℝ) (hab : a ≤ b) (q : ℝ → Hyperboloid E)
    (hq : ContinuousOn q (Set.Icc a b))
    (hquasi : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      L⁻¹ * dist s t - C ≤ dist (q s) (q t) ∧
        dist (q s) (q t) ≤ L * dist s t + C)
    (d : ℝ) (hd : 0 ≤ d) (ha : q a = origin)
    (hb : q b = geodesicLine origin (0, e)
      (by simp [lorentzForm_apply, he]) (by simp [lorentzForm_apply]) d) :
    let c := geodesicLine (origin : Hyperboloid E) (0, e)
      (by simp [lorentzForm_apply, he]) (by simp [lorentzForm_apply])
    let R := C + 1 + Real.log (4 * L ^ 2)
    let D := (2 * L ^ 2 + 1) * R + (L ^ 2 + 1) * C + 1
    Metric.hausdorffEDist (q '' Set.Icc a b) (c '' Set.Icc 0 d) ≤
      ENNReal.ofReal (L ^ 2 * D + (L ^ 2 + 1) * C) := by
  let c := geodesicLine (origin : Hyperboloid E) (0, e)
    (by simp [lorentzForm_apply, he]) (by simp [lorentzForm_apply])
  let R := C + 1 + Real.log (4 * L ^ 2)
  let D := (2 * L ^ 2 + 1) * R + (L ^ 2 + 1) * C + 1
  let B := L ^ 2 * D + (L ^ 2 + 1) * C
  change Metric.hausdorffEDist (q '' Set.Icc a b) (c '' Set.Icc 0 d) ≤ ENNReal.ofReal B
  change q b = c d at hb
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLsq : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
  have hlog : 0 ≤ Real.log (4 * L ^ 2) := Real.log_nonneg (by nlinarith)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDB : D ≤ B := by
    have hm := mul_le_mul_of_nonneg_right hLsq hD
    dsimp [B]
    nlinarith [mul_nonneg (sq_nonneg L) hC]
  have hc : Isometry c := isometry_geodesicLine _ _ _ _
  have hc0 : c 0 = origin := geodesicLine_zero _ _ _ _
  let p (z : Hyperboloid E) := Real.arsinh (inner ℝ (lineProjection e he z).space e)
  have hp : Continuous p := Real.continuous_arsinh.comp
    ((continuous_space.comp (continuous_lineProjection e he)).inner continuous_const)
  have hcoord (z : Hyperboloid E) : c (p z) = lineProjection e he z := by
    obtain ⟨r, hr⟩ := lineProjection_mem_range e he z
    change c r = lineProjection e he z at hr
    have hpz : p z = r := by
      dsimp [p]
      rw [← hr]
      simp only [c, geodesicLine_space, origin_space, smul_zero, zero_add,
        real_inner_smul_left, real_inner_self_eq_norm_sq, he, one_pow, mul_one,
        Real.arsinh_sinh]
    rw [hpz]
    exact hr
  have hfix (r : ℝ) : lineProjection e he (c r) = c r :=
    (eq_lineProjection_of_dist_le e he (c r) (c r) ⟨r, rfl⟩
      (by rw [dist_self]; exact dist_nonneg)).symm
  have hpcr (r : ℝ) : p (c r) = r := hc.injective ((hcoord (c r)).trans (hfix r))
  let s (t : ℝ) := p (q t)
  have hs : ContinuousOn s (Set.Icc a b) := hp.comp_continuousOn hq
  have hsa : s a = 0 := by simpa only [s, ha, hc0] using hpcr 0
  have hsb : s b = d := by simpa only [s, hb] using hpcr d
  have hIa : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hIb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have htube (t : ℝ) (ht : t ∈ Set.Icc a b) :
      dist (q t) (lineProjection e he (q t)) ≤ D :=
    dist_lineProjection_le_of_quasi_geodesic e he L C hL hC a b q hq hquasi
      ⟨0, hc0.trans ha.symm⟩ ⟨d, hb.symm⟩ t ht
  have hparam (u v : ℝ) (hu : u ∈ Set.Icc a b) (hv : v ∈ Set.Icc a b)
      (huv : dist (q u) (q v) ≤ D) : dist u v ≤ L * (D + C) := by
    have hh := (hquasi u hu v hv).1
    have hbnd : L⁻¹ * dist u v ≤ D + C := by linarith only [hh, huv]
    have hm := mul_le_mul_of_nonneg_left hbnd hLpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hLpos.ne', one_mul] at hm
    exact hm
  have hnear (u v : ℝ) (hu : u ∈ Set.Icc a b) (hv : v ∈ Set.Icc a b)
      (huv : dist u v ≤ L * (D + C)) : dist (q u) (q v) ≤ B := by
    have hupper := (hquasi u hu v hv).2
    have hm := mul_le_mul_of_nonneg_left huv hLpos.le
    dsimp [B]
    nlinarith only [hupper, hm]
  apply Metric.hausdorffEDist_le_of_mem_edist
  · rintro _ ⟨t, ht, rfl⟩
    by_cases hst0 : 0 ≤ s t
    · by_cases hstd : s t ≤ d
      · refine ⟨c (s t), ⟨s t, ⟨hst0, hstd⟩, rfl⟩, ?_⟩
        rw [edist_dist]
        apply ENNReal.ofReal_le_ofReal
        simpa only [s, hcoord] using (htube t ht).trans hDB
      · obtain ⟨u, hu, hsu⟩ := intermediate_value_Icc ht.1
          (hs.mono (Set.Icc_subset_Icc le_rfl ht.2))
          (show d ∈ Set.Icc (s a) (s t) by rw [hsa]; exact ⟨hd, (lt_of_not_ge hstd).le⟩)
        have hIu : u ∈ Set.Icc a b := ⟨hu.1, hu.2.trans ht.2⟩
        have hpu : lineProjection e he (q u) = q b := by
          rw [← hcoord (q u)]
          change c (s u) = q b
          rw [hsu, hb]
        have hret : dist (q u) (q b) ≤ D := by simpa only [hpu] using htube u hIu
        have htime : dist u b ≤ L * (D + C) := hparam u b hIu hIb hret
        have hdist : dist t b ≤ dist u b := by
          simp only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2),
            abs_of_nonpos (sub_nonpos.mpr hIu.2)]
          linarith [hu.2]
        refine ⟨q b, ⟨d, ⟨hd, le_rfl⟩, hb.symm⟩, ?_⟩
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (hnear t b ht hIb (hdist.trans htime))
    · obtain ⟨v, hv, hsv⟩ := intermediate_value_Icc ht.2
        (hs.mono (Set.Icc_subset_Icc ht.1 le_rfl))
        (show (0 : ℝ) ∈ Set.Icc (s t) (s b) by rw [hsb]; exact ⟨(lt_of_not_ge hst0).le, hd⟩)
      have hIv : v ∈ Set.Icc a b := ⟨ht.1.trans hv.1, hv.2⟩
      have hpv : lineProjection e he (q v) = q a := by
        rw [← hcoord (q v)]
        change c (s v) = q a
        rw [hsv, hc0, ha]
      have hret : dist (q a) (q v) ≤ D := by
        simpa only [hpv, dist_comm (q v) (q a)] using htube v hIv
      have htime : dist a v ≤ L * (D + C) := hparam a v hIa hIv hret
      have hdist : dist t a ≤ dist a v := by
        simp only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1),
          abs_of_nonpos (sub_nonpos.mpr hIv.1)]
        linarith [hv.1]
      refine ⟨q a, ⟨0, ⟨le_rfl, hd⟩, hc0.trans ha.symm⟩, ?_⟩
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hnear t a ht hIa (hdist.trans htime))
  · rintro _ ⟨r, hr, rfl⟩
    obtain ⟨t, ht, hst⟩ := intermediate_value_Icc hab hs
      (show r ∈ Set.Icc (s a) (s b) by rwa [hsa, hsb])
    have hpt : lineProjection e he (q t) = c r := by
      rw [← hcoord (q t)]
      exact congrArg c hst
    refine ⟨q t, ⟨t, ht, rfl⟩, ?_⟩
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    simpa only [hpt, dist_comm (q t) (c r)] using (htube t ht).trans hDB

theorem morse_lemma (L C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (a b : ℝ) (hab : a ≤ b) (q : ℝ → Hyperboloid E)
    (hq : ContinuousOn q (Set.Icc a b))
    (hquasi : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      L⁻¹ * dist s t - C ≤ dist (q s) (q t) ∧
        dist (q s) (q t) ≤ L * dist s t + C) :
    let R := C + 1 + Real.log (4 * L ^ 2)
    let D := (2 * L ^ 2 + 1) * R + (L ^ 2 + 1) * C + 1
    Metric.hausdorffEDist (q '' Set.Icc a b)
      {z : Hyperboloid E | dist (q a) z + dist z (q b) = dist (q a) (q b)} ≤
      ENNReal.ofReal (L ^ 2 * D + (L ^ 2 + 1) * C) := by
  let R := C + 1 + Real.log (4 * L ^ 2)
  let D := (2 * L ^ 2 + 1) * R + (L ^ 2 + 1) * C + 1
  let B := L ^ 2 * D + (L ^ 2 + 1) * C
  change Metric.hausdorffEDist (q '' Set.Icc a b)
    {z : Hyperboloid E | dist (q a) z + dist z (q b) = dist (q a) (q b)} ≤ ENNReal.ofReal B
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLsq : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
  have hlog : 0 ≤ Real.log (4 * L ^ 2) := Real.log_nonneg (by nlinarith)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hIa : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hIb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  by_cases hends : q a = q b
  · have hseg : {z : Hyperboloid E | dist (q a) z + dist z (q b) = dist (q a) (q b)} =
        {q a} := by
      ext z
      change (dist (q a) z + dist z (q b) = dist (q a) (q b)) ↔ z = q a
      rw [← hends, dist_self, dist_comm z (q a)]
      constructor
      · intro hz
        have hz0 : dist (q a) z = 0 := by linarith
        exact (dist_eq_zero.mp hz0).symm
      · rintro rfl
        simp
    have habound : dist a b ≤ L * C := by
      have hlower := (hquasi a hIa b hIb).1
      rw [hends, dist_self] at hlower
      have hh : L⁻¹ * dist a b ≤ C := by linarith only [hlower]
      have hm := mul_le_mul_of_nonneg_left hh hLpos.le
      rw [← mul_assoc, mul_inv_cancel₀ hLpos.ne', one_mul] at hm
      exact hm
    rw [hseg]
    apply Metric.hausdorffEDist_le_of_mem_edist
    · rintro _ ⟨t, ht, rfl⟩
      have hdist : dist t a ≤ dist a b := by
        simp only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1),
          abs_of_nonpos (sub_nonpos.mpr hab)]
        linarith [ht.2]
      have hupper := (hquasi t ht a hIa).2
      have hm := mul_le_mul_of_nonneg_left (hdist.trans habound) hLpos.le
      have hbound : dist (q t) (q a) ≤ B := by
        dsimp [B]
        nlinarith only [hupper, hm, mul_nonneg (sq_nonneg L) hD]
      refine ⟨q a, Set.mem_singleton _, ?_⟩
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal hbound
    · intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact ⟨q a, ⟨a, hIa, rfl⟩, by simp⟩
  let g := (boost (q a)).symm
  let f (t : ℝ) := g (q t)
  have hf : ContinuousOn f (Set.Icc a b) := g.continuous.comp_continuousOn hq
  have hfquasi : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      L⁻¹ * dist s t - C ≤ dist (f s) (f t) ∧
        dist (f s) (f t) ≤ L * dist s t + C := by
    intro s hs t ht
    simpa only [f, g.dist_eq] using hquasi s hs t ht
  have hfa : f a = origin := by
    change (boost (q a)).symm (q a) = origin
    simpa only [boost_origin] using (boost (q a)).symm_apply_apply (origin : Hyperboloid E)
  have hne : (origin : Hyperboloid E) ≠ f b := by
    intro h
    apply hends
    apply g.injective
    change f a = f b
    exact hfa.trans h
  obtain ⟨v, hv, ho, hend⟩ := exists_geodesicLine_through hne
  have hvt : v.1 = 0 := by
    simpa only [lorentzForm_apply, origin_time, origin_space, inner_zero_left,
      one_mul, zero_sub, neg_eq_zero] using ho
  have hunit : ‖v.2‖ = 1 := by
    have hvv := hv
    rw [lorentzForm_apply, hvt, zero_mul, sub_zero, real_inner_self_eq_norm_sq] at hvv
    nlinarith [norm_nonneg v.2]
  let d := dist (origin : Hyperboloid E) (f b)
  let c := geodesicLine (origin : Hyperboloid E) (0, v.2)
    (by simp [lorentzForm_apply, hunit]) (by simp [lorentzForm_apply])
  have hcline (t : ℝ) : c t = geodesicLine origin v hv ho t := by
    apply ext
    rfl
  have hbaxis : f b = c d := hend.symm.trans (hcline d).symm
  have haxis := hausdorffEDist_axis_segment_le v.2 hunit L C hL hC a b hab f hf hfquasi
    d dist_nonneg hfa hbaxis
  change Metric.hausdorffEDist (f '' Set.Icc a b) (c '' Set.Icc 0 d) ≤ ENNReal.ofReal B at haxis
  have hsegment : {z : Hyperboloid E | dist (f a) z + dist z (f b) = dist (f a) (f b)} =
      c '' Set.Icc 0 d := by
    rw [hfa, hbaxis]
    have hc0 : c 0 = origin := geodesicLine_zero _ _ _ _
    have hs : {z : Hyperboloid E | dist (c 0) z + dist z (c d) = dist (c 0) (c d)} =
        c '' Set.Icc 0 d := metric_segment_eq_image_geodesicLine
      (origin : Hyperboloid E) (0, v.2) (by simp [lorentzForm_apply, hunit])
      (by simp [lorentzForm_apply]) 0 d dist_nonneg
    simpa only [hc0] using hs
  have himage : g '' {z : Hyperboloid E | dist (q a) z + dist z (q b) = dist (q a) (q b)} =
      {z : Hyperboloid E | dist (f a) z + dist z (f b) = dist (f a) (f b)} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change dist (q a) w + dist w (q b) = dist (q a) (q b) at hw
      change dist (g (q a)) (g w) + dist (g w) (g (q b)) = dist (g (q a)) (g (q b))
      simpa only [g.dist_eq] using hw
    · intro hz
      change dist (f a) z + dist z (f b) = dist (f a) (f b) at hz
      refine ⟨g.symm z, ?_, g.apply_symm_apply z⟩
      change dist (q a) (g.symm z) + dist (g.symm z) (q b) = dist (q a) (q b)
      rw [← g.dist_eq (q a) (g.symm z), ← g.dist_eq (g.symm z) (q b),
        ← g.dist_eq (q a) (q b)]
      simpa only [f, g.apply_symm_apply] using hz
  calc
    Metric.hausdorffEDist (q '' Set.Icc a b)
        {z : Hyperboloid E | dist (q a) z + dist z (q b) = dist (q a) (q b)} =
      Metric.hausdorffEDist (g '' (q '' Set.Icc a b))
        (g '' {z : Hyperboloid E | dist (q a) z + dist z (q b) = dist (q a) (q b)}) :=
      (Metric.hausdorffEDist_image g.isometry).symm
    _ = Metric.hausdorffEDist (f '' Set.Icc a b) (c '' Set.Icc 0 d) := by
      simp only [himage, hsegment, Set.image_image]
      rfl
    _ ≤ ENNReal.ofReal B := haxis

end DifferentialGeometry.Hyperboloid
