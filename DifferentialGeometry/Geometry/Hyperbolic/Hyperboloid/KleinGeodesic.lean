import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.GeodesicSegment
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.GeodesicBoundary
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem klein_denominator_pos (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0) (t : ℝ) :
    0 < x.time + Real.tanh t * v.1 := by
  have htime : (geodesicLine x v hv ho t).time =
      Real.cosh t * (x.time + Real.tanh t * v.1) := by
    rw [geodesicLine_time, Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos t).ne']
  have h := (geodesicLine x v hv ho t).time_pos
  rw [htime] at h
  exact (mul_pos_iff_of_pos_left (Real.cosh_pos t)).mp h

private theorem kleinHomeomorph_image_geodesicLine_Icc (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0)
    (d : ℝ) (hd : 0 < d) :
    (fun t => (kleinHomeomorph (geodesicLine x v hv ho t) : E)) '' Set.Icc 0 d =
      segment ℝ (kleinHomeomorph x : E) (kleinHomeomorph (geodesicLine x v hv ho d) : E) := by
  let D : ℝ → ℝ := fun t => x.time + Real.tanh t * v.1
  have hD (t : ℝ) : 0 < D t := klein_denominator_pos x v hv ho t
  have hq : 0 < Real.tanh d := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hd) (Real.cosh_pos d)
  let θ : ℝ → ℝ := fun t => Real.tanh t * D d / (Real.tanh d * D t)
  have hθ0 : θ 0 = 0 := by simp [θ]
  have hθd : θ d = 1 := by
    exact div_self (mul_ne_zero hq.ne' (hD d).ne')
  have hcont : Continuous θ := by
    have htanh : Continuous Real.tanh := by
      rw [show Real.tanh = fun t => Real.sinh t / Real.cosh t from
        funext Real.tanh_eq_sinh_div_cosh]
      exact Real.continuous_sinh.div Real.continuous_cosh (fun t => (Real.cosh_pos t).ne')
    exact (htanh.mul_const (D d)).div
      (continuous_const.mul (continuous_const.add (htanh.mul_const v.1)))
      (fun t => mul_ne_zero hq.ne' (hD t).ne')
  have hθmem (t : ℝ) (ht : t ∈ Set.Icc 0 d) : θ t ∈ Set.Icc 0 1 := by
    have ht0 : 0 ≤ Real.tanh t := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.mpr ht.1) (Real.cosh_pos t).le
    have htd : Real.tanh t ≤ Real.tanh d :=
      (Real.artanh_le_artanh_iff
        ⟨Real.neg_one_lt_tanh t, Real.tanh_lt_one t⟩
        ⟨Real.neg_one_lt_tanh d, Real.tanh_lt_one d⟩).mp (by
          simpa only [Real.artanh_tanh] using ht.2)
    refine ⟨div_nonneg (mul_nonneg ht0 (hD d).le) (mul_nonneg hq.le (hD t).le), ?_⟩
    apply (div_le_one (mul_pos hq (hD t))).mpr
    change Real.tanh t * (x.time + Real.tanh d * v.1) ≤
      Real.tanh d * (x.time + Real.tanh t * v.1)
    nlinarith [mul_nonneg x.time_pos.le (sub_nonneg.mpr htd)]
  have hformula (t : ℝ) :
      (kleinHomeomorph (geodesicLine x v hv ho t) : E) =
        (1 - θ t) • (kleinHomeomorph x : E) +
          θ t • (kleinHomeomorph (geodesicLine x v hv ho d) : E) := by
    have hcoef₁ : (1 - θ t) * x.time⁻¹ + θ t * (D d)⁻¹ = (D t)⁻¹ := by
      dsimp only [θ]
      field_simp [x.time_pos.ne', hq.ne', (hD d).ne', (hD t).ne']
      dsimp only [D]
      ring
    have hcoef₂ : θ t * (D d)⁻¹ * Real.tanh d = (D t)⁻¹ * Real.tanh t := by
      dsimp only [θ]
      field_simp [hq.ne', (hD d).ne', (hD t).ne']
    rw [kleinHomeomorph_geodesicLine, kleinHomeomorph_geodesicLine, kleinHomeomorph_apply_coe]
    change (D t)⁻¹ • (x.space + Real.tanh t • v.2) =
      (1 - θ t) • (x.time⁻¹ • x.space) + θ t • ((D d)⁻¹ • (x.space + Real.tanh d • v.2))
    simp only [smul_add, smul_smul]
    rw [← add_assoc, ← add_smul, hcoef₁, ← mul_assoc, hcoef₂]
  rw [segment_eq_image]
  apply Set.Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    exact ⟨θ t, hθmem t ht, (hformula t).symm⟩
  · rintro z ⟨u, hu, rfl⟩
    have hu' : u ∈ Set.Icc (θ 0) (θ d) := by rwa [hθ0, hθd]
    obtain ⟨t, ht, htu⟩ := intermediate_value_Icc hd.le hcont.continuousOn hu'
    refine ⟨t, ht, ?_⟩
    dsimp only
    rw [hformula t, htu]

theorem kleinHomeomorph_image_metric_segment (a b : Hyperboloid E) :
    (fun z : Hyperboloid E => (kleinHomeomorph z : E)) ''
      {z | dist a z + dist z b = dist a b} =
        segment ℝ (kleinHomeomorph a : E) (kleinHomeomorph b : E) := by
  by_cases hab : a = b
  · subst b
    have hs : {z : Hyperboloid E | dist a z + dist z a = dist a a} = {a} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, dist_self]
      constructor
      · intro h
        have ha : 0 ≤ dist a z := dist_nonneg
        have hz : 0 ≤ dist z a := dist_nonneg
        exact (dist_eq_zero.mp (by linarith : dist a z = 0)).symm
      · rintro rfl
        simp
    rw [hs, Set.image_singleton, segment_same]
  · obtain ⟨v, hv, ho, hb⟩ := exists_geodesicLine_through hab
    have hs := metric_segment_eq_image_geodesicLine a v hv ho 0 (dist a b) dist_nonneg
    rw [geodesicLine_zero, hb] at hs
    rw [hs, ← Set.image_comp]
    have h := kleinHomeomorph_image_geodesicLine_Icc a v hv ho (dist a b) (dist_pos.mpr hab)
    simpa only [Function.comp_def, hb] using h

theorem exists_geodesicLine_with_endpoints
    (ξminus ξplus : Metric.sphere (0 : E) 1) (hξ : ξminus ≠ ξplus) :
    ∃ (x : Hyperboloid E) (v : ℝ × E) (hv : lorentzForm E v v = 1)
      (ho : lorentzForm E (x.time, x.space) v = 0),
      (x.time - v.1)⁻¹ • (x.space - v.2) = (ξminus : E) ∧
      (x.time + v.1)⁻¹ • (x.space + v.2) = (ξplus : E) ∧
      (fun z : Hyperboloid E => (kleinHomeomorph z : E)) ''
        Set.range (geodesicLine x v hv ho) = openSegment ℝ (ξminus : E) (ξplus : E) := by
  let u : E := ξminus
  let w : E := ξplus
  have hu : ‖u‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using ξminus.property
  have hw : ‖w‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using ξplus.property
  have huw : u ≠ w := fun h => hξ (Subtype.ext h)
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hww : inner ℝ w w = 1 := by rw [real_inner_self_eq_norm_sq, hw, one_pow]
  have hwu : inner ℝ w u = inner ℝ u w := real_inner_comm _ _
  have hδ : 0 < 1 - inner ℝ u w := by
    have hn := norm_sub_sq_real u w
    rw [hu, hw] at hn
    have hp : 0 < ‖u - w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr huw))
    nlinarith
  let s : ℝ := Real.sqrt (2 * (1 - inner ℝ u w))
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos (by norm_num) hδ)
  have hs₂ : s ^ 2 = 2 * (1 - inner ℝ u w) := Real.sq_sqrt (mul_pos (by norm_num) hδ).le
  let x : Hyperboloid E :=
    { time := 2 / s
      space := s⁻¹ • (w + u)
      time_pos := div_pos (by norm_num) hs
      time_sq_sub_inner_self := by
        simp only [real_inner_smul_left, real_inner_smul_right,
          inner_add_left, inner_add_right, huu, hww, hwu]
        field_simp [hs.ne']
        nlinarith [hs₂] }
  let v : ℝ × E := (0, s⁻¹ • (w - u))
  have hv : lorentzForm E v v = 1 := by
    simp only [v, lorentzForm_apply, real_inner_smul_left, real_inner_smul_right,
      inner_sub_left, inner_sub_right, huu, hww, hwu, mul_zero, sub_zero]
    field_simp [hs.ne']
    nlinarith [hs₂]
  have ho : lorentzForm E (x.time, x.space) v = 0 := by
    simp only [x, v, lorentzForm_apply, real_inner_smul_left, real_inner_smul_right,
      inner_sub_right, inner_add_left, huu, hww, hwu, mul_zero, sub_zero]
    ring
  have hscale : (2 / s)⁻¹ * s⁻¹ = (1 / 2 : ℝ) := by field_simp [hs.ne']
  have hback : (x.time - v.1)⁻¹ • (x.space - v.2) = u := by
    change (2 / s - 0)⁻¹ • (s⁻¹ • (w + u) - s⁻¹ • (w - u)) = u
    rw [sub_zero, ← smul_sub, smul_smul, hscale]
    module
  have hforward : (x.time + v.1)⁻¹ • (x.space + v.2) = w := by
    change (2 / s + 0)⁻¹ • (s⁻¹ • (w + u) + s⁻¹ • (w - u)) = w
    rw [add_zero, ← smul_add, smul_smul, hscale]
    module
  have hformula (t : ℝ) :
      (kleinHomeomorph (geodesicLine x v hv ho t) : E) =
        (1 - (Real.tanh t + 1) / 2) • u + ((Real.tanh t + 1) / 2) • w := by
    rw [kleinHomeomorph_geodesicLine]
    change (2 / s + Real.tanh t * 0)⁻¹ •
      (s⁻¹ • (w + u) + Real.tanh t • (s⁻¹ • (w - u))) = _
    rw [mul_zero, add_zero]
    rw [smul_comm (Real.tanh t) s⁻¹, ← smul_add, smul_smul, hscale]
    module
  refine ⟨x, v, hv, ho, hback, hforward, ?_⟩
  rw [openSegment_eq_image]
  apply Set.Subset.antisymm
  · rintro z ⟨_, ⟨t, rfl⟩, rfl⟩
    refine ⟨(Real.tanh t + 1) / 2, ?_, (hformula t).symm⟩
    exact ⟨by linarith [Real.neg_one_lt_tanh t], by linarith [Real.tanh_lt_one t]⟩
  · rintro z ⟨a, ha, rfl⟩
    let t := Real.artanh (2 * a - 1)
    have ht : Real.tanh t = 2 * a - 1 :=
      Real.tanh_artanh ⟨by linarith [ha.1], by linarith [ha.2]⟩
    refine ⟨geodesicLine x v hv ho t, ⟨t, rfl⟩, ?_⟩
    dsimp only
    rw [hformula t, ht]
    have heq : (2 * a - 1 + 1) / 2 = a := by ring
    rw [heq]

theorem kleinHomeomorph_image_range_geodesicLine (x : Hyperboloid E) (v : ℝ × E)
    (hv : lorentzForm E v v = 1) (ho : lorentzForm E (x.time, x.space) v = 0) :
    (fun z : Hyperboloid E => (kleinHomeomorph z : E)) ''
      Set.range (geodesicLine x v hv ho) =
        openSegment ℝ ((x.time - v.1)⁻¹ • (x.space - v.2))
          ((x.time + v.1)⁻¹ • (x.space + v.2)) := by
  let D : ℝ → ℝ := fun t => x.time + Real.tanh t * v.1
  let α : ℝ → ℝ := fun t => (1 - Real.tanh t) * (x.time - v.1) / (2 * D t)
  let β : ℝ → ℝ := fun t => (1 + Real.tanh t) * (x.time + v.1) / (2 * D t)
  have hD (t : ℝ) : 0 < D t := klein_denominator_pos x v hv ho t
  have hm := time_sub_fst_pos x v hv ho
  have hp := time_add_fst_pos x v hv ho
  have hα (t : ℝ) : 0 < α t :=
    div_pos (mul_pos (sub_pos.mpr (Real.tanh_lt_one t)) hm) (mul_pos (by norm_num) (hD t))
  have hβ (t : ℝ) : 0 < β t :=
    div_pos (mul_pos (by linarith [Real.neg_one_lt_tanh t]) hp) (mul_pos (by norm_num) (hD t))
  have hsum (t : ℝ) : α t + β t = 1 := by
    dsimp only [α, β]
    rw [← add_div]
    apply (div_eq_one_iff_eq (mul_ne_zero (by norm_num) (hD t).ne')).mpr
    dsimp only [D]
    ring
  have hformula (t : ℝ) :
      (kleinHomeomorph (geodesicLine x v hv ho t) : E) =
        α t • ((x.time - v.1)⁻¹ • (x.space - v.2)) +
          β t • ((x.time + v.1)⁻¹ • (x.space + v.2)) := by
    have hcoef₁ : α t * (x.time - v.1)⁻¹ + β t * (x.time + v.1)⁻¹ = (D t)⁻¹ := by
      dsimp only [α, β]
      field_simp [hm.ne', hp.ne', (hD t).ne']
      ring
    have hcoef₂ : -(α t * (x.time - v.1)⁻¹) + β t * (x.time + v.1)⁻¹ =
        (D t)⁻¹ * Real.tanh t := by
      dsimp only [α, β]
      field_simp [hm.ne', hp.ne', (hD t).ne']
      ring
    rw [kleinHomeomorph_geodesicLine]
    change (D t)⁻¹ • (x.space + Real.tanh t • v.2) = _
    calc
      _ = (D t)⁻¹ • x.space + ((D t)⁻¹ * Real.tanh t) • v.2 := by module
      _ = (α t * (x.time - v.1)⁻¹ + β t * (x.time + v.1)⁻¹) • x.space +
          (-(α t * (x.time - v.1)⁻¹) + β t * (x.time + v.1)⁻¹) • v.2 := by
        rw [hcoef₁, hcoef₂]
      _ = _ := by module
  apply Set.Subset.antisymm
  · rintro z ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨α t, β t, hα t, hβ t, hsum t, (hformula t).symm⟩
  · rintro z ⟨a, b, ha, hb, hab, hz⟩
    have haeq : a = 1 - b := by linarith
    subst a
    let d : ℝ := (1 - b) * (x.time + v.1) + b * (x.time - v.1)
    have hd : 0 < d := add_pos (mul_pos ha hp) (mul_pos hb hm)
    let q : ℝ := (b * (x.time - v.1) - (1 - b) * (x.time + v.1)) / d
    have hq : q ∈ Set.Ioo (-1) 1 := by
      constructor
      · apply (lt_div_iff₀ hd).mpr
        dsimp only [d]
        nlinarith [mul_pos hb hm]
      · apply (div_lt_one hd).mpr
        dsimp only [d]
        nlinarith [mul_pos ha hp]
    let t := Real.artanh q
    have ht : Real.tanh t = q := Real.tanh_artanh hq
    have hβt : β t = b := by
      apply (div_eq_iff (mul_ne_zero (by norm_num) (hD t).ne')).mpr
      dsimp only [D]
      rw [ht]
      dsimp only [q]
      field_simp [hd.ne']
      dsimp only [d]
      ring
    have hαt : α t = 1 - b := by linarith [hsum t]
    refine ⟨geodesicLine x v hv ho t, ⟨t, rfl⟩, ?_⟩
    dsimp only
    rw [hformula t, hαt, hβt]
    exact hz

end DifferentialGeometry.Hyperboloid
