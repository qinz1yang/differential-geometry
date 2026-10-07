import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryMap
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryMetric
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
private theorem norm_sum_three_sq_le (a b c : F) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have ht := (norm_add_le (a + b) c).trans (add_le_add (norm_add_le a b) le_rfl)
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr ht
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖b‖ - ‖c‖)]

private theorem boundaryMap_dist_le_of_origin_fixed
    (L C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (f : C(Hyperboloid E, Hyperboloid F))
    (hf : ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C)
    (hf0 : f origin = origin) (ξ η : Metric.sphere (0 : E) 1) :
    let R := C + 1 + Real.log (4 * L ^ 2)
    let D := (2 * L ^ 2 + 1) * R + (L ^ 2 + 1) * C + 1
    let M := L ^ 2 * D + (L ^ 2 + 1) * C
    let A := 8 * Real.cosh (2 * (M + 1)) + 4
    dist (boundaryMap f ⟨L, C, hL, hC, hf⟩ ξ) (boundaryMap f ⟨L, C, hL, hC, hf⟩ η) ≤
      max 1 (Real.sqrt ((6 * A + 12 * Real.cosh (2 * L + C)) * Real.exp C)) *
        Real.rpow (dist ξ η / 2) (1 / (2 * L)) := by
  let R := C + 1 + Real.log (4 * L ^ 2)
  let D := (2 * L ^ 2 + 1) * R + (L ^ 2 + 1) * C + 1
  let M := L ^ 2 * D + (L ^ 2 + 1) * C
  let A := 8 * Real.cosh (2 * (M + 1)) + 4
  let Q := 6 * A + 12 * Real.cosh (2 * L + C)
  let H := max 1 (Real.sqrt (Q * Real.exp C))
  let g := boundaryMap f ⟨L, C, hL, hC, hf⟩
  change dist (g ξ) (g η) ≤ H * Real.rpow (dist ξ η / 2) (1 / (2 * L))
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hH : 0 ≤ H := zero_le_one.trans (le_max_left _ _)
  by_cases heq : ξ = η
  · subst η
    simp only [dist_self, zero_div, Real.rpow_eq_pow, Real.zero_rpow (by positivity : (1 / (2 * L) : ℝ) ≠ 0), mul_zero, le_refl]
  let δ := dist ξ η / 2
  have hδ : 0 < δ := div_pos (dist_pos.mpr heq) (by norm_num)
  have hδ1 : δ ≤ 1 := by
    have hn := norm_sub_le (ξ : E) (η : E)
    rw [norm_eq_of_mem_sphere, norm_eq_of_mem_sphere] at hn
    change dist ξ η / 2 ≤ 1
    simpa only [Subtype.dist_eq, dist_eq_norm] using (show ‖(ξ : E) - (η : E)‖ / 2 ≤ 1 by linarith)
  let t := -Real.log δ
  have ht : 0 ≤ t := neg_nonneg.mpr (Real.log_nonpos hδ.le hδ1)
  have hscale : Real.exp t * δ = 1 := by
    rw [show t = -Real.log δ from rfl, Real.exp_neg, Real.exp_log hδ, inv_mul_cancel₀ hδ.ne']
  let ray (u : Metric.sphere (0 : E) 1) : ℝ → Hyperboloid E :=
    geodesicLine origin (0, (u : E))
      (by simp [lorentzForm_apply, norm_eq_of_mem_sphere]) (by simp [lorentzForm_apply])
  have hray (u : Metric.sphere (0 : E) 1) : Isometry (ray u) := isometry_geodesicLine _ _ _ _
  have hray0 (u : Metric.sphere (0 : E) 1) : ray u 0 = origin := geodesicLine_zero _ _ _ _
  have hraydist (u : Metric.sphere (0 : E) 1) : dist origin (ray u t) = t := by
    rw [← hray0 u, (hray u).dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg ht]
  have hcosh : Real.cosh (dist (ray ξ t) (ray η t)) =
      1 + 2 * Real.sinh t ^ 2 * δ ^ 2 := by
    have hn := norm_sub_sq_real (ξ : E) (η : E)
    rw [norm_eq_of_mem_sphere, norm_eq_of_mem_sphere] at hn
    have hd : ‖(ξ : E) - (η : E)‖ = 2 * δ := by
      change ‖(ξ : E) - (η : E)‖ = 2 * (dist ξ η / 2)
      rw [Subtype.dist_eq, dist_eq_norm]
      ring
    rw [hd] at hn
    rw [cosh_dist]
    simp only [ray, geodesicLine_time, geodesicLine_space, origin_time, origin_space,
      mul_one, mul_zero, add_zero, smul_zero, zero_add, real_inner_smul_left, real_inner_smul_right]
    nlinarith [Real.cosh_sq_sub_sinh_sq t]
  have hsep : dist (ray ξ t) (ray η t) ≤ 2 := by
    have hs0 : 0 ≤ Real.sinh t := Real.sinh_nonneg_iff.mpr ht
    have hs : 2 * Real.sinh t ≤ Real.exp t := by
      linarith [Real.cosh_add_sinh t, Real.sinh_lt_cosh (x := t)]
    have hscaled := mul_le_mul_of_nonneg_right hs hδ.le
    have hsδ : 0 ≤ Real.sinh t * δ := mul_nonneg hs0 hδ.le
    have hsδle : Real.sinh t * δ ≤ 1 / 2 := by nlinarith only [hscaled, hscale]
    have hsδsq := (sq_le_sq₀ hsδ (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr hsδle
    have hcsmall : Real.cosh (dist (ray ξ t) (ray η t)) ≤ 3 / 2 := by
      rw [hcosh]
      nlinarith only [hsδsq]
    have hc2 : (3 / 2 : ℝ) ≤ Real.cosh 2 := by
      have hs1 : (1 : ℝ) ≤ Real.sinh 1 := Real.self_le_sinh_iff.mpr zero_le_one
      have hc := Real.cosh_two_mul (1 : ℝ)
      norm_num only [mul_one] at hc
      nlinarith [Real.cosh_sq_sub_sinh_sq (1 : ℝ)]
    have hh := Real.cosh_le_cosh.mp (hcsmall.trans hc2)
    simpa only [abs_of_nonneg dist_nonneg, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hh
  have herror (u : Metric.sphere (0 : E) 1) :
      ‖(kleinHomeomorph (f (ray u t)) : F) - (g u : F)‖ ^ 2 ≤ A * Real.exp (C - t / L) := by
    apply norm_kleinHomeomorph_sub_limit_sq_le (fun s => f (ray u s)) hL hC
      (f.continuous.comp (hray u).continuous).continuousOn
      (by rw [hray0, hf0])
    · intro s hs w hw
      simpa only [(hray u).dist_eq] using hf (ray u s) (ray u w)
    · exact tendsto_kleinHomeomorph_boundaryMap_origin_ray f ⟨L, C, hL, hC, hf⟩
        (u : E) (norm_eq_of_mem_sphere u)
    · exact ht
  let x := f (ray ξ t)
  let y := f (ray η t)
  have hxy : dist x y ≤ 2 * L + C := by
    have hh := (hf (ray ξ t) (ray η t)).2
    have hm := mul_le_mul_of_nonneg_left hsep hLp.le
    dsimp only [x, y]
    linarith
  have hrad : t / L - C ≤ dist origin x := by
    have hh := (hf origin (ray ξ t)).1
    rw [hf0, hraydist] at hh
    simpa only [div_eq_mul_inv, mul_comm] using hh
  have hinv : x.time⁻¹ ≤ 2 * Real.exp (C - t / L) := by
    have hlow : Real.exp (dist origin x) ≤ 2 * x.time := by
      rw [← cosh_dist_origin, Real.cosh_eq]
      linarith [Real.exp_pos (-dist origin x)]
    have hb : x.time⁻¹ ≤ 2 * Real.exp (-dist origin x) := by
      rw [Real.exp_neg, ← div_eq_mul_inv]
      apply (le_div_iff₀ (Real.exp_pos _)).mpr
      have hm := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr x.time_pos.le)
      have he := inv_mul_cancel₀ x.time_pos.ne'
      nlinarith only [hm, he]
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith only [hrad])) (by norm_num))
  have hmiddle : ‖(kleinHomeomorph x : F) - (kleinHomeomorph y : F)‖ ^ 2 ≤
      4 * Real.cosh (2 * L + C) * Real.exp (C - t / L) := by
    refine (norm_kleinHomeomorph_sub_sq_le x y hxy).trans ?_
    have hh := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ 2 * Real.cosh (2 * L + C))
    nlinarith only [hh]
  have htotal : dist (g ξ) (g η) ^ 2 ≤ Q * Real.exp (C - t / L) := by
    have hs := norm_sum_three_sq_le ((g ξ : F) - (kleinHomeomorph x : F))
      ((kleinHomeomorph x : F) - (kleinHomeomorph y : F)) ((kleinHomeomorph y : F) - (g η : F))
    have hsum : ((g ξ : F) - (kleinHomeomorph x : F)) +
        ((kleinHomeomorph x : F) - (kleinHomeomorph y : F)) +
          ((kleinHomeomorph y : F) - (g η : F)) = (g ξ : F) - (g η : F) := by abel
    rw [hsum, norm_sub_rev (g ξ : F) (kleinHomeomorph x : F)] at hs
    have hξ := herror ξ
    have hη := herror η
    simp only [Subtype.dist_eq, dist_eq_norm]
    dsimp only [Q]
    nlinarith only [hs, hξ, hη, hmiddle]
  let q := Real.rpow δ (1 / (2 * L))
  have hq : 0 ≤ q := Real.rpow_nonneg hδ.le _
  have hfactor : Real.exp (C - t / L) = Real.exp C * q ^ 2 := by
    rw [show q = Real.rpow δ (1 / (2 * L)) from rfl, Real.rpow_eq_pow, Real.rpow_def_of_pos hδ, sq, ← Real.exp_add,
      ← Real.exp_add]
    congr 1
    dsimp only [t]
    field_simp
    ring
  have hHsq : Q * Real.exp C ≤ H ^ 2 := by
    have hs := (sq_le_sq₀ (Real.sqrt_nonneg (Q * Real.exp C)) hH).mpr (le_max_right _ _)
    rwa [Real.sq_sqrt (mul_nonneg hQ (Real.exp_pos _).le)] at hs
  have hfinal : dist (g ξ) (g η) ^ 2 ≤ (H * q) ^ 2 := by
    rw [hfactor] at htotal
    have hh := mul_le_mul_of_nonneg_right hHsq (sq_nonneg q)
    nlinarith only [htotal, hh]
  exact (sq_le_sq₀ dist_nonneg (mul_nonneg hH hq)).mp hfinal

theorem exists_boundaryMap_half_chord_bound
    (L C B : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ (f : C(Hyperboloid E, Hyperboloid F))
      (hf : ∀ x y : Hyperboloid E,
        L⁻¹ * dist x y - C ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ L * dist x y + C),
      dist (origin : Hyperboloid F) (f origin) ≤ B →
      ∀ ξ η : Metric.sphere (0 : E) 1,
        dist (boundaryMap f ⟨L, C, hL, hC, hf⟩ ξ) (boundaryMap f ⟨L, C, hL, hC, hf⟩ η) / 2 ≤
          H * Real.rpow (dist ξ η / 2) (1 / (2 * L)) := by
  let R := C + 1 + Real.log (4 * L ^ 2)
  let D := (2 * L ^ 2 + 1) * R + (L ^ 2 + 1) * C + 1
  let M := L ^ 2 * D + (L ^ 2 + 1) * C
  let A := 8 * Real.cosh (2 * (M + 1)) + 4
  let H0 := max 1 (Real.sqrt ((6 * A + 12 * Real.cosh (2 * L + C)) * Real.exp C))
  refine ⟨Real.exp B * H0, ?_, ?_⟩
  · have hh : (1 : ℝ) * 1 ≤ Real.exp B * H0 :=
      mul_le_mul (Real.one_le_exp_iff.mpr hB) (le_max_left 1 _) zero_le_one (Real.exp_pos B).le
    simpa only [one_mul] using hh
  intro f hf hfB ξ η
  let e := boost (f origin)
  let f0 : C(Hyperboloid E, Hyperboloid F) := (e.symm : C(Hyperboloid F, Hyperboloid F)).comp f
  have hf0 : ∀ x y : Hyperboloid E,
      L⁻¹ * dist x y - C ≤ dist (f0 x) (f0 y) ∧ dist (f0 x) (f0 y) ≤ L * dist x y + C := by
    intro x y
    simpa only [f0, ContinuousMap.comp_apply, ContinuousMap.coe_apply, e.symm.dist_eq] using hf x y
  have hf00 : f0 origin = origin := by
    change (boost (f origin)).symm (f origin) = origin
    simpa only [boost_origin] using (boost (f origin)).symm_apply_apply (origin : Hyperboloid F)
  have heq (u : Metric.sphere (0 : E) 1) :
      boundaryMap f ⟨L, C, hL, hC, hf⟩ u =
        boundaryHomeomorph e (boundaryMap f0 ⟨L, C, hL, hC, hf0⟩ u) := by
    have hcomp := boundaryMap_comp f0 (e : C(Hyperboloid F, Hyperboloid F))
      ⟨L, C, hL, hC, hf0⟩ ⟨1, 0, by norm_num, by norm_num, fun x y => by simp [e.dist_eq]⟩
    have hfun : (e : C(Hyperboloid F, Hyperboloid F)).comp f0 = f := by
      apply ContinuousMap.ext
      intro x
      exact e.apply_symm_apply (f x)
    simp only [hfun, boundaryMap_isometryEquiv] at hcomp
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_apply] using
      congrArg (fun k => k u) hcomp
  have hnorm := boundaryMap_dist_le_of_origin_fixed L C hL hC f0 hf0 hf00 ξ η
  change dist (boundaryMap f0 ⟨L, C, hL, hC, hf0⟩ ξ)
    (boundaryMap f0 ⟨L, C, hL, hC, hf0⟩ η) ≤ H0 * Real.rpow (dist ξ η / 2) (1 / (2 * L)) at hnorm
  have hlip := (lipschitzWith_boundaryHomeomorph e).dist_le_mul
    (boundaryMap f0 ⟨L, C, hL, hC, hf0⟩ ξ) (boundaryMap f0 ⟨L, C, hL, hC, hf0⟩ η)
  change dist (boundaryHomeomorph e _) (boundaryHomeomorph e _) ≤
    Real.exp (dist (origin : Hyperboloid F) (e origin)) * _ at hlip
  have hbase : dist (origin : Hyperboloid F) (e origin) ≤ B := by
    simpa only [e, boost_origin] using hfB
  have heB := Real.exp_le_exp.mpr hbase
  rw [heq ξ, heq η]
  have hprod := mul_le_mul heB hnorm dist_nonneg (Real.exp_pos B).le
  have hdist := hlip.trans hprod
  nlinarith only [hdist, dist_nonneg (x := boundaryHomeomorph e (boundaryMap f0 ⟨L, C, hL, hC, hf0⟩ ξ))
    (y := boundaryHomeomorph e (boundaryMap f0 ⟨L, C, hL, hC, hf0⟩ η))]

end DifferentialGeometry.Hyperboloid
