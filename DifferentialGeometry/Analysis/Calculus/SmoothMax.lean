import DifferentialGeometry.Analysis.Calculus.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped ContDiff

namespace Real

noncomputable def smoothMax (ε x y : ℝ) : ℝ :=
  (x + y + smoothAbs ε (x - y)) / 2

namespace smoothMax

theorem contDiff (ε : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => smoothMax ε p.1 p.2) :=
  ((contDiff_fst.add contDiff_snd).add
    ((smoothAbs.contDiff ε).comp (contDiff_fst.sub contDiff_snd))).div_const 2

theorem comm {ε : ℝ} (hε : ε ≠ 0) (x y : ℝ) : smoothMax ε x y = smoothMax ε y x := by
  unfold smoothMax
  rw [show y - x = -(x - y) by ring, smoothAbs.neg hε]
  ring

theorem add_right (ε x y a : ℝ) :
    smoothMax ε (x + a) (y + a) = smoothMax ε x y + a := by
  unfold smoothMax
  rw [show x + a - (y + a) = x - y by ring]
  ring

theorem eq_max_of_le {ε x y : ℝ} (hε : 0 < ε) (hxy : ε ≤ |x - y|) :
    smoothMax ε x y = max x y := by
  unfold smoothMax
  rw [smoothAbs.eq_abs_of_le hε hxy]
  rcases le_total x y with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem sub_max_mem_Icc {ε : ℝ} (hε : 0 < ε) (x y : ℝ) :
    smoothMax ε x y - max x y ∈ Set.Icc 0 ε := by
  obtain ⟨hl, hu⟩ := smoothAbs.sub_abs_mem_Icc hε (x - y)
  unfold smoothMax
  rcases le_total x y with h | h
  · rw [max_eq_right h]
    rw [abs_of_nonpos (sub_nonpos.mpr h)] at hl hu
    constructor <;> linarith
  · rw [max_eq_left h]
    rw [abs_of_nonneg (sub_nonneg.mpr h)] at hl hu
    constructor <;> linarith

theorem max_le {ε : ℝ} (hε : 0 < ε) (x y : ℝ) : max x y ≤ smoothMax ε x y :=
  sub_nonneg.mp (sub_max_mem_Icc hε x y).1

theorem le_max_add {ε : ℝ} (hε : 0 < ε) (x y : ℝ) : smoothMax ε x y ≤ max x y + ε := by
  have h := (sub_max_mem_Icc hε x y).2
  linarith

theorem monotone_left (ε y : ℝ) : Monotone (fun x => smoothMax ε x y) := by
  intro x z hxz
  have h := (smoothAbs.lipschitzWith ε).dist_le_mul (x - y) (z - y)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul,
    show x - y - (z - y) = x - z by ring,
    abs_of_nonpos (sub_nonpos.mpr hxz)] at h
  have hh := (abs_le.mp h).2
  unfold smoothMax
  linarith

theorem monotone_right (ε x : ℝ) : Monotone (smoothMax ε x) := by
  intro y z hyz
  have h := (smoothAbs.lipschitzWith ε).dist_le_mul (x - y) (x - z)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul,
    show x - y - (x - z) = z - y by ring,
    abs_of_nonneg (sub_nonneg.mpr hyz)] at h
  have hh := (abs_le.mp h).2
  unfold smoothMax
  linarith

theorem abs_sub_le_max (ε x y x' y' : ℝ) :
    |smoothMax ε x y - smoothMax ε x' y'| ≤ max |x - x'| |y - y'| := by
  let d := max |x - x'| |y - y'|
  have hxx : |x - x'| ≤ d := le_max_left _ _
  have hyy : |y - y'| ≤ d := le_max_right _ _
  have hupper : smoothMax ε x y ≤ smoothMax ε x' y' + d := by
    calc
      smoothMax ε x y ≤ smoothMax ε (x' + d) y :=
        (monotone_left ε y) (by linarith [(abs_le.mp hxx).2])
      _ ≤ smoothMax ε (x' + d) (y' + d) :=
        (monotone_right ε (x' + d)) (by linarith [(abs_le.mp hyy).2])
      _ = smoothMax ε x' y' + d := add_right ε x' y' d
  have hlower : smoothMax ε x' y' ≤ smoothMax ε x y + d := by
    calc
      smoothMax ε x' y' ≤ smoothMax ε (x + d) y' :=
        (monotone_left ε y') (by linarith [(abs_le.mp hxx).1])
      _ ≤ smoothMax ε (x + d) (y + d) :=
        (monotone_right ε (x + d)) (by linarith [(abs_le.mp hyy).1])
      _ = smoothMax ε x y + d := add_right ε x y d
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem lipschitzWith (ε : ℝ) :
    LipschitzWith 1 (fun p : ℝ × ℝ => smoothMax ε p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simpa only [Prod.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] using
    abs_sub_le_max ε p.1 p.2 q.1 q.2

theorem convexOn {ε : ℝ} (hε : 0 < ε) :
    ConvexOn ℝ Set.univ (fun p : ℝ × ℝ => smoothMax ε p.1 p.2) := by
  let L : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ
  have hA : ConvexOn ℝ Set.univ (fun p : ℝ × ℝ => smoothAbs ε (p.1 - p.2)) := by
    simpa only [Set.preimage_univ, Function.comp_def, L, LinearMap.sub_apply,
      LinearMap.fst_apply, LinearMap.snd_apply] using (smoothAbs.convexOn hε).comp_linearMap L
  have hlin : ConvexOn ℝ Set.univ (fun p : ℝ × ℝ => p.1 + p.2) :=
    (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).convexOn convex_univ
  have h := ConvexOn.smul (show (0 : ℝ) ≤ (2 : ℝ)⁻¹ by norm_num) (hlin.add hA)
  convert! h using 1
  funext p
  dsimp [smoothMax]
  ring

theorem mul_left (a ε x y : ℝ) :
    smoothMax (a * ε) (a * x) (a * y) = a * smoothMax ε x y := by
  unfold smoothMax
  rw [← mul_sub, smoothAbs.mul_left]
  ring

theorem div (ε x y a : ℝ) :
    smoothMax (ε / a) (x / a) (y / a) = smoothMax ε x y / a := by
  simpa only [div_eq_mul_inv, mul_comm] using smoothMax.mul_left a⁻¹ ε x y

theorem deriv_left_mem_Icc (ε x y : ℝ) :
    deriv (fun z => Real.smoothMax ε z y) x ∈ Set.Icc (0 : ℝ) 1 := by
  have hLip : LipschitzWith 1 (fun z => Real.smoothMax ε z y) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, sub_self, abs_zero,
      max_eq_left (abs_nonneg (a - b))] using abs_sub_le_max ε a y b y
  have hbound := norm_deriv_le_of_lipschitz hLip (x₀ := x)
  refine ⟨(monotone_left ε y).deriv_nonneg, ?_⟩
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, NNReal.coe_one] using hbound)

theorem deriv_right_mem_Icc (ε x y : ℝ) :
    deriv (Real.smoothMax ε x) y ∈ Set.Icc (0 : ℝ) 1 := by
  have hLip : LipschitzWith 1 (Real.smoothMax ε x) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, sub_self, abs_zero,
      max_eq_right (abs_nonneg (a - b))] using abs_sub_le_max ε x a x b
  have hbound := norm_deriv_le_of_lipschitz hLip (x₀ := y)
  refine ⟨(monotone_right ε x).deriv_nonneg, ?_⟩
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, NNReal.coe_one] using hbound)

theorem fderiv_apply_one_one (ε x y : ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => Real.smoothMax ε p.1 p.2) (x, y) (1, 1) = 1 := by
  have h := ((contDiff ε).differentiable (by simp) (x, y)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => (x + t, y + t)) (1, 1) 0 :=
    ((hasDerivAt_id 0).const_add x).prodMk ((hasDerivAt_id 0).const_add y)
  have hbase : HasFDerivAt (fun p : ℝ × ℝ => Real.smoothMax ε p.1 p.2)
      (fderiv ℝ (fun p : ℝ × ℝ => Real.smoothMax ε p.1 p.2) (x, y))
      (x + 0, y + 0) := by simpa only [add_zero] using h
  have hc := hbase.comp_hasDerivAt 0 hline
  have hid : HasDerivAt (fun t : ℝ => Real.smoothMax ε (x + t) (y + t)) 1 0 := by
    simpa only [Real.smoothMax.add_right, id_eq] using
      (hasDerivAt_id 0).const_add (Real.smoothMax ε x y)
  simpa only [add_zero] using hc.unique hid
theorem surjective_fderiv_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ × ℝ} {f' : E →L[ℝ] ℝ × ℝ} {x : E}
    (hdf : HasFDerivAt f f' x) (hsurj : Function.Surjective f') (ε : ℝ) :
    Function.Surjective (fderiv ℝ (fun y => Real.smoothMax ε (f y).1 (f y).2) x) := by
  have h := (((contDiff ε).differentiable (by simp) (f x)).hasFDerivAt.comp x hdf).fderiv
  simp only [Function.comp_def] at h
  intro y
  obtain ⟨v, hv⟩ := hsurj (y, y)
  refine ⟨v, ?_⟩
  rw [h, ContinuousLinearMap.comp_apply, hv,
    show (y, y) = y • (1, 1) by simp, map_smul]
  have hp := fderiv_apply_one_one ε (f x).1 (f x).2
  simp only [hp, smul_eq_mul, mul_one]

theorem comp_convexOn {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {s : Set E} {f g : E → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hf : ConvexOn ℝ s f) (hg : ConvexOn ℝ s g) :
    ConvexOn ℝ s (fun x => smoothMax ε (f x) (g x)) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hleft := monotone_left ε (g (a • x + b • y)) (hf.2 hx hy ha hb hab)
  have hright := monotone_right ε (a • f x + b • f y) (hg.2 hx hy ha hb hab)
  exact (hleft.trans hright).trans ((convexOn hε).2 (Set.mem_univ (f x, g x))
    (Set.mem_univ (f y, g y)) ha hb hab)

theorem deriv_comp_neg {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hf' : deriv f x < 0) (hg' : deriv g x < 0) (ε : ℝ) :
    deriv (fun t => Real.smoothMax ε (f t) (g t)) x < 0 := by
  let d := deriv (Real.smoothAbs ε) (f x - g x)
  have hd : |d| ≤ 1 := by
    simpa only [Real.norm_eq_abs, NNReal.coe_one] using
      norm_deriv_le_of_lipschitz (Real.smoothAbs.lipschitzWith ε) (x₀ := f x - g x)
  have habs := ((Real.smoothAbs.contDiff ε).differentiable (by simp)
    (f x - g x)).hasDerivAt.comp x (hf.hasDerivAt.sub hg.hasDerivAt)
  have hh := ((hf.hasDerivAt.add hg.hasDerivAt).add habs).div_const 2
  simp only [Pi.add_apply, Pi.sub_apply, Function.comp_def] at hh
  have heq : deriv (fun t => Real.smoothMax ε (f t) (g t)) x =
      ((1 + d) * deriv f x + (1 - d) * deriv g x) / 2 := by
    rw [show (fun t => Real.smoothMax ε (f t) (g t)) =
      (fun t => (f t + g t + Real.smoothAbs ε (f t - g t)) / 2) from rfl, hh.deriv]
    dsimp [d]
    ring
  rw [heq]
  have h1 : 0 ≤ 1 + d := by linarith [(abs_le.mp hd).1]
  have h2 : 0 ≤ 1 - d := by linarith [(abs_le.mp hd).2]
  have hn1 := mul_nonpos_of_nonneg_of_nonpos h1 hf'.le
  have hn2 := mul_nonpos_of_nonneg_of_nonpos h2 hg'.le
  rcases lt_or_eq_of_le h1 with hpos | hz
  · have hh := mul_neg_of_pos_of_neg hpos hf'
    linarith
  · have hh := mul_neg_of_pos_of_neg (show 0 < 1 - d by linarith) hg'
    linarith

end smoothMax
end Real
