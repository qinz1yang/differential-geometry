import DifferentialGeometry.Analysis.Calculus.SmoothTransition
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

end smoothMax
end Real
