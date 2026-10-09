import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksSlices
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Chapter-14 assembly, item L1, G3b / T1′: one-dimensional profiles of the necks

Lane ASM-L1e. The neck of a rim is `N (z, τ) = M̂ (z, g (8 τ))` for a master bicollar `M̂` whose
rim part is `rimChart (θ(z), f (8 (‖z‖ - 1)), s)` (lane notes in `build-logs/resume/state-ASM-L1e.md`).
This file provides the one-dimensional and radial ingredients.

* `planeUnit z`: the circle point of the direction of a nonzero vector of the plane
  (`planeOfCircle (planeUnit z) = ‖z‖⁻¹ • z`), smooth off the origin.
* `diskClamp w`: `w` as a point of the closed disk when `‖w‖ ≤ 1` (the centre otherwise).
* `exists_compression_profile`: a smooth function with positive derivative, the identity on
  `[c₁, c₂]` and with values in `(c₁ - κ, c₂ + κ)`: the primitive of
  `B + (1 - B) θ / (1 + t²)` with a plateau `B` (smooth transitions) and a small `θ`. It compresses
  the rim-chart coordinates of the closed neck box into the open rim box.
* `standardRimRounding_comp_nonpos_iff`: strictly increasing reparametrizations of both coordinates
  that are the identity on `[0, 3/4]` preserve the ball–handle side `{ψ ≤ 0}` of the standard rim
  rounding (the fillet lies in the band `x + y < 3/4`).
* radial maps `z ↦ φ (‖z‖²) • z`: smoothness, norm, injectivity and bijectivity of the differential
  (`radialMap`).
* `exists_handleRadialProfile`: the radial profile `P` of the handle side of a neck: smooth,
  `P 1 = 1`, `P > 0` and `r ↦ r P (r²)` strictly increasing on `[0, 1]`, and
  `r P (r²) = ρ (8 (r - 1))` near the rim (`1 - 11/128 ≤ r ≤ 1`), so that the handle side of the
  neck is the rim chart in the handle's product coordinates there.
-/

set_option autoImplicit false

noncomputable section

open Set Function Real
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

/-! ## The direction of a vector of the plane -/

/-- The circle point of the direction of a vector of the plane (`1` at the origin). -/
def planeUnit (z : EuclideanSpace ℝ (Fin 2)) : Circle :=
  unitOf (Complex.orthonormalBasisOneI.repr.symm z)

theorem planeOfCircle_planeUnit {z : EuclideanSpace ℝ (Fin 2)} (hz : z ≠ 0) :
    planeOfCircle (planeUnit z) = ‖z‖⁻¹ • z := by
  have hne : Complex.orthonormalBasisOneI.repr.symm z ≠ 0 := by
    intro h0
    apply hz
    have := congrArg Complex.orthonormalBasisOneI.repr h0
    simpa only [LinearIsometryEquiv.apply_symm_apply, map_zero] using this
  rw [planeOfCircle, planeUnit, coe_unitOf hne, LinearIsometryEquiv.norm_map, map_smul,
    LinearIsometryEquiv.apply_symm_apply]

theorem norm_smul_planeOfCircle_planeUnit {z : EuclideanSpace ℝ (Fin 2)} (hz : z ≠ 0) :
    ‖z‖ • planeOfCircle (planeUnit z) = z := by
  rw [planeOfCircle_planeUnit hz, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]

theorem planeUnit_smul_planeOfCircle {r : ℝ} (hr : 0 < r) (θ : Circle) :
    planeUnit (r • planeOfCircle θ) = θ := by
  rw [planeUnit, planeOfCircle, map_smul, LinearIsometryEquiv.symm_apply_apply]
  exact unitOf_smul hr θ

theorem planeUnit_smul {r : ℝ} (hr : 0 < r) (z : EuclideanSpace ℝ (Fin 2)) :
    planeUnit (r • z) = planeUnit z := by
  by_cases hz : z = 0
  · rw [hz, smul_zero]
  · have h := planeUnit_smul_planeOfCircle (mul_pos hr (norm_pos_iff.mpr hz)) (planeUnit z)
    rwa [mul_smul, norm_smul_planeOfCircle_planeUnit hz] at h

theorem contMDiffOn_planeUnit :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (𝓡 1) ∞ planeUnit {z | z ≠ 0} := by
  refine contMDiffOn_unitOf.comp
    Complex.orthonormalBasisOneI.repr.symm.contDiff.contMDiff.contMDiffOn ?_
  intro z hz h0
  apply hz
  have := congrArg Complex.orthonormalBasisOneI.repr h0
  simpa only [LinearIsometryEquiv.apply_symm_apply, map_zero] using this

/-- `w` as a point of the closed disk when `‖w‖ ≤ 1`, the centre otherwise. -/
def diskClamp (w : EuclideanSpace ℝ (Fin 2)) : ClosedCell 2 :=
  if h : ‖w‖ ≤ 1 then ⟨w, h⟩ else ⟨0, by simp⟩

theorem diskClamp_val {w : EuclideanSpace ℝ (Fin 2)} (h : ‖w‖ ≤ 1) :
    (diskClamp w : EuclideanSpace ℝ (Fin 2)) = w := by
  rw [diskClamp, dite_eq_left h]

/-! ## Compression profiles -/

/-- A smooth plateau: `1` on `[c₁, c₂]`, `0` off `(c₁ - δ, c₂ + δ)`, values in `[0, 1]`. -/
def plateau (c₁ c₂ δ t : ℝ) : ℝ :=
  smoothTransition ((t - (c₁ - δ)) / δ) * smoothTransition ((c₂ + δ - t) / δ)

theorem contDiff_plateau (c₁ c₂ δ : ℝ) : ContDiff ℝ ∞ (plateau c₁ c₂ δ) := by
  unfold plateau
  exact (smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ)).mul
    (smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const δ))

theorem plateau_nonneg (c₁ c₂ δ t : ℝ) : 0 ≤ plateau c₁ c₂ δ t :=
  mul_nonneg (smoothTransition.nonneg _) (smoothTransition.nonneg _)

theorem plateau_le_one (c₁ c₂ δ t : ℝ) : plateau c₁ c₂ δ t ≤ 1 := by
  unfold plateau
  have h1 := smoothTransition.le_one ((t - (c₁ - δ)) / δ)
  have h2 := smoothTransition.le_one ((c₂ + δ - t) / δ)
  have h3 := smoothTransition.nonneg ((t - (c₁ - δ)) / δ)
  have h4 := smoothTransition.nonneg ((c₂ + δ - t) / δ)
  nlinarith

theorem plateau_eq_one {c₁ c₂ δ t : ℝ} (hδ : 0 < δ) (ht : t ∈ Icc c₁ c₂) :
    plateau c₁ c₂ δ t = 1 := by
  unfold plateau
  rw [smoothTransition.one_of_one_le, smoothTransition.one_of_one_le, mul_one]
  · rw [le_div_iff₀ hδ]
    linarith [ht.2]
  · rw [le_div_iff₀ hδ]
    linarith [ht.1]

theorem plateau_eq_zero_of_le {c₁ c₂ δ t : ℝ} (hδ : 0 < δ) (ht : c₂ + δ ≤ t) :
    plateau c₁ c₂ δ t = 0 := by
  unfold plateau
  rw [smoothTransition.zero_of_nonpos (x := (c₂ + δ - t) / δ), mul_zero]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le

theorem plateau_eq_zero_of_ge {c₁ c₂ δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ c₁ - δ) :
    plateau c₁ c₂ δ t = 0 := by
  unfold plateau
  rw [smoothTransition.zero_of_nonpos (x := (t - (c₁ - δ)) / δ), zero_mul]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le

/-- The integrable weight `1 / (1 + t²)` (total mass `π`). -/
def rimWeight (t : ℝ) : ℝ := 1 / (1 + t ^ 2)

theorem contDiff_rimWeight : ContDiff ℝ ∞ rimWeight := by
  unfold rimWeight
  exact contDiff_const.div (contDiff_const.add (contDiff_id.pow 2)) (fun t => by positivity)

theorem rimWeight_pos (t : ℝ) : 0 < rimWeight t := by
  unfold rimWeight
  positivity

theorem rimWeight_le_one (t : ℝ) : rimWeight t ≤ 1 := by
  unfold rimWeight
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg t]

/-- The integrand of the compression profile. -/
def compressionDensity (c₁ c₂ δ θ t : ℝ) : ℝ :=
  plateau c₁ c₂ δ t + (1 - plateau c₁ c₂ δ t) * (θ * rimWeight t)

theorem contDiff_compressionDensity (c₁ c₂ δ θ : ℝ) :
    ContDiff ℝ ∞ (compressionDensity c₁ c₂ δ θ) := by
  unfold compressionDensity
  exact (contDiff_plateau c₁ c₂ δ).add
    ((contDiff_const.sub (contDiff_plateau c₁ c₂ δ)).mul (contDiff_const.mul contDiff_rimWeight))

theorem compressionDensity_pos {c₁ c₂ δ θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (t : ℝ) :
    0 < compressionDensity c₁ c₂ δ θ t := by
  unfold compressionDensity
  have hB0 := plateau_nonneg c₁ c₂ δ t
  have hB1 := plateau_le_one c₁ c₂ δ t
  have hw := rimWeight_pos t
  have hw1 := rimWeight_le_one t
  have hθw : θ * rimWeight t ≤ 1 := by nlinarith
  have hθw0 : 0 < θ * rimWeight t := mul_pos hθ hw
  nlinarith

theorem compressionDensity_le {c₁ c₂ δ θ : ℝ} (hθ : 0 < θ) (t : ℝ) :
    compressionDensity c₁ c₂ δ θ t ≤ plateau c₁ c₂ δ t + θ * rimWeight t := by
  unfold compressionDensity
  have hB0 := plateau_nonneg c₁ c₂ δ t
  have : 0 ≤ θ * rimWeight t := (mul_pos hθ (rimWeight_pos t)).le
  nlinarith

theorem compressionDensity_eq_one {c₁ c₂ δ θ t : ℝ} (hδ : 0 < δ) (ht : t ∈ Icc c₁ c₂) :
    compressionDensity c₁ c₂ δ θ t = 1 := by
  unfold compressionDensity
  rw [plateau_eq_one hδ ht]
  ring

/-- The integral of the plateau over `[c₂, y]` is at most `δ`. -/
theorem integral_plateau_right_le {c₁ c₂ δ : ℝ} (hδ : 0 < δ) {y : ℝ} (hy : c₂ ≤ y) :
    ∫ t in c₂..y, plateau c₁ c₂ δ t ≤ δ := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (plateau c₁ c₂ δ) MeasureTheory.volume a b :=
    fun a b => (contDiff_plateau c₁ c₂ δ).continuous.intervalIntegrable a b
  by_cases hym : y ≤ c₂ + δ
  · calc ∫ t in c₂..y, plateau c₁ c₂ δ t ≤ ∫ _ in c₂..y, (1 : ℝ) :=
          intervalIntegral.integral_mono_on hy (hint _ _) intervalIntegrable_const
            (fun t _ => plateau_le_one c₁ c₂ δ t)
      _ = y - c₂ := by simp
      _ ≤ δ := by linarith
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint c₂ (c₂ + δ))
      (hint (c₂ + δ) y)
    have hzero : ∫ t in (c₂ + δ)..y, plateau c₁ c₂ δ t = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
      · simp
      · intro t ht
        rw [uIcc_of_le (le_of_not_ge hym)] at ht
        exact plateau_eq_zero_of_le hδ ht.1
    have hfirst : ∫ t in c₂..(c₂ + δ), plateau c₁ c₂ δ t ≤ δ := by
      calc ∫ t in c₂..(c₂ + δ), plateau c₁ c₂ δ t ≤ ∫ _ in c₂..(c₂ + δ), (1 : ℝ) :=
            intervalIntegral.integral_mono_on (by linarith) (hint _ _) intervalIntegrable_const
              (fun t _ => plateau_le_one c₁ c₂ δ t)
        _ = δ := by simp
    linarith

/-- The integral of the plateau over `[y, c₁]` is at most `δ`. -/
theorem integral_plateau_left_le {c₁ c₂ δ : ℝ} (hδ : 0 < δ) {y : ℝ} (hy : y ≤ c₁) :
    ∫ t in y..c₁, plateau c₁ c₂ δ t ≤ δ := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (plateau c₁ c₂ δ) MeasureTheory.volume a b :=
    fun a b => (contDiff_plateau c₁ c₂ δ).continuous.intervalIntegrable a b
  by_cases hym : c₁ - δ ≤ y
  · calc ∫ t in y..c₁, plateau c₁ c₂ δ t ≤ ∫ _ in y..c₁, (1 : ℝ) :=
          intervalIntegral.integral_mono_on hy (hint _ _) intervalIntegrable_const
            (fun t _ => plateau_le_one c₁ c₂ δ t)
      _ = c₁ - y := by simp
      _ ≤ δ := by linarith
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint y (c₁ - δ))
      (hint (c₁ - δ) c₁)
    have hzero : ∫ t in y..(c₁ - δ), plateau c₁ c₂ δ t = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
      · simp
      · intro t ht
        rw [uIcc_of_le (le_of_not_ge hym)] at ht
        exact plateau_eq_zero_of_ge hδ ht.2
    have hsecond : ∫ t in (c₁ - δ)..c₁, plateau c₁ c₂ δ t ≤ δ := by
      calc ∫ t in (c₁ - δ)..c₁, plateau c₁ c₂ δ t ≤ ∫ _ in (c₁ - δ)..c₁, (1 : ℝ) :=
            intervalIntegral.integral_mono_on (by linarith) (hint _ _) intervalIntegrable_const
              (fun t _ => plateau_le_one c₁ c₂ δ t)
        _ = δ := by simp
    linarith

theorem integral_weight_le {θ : ℝ} (hθ : 0 < θ) (a b : ℝ) :
    ∫ t in a..b, θ * rimWeight t < θ * π := by
  rw [intervalIntegral.integral_const_mul]
  unfold rimWeight
  rw [integral_one_div_one_add_sq]
  have h1 := arctan_lt_pi_div_two b
  have h2 := neg_pi_div_two_lt_arctan a
  have : arctan b - arctan a < π := by linarith
  exact mul_lt_mul_of_pos_left this hθ

/-- **Compression profile.** A smooth function with positive derivative, the identity on
`[c₁, c₂]`, with values in `(c₁ - κ, c₂ + κ)`. -/
theorem exists_compression_profile {c₁ c₂ κ : ℝ} (hc : c₁ < c₂) (hκ : 0 < κ) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ (∀ y, 0 < deriv g y) ∧ (∀ y ∈ Icc c₁ c₂, g y = y) ∧
      ∀ y, c₁ - κ < g y ∧ g y < c₂ + κ := by
  set δ : ℝ := κ / 2 with hδdef
  set θ : ℝ := min 1 (κ / (4 * π)) with hθdef
  have hδ : 0 < δ := by positivity
  have hθ : 0 < θ := lt_min one_pos (by positivity)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθπ : θ * π ≤ κ / 4 := by
    have h := mul_le_mul_of_nonneg_right (min_le_right 1 (κ / (4 * π))) pi_pos.le
    rw [← hθdef] at h
    calc θ * π ≤ κ / (4 * π) * π := h
      _ = κ / 4 := by field_simp
  let h : ℝ → ℝ := compressionDensity c₁ c₂ δ θ
  have hh : ContDiff ℝ ∞ h := contDiff_compressionDensity c₁ c₂ δ θ
  have hcont : Continuous h := hh.continuous
  let g : ℝ → ℝ := fun y => c₁ + ∫ t in c₁..y, h t
  have hgd : ∀ y, HasDerivAt g (h y) y := fun y =>
    ((hcont.integral_hasStrictDerivAt c₁ y).hasDerivAt).const_add c₁
  have hderiv : deriv g = h := funext fun y => (hgd y).deriv
  have hint : ∀ a b : ℝ, IntervalIntegrable h MeasureTheory.volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have hid : ∀ y ∈ Icc c₁ c₂, g y = y := by
    intro y hy
    change c₁ + ∫ t in c₁..y, h t = y
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
    · simp
    · intro t ht
      rw [uIcc_of_le hy.1] at ht
      exact compressionDensity_eq_one hδ ⟨ht.1, ht.2.trans hy.2⟩
  have hmono : StrictMono g := strictMono_of_deriv_pos (fun y => by
    rw [hderiv]
    exact compressionDensity_pos hθ hθ1 y)
  refine ⟨g, ?_, ?_, hid, ?_⟩
  · rw [contDiff_infty_iff_deriv]
    exact ⟨fun y => (hgd y).differentiableAt, hderiv ▸ hh⟩
  · intro y
    rw [hderiv]
    exact compressionDensity_pos hθ hθ1 y
  · intro y
    have hgc₁ : g c₁ = c₁ := hid c₁ ⟨le_rfl, hc.le⟩
    have hgc₂ : g c₂ = c₂ := hid c₂ ⟨hc.le, le_rfl⟩
    constructor
    · by_cases hy : c₁ ≤ y
      · have := hmono.monotone hy
        linarith
      · push Not at hy
        -- `g y = c₁ - ∫_y^{c₁} h`
        have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint c₁ y) (hint y c₁)
        rw [intervalIntegral.integral_same] at hsplit
        have hP : IntervalIntegrable (plateau c₁ c₂ δ) MeasureTheory.volume y c₁ :=
          (contDiff_plateau c₁ c₂ δ).continuous.intervalIntegrable _ _
        have hW : IntervalIntegrable (fun t => θ * rimWeight t) MeasureTheory.volume y c₁ :=
          (continuous_const.mul contDiff_rimWeight.continuous).intervalIntegrable _ _
        have hbound : ∫ t in y..c₁, h t ≤
            ∫ t in y..c₁, (plateau c₁ c₂ δ t + θ * rimWeight t) :=
          intervalIntegral.integral_mono_on hy.le (hint _ _) (hP.add hW)
            (fun t _ => compressionDensity_le hθ t)
        rw [intervalIntegral.integral_add hP hW] at hbound
        have h1 := integral_plateau_left_le (c₂ := c₂) hδ hy.le
        have h2 := integral_weight_le hθ y c₁
        change c₁ - κ < c₁ + ∫ t in c₁..y, h t
        linarith
    · by_cases hy : y ≤ c₂
      · have := hmono.monotone hy
        linarith
      · push Not at hy
        have hsplit := intervalIntegral.integral_add_adjacent_intervals (hint c₁ c₂) (hint c₂ y)
        have hc₂' : ∫ t in c₁..c₂, h t = c₂ - c₁ := by
          have := hgc₂
          change c₁ + ∫ t in c₁..c₂, h t = c₂ at this
          linarith
        have hP : IntervalIntegrable (plateau c₁ c₂ δ) MeasureTheory.volume c₂ y :=
          (contDiff_plateau c₁ c₂ δ).continuous.intervalIntegrable _ _
        have hW : IntervalIntegrable (fun t => θ * rimWeight t) MeasureTheory.volume c₂ y :=
          (continuous_const.mul contDiff_rimWeight.continuous).intervalIntegrable _ _
        have hbound : ∫ t in c₂..y, h t ≤
            ∫ t in c₂..y, (plateau c₁ c₂ δ t + θ * rimWeight t) :=
          intervalIntegral.integral_mono_on hy.le (hint _ _) (hP.add hW)
            (fun t _ => compressionDensity_le hθ t)
        rw [intervalIntegral.integral_add hP hW] at hbound
        have h1 := integral_plateau_right_le (c₁ := c₁) hδ hy.le
        have h2 := integral_weight_le hθ c₂ y
        change c₁ + ∫ t in c₁..y, h t < c₂ + κ
        linarith

/-! ## Reparametrizations preserving the rounded side -/

/-- Strictly increasing reparametrizations of both rim coordinates that are the identity on
`[0, 3/4]` preserve the ball–handle side `{ψ ≤ 0}` of the standard rim rounding. -/
theorem standardRimRounding_comp_nonpos_iff {f g : ℝ → ℝ} (hf : StrictMono f)
    (hg : StrictMono g) (hf0 : ∀ x ∈ Icc (0 : ℝ) (3 / 4), f x = x)
    (hg0 : ∀ y ∈ Icc (0 : ℝ) (3 / 4), g y = y) {x y : ℝ} :
    standardRimRounding (f x, g y) ≤ 0 ↔ standardRimRounding (x, y) ≤ 0 := by
  have hf00 : f 0 = 0 := hf0 0 ⟨le_rfl, by norm_num⟩
  have hg00 : g 0 = 0 := hg0 0 ⟨le_rfl, by norm_num⟩
  have hf34 : f (3 / 4) = 3 / 4 := hf0 _ ⟨by norm_num, le_rfl⟩
  have hg34 : g (3 / 4) = 3 / 4 := hg0 _ ⟨by norm_num, le_rfl⟩
  constructor
  · intro h
    by_cases hy : g y ≤ 0
    · apply standardRimRounding_nonpos_of
      left
      by_contra hy'
      have := hg (not_le.mp hy')
      rw [hg00] at this
      exact absurd hy (not_le.mpr this)
    by_cases hx : f x ≤ 0
    · apply standardRimRounding_nonpos_of
      right
      by_contra hx'
      have := hf (not_le.mp hx')
      rw [hf00] at this
      exact absurd hx (not_le.mpr this)
    push Not at hx hy
    have hband := band_of_standardRimRounding_nonpos (f x, g y) hx hy h
    have hx0 : 0 < x := by
      by_contra hx0
      have := hf.monotone (not_lt.mp hx0)
      rw [hf00] at this
      linarith
    have hy0 : 0 < y := by
      by_contra hy0
      have := hg.monotone (not_lt.mp hy0)
      rw [hg00] at this
      linarith
    have hx1 : x < 3 / 4 := by
      by_contra hx1
      have := hf.monotone (not_lt.mp hx1)
      rw [hf34] at this
      simp only at hband
      linarith
    have hy1 : y < 3 / 4 := by
      by_contra hy1
      have := hg.monotone (not_lt.mp hy1)
      rw [hg34] at this
      simp only at hband
      linarith
    rwa [hf0 x ⟨hx0.le, hx1.le⟩, hg0 y ⟨hy0.le, hy1.le⟩] at h
  · intro h
    rcases standardRimRounding_nonpos_iff_or_fillet.mp h with hy | hx | ⟨hx, hy, -, hψ⟩
    · apply standardRimRounding_nonpos_of
      left
      have := hg.monotone hy
      rwa [hg00] at this
    · apply standardRimRounding_nonpos_of
      right
      have := hf.monotone hx
      rwa [hf00] at this
    · have hband := band_of_standardRimRounding_nonpos (x, y) hx hy hψ
      simp only at hband
      rwa [hf0 x ⟨hx.le, by linarith⟩, hg0 y ⟨hy.le, by linarith⟩]

/-! ## Radial maps of the plane -/

/-- The radial map `z ↦ φ (‖z‖²) • z`. -/
def radialMap (φ : ℝ → ℝ) (z : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  φ (‖z‖ ^ 2) • z

theorem contDiff_radialMap {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (radialMap φ) :=
  (hφ.comp (contDiff_norm_sq ℝ)).smul contDiff_id

theorem norm_radialMap {φ : ℝ → ℝ} (z : EuclideanSpace ℝ (Fin 2)) :
    ‖radialMap φ z‖ = |φ (‖z‖ ^ 2)| * ‖z‖ := by
  rw [radialMap, norm_smul, Real.norm_eq_abs]

/-- The differential of a radial map. -/
theorem hasFDerivAt_radialMap {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (z : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt (radialMap φ)
      (φ (‖z‖ ^ 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) +
        (deriv φ (‖z‖ ^ 2) • (2 • (innerSL ℝ z))).smulRight z) z := by
  have h1 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin 2) => ‖w‖ ^ 2) (2 • innerSL ℝ z) z :=
    hasStrictFDerivAt_norm_sq z |>.hasFDerivAt
  have h2 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin 2) => φ (‖w‖ ^ 2))
      (deriv φ (‖z‖ ^ 2) • (2 • innerSL ℝ z)) z := by
    have hd : HasDerivAt φ (deriv φ (‖z‖ ^ 2)) (‖z‖ ^ 2) :=
      ((hφ.differentiable (by simp)) _).hasDerivAt
    exact hd.comp_hasFDerivAt z h1
  exact h2.smul (hasFDerivAt_id z)

/-- The differential of a radial map is bijective where `φ (r²) ≠ 0` and `(r φ (r²))' ≠ 0`. -/
theorem bijective_fderiv_radialMap {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {z : EuclideanSpace ℝ (Fin 2)} (h0 : φ (‖z‖ ^ 2) ≠ 0)
    (h1 : φ (‖z‖ ^ 2) + 2 * ‖z‖ ^ 2 * deriv φ (‖z‖ ^ 2) ≠ 0) :
    Bijective (fderiv ℝ (radialMap φ) z) := by
  rw [(hasFDerivAt_radialMap hφ z).fderiv]
  set L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    φ (‖z‖ ^ 2) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) +
      (deriv φ (‖z‖ ^ 2) • (2 • (innerSL ℝ z))).smulRight z with hL
  have hLv : ∀ v, L v = φ (‖z‖ ^ 2) • v + (deriv φ (‖z‖ ^ 2) * (2 * inner ℝ z v)) • z := by
    intro v
    have e : deriv φ (‖z‖ ^ 2) * (2 * inner ℝ z v) =
        deriv φ (‖z‖ ^ 2) * inner ℝ z v + deriv φ (‖z‖ ^ 2) * inner ℝ z v := by ring
    rw [e]
    simp [hL, two_smul]
  have hinj : Injective L := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    rw [hLv] at hv
    have hin := congrArg (fun w => inner ℝ z w) hv
    simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, inner_zero_right]
      at hin
    have hzv : inner ℝ z v = 0 := by
      have : (φ (‖z‖ ^ 2) + 2 * ‖z‖ ^ 2 * deriv φ (‖z‖ ^ 2)) * inner ℝ z v = 0 := by
        linear_combination hin
      exact (mul_eq_zero.mp this).resolve_left h1
    rw [hzv, mul_zero, mul_zero, zero_smul, add_zero] at hv
    exact (smul_eq_zero.mp hv).resolve_left h0
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := L.toLinearMap)).mp hinj⟩

/-- The radial derivative of `r ↦ r P (r²)`. -/
theorem hasDerivAt_mul_comp_sq {P : ℝ → ℝ} (hP : ContDiff ℝ ∞ P) (r : ℝ) :
    HasDerivAt (fun r : ℝ => r * P (r ^ 2)) (P (r ^ 2) + 2 * r ^ 2 * deriv P (r ^ 2)) r := by
  have hd : HasDerivAt P (deriv P (r ^ 2)) (r ^ 2) := ((hP.differentiable (by simp)) _).hasDerivAt
  have h2 : HasDerivAt (fun r : ℝ => P (r ^ 2)) (deriv P (r ^ 2) * (2 * r)) r := by
    have hsq : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    exact HasDerivAt.comp (h := fun r : ℝ => r ^ 2) r hd hsq
  have h3 := (hasDerivAt_id' r).mul h2
  convert h3 using 1
  ring

theorem deriv_mul_comp_sq {P : ℝ → ℝ} (hP : ContDiff ℝ ∞ P) (r : ℝ) :
    deriv (fun r : ℝ => r * P (r ^ 2)) r = P (r ^ 2) + 2 * r ^ 2 * deriv P (r ^ 2) :=
  (hasDerivAt_mul_comp_sq hP r).deriv

/-- A radial map whose profile `r ↦ r φ (r²)` is strictly increasing on `[0, R]`, with `φ > 0`
there, is injective on the closed ball of radius `R`. -/
theorem radialMap_injOn {φ : ℝ → ℝ} {R : ℝ}
    (hpos : ∀ r, 0 ≤ r → r ≤ R → 0 < φ (r ^ 2))
    (hmono : StrictMonoOn (fun r : ℝ => r * φ (r ^ 2)) (Icc 0 R)) :
    InjOn (radialMap φ) (Metric.closedBall 0 R) := by
  intro z hz z' hz' h
  rw [Metric.mem_closedBall, dist_zero_right] at hz hz'
  have hn := congrArg norm h
  rw [norm_radialMap, norm_radialMap, abs_of_pos (hpos _ (norm_nonneg _) hz),
    abs_of_pos (hpos _ (norm_nonneg _) hz'), mul_comm, mul_comm _ ‖z'‖] at hn
  have hzz : ‖z‖ = ‖z'‖ := hmono.injOn ⟨norm_nonneg _, hz⟩ ⟨norm_nonneg _, hz'⟩ hn
  have h' : φ (‖z‖ ^ 2) • z = φ (‖z‖ ^ 2) • z' := by
    have := h
    rw [radialMap, radialMap, ← hzz] at this
    exact this
  exact smul_right_injective _ (hpos _ (norm_nonneg _) hz).ne' h'

/-! ## The radial profile of the handle side -/

theorem sqrt_sq_of_nonneg' {r : ℝ} (hr : 0 ≤ r) : √(r ^ 2) = r :=
  Real.sqrt_sq hr

/-- The radial profile of the handle side of a neck. -/
def handleRadialProfile (ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ρ (-3 / 4) + smoothTransition ((t - (233 / 256) ^ 2) / ((117 / 128) ^ 2 - (233 / 256) ^ 2)) *
    (ρ (8 * (√t - 1)) / √t - ρ (-3 / 4))

theorem handleRadialProfile_mul_sq (ρ : ℝ → ℝ) {r : ℝ} (hr : 0 < r) :
    r * handleRadialProfile ρ (r ^ 2) = ρ (-3 / 4) * r +
      smoothTransition ((r ^ 2 - (233 / 256) ^ 2) / ((117 / 128) ^ 2 - (233 / 256) ^ 2)) *
        (ρ (8 * (r - 1)) - ρ (-3 / 4) * r) := by
  unfold handleRadialProfile
  rw [sqrt_sq_of_nonneg' hr.le]
  field_simp

/-- **The radial profile of the handle side.** -/
theorem exists_handleRadialProfile {a : ℝ} (ha : 3 / 4 < a) {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρ0 : ρ 0 = 1) (hρd : ∀ x ∈ Ioc (-a) 0, 0 < ρ x ∧ 0 < deriv ρ x) :
    ∃ P : ℝ → ℝ, ContDiff ℝ ∞ P ∧ P 1 = 1 ∧ (∀ s, 0 ≤ s → s ≤ 1 → 0 < P s) ∧
      (∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P (r ^ 2)) r) ∧
      ∀ r, 1 - 11 / 128 ≤ r → r ≤ 1 → r * P (r ^ 2) = ρ (8 * (r - 1)) := by
  set t₀ : ℝ := (233 / 256) ^ 2 with ht₀
  set t₁ : ℝ := (117 / 128) ^ 2 with ht₁
  have ht01 : t₀ < t₁ := by rw [ht₀, ht₁]; norm_num
  have ht0pos : 0 < t₀ := by rw [ht₀]; norm_num
  set β : ℝ → ℝ := fun t => smoothTransition ((t - t₀) / (t₁ - t₀)) with hβ
  have hβc : ContDiff ℝ ∞ β :=
    smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  have hβ0 : ∀ t, t ≤ t₀ → β t = 0 := fun t ht =>
    smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
  have hβ1 : ∀ t, t₁ ≤ t → β t = 1 := fun t ht => smoothTransition.one_of_one_le (by
    rw [le_div_iff₀ (by linarith)]
    linarith)
  have hβmono : Monotone β := fun x y hxy =>
    smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) (by linarith))
  have hβnn : ∀ t, 0 ≤ β t := fun t => smoothTransition.nonneg _
  have hβle : ∀ t, β t ≤ 1 := fun t => smoothTransition.le_one _
  set lam : ℝ := ρ (-3 / 4) with hlamdef
  have hmem34 : (-3 / 4 : ℝ) ∈ Ioc (-a) 0 := ⟨by linarith, by norm_num⟩
  have hlam : 0 < lam := (hρd _ hmem34).1
  -- `ρ` is increasing on `[-3/4, 0]`
  have hρmono : StrictMonoOn ρ (Icc (-3 / 4) 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hρ.continuous.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    exact (hρd x ⟨by linarith [hx.1], hx.2.le⟩).2
  have hP : handleRadialProfile ρ = fun t => lam + β t * (ρ (8 * (√t - 1)) / √t - lam) := rfl
  have hPc : ContDiff ℝ ∞ (handleRadialProfile ρ) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : t < t₀
    · have hev : handleRadialProfile ρ =ᶠ[𝓝 t] fun _ => lam := by
        filter_upwards [Iio_mem_nhds ht] with t' ht'
        rw [hP]
        simp only
        rw [hβ0 t' (le_of_lt ht'), zero_mul, add_zero]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have htpos : t ≠ 0 := by
        intro h0
        rw [h0] at ht
        exact ht ht0pos
      rw [hP]
      have hsq : ContDiffAt ℝ ∞ (fun t : ℝ => √t) t := Real.contDiffAt_sqrt htpos
      have hsqne : √t ≠ 0 := by
        rw [Real.sqrt_ne_zero']
        push Not at ht
        linarith
      exact contDiffAt_const.add (hβc.contDiffAt.mul
        (((hρ.contDiffAt.comp t (contDiffAt_const.mul (hsq.sub contDiffAt_const))).div hsq hsqne).sub
          contDiffAt_const))
  refine ⟨handleRadialProfile ρ, hPc, ?_, ?_, ?_, ?_⟩
  · rw [hP]
    simp only [Real.sqrt_one, sub_self, mul_zero, hρ0, div_one]
    rw [hβ1 1 (by rw [ht₁]; norm_num)]
    ring
  · intro s hs0 hs1
    rw [hP]
    simp only
    by_cases hst : s ≤ t₀
    · rw [hβ0 s hst, zero_mul, add_zero]
      exact hlam
    · push Not at hst
      have hsqrt : 233 / 256 ≤ √s := by
        rw [show (233 / 256 : ℝ) = √t₀ by rw [ht₀, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt hst.le
      have hsqrt1 : √s ≤ 1 := by
        rw [show (1 : ℝ) = √1 by rw [Real.sqrt_one]]
        exact Real.sqrt_le_sqrt hs1
      have hx : 8 * (√s - 1) ∈ Ioc (-a) 0 := ⟨by linarith, by linarith⟩
      have hq : 0 < ρ (8 * (√s - 1)) / √s := div_pos (hρd _ hx).1 (by linarith)
      have h0 := hβnn s
      have h1 := hβle s
      by_cases hb : β s ≤ 1 / 2
      · nlinarith [mul_nonneg h0 hq.le]
      · push Not at hb
        nlinarith [mul_nonneg (sub_nonneg.mpr h1) hlam.le]
  · intro r hr0 hr1
    by_cases hrt : r ^ 2 < t₀
    · -- near the centre the profile is linear
      have hev : (fun r : ℝ => r * handleRadialProfile ρ (r ^ 2)) =ᶠ[𝓝 r] fun r => lam * r := by
        have hopen : IsOpen {r : ℝ | r ^ 2 < t₀} :=
          isOpen_lt (continuous_pow 2) continuous_const
        filter_upwards [hopen.mem_nhds hrt] with r' hr'
        rw [hP]
        simp only
        rw [hβ0 _ (le_of_lt hr'), zero_mul, add_zero, mul_comm]
      rw [hev.deriv_eq]
      have : HasDerivAt (fun r : ℝ => lam * r) lam r := by
        simpa using (hasDerivAt_id r).const_mul lam
      rw [this.deriv]
      exact hlam
    · push Not at hrt
      have hr : 233 / 256 ≤ r := by
        by_contra hcon
        push Not at hcon
        have : r ^ 2 < t₀ := by rw [ht₀]; nlinarith
        linarith
      have hrpos : 0 < r := by linarith
      have hx : 8 * (r - 1) ∈ Ioc (-a) 0 := ⟨by linarith, by linarith⟩
      -- the profile near `r`
      set F : ℝ → ℝ := fun r => lam * r + β (r ^ 2) * (ρ (8 * (r - 1)) - lam * r) with hF
      have hev : (fun r : ℝ => r * handleRadialProfile ρ (r ^ 2)) =ᶠ[𝓝 r] F := by
        filter_upwards [Ioi_mem_nhds hrpos] with r' hr'
        exact handleRadialProfile_mul_sq ρ hr'
      have hβd : HasDerivAt (fun r : ℝ => β (r ^ 2)) (deriv β (r ^ 2) * (2 * r)) r := by
        have hd : HasDerivAt β (deriv β (r ^ 2)) (r ^ 2) :=
          ((hβc.differentiable (by simp)) _).hasDerivAt
        have hsq : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
          simpa using hasDerivAt_pow 2 r
        exact HasDerivAt.comp (h := fun r : ℝ => r ^ 2) r hd hsq
      have hρd' : HasDerivAt (fun r : ℝ => ρ (8 * (r - 1))) (deriv ρ (8 * (r - 1)) * 8) r := by
        have hd : HasDerivAt ρ (deriv ρ (8 * (r - 1))) (8 * (r - 1)) :=
          ((hρ.differentiable (by simp)) _).hasDerivAt
        have hlin : HasDerivAt (fun r : ℝ => 8 * (r - 1)) 8 r := by
          simpa using ((hasDerivAt_id r).sub_const 1).const_mul 8
        exact hd.comp r hlin
      have hFd : HasDerivAt F (lam + (deriv β (r ^ 2) * (2 * r) * (ρ (8 * (r - 1)) - lam * r) +
          β (r ^ 2) * (deriv ρ (8 * (r - 1)) * 8 - lam))) r := by
        have hlin : HasDerivAt (fun r : ℝ => lam * r) lam r := by
          simpa using (hasDerivAt_id r).const_mul lam
        exact hlin.add (hβd.mul (hρd'.sub hlin))
      rw [hev.deriv_eq, hFd.deriv]
      have hβ'nn : 0 ≤ deriv β (r ^ 2) := hβmono.deriv_nonneg
      have hρge : lam ≤ ρ (8 * (r - 1)) := by
        rcases eq_or_lt_of_le (show (-3 / 4 : ℝ) ≤ 8 * (r - 1) by linarith) with heq | hlt
        · rw [hlamdef, heq]
        · exact (hρmono ⟨le_rfl, by norm_num⟩ ⟨hlt.le, by linarith⟩ hlt).le
      have hterm : 0 ≤ deriv β (r ^ 2) * (2 * r) * (ρ (8 * (r - 1)) - lam * r) := by
        apply mul_nonneg (mul_nonneg hβ'nn (by linarith))
        nlinarith
      have hρ' := (hρd _ hx).2
      have h0 := hβnn (r ^ 2)
      have h1 := hβle (r ^ 2)
      have hmain : 0 < lam + β (r ^ 2) * (deriv ρ (8 * (r - 1)) * 8 - lam) := by
        by_cases hb : β (r ^ 2) ≤ 1 / 2
        · nlinarith [mul_nonneg h0 hρ'.le]
        · push Not at hb
          nlinarith [mul_nonneg (sub_nonneg.mpr h1) hlam.le]
      linarith
  · intro r hr hr1
    have hrpos : 0 < r := by linarith
    rw [handleRadialProfile_mul_sq ρ hrpos]
    rw [show smoothTransition ((r ^ 2 - (233 / 256) ^ 2) / ((117 / 128) ^ 2 - (233 / 256) ^ 2)) = 1
      from hβ1 (r ^ 2) (by rw [ht₁]; nlinarith)]
    ring

end GC.GraphManifold.Assembly
