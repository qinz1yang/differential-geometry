import DifferentialGeometry.Geometry.Comparison.FourPoint
import DifferentialGeometry.Geometry.Metric.RadialConeData

/-!
# Chords of rays under nonnegative four-point comparison

Tier T1 ("RayChord") of the Tits-cone producer of chapter 13: steps I1–I4 of the design
`docs/geometrization/chapter13/design-tits-cone-20261004.md` (§2, frozen interface §4), the metric
form of the blueprint's LFR55–LFR56 (`docs/geometrization/blueprint/master207A.tex:29600–29926`).

A ray from `q` is a map `γ : ℝ≥0 → Y` with `Isometry γ ∧ γ 0 = q`; it is written inline, so no
predicate is introduced. Throughout, `Y` satisfies `fourPointComparison 0 univ`, and
`K(x, y) = radialConeKernel q x y = (|qx|² + |qy|² - |xy|²) / 2`.

* I1 `radialConeKernel_le_mul_of_segment`: along a segment from `q`, `K` is sub-proportional.
  This is the κ = 0 quadratic side comparison `quadratic_side_comparison_of_fourPointComparison`
  (`FourPoint.lean:72`) rewritten in the kernel.
* `mul_mul_radialConeKernel_le_of_ray`: the normalized kernel `K(γ s, σ u) / (s u)`, the cosine of
  the Euclidean comparison angle at `q`, is monotone in both radii; equivalently the comparison angle
  is antitone (`metricComparisonAngle_le_of_ray`).
* I2 `antitoneOn_dist_div_of_ray`: the chord quotient `d(γ t, σ t) / t` is antitone on `t > 0`, and
  it converges to its infimum `rayChordLimit γ σ` (`tendsto_dist_div_rayChordLimit`). More generally
  `d(γ (a t), σ (b t)) / t` is antitone in `t` (`antitoneOn_dist_mul_div_of_ray`).
* I3 `tendsto_dist_mul_div_of_ray`: the cosine law at infinity,
  `d(γ (a t), σ (b t)) / t → √((a - b)² + a b ρ∞²)` for all radii `a, b ≥ 0`, with
  `ρ∞ = rayChordLimit`.
  The comparison angle converges to the limit angle `θ∞ = arccos (1 - ρ∞² / 2)`
  (`tendsto_metricComparisonAngle_of_ray`), and the limit is the Euclidean cone chord
  `√(a² + b² - 2 a b cos θ∞)` (`sqrt_rayChord_eq_sqrt_cos`).
* I4 `sqrt_le_dist_mul_div_of_ray`: the limit chord never exceeds the quotient at any scale `t > 0`.
* The limit chord is homogeneous (`sqrt_rayChord_mul_left`), and on (ray, radius) pairs it is
  symmetric, vanishes on the diagonal and satisfies the triangle inequality
  (`sqrt_rayChord_comm`, `sqrt_rayChord_self`, `sqrt_rayChord_triangle`), so it is a
  pseudo-distance.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped NNReal Topology

namespace GC.MetricGeometry

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {Y : Type*} [MetricSpace Y]

/-- The asymptotic chord `inf_{t>0} d(γ t, σ t) / t` of two maps `ℝ≥0 → Y`. For two rays from a
common point of a space with `fourPointComparison 0 univ` it is the limit of `d(γ t, σ t) / t`
(`tendsto_dist_div_rayChordLimit`). -/
def rayChordLimit (γ σ : ℝ≥0 → Y) : ℝ :=
  ⨅ t : {t : ℝ≥0 // 0 < t}, dist (γ t) (σ t) / (t : ℝ)

/-! ## The infimum -/

theorem rayChordLimit_le (γ σ : ℝ≥0 → Y) {t : ℝ≥0} (ht : 0 < t) :
    rayChordLimit γ σ ≤ dist (γ t) (σ t) / (t : ℝ) :=
  ciInf_le ⟨0, by rintro _ ⟨s, rfl⟩; positivity⟩ (⟨t, ht⟩ : {t : ℝ≥0 // 0 < t})

theorem rayChordLimit_nonneg (γ σ : ℝ≥0 → Y) : 0 ≤ rayChordLimit γ σ := by
  have : Nonempty {t : ℝ≥0 // 0 < t} := ⟨⟨1, one_pos⟩⟩
  exact le_ciInf fun t => by positivity

theorem rayChordLimit_comm (γ σ : ℝ≥0 → Y) : rayChordLimit γ σ = rayChordLimit σ γ := by
  unfold rayChordLimit
  congr 1
  funext t
  rw [dist_comm]

theorem rayChordLimit_self (γ : ℝ≥0 → Y) : rayChordLimit γ γ = 0 := by
  simp [rayChordLimit]

/-! ## Rays -/

theorem dist_of_ray {q : Y} {γ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q) (t : ℝ≥0) :
    dist q (γ t) = t := by
  rw [← hγ.2, hγ.1.dist_eq, NNReal.dist_eq, NNReal.coe_zero, zero_sub, abs_neg,
    abs_of_nonneg (NNReal.coe_nonneg t)]

theorem rayChordLimit_le_two {q : Y} {γ σ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q)
    (hσ : Isometry σ ∧ σ 0 = q) : rayChordLimit γ σ ≤ 2 := by
  have h := rayChordLimit_le γ σ (one_pos : (0 : ℝ≥0) < 1)
  have h2 : dist (γ 1) (σ 1) ≤ 2 := by
    calc dist (γ 1) (σ 1) ≤ dist q (γ 1) + dist q (σ 1) := by
          rw [dist_comm q (γ 1)]; exact dist_triangle _ _ _
      _ = 2 := by rw [dist_of_ray hγ, dist_of_ray hσ]; norm_num
  rw [NNReal.coe_one, div_one] at h
  exact h.trans h2

/-- The kernel of two points on rays from `q`, through their distance. -/
theorem radialConeKernel_of_ray {q : Y} {γ σ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q)
    (hσ : Isometry σ ∧ σ 0 = q) (s u : ℝ≥0) :
    radialConeKernel q (γ s) (σ u) = ((s : ℝ) ^ 2 + (u : ℝ) ^ 2 - dist (γ s) (σ u) ^ 2) / 2 := by
  rw [radialConeKernel, dist_of_ray hγ, dist_of_ray hσ]

/-! ## I1: the kernel along segments and rays -/

/-- I1 (metric LFR55): if `z` lies on a segment from `q` to `b` at fraction `t`, then
`K(z, v) ≤ t K(b, v)` for every `v`. -/
theorem radialConeKernel_le_mul_of_segment (hcomp : fourPointComparison 0 (univ : Set Y))
    {q b z : Y} (v : Y) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hqz : dist q z = t * dist q b) (hzb : dist z b = (1 - t) * dist q b) :
    radialConeKernel q z v ≤ t * radialConeKernel q b v := by
  have h := quadratic_side_comparison_of_fourPointComparison hcomp (mem_univ q) (mem_univ b)
    (mem_univ z) (mem_univ v) ht hqz hzb
  rw [radialConeKernel, radialConeKernel, hqz, dist_comm z v, dist_comm b v]
  rw [dist_comm v q] at h
  linarith

/-- I1 along a ray: `t K(γ s, v) ≤ s K(γ t, v)` for `s ≤ t`. -/
theorem mul_radialConeKernel_le_of_ray (hcomp : fourPointComparison 0 (univ : Set Y)) {q : Y}
    {γ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q) (v : Y) {s t : ℝ≥0} (hst : s ≤ t) :
    (t : ℝ) * radialConeKernel q (γ s) v ≤ s * radialConeKernel q (γ t) v := by
  rcases (zero_le : (0 : ℝ≥0) ≤ t).eq_or_lt with ht | ht
  · have hs : s = 0 := le_antisymm (hst.trans ht.ge) (zero_le : (0 : ℝ≥0) ≤ s)
    simp [← ht, hs]
  · have htR : (0 : ℝ) < t := ht
    have hstR : (s : ℝ) ≤ t := hst
    have hfrac : (s : ℝ) / t ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (NNReal.coe_nonneg s) htR.le, div_le_one_of_le₀ hstR htR.le⟩
    have h := radialConeKernel_le_mul_of_segment hcomp v hfrac (q := q) (b := γ t) (z := γ s)
      (by rw [dist_of_ray hγ, dist_of_ray hγ, div_mul_cancel₀ _ htR.ne'])
      (by
        rw [hγ.1.dist_eq, NNReal.dist_eq, dist_of_ray hγ, abs_of_nonpos (by linarith), sub_mul,
          one_mul, div_mul_cancel₀ _ htR.ne']
        ring)
    calc (t : ℝ) * radialConeKernel q (γ s) v ≤ t * ((s / t) * radialConeKernel q (γ t) v) :=
          mul_le_mul_of_nonneg_left h htR.le
      _ = s * radialConeKernel q (γ t) v := by field_simp

/-- Monotonicity of the normalized kernel `K(γ s, σ u) / (s u)` (the cosine of the comparison angle
at `q`) in both radii, in multiplied-out form. -/
theorem mul_mul_radialConeKernel_le_of_ray (hcomp : fourPointComparison 0 (univ : Set Y))
    {q : Y} {γ σ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q) (hσ : Isometry σ ∧ σ 0 = q)
    {s s' u u' : ℝ≥0} (hs : s ≤ s') (hu : u ≤ u') :
    (s' : ℝ) * u' * radialConeKernel q (γ s) (σ u) ≤
      s * u * radialConeKernel q (γ s') (σ u') := by
  have h1 := mul_radialConeKernel_le_of_ray hcomp hγ (σ u) hs
  have h2 := mul_radialConeKernel_le_of_ray hcomp hσ (γ s') hu
  rw [radialConeKernel_comm q (σ u), radialConeKernel_comm q (σ u')] at h2
  calc (s' : ℝ) * u' * radialConeKernel q (γ s) (σ u)
      = u' * (s' * radialConeKernel q (γ s) (σ u)) := by ring
    _ ≤ u' * (s * radialConeKernel q (γ s') (σ u)) :=
        mul_le_mul_of_nonneg_left h1 (NNReal.coe_nonneg u')
    _ = s * (u' * radialConeKernel q (γ s') (σ u)) := by ring
    _ ≤ s * (u * radialConeKernel q (γ s') (σ u')) :=
        mul_le_mul_of_nonneg_left h2 (NNReal.coe_nonneg s)
    _ = s * u * radialConeKernel q (γ s') (σ u') := by ring

/-! ## Two-sided bounds for the kernel and the distance -/

/-- Upper bound for the kernel by the limit chord: `K(γ s, σ u) ≤ s u (1 - ρ∞² / 2)`. -/
theorem radialConeKernel_le_of_ray (hcomp : fourPointComparison 0 (univ : Set Y))
    {q : Y} {γ σ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q) (hσ : Isometry σ ∧ σ 0 = q)
    (s u : ℝ≥0) :
    radialConeKernel q (γ s) (σ u) ≤ s * u * (1 - rayChordLimit γ σ ^ 2 / 2) := by
  rcases (zero_le : (0 : ℝ≥0) ≤ max s u).eq_or_lt with hM | hM
  · have hs : s = 0 := le_antisymm ((le_max_left s u).trans hM.ge) (zero_le : (0 : ℝ≥0) ≤ s)
    have hu : u = 0 := le_antisymm ((le_max_right s u).trans hM.ge) (zero_le : (0 : ℝ≥0) ≤ u)
    simp [radialConeKernel, hs, hu, hγ.2, hσ.2]
  · set M := max s u with hMdef
    have hMR : (0 : ℝ) < M := hM
    have hK := mul_mul_radialConeKernel_le_of_ray hcomp hγ hσ (le_max_left s u)
      (le_max_right s u)
    rw [← hMdef] at hK
    have hL := rayChordLimit_le γ σ hM
    rw [le_div_iff₀ hMR] at hL
    have hL0 := rayChordLimit_nonneg γ σ
    have hLsq : (rayChordLimit γ σ * M) ^ 2 ≤ dist (γ M) (σ M) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hL0 hMR.le) hL 2
    have hdiag : radialConeKernel q (γ M) (σ M) ≤
        (M : ℝ) ^ 2 * (1 - rayChordLimit γ σ ^ 2 / 2) := by
      rw [radialConeKernel_of_ray hγ hσ]
      nlinarith [hLsq]
    have hsu : (0 : ℝ) ≤ s * u := mul_nonneg (NNReal.coe_nonneg s) (NNReal.coe_nonneg u)
    have hchain : (M : ℝ) * M * radialConeKernel q (γ s) (σ u) ≤
        (M : ℝ) * M * (s * u * (1 - rayChordLimit γ σ ^ 2 / 2)) := by
      calc (M : ℝ) * M * radialConeKernel q (γ s) (σ u)
          ≤ s * u * radialConeKernel q (γ M) (σ M) := hK
        _ ≤ s * u * ((M : ℝ) ^ 2 * (1 - rayChordLimit γ σ ^ 2 / 2)) :=
            mul_le_mul_of_nonneg_left hdiag hsu
        _ = (M : ℝ) * M * (s * u * (1 - rayChordLimit γ σ ^ 2 / 2)) := by ring
    exact le_of_mul_le_mul_left hchain (mul_pos hMR hMR)

/-- Lower bound for the kernel by the chord at a smaller radius `m ≤ s, u`. -/
theorem le_radialConeKernel_of_ray (hcomp : fourPointComparison 0 (univ : Set Y))
    {q : Y} {γ σ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q) (hσ : Isometry σ ∧ σ 0 = q)
    {m s u : ℝ≥0} (hm : 0 < m) (hms : m ≤ s) (hmu : m ≤ u) :
    s * u * (1 - (dist (γ m) (σ m) / m) ^ 2 / 2) ≤ radialConeKernel q (γ s) (σ u) := by
  have hmR : (0 : ℝ) < m := hm
  have hK := mul_mul_radialConeKernel_le_of_ray hcomp hγ hσ hms hmu
  have hdiag : radialConeKernel q (γ m) (σ m) =
      (m : ℝ) ^ 2 * (1 - (dist (γ m) (σ m) / m) ^ 2 / 2) := by
    rw [radialConeKernel_of_ray hγ hσ]
    field_simp
    ring
  rw [hdiag] at hK
  have hchain : (m : ℝ) * m * (s * u * (1 - (dist (γ m) (σ m) / m) ^ 2 / 2)) ≤
      (m : ℝ) * m * radialConeKernel q (γ s) (σ u) := by
    calc (m : ℝ) * m * (s * u * (1 - (dist (γ m) (σ m) / m) ^ 2 / 2))
        = s * u * ((m : ℝ) ^ 2 * (1 - (dist (γ m) (σ m) / m) ^ 2 / 2)) := by ring
      _ ≤ m * m * radialConeKernel q (γ s) (σ u) := hK
  exact le_of_mul_le_mul_left hchain (mul_pos hmR hmR)

/-- Lower bound for distances on two rays: `(s - u)² + s u ρ∞² ≤ d(γ s, σ u)²`. -/
theorem sub_sq_add_mul_rayChordLimit_sq_le_dist_sq (hcomp : fourPointComparison 0 (univ : Set Y))
    {q : Y} {γ σ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q) (hσ : Isometry σ ∧ σ 0 = q)
    (s u : ℝ≥0) :
    ((s : ℝ) - u) ^ 2 + s * u * rayChordLimit γ σ ^ 2 ≤ dist (γ s) (σ u) ^ 2 := by
  have h := radialConeKernel_le_of_ray hcomp hγ hσ s u
  rw [radialConeKernel_of_ray hγ hσ] at h
  linarith

/-- Upper bound for distances on two rays through the chord at a smaller radius `m ≤ s, u`:
`d(γ s, σ u)² ≤ (s - u)² + s u (d(γ m, σ m) / m)²`. -/
theorem dist_sq_le_of_ray (hcomp : fourPointComparison 0 (univ : Set Y))
    {q : Y} {γ σ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q) (hσ : Isometry σ ∧ σ 0 = q)
    {m s u : ℝ≥0} (hm : 0 < m) (hms : m ≤ s) (hmu : m ≤ u) :
    dist (γ s) (σ u) ^ 2 ≤ ((s : ℝ) - u) ^ 2 + s * u * (dist (γ m) (σ m) / m) ^ 2 := by
  have h := le_radialConeKernel_of_ray hcomp hγ hσ hm hms hmu
  rw [radialConeKernel_of_ray hγ hσ] at h
  linarith

/-! ## I2: monotonicity and convergence of the chord quotient -/

/-- I2: the chord quotient of two rays is antitone on `t > 0`. -/
theorem antitoneOn_dist_div_of_ray (hcomp : fourPointComparison 0 (univ : Set Y))
    {q : Y} {γ σ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q) (hσ : Isometry σ ∧ σ 0 = q) :
    AntitoneOn (fun t : ℝ≥0 => dist (γ t) (σ t) / (t : ℝ)) (Ioi 0) := by
  intro s hs t ht hst
  have hsR : (0 : ℝ) < s := hs
  have htR : (0 : ℝ) < t := ht
  have h := dist_sq_le_of_ray hcomp hγ hσ (hs : 0 < s) hst hst
  have h' : dist (γ t) (σ t) ≤ t * (dist (γ s) (σ s) / s) := by
    apply (sq_le_sq₀ dist_nonneg (by positivity)).mp
    rw [mul_pow]
    linarith
  change dist (γ t) (σ t) / t ≤ dist (γ s) (σ s) / s
  rw [div_le_iff₀ htR]
  linarith

/-- The chord quotient of two rays converges to its infimum `rayChordLimit`. -/
theorem tendsto_dist_div_rayChordLimit (hcomp : fourPointComparison 0 (univ : Set Y))
    {q : Y} {γ σ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q) (hσ : Isometry σ ∧ σ 0 = q) :
    Tendsto (fun t : ℝ≥0 => dist (γ t) (σ t) / (t : ℝ)) atTop (𝓝 (rayChordLimit γ σ)) := by
  have : Nonempty {t : ℝ≥0 // 0 < t} := ⟨⟨1, one_pos⟩⟩
  rw [tendsto_order]
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with t ht
    exact hc.trans_le (rayChordLimit_le γ σ ht)
  · obtain ⟨⟨t₀, ht₀⟩, hlt⟩ := exists_lt_of_ciInf_lt hc
    filter_upwards [eventually_ge_atTop t₀] with t ht
    exact (antitoneOn_dist_div_of_ray hcomp hγ hσ (show t₀ ∈ Ioi 0 from ht₀)
      (show t ∈ Ioi 0 from ht₀.trans_le ht) ht).trans_lt hlt

/-- The rescaled distance `d(γ (a t), σ (b t)) / t` is antitone on `t > 0` (as `D_R` in LFR56). -/
theorem antitoneOn_dist_mul_div_of_ray (hcomp : fourPointComparison 0 (univ : Set Y))
    {q : Y} {γ σ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q) (hσ : Isometry σ ∧ σ 0 = q)
    (a b : ℝ≥0) :
    AntitoneOn (fun t : ℝ≥0 => dist (γ (a * t)) (σ (b * t)) / (t : ℝ)) (Ioi 0) := by
  intro s hs t ht hst
  have hsR : (0 : ℝ) < s := hs
  have htR : (0 : ℝ) < t := ht
  -- `t² K_s ≤ s² K_t` for the kernels at the two scales
  have hK : (t : ℝ) ^ 2 * radialConeKernel q (γ (a * s)) (σ (b * s)) ≤
      (s : ℝ) ^ 2 * radialConeKernel q (γ (a * t)) (σ (b * t)) := by
    rcases (zero_le : (0 : ℝ≥0) ≤ a).eq_or_lt with ha | ha
    · simp [← ha, hγ.2, radialConeKernel]
    rcases (zero_le : (0 : ℝ≥0) ≤ b).eq_or_lt with hb | hb
    · simp [← hb, hσ.2, radialConeKernel, dist_comm]
    have haR : (0 : ℝ) < a := ha
    have hbR : (0 : ℝ) < b := hb
    have h := mul_mul_radialConeKernel_le_of_ray hcomp hγ hσ
      (mul_le_mul_of_nonneg_left hst (zero_le : (0 : ℝ≥0) ≤ a))
      (mul_le_mul_of_nonneg_left hst (zero_le : (0 : ℝ≥0) ≤ b))
    push_cast at h
    have hab : (0 : ℝ) < a * b := mul_pos haR hbR
    have h' : (a : ℝ) * b * ((t : ℝ) ^ 2 * radialConeKernel q (γ (a * s)) (σ (b * s))) ≤
        (a : ℝ) * b * ((s : ℝ) ^ 2 * radialConeKernel q (γ (a * t)) (σ (b * t))) := by
      linarith
    exact le_of_mul_le_mul_left h' hab
  have hs2 := radialConeKernel_of_ray hγ hσ (a * s) (b * s)
  have ht2 := radialConeKernel_of_ray hγ hσ (a * t) (b * t)
  push_cast at hs2 ht2
  -- compare the squares `d_t² s² ≤ d_s² t²`
  have hsq : (dist (γ (a * t)) (σ (b * t)) * s) ^ 2 ≤ (dist (γ (a * s)) (σ (b * s)) * t) ^ 2 := by
    rw [hs2, ht2] at hK
    nlinarith [hK]
  have hle := (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  change dist (γ (a * t)) (σ (b * t)) / t ≤ dist (γ (a * s)) (σ (b * s)) / s
  rw [div_le_div_iff₀ htR hsR]
  linarith

/-! ## I3 and I4: the cosine law at infinity -/

/-- I4: domination — the limit chord never exceeds the rescaled distance. -/
theorem sqrt_le_dist_mul_div_of_ray (hcomp : fourPointComparison 0 (univ : Set Y))
    {q : Y} {γ σ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q) (hσ : Isometry σ ∧ σ 0 = q)
    (a b t : ℝ≥0) (ht : 0 < t) :
    Real.sqrt (((a : ℝ) - b) ^ 2 + a * b * rayChordLimit γ σ ^ 2) ≤
      dist (γ (a * t)) (σ (b * t)) / (t : ℝ) := by
  have htR : (0 : ℝ) < t := ht
  have h := sub_sq_add_mul_rayChordLimit_sq_le_dist_sq hcomp hγ hσ (a * t) (b * t)
  push_cast at h
  rw [← Real.sqrt_sq (div_nonneg dist_nonneg htR.le)]
  apply Real.sqrt_le_sqrt
  rw [div_pow, le_div_iff₀ (by positivity)]
  have hid : (((a : ℝ) - b) ^ 2 + a * b * rayChordLimit γ σ ^ 2) * (t : ℝ) ^ 2 =
      ((a : ℝ) * t - b * t) ^ 2 + a * t * (b * t) * rayChordLimit γ σ ^ 2 := by ring
  rw [hid]
  exact h

/-- I3: the cosine law at infinity, for all radii (zero included). -/
theorem tendsto_dist_mul_div_of_ray (hcomp : fourPointComparison 0 (univ : Set Y))
    {q : Y} {γ σ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q) (hσ : Isometry σ ∧ σ 0 = q)
    (a b : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => dist (γ (a * t)) (σ (b * t)) / (t : ℝ)) atTop
      (𝓝 (Real.sqrt (((a : ℝ) - b) ^ 2 + a * b * rayChordLimit γ σ ^ 2))) := by
  rcases (zero_le : (0 : ℝ≥0) ≤ min a b).eq_or_lt with hm | hm
  · -- one radius vanishes: the quotient is constant for `t > 0`
    have key : ∀ t : ℝ≥0, 0 < t → dist (γ (a * t)) (σ (b * t)) / (t : ℝ) =
        Real.sqrt (((a : ℝ) - b) ^ 2 + a * b * rayChordLimit γ σ ^ 2) := by
      intro t ht
      have htR : (0 : ℝ) < t := ht
      rcases min_eq_iff.mp hm.symm with ⟨ha, -⟩ | ⟨hb, -⟩
      · rw [ha, zero_mul, hγ.2, dist_of_ray hσ, NNReal.coe_mul, NNReal.coe_zero,
          mul_div_cancel_right₀ _ htR.ne', zero_sub, zero_mul, zero_mul, add_zero, neg_sq,
          Real.sqrt_sq (NNReal.coe_nonneg b)]
      · rw [hb, zero_mul, hσ.2, dist_comm, dist_of_ray hγ, NNReal.coe_mul, NNReal.coe_zero,
          mul_div_cancel_right₀ _ htR.ne', sub_zero, mul_zero, zero_mul, add_zero,
          Real.sqrt_sq (NNReal.coe_nonneg a)]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with t ht using (key t ht).symm
  · set m := min a b with hmdef
    have hscale : Tendsto (fun t : ℝ≥0 => m * t) atTop atTop := tendsto_id.const_mul_atTop hm
    have hlim : Tendsto (fun t : ℝ≥0 => dist (γ (m * t)) (σ (m * t)) / ((m * t : ℝ≥0) : ℝ))
        atTop (𝓝 (rayChordLimit γ σ)) :=
      (tendsto_dist_div_rayChordLimit hcomp hγ hσ).comp hscale
    have hup : Tendsto (fun t : ℝ≥0 => Real.sqrt (((a : ℝ) - b) ^ 2 +
        a * b * (dist (γ (m * t)) (σ (m * t)) / ((m * t : ℝ≥0) : ℝ)) ^ 2)) atTop
        (𝓝 (Real.sqrt (((a : ℝ) - b) ^ 2 + a * b * rayChordLimit γ σ ^ 2))) :=
      (Real.continuous_sqrt.tendsto _).comp
        (tendsto_const_nhds.add (tendsto_const_nhds.mul (hlim.pow 2)))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    · filter_upwards [eventually_gt_atTop 0] with t ht
      exact sqrt_le_dist_mul_div_of_ray hcomp hγ hσ a b t ht
    · filter_upwards [eventually_gt_atTop 0] with t ht
      have htR : (0 : ℝ) < t := ht
      have h := dist_sq_le_of_ray hcomp hγ hσ (m := m * t) (s := a * t) (u := b * t)
        (mul_pos hm ht) (mul_le_mul_of_nonneg_right (min_le_left a b) (zero_le : (0 : ℝ≥0) ≤ t))
        (mul_le_mul_of_nonneg_right (min_le_right a b) (zero_le : (0 : ℝ≥0) ≤ t))
      set ρ := dist (γ (m * t)) (σ (m * t)) / ((m * t : ℝ≥0) : ℝ)
      push_cast at h
      change dist (γ (a * t)) (σ (b * t)) / t ≤ Real.sqrt (((a : ℝ) - b) ^ 2 + a * b * ρ ^ 2)
      rw [← Real.sqrt_sq (div_nonneg dist_nonneg htR.le)]
      apply Real.sqrt_le_sqrt
      rw [div_pow, div_le_iff₀ (by positivity)]
      have hid : (((a : ℝ) - b) ^ 2 + a * b * ρ ^ 2) * (t : ℝ) ^ 2 =
          ((a : ℝ) * t - b * t) ^ 2 + a * t * (b * t) * ρ ^ 2 := by ring
      rw [hid]
      exact h

/-! ## The limit angle -/

/-- The comparison angle at `q` of two points on rays is antitone in both radii. -/
theorem metricComparisonAngle_le_of_ray (hcomp : fourPointComparison 0 (univ : Set Y))
    {q : Y} {γ σ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q) (hσ : Isometry σ ∧ σ 0 = q)
    {s s' u u' : ℝ≥0} (hs : 0 < s) (hss' : s ≤ s') (hu : 0 < u) (huu' : u ≤ u') :
    metricComparisonAngle (γ s') q (σ u') ≤ metricComparisonAngle (γ s) q (σ u) := by
  have hcos : ∀ x y : ℝ≥0, comparisonCosine (dist q (γ x)) (dist q (σ y)) (dist (γ x) (σ y)) =
      radialConeKernel q (γ x) (σ y) / (x * y) := by
    intro x y
    rw [radialConeKernel_of_ray hγ hσ, dist_of_ray hγ, dist_of_ray hσ]
    ring
  have hsR : (0 : ℝ) < s := hs
  have huR : (0 : ℝ) < u := hu
  have hs'R : (0 : ℝ) < s' := hsR.trans_le hss'
  have hu'R : (0 : ℝ) < u' := huR.trans_le huu'
  unfold metricComparisonAngle comparisonAngle
  rw [hcos, hcos]
  apply Real.arccos_le_arccos
  rw [div_le_div_iff₀ (mul_pos hsR huR) (mul_pos hs'R hu'R)]
  have h := mul_mul_radialConeKernel_le_of_ray hcomp hγ hσ hss' huu'
  linarith

/-- The comparison angle at `q` of `γ (a t)` and `σ (b t)` converges to the limit angle
`arccos (1 - ρ∞² / 2)` (`a, b > 0`). -/
theorem tendsto_metricComparisonAngle_of_ray (hcomp : fourPointComparison 0 (univ : Set Y))
    {q : Y} {γ σ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q) (hσ : Isometry σ ∧ σ 0 = q)
    {a b : ℝ≥0} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun t : ℝ≥0 => metricComparisonAngle (γ (a * t)) q (σ (b * t))) atTop
      (𝓝 (Real.arccos (1 - rayChordLimit γ σ ^ 2 / 2))) := by
  have haR : (0 : ℝ) < a := ha
  have hbR : (0 : ℝ) < b := hb
  have hI3 := tendsto_dist_mul_div_of_ray hcomp hγ hσ a b
  have hcont := (Real.continuous_arccos.tendsto _).comp
    (((tendsto_const_nhds (x := (a : ℝ) ^ 2 + (b : ℝ) ^ 2)).sub (hI3.pow 2)).div_const
      (2 * (a : ℝ) * b))
  have hval : ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 -
      Real.sqrt (((a : ℝ) - b) ^ 2 + a * b * rayChordLimit γ σ ^ 2) ^ 2) / (2 * a * b) =
      1 - rayChordLimit γ σ ^ 2 / 2 := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
    ring
  rw [hval] at hcont
  apply hcont.congr'
  filter_upwards [eventually_gt_atTop 0] with t ht
  have htR : (0 : ℝ) < t := ht
  simp only [Function.comp_apply]
  rw [metricComparisonAngle, comparisonAngle, comparisonCosine, dist_of_ray hγ, dist_of_ray hσ]
  congr 1
  push_cast
  field_simp

/-- The cosine of the limit angle is `1 - ρ∞² / 2`. -/
theorem cos_arccos_rayChordLimit {q : Y} {γ σ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q)
    (hσ : Isometry σ ∧ σ 0 = q) :
    Real.cos (Real.arccos (1 - rayChordLimit γ σ ^ 2 / 2)) = 1 - rayChordLimit γ σ ^ 2 / 2 := by
  have h0 := rayChordLimit_nonneg γ σ
  have h2 := rayChordLimit_le_two hγ hσ
  exact Real.cos_arccos (by nlinarith) (by nlinarith)

/-- The limit chord is the Euclidean cone chord of the limit angle `θ∞ = arccos (1 - ρ∞² / 2)`. -/
theorem sqrt_rayChord_eq_sqrt_cos {q : Y} {γ σ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q)
    (hσ : Isometry σ ∧ σ 0 = q) (a b : ℝ≥0) :
    Real.sqrt (((a : ℝ) - b) ^ 2 + a * b * rayChordLimit γ σ ^ 2) =
      Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2 -
        2 * a * b * Real.cos (Real.arccos (1 - rayChordLimit γ σ ^ 2 / 2))) := by
  rw [cos_arccos_rayChordLimit hγ hσ]
  congr 1
  ring

/-! ## The limit chord on (ray, radius) pairs -/

/-- Homogeneity of the cone chord in the radii. -/
theorem sqrt_rayChord_mul_left (ρ : ℝ) (a b c : ℝ≥0) :
    Real.sqrt ((((c * a : ℝ≥0) : ℝ) - (c * b : ℝ≥0)) ^ 2 + (c * a : ℝ≥0) * (c * b : ℝ≥0) * ρ ^ 2) =
      c * Real.sqrt (((a : ℝ) - b) ^ 2 + a * b * ρ ^ 2) := by
  push_cast
  rw [show ((c : ℝ) * a - c * b) ^ 2 + c * a * (c * b) * ρ ^ 2 =
      (c : ℝ) ^ 2 * (((a : ℝ) - b) ^ 2 + a * b * ρ ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (NNReal.coe_nonneg c)]

theorem sqrt_rayChord_comm (γ σ : ℝ≥0 → Y) (a b : ℝ≥0) :
    Real.sqrt (((a : ℝ) - b) ^ 2 + a * b * rayChordLimit γ σ ^ 2) =
      Real.sqrt (((b : ℝ) - a) ^ 2 + b * a * rayChordLimit σ γ ^ 2) := by
  rw [rayChordLimit_comm γ σ]
  congr 1
  ring

theorem sqrt_rayChord_self (γ : ℝ≥0 → Y) (a : ℝ≥0) :
    Real.sqrt (((a : ℝ) - a) ^ 2 + a * a * rayChordLimit γ γ ^ 2) = 0 := by
  simp [rayChordLimit_self]

/-- The triangle inequality for the limit chord of rays. -/
theorem rayChordLimit_triangle (hcomp : fourPointComparison 0 (univ : Set Y))
    {q : Y} {γ σ τ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q) (hσ : Isometry σ ∧ σ 0 = q)
    (hτ : Isometry τ ∧ τ 0 = q) :
    rayChordLimit γ τ ≤ rayChordLimit γ σ + rayChordLimit σ τ :=
  le_of_tendsto_of_tendsto' (tendsto_dist_div_rayChordLimit hcomp hγ hτ)
    ((tendsto_dist_div_rayChordLimit hcomp hγ hσ).add (tendsto_dist_div_rayChordLimit hcomp hσ hτ))
    fun t => by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (dist_triangle _ _ _) (NNReal.coe_nonneg t)

/-- The triangle inequality for the cone chord on (ray, radius) pairs. -/
theorem sqrt_rayChord_triangle (hcomp : fourPointComparison 0 (univ : Set Y))
    {q : Y} {γ σ τ : ℝ≥0 → Y} (hγ : Isometry γ ∧ γ 0 = q) (hσ : Isometry σ ∧ σ 0 = q)
    (hτ : Isometry τ ∧ τ 0 = q) (a b c : ℝ≥0) :
    Real.sqrt (((a : ℝ) - c) ^ 2 + a * c * rayChordLimit γ τ ^ 2) ≤
      Real.sqrt (((a : ℝ) - b) ^ 2 + a * b * rayChordLimit γ σ ^ 2) +
        Real.sqrt (((b : ℝ) - c) ^ 2 + b * c * rayChordLimit σ τ ^ 2) :=
  le_of_tendsto_of_tendsto' (tendsto_dist_mul_div_of_ray hcomp hγ hτ a c)
    ((tendsto_dist_mul_div_of_ray hcomp hγ hσ a b).add
      (tendsto_dist_mul_div_of_ray hcomp hσ hτ b c))
    fun t => by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (dist_triangle _ _ _) (NNReal.coe_nonneg t)

end GC.MetricGeometry
