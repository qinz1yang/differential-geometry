import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromovModelChange
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.HalfProductRatio
import DifferentialGeometry.Geometry.Curvature.SectionalRicciBound
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The flat torus of a hyperbolic cusp: area ratio and half-product ratio (route R3, statement M)

For a hyperbolic cusp `H`, the torus metric `g_T = H.torusMetric` is flat (`H.torus_flat`), hence
has Ricci curvature `≥ 0`. Bishop–Gromov in dimension two — transferred to the product model
`torusModel = (𝓡 1).prod (𝓡 1)` by `bishopGromov_of_continuousLinearEquiv` — gives, for the area
`A_x(s)` of the `g_T`-ball of radius `s` (in `g_T`'s OWN length distance),
`A_x(b)/b² ≤ A_x(s)/s² ≤ π` for `0 < s ≤ b`, and `A_x(r) ≤ π r²` for every `r`.
Plugged into the one-dimensional kernel `torus_halfBall_div_cube_antitone_of_area_ratio`, this gives
statement M: the half-product volume ratio `F(r)/r³`, `F(r) = ∫_{max(-r,-z₁)}^r A_x(√(r² - y²)) dy`,
is antitone at every height `z₁ ≥ 0`.
Corollary for statement G: if all `g_T`-distances are `≤ D` then `Area(T², g_T) ≤ π D²`; with
`D = 2δ` this is `Area ≤ 4πδ²` (replacing the Dirichlet-cell argument of B:7641–7653).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

/-- The model vector space of the torus has dimension two. -/
theorem finrank_torusModelSpace :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) = 2 := by
  rw [Module.finrank_prod, finrank_euclideanSpace_fin]

/-- The torus metric of a hyperbolic cusp is flat, so its Ricci curvature is bounded below by `0`. -/
theorem torus_ricciBoundedBelow_zero (Hc : HyperbolicCusp) :
    Riemannian.BonnetMyers.RicciBoundedBelow Hc.torusMetric 0 := by
  let : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) :=
    ⟨by rw [finrank_torusModelSpace]; norm_num⟩
  have h := ricciBoundedBelow_of_orthonormal_sectional_bound Hc.torusMetric
    finrank_torusModelSpace.ge (k := 0) fun x v w _ _ _ => (Hc.torus_flat x v w).ge
  rw [mul_zero] at h
  exact h

/-- Bishop–Gromov for the flat torus (cross form, `ℝ≥0∞`): for `0 < s ≤ b`,
`A_x(b) · π s² ≤ π b² · A_x(s)`. -/
theorem torus_ballVolume_cross (Hc : HyperbolicCusp) (x : Torus) {s b : ℝ}
    (hs : 0 < s) (hsb : s ≤ b) :
    ballVolume Hc.torusMetric x b * ENNReal.ofReal (Real.pi * s ^ 2) ≤
      ENNReal.ofReal (Real.pi * b ^ 2) * ballVolume Hc.torusMetric x s := by
  let : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) :=
    ⟨by rw [finrank_torusModelSpace]; norm_num⟩
  have hRic : Riemannian.BonnetMyers.RicciBoundedBelow Hc.torusMetric
      (((Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) - 1 : ℕ) : ℝ) *
        0) := by
    rw [mul_zero]
    exact torus_ricciBoundedBelow_zero Hc
  have h := (bishopGromov_of_continuousLinearEquiv
    (ContinuousLinearEquiv.ofFinrankEq (finrank_torusModelSpace.trans
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)).symm)) Hc.torusMetric hRic x).1 hs hsb
    (by simp)
  simpa only [finrank_torusModelSpace, modelVolume_zero 2 _ (by norm_num),
    euclideanUnitBallVolume_two] using h

/-- Bishop–Gromov for the flat torus (absolute form): `A_x(r) ≤ π r²` for every `r`. -/
theorem torus_ballVolume_le_pi_mul_sq (Hc : HyperbolicCusp) (x : Torus) (r : ℝ) :
    ballVolume Hc.torusMetric x r ≤ ENNReal.ofReal (Real.pi * r ^ 2) := by
  rcases le_or_gt r 0 with hr | hr
  · have hempty : riemannianBallOf Hc.torusMetric x r = ∅ := by
      ext y
      simp only [riemannianBallOf, mem_ofPred_eq, ENNReal.ofReal_of_nonpos hr, not_lt_zero,
        mem_empty_iff_false]
    simp only [ballVolume, hempty, measure_empty, zero_le]
  · let : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) :=
      ⟨by rw [finrank_torusModelSpace]; norm_num⟩
    have hRic : Riemannian.BonnetMyers.RicciBoundedBelow Hc.torusMetric
        (((Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) - 1 : ℕ) : ℝ) *
          0) := by
      rw [mul_zero]
      exact torus_ricciBoundedBelow_zero Hc
    have h := (bishopGromov_of_continuousLinearEquiv
      (ContinuousLinearEquiv.ofFinrankEq (finrank_torusModelSpace.trans
        (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2)).symm)) Hc.torusMetric hRic x).2 hr
      (by simp)
    simpa only [finrank_torusModelSpace, modelVolume_zero 2 _ (by norm_num),
      euclideanUnitBallVolume_two] using h

/-- The `g_T`-ball areas are finite. -/
theorem torus_ballVolume_ne_top (Hc : HyperbolicCusp) (x : Torus) (r : ℝ) :
    ballVolume Hc.torusMetric x r ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (torus_ballVolume_le_pi_mul_sq Hc x r)

/-- M.1 (2D Bishop–Gromov for the flat torus, with `g_T`'s OWN distance and area), in the form of
the interface: for `0 < s ≤ b`, `A(b)/b² ≤ A(s)/s² ≤ π`. -/
theorem torus_area_ratio (Hc : HyperbolicCusp) (x : Torus) {s b : ℝ} (hs : 0 < s)
    (hsb : s ≤ b) :
    let A : ℝ → ℝ := fun r => (ballVolume Hc.torusMetric x r).toReal
    A b / b ^ 2 ≤ A s / s ^ 2 ∧ A s / s ^ 2 ≤ Real.pi := by
  intro A
  have hb : 0 < b := hs.trans_le hsb
  have hcross := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (torus_ballVolume_ne_top Hc x s))
    (torus_ballVolume_cross Hc x hs hsb)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)] at hcross
  have habs := ENNReal.toReal_mono ENNReal.ofReal_ne_top (torus_ballVolume_le_pi_mul_sq Hc x s)
  rw [ENNReal.toReal_ofReal (by positivity)] at habs
  refine ⟨?_, ?_⟩
  · rw [div_le_div_iff₀ (pow_pos hb 2) (pow_pos hs 2)]
    have key : A b * s ^ 2 * Real.pi ≤ A s * b ^ 2 * Real.pi := by
      calc A b * s ^ 2 * Real.pi
          = (ballVolume Hc.torusMetric x b).toReal * (Real.pi * s ^ 2) := by ring
        _ ≤ Real.pi * b ^ 2 * (ballVolume Hc.torusMetric x s).toReal := hcross
        _ = A s * b ^ 2 * Real.pi := by ring
    exact le_of_mul_le_mul_right key Real.pi_pos
  · rw [div_le_iff₀ (pow_pos hs 2)]
    exact habs

/-- M (half-product ratio at every height): with `A` the `g_T`-ball area, the flat half-ball volume
`F(r) = ∫_{max(-r,-z₁)}^r A(√(r² - y²)) dy` satisfies `F(b)/b³ ≤ F(s)/s³` for `z₁ ≥ 0`,
`0 < s ≤ b`. Consumer of `torus_area_ratio` through the one-dimensional kernel. -/
theorem torus_halfBall_div_cube_antitone (Hc : HyperbolicCusp) (x : Torus)
    {z₁ s b : ℝ} (hz₁ : 0 ≤ z₁) (hs : 0 < s) (hsb : s ≤ b) :
    (∫ y in max (-b) (-z₁)..b, (ballVolume Hc.torusMetric x (Real.sqrt (b ^ 2 - y ^ 2))).toReal) /
        b ^ 3 ≤
      (∫ y in max (-s) (-z₁)..s, (ballVolume Hc.torusMetric x (Real.sqrt (s ^ 2 - y ^ 2))).toReal) /
        s ^ 3 :=
  torus_halfBall_div_cube_antitone_of_area_ratio Hc x
    (fun _ _ hs' hsb' => (torus_area_ratio Hc x hs' hsb').1) hz₁ hs hsb

/-- Corollary for G: if every `g_T`-distance is at most `D`, then `Area(T², g_T) ≤ π D²`
(no sign condition on `D`; balls of radius `r > |D|` are the whole torus, then `r ↓ |D|`). -/
theorem torus_area_le_pi_mul_sq_of_dist_le (Hc : HyperbolicCusp) {D : ℝ}
    (hD : ∀ y z : Torus, riemannianEDistOf Hc.torusMetric y z ≤ ENNReal.ofReal D) :
    Integral.Measure.riemannianVolumeMeasure torusModel Torus Hc.torusMetric univ ≤
      ENNReal.ofReal (Real.pi * D ^ 2) := by
  let x : Torus := ((1 : Circle), (1 : Circle))
  have hball (r : ℝ) (hr : |D| < r) :
      Integral.Measure.riemannianVolumeMeasure torusModel Torus Hc.torusMetric univ =
        ballVolume Hc.torusMetric x r := by
    have hrpos : 0 < r := (abs_nonneg D).trans_lt hr
    have huniv : riemannianBallOf Hc.torusMetric x r = univ := by
      ext y
      simp only [riemannianBallOf, mem_ofPred_eq, mem_univ, iff_true]
      exact (hD x y).trans_lt ((ENNReal.ofReal_le_ofReal (le_abs_self D)).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff hrpos).2 hr))
    rw [ballVolume, huniv]
  have hne : Integral.Measure.riemannianVolumeMeasure torusModel Torus Hc.torusMetric univ ≠ ⊤ := by
    rw [hball (|D| + 1) (by linarith)]
    exact torus_ballVolume_ne_top Hc x _
  have hreal (r : ℝ) (hr : |D| < r) :
      (Integral.Measure.riemannianVolumeMeasure torusModel Torus Hc.torusMetric univ).toReal ≤
        Real.pi * r ^ 2 := by
    rw [hball r hr]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (torus_ballVolume_le_pi_mul_sq Hc x r)
    rwa [ENNReal.toReal_ofReal (by positivity)] at h
  have hlim : Tendsto (fun r : ℝ => Real.pi * r ^ 2) (𝓝[>] |D|) (𝓝 (Real.pi * |D| ^ 2)) :=
    ((continuous_const.mul (continuous_pow 2)).tendsto |D|).mono_left nhdsWithin_le_nhds
  have hle : (Integral.Measure.riemannianVolumeMeasure torusModel Torus Hc.torusMetric
      univ).toReal ≤ Real.pi * D ^ 2 := by
    rw [← sq_abs D]
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hreal r hr
  rw [← ENNReal.ofReal_toReal hne]
  exact ENNReal.ofReal_le_ofReal hle

/-- Corollary for G in the design's form: `diam(T², g_T) ≤ 2δ` gives `Area(T², g_T) ≤ 4πδ²`. -/
theorem torus_area_le_four_pi_mul_sq_of_dist_le_two_mul (Hc : HyperbolicCusp)
    {δ : ℝ} (hδ : ∀ y z : Torus, riemannianEDistOf Hc.torusMetric y z ≤ ENNReal.ofReal (2 * δ)) :
    (Integral.Measure.riemannianVolumeMeasure torusModel Torus Hc.torusMetric univ).toReal ≤
      4 * Real.pi * δ ^ 2 := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (torus_area_le_pi_mul_sq_of_dist_le Hc hδ)
  rw [ENNReal.toReal_ofReal (by positivity)] at h
  linarith [h, show Real.pi * (2 * δ) ^ 2 = 4 * Real.pi * δ ^ 2 by ring]

end DifferentialGeometry.Geometry.Collapse
