import DifferentialGeometry.Geometry.Geodesic.Naturality.PullbackChartGeodesic
import DifferentialGeometry.Analysis.FiniteDimensional.BilinearPositivity
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Arsinh

set_option autoImplicit false
noncomputable section
open Set Bundle Function
open scoped Manifold ContDiff Topology
namespace GC.LongTime.CuspP1
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.MetricKoszul
open DifferentialGeometry.Geometry.Riemannian.Geodesic (hasGeodesicEquationAt_comp_of_pullback)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Warp
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable local instance warpDualNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance warpDualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
noncomputable local instance warpBilinNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance warpBilinNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- `ℓ ⊗ ℓ`. -/
def sqf (ℓ : E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] ℝ := (ContinuousLinearMap.mul ℝ ℝ).bilinearComp ℓ ℓ

/-- Coefficients of the warped metric `dt² + e^{-t}(du₀² + du₁²)` in the coordinate
functionals `(p₀, p₁, p₂)`. -/
def warpCoeff (p0 p1 p2 : E →L[ℝ] ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  sqf p2 + Real.exp (-p2 x) • (sqf p0 + sqf p1)

omit [FiniteDimensional ℝ E] in
theorem warpCoeff_apply (p0 p1 p2 : E →L[ℝ] ℝ) (x v w : E) :
    warpCoeff p0 p1 p2 x v w = p2 v * p2 w + Real.exp (-p2 x) * (p0 v * p0 w + p1 v * p1 w) := by
  simp [warpCoeff, sqf]
  ring

theorem warpCoeff_isCoercive (p0 p1 p2 : E →L[ℝ] ℝ)
    (hinj : ∀ v : E, p0 v = 0 → p1 v = 0 → p2 v = 0 → v = 0) (x : E) :
    IsCoercive (warpCoeff p0 p1 p2 x) := by
  apply DifferentialGeometry.Analysis.isCoercive_of_pos_diagonal
  intro v hv
  rw [warpCoeff_apply]
  have h : p0 v ≠ 0 ∨ p1 v ≠ 0 ∨ p2 v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (hinj v hcon.1 hcon.2.1 hcon.2.2)
  have he := Real.exp_pos (-p2 x)
  rcases h with h | h | h
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (p1 v), sq_nonneg (p2 v), mul_pos he (sq_pos_of_ne_zero h), mul_nonneg he.le (sq_nonneg (p1 v))]
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (p0 v), sq_nonneg (p2 v), mul_pos he (sq_pos_of_ne_zero h), mul_nonneg he.le (sq_nonneg (p0 v))]
  · nlinarith [sq_pos_of_ne_zero h, sq_nonneg (p0 v), sq_nonneg (p1 v), mul_nonneg he.le (sq_nonneg (p0 v)), mul_nonneg he.le (sq_nonneg (p1 v))]


omit [FiniteDimensional ℝ E] in
theorem hasFDerivAt_warpCoeff (p0 p1 p2 : E →L[ℝ] ℝ) (x : E) :
    HasFDerivAt (warpCoeff p0 p1 p2)
      (((-Real.exp (-p2 x)) • p2).smulRight (sqf p0 + sqf p1)) x := by
  have h1 : HasFDerivAt (fun y : E => Real.exp (-p2 y)) ((-Real.exp (-p2 x)) • p2) x := by
    have := (p2.hasFDerivAt (x := x)).neg.exp
    convert this using 1
    simp
  exact (h1.smul_const (sqf p0 + sqf p1)).const_add (sqf p2)

omit [FiniteDimensional ℝ E] in
theorem fderiv_warpCoeff_apply (p0 p1 p2 : E →L[ℝ] ℝ) (x u v w : E) :
    fderiv ℝ (warpCoeff p0 p1 p2) x u v w =
      (-Real.exp (-p2 x)) * p2 u * (p0 v * p0 w + p1 v * p1 w) := by
  rw [(hasFDerivAt_warpCoeff p0 p1 p2 x).fderiv]
  simp [sqf]
  ring

theorem warp_raisedKoszul_apply (p0 p1 p2 : E →L[ℝ] ℝ)
    (hinj : ∀ v : E, p0 v = 0 → p1 v = 0 → p2 v = 0 → v = 0) (x u w : E) :
    warpCoeff p0 p1 p2 x (raisedKoszulOp (warpCoeff p0 p1 p2 x)
      (fderiv ℝ (warpCoeff p0 p1 p2) x) u u) w =
      (-Real.exp (-p2 x)) * p2 u * (p0 u * p0 w + p1 u * p1 w) -
        (1 / 2) * ((-Real.exp (-p2 x)) * p2 w * (p0 u * p0 u + p1 u * p1 u)) := by
  rw [raisedKoszulOp_eq (warpCoeff_isCoercive p0 p1 p2 hinj x), apply_koszul_vec]
  simp only [koszul_cov_apply, fderiv_warpCoeff_apply]
  ring


variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Explicit geodesics of the warped chart metric** (frozen CP1-F3, step 3).  `F : E → M` a `C²`
map on the open set `U` whose pulled-back metric is `warpCoeff`; the curve
`γ τ = m + f τ • ev + h τ • k` with `f'' = h' f'`, `h'' = -½ e^{-(p₂ m + h)} f'²` is mapped to a
geodesic of `g` at every `τ` with `γ τ ∈ U`. -/
theorem warp_curve_geodesic_CPF3 (p0 p1 p2 : E →L[ℝ] ℝ)
    (hcoord : ∀ v : E, p0 v = 0 → p1 v = 0 → p2 v = 0 → v = 0)
    (g : SmoothRiemannianMetric I M) {F : E → M} {U : Set E} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(ℝ, E) I 2 F U)
    (hmetric : ∀ x ∈ U, ∀ v w : E, g.inner (F x) (mfderiv 𝓘(ℝ, E) I F x v)
      (mfderiv 𝓘(ℝ, E) I F x w) = warpCoeff p0 p1 p2 x v w)
    (m ev k : E) (hk0 : p0 k = 0) (hk1 : p1 k = 0) (hk2 : p2 k = 1) (hev2 : p2 ev = 0)
    (hm2 : p2 m = 0) (hev : p0 ev * p0 ev + p1 ev * p1 ev = 1)
    (f f' f'' h h' h'' : ℝ → ℝ)
    (hf : ∀ τ, HasDerivAt f (f' τ) τ) (hf' : ∀ τ, HasDerivAt f' (f'' τ) τ)
    (hh : ∀ τ, HasDerivAt h (h' τ) τ) (hh' : ∀ τ, HasDerivAt h' (h'' τ) τ)
    (hode1 : ∀ τ, f'' τ = h' τ * f' τ)
    (hode2 : ∀ τ, h'' τ = -(1 / 2) * Real.exp (-h τ) * (f' τ * f' τ))
    (J : Set ℝ) (hJ : ∀ τ ∈ J, m + f τ • ev + h τ • k ∈ U) :
    Geodesic.IsGeodesicOn (I := I) g (fun τ => F (m + f τ • ev + h τ • k)) J := by
  intro τ hτ
  set γ : ℝ → E := fun s => m + f s • ev + h s • k with hγ
  set γ' : ℝ → E := fun s => f' s • ev + h' s • k with hγ'
  have hd : ∀ s, HasDerivAt γ (γ' s) s := fun s =>
    (((hf s).smul_const ev).const_add m).add ((hh s).smul_const k)
  have hdd : HasDerivAt γ' (f'' τ • ev + h'' τ • k) τ :=
    ((hf' τ).smul_const ev).add ((hh' τ).smul_const k)
  have hp2γ : ∀ s, p2 (γ s) = h s := fun s => by simp [hγ, hm2, hev2, hk2]
  have hinj : ∀ x ∈ U, Function.Injective (mfderiv 𝓘(ℝ, E) I F x) := by
    intro x hx
    obtain ⟨c, hc, hB⟩ := warpCoeff_isCoercive p0 p1 p2 hcoord x
    have key : ∀ a b : E, mfderiv 𝓘(ℝ, E) I F x a = mfderiv 𝓘(ℝ, E) I F x b → a = b := by
      intro a b hab
      by_contra hne
      have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
      have hD : mfderiv 𝓘(ℝ, E) I F x (a - b) = 0 :=
        (mfderiv 𝓘(ℝ, E) I F x).map_sub a b |>.trans (sub_eq_zero.mpr hab)
      have h0 := hmetric x hx (a - b) (a - b)
      rw [hD] at h0
      have hpos := hB (a - b)
      have hn : 0 < ‖a - b‖ := norm_pos_iff.mpr hsub
      have : g.inner (F x) (0 : TangentSpace I (F x)) 0 = 0 := by simp
      rw [this] at h0
      have := mul_pos (mul_pos hc hn) hn
      linarith
    exact key
  refine hasGeodesicEquationAt_comp_of_pullback g hU hF hinj (γ := γ) (γ' := γ')
    (hJ τ hτ) (Filter.Eventually.of_forall hd) ?_
  have hev_eq : pullbackMetricCoefficients g F =ᶠ[nhds (γ τ)] warpCoeff p0 p1 p2 := by
    filter_upwards [hU.mem_nhds (hJ τ hτ)] with x hx
    ext v w
    rw [pullbackMetricCoefficients_apply, hmetric x hx]
  rw [hev_eq.fderiv_eq, hev_eq.eq_of_nhds]
  convert hdd using 1
  apply (warpCoeff_isCoercive p0 p1 p2 hcoord (γ τ)).bilin_injective
  ext w
  rw [map_neg, neg_apply, warp_raisedKoszul_apply p0 p1 p2 hcoord, warpCoeff_apply]
  simp only [hγ', hp2γ, map_add, map_smul, smul_eq_mul, hk0, hk1, hk2, hev2, hode1, hode2]
  linear_combination (-(1 / 2) * Real.exp (-h τ) * p2 w * (f' τ * f' τ)) * hev

end Warp

/-! ### The explicit semicircle -/

/-- `u`-displacement `2R tanh(τ/2)` of the geodesic semicircle. -/
def scF (R τ : ℝ) : ℝ := 2 * R * (Real.sinh (τ / 2) / Real.cosh (τ / 2))
def scF' (R τ : ℝ) : ℝ := R / Real.cosh (τ / 2) ^ 2
def scF'' (R τ : ℝ) : ℝ := -R * Real.sinh (τ / 2) / Real.cosh (τ / 2) ^ 3
/-- depth `2 log R - 2 log cosh(τ/2)` of the geodesic semicircle. -/
def scH (R τ : ℝ) : ℝ := 2 * Real.log R - 2 * Real.log (Real.cosh (τ / 2))
def scH' (R τ : ℝ) : ℝ := -(Real.sinh (τ / 2) / Real.cosh (τ / 2))
def scH'' (R τ : ℝ) : ℝ := -(1 / 2) / Real.cosh (τ / 2) ^ 2

theorem hasDerivAt_sinh_half (τ : ℝ) :
    HasDerivAt (fun r : ℝ => Real.sinh (r / 2)) (Real.cosh (τ / 2) / 2) τ := by
  refine (((hasDerivAt_id τ).div_const 2).sinh : HasDerivAt (fun r : ℝ => Real.sinh (r / 2)) _ τ).congr_deriv ?_
  simp <;> ring

theorem hasDerivAt_cosh_half (τ : ℝ) :
    HasDerivAt (fun r : ℝ => Real.cosh (r / 2)) (Real.sinh (τ / 2) / 2) τ := by
  refine (((hasDerivAt_id τ).div_const 2).cosh : HasDerivAt (fun r : ℝ => Real.cosh (r / 2)) _ τ).congr_deriv ?_
  simp <;> ring

theorem hasDerivAt_scF (R τ : ℝ) : HasDerivAt (scF R) (scF' R τ) τ := by
  have hc := Real.cosh_pos (τ / 2)
  have := ((hasDerivAt_sinh_half τ).div (hasDerivAt_cosh_half τ) hc.ne').const_mul (2 * R)
  refine (this : HasDerivAt (scF R) _ τ).congr_deriv ?_
  unfold scF'
  have h := Real.cosh_sq (τ / 2)
  field_simp
  linear_combination R * h

theorem hasDerivAt_scF' (R τ : ℝ) : HasDerivAt (scF' R) (scF'' R τ) τ := by
  have hc := Real.cosh_pos (τ / 2)
  have := ((hasDerivAt_cosh_half τ).pow 2)
  have h2 := (hasDerivAt_const τ R).div this (pow_pos hc 2).ne'
  refine (h2 : HasDerivAt (scF' R) _ τ).congr_deriv ?_
  unfold scF''
  simp only [Pi.pow_apply]
  field_simp
  ring

theorem hasDerivAt_scH (R τ : ℝ) : HasDerivAt (scH R) (scH' R τ) τ := by
  have hc := Real.cosh_pos (τ / 2)
  have := ((hasDerivAt_cosh_half τ).log hc.ne').const_mul 2
  have h2 := (hasDerivAt_const τ (2 * Real.log R)).sub this
  refine (h2 : HasDerivAt (scH R) _ τ).congr_deriv ?_
  unfold scH'
  ring

theorem hasDerivAt_scH' (R τ : ℝ) : HasDerivAt (scH' R) (scH'' R τ) τ := by
  have hc := Real.cosh_pos (τ / 2)
  have := ((hasDerivAt_sinh_half τ).div (hasDerivAt_cosh_half τ) hc.ne').neg
  refine (this : HasDerivAt (scH' R) _ τ).congr_deriv ?_
  unfold scH''
  field_simp
  nlinarith [Real.cosh_sq (τ / 2)]

theorem scF''_eq (R τ : ℝ) : scF'' R τ = scH' R τ * scF' R τ := by
  unfold scF'' scH' scF'
  have hc := Real.cosh_pos (τ / 2)
  field_simp

theorem scH''_eq {R : ℝ} (hR : 0 < R) (τ : ℝ) :
    scH'' R τ = -(1 / 2) * Real.exp (-scH R τ) * (scF' R τ * scF' R τ) := by
  unfold scH'' scH scF'
  have hc := Real.cosh_pos (τ / 2)
  have : Real.exp (-(2 * Real.log R - 2 * Real.log (Real.cosh (τ / 2)))) =
      Real.cosh (τ / 2) ^ 2 / R ^ 2 := by
    rw [show -(2 * Real.log R - 2 * Real.log (Real.cosh (τ / 2))) =
      2 * Real.log (Real.cosh (τ / 2)) - 2 * Real.log R by ring, Real.exp_sub,
      show 2 * Real.log (Real.cosh (τ / 2)) = Real.log (Real.cosh (τ / 2) ^ 2) by
        rw [Real.log_pow]; norm_num,
      show 2 * Real.log R = Real.log (R ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (pow_pos hc 2), Real.exp_log (pow_pos hR 2)]
  rw [this]
  field_simp

/-- Existence of the semicircle through two points at depth `s` and horizontal distance `ℓ`. -/
theorem exists_semicircle_CPF3 {s ℓ : ℝ} (hs : 0 < s) (hℓ : 0 < ℓ) :
    ∃ a R : ℝ, 0 < a ∧ 0 < R ∧ scF R a = ℓ / 2 ∧ scH R a = s ∧ scH R (-a) = s ∧
      (∀ τ ∈ Set.Icc (-a) a, s ≤ scH R τ) ∧ s < scH R 0 := by
  set z0 : ℝ := Real.exp (s / 2) with hz0
  have hz0pos : 0 < z0 := Real.exp_pos _
  set σ : ℝ := Real.arsinh (ℓ / (4 * z0)) with hσ
  have hsinh : Real.sinh σ = ℓ / (4 * z0) := Real.sinh_arsinh _
  have hσpos : 0 < σ := Real.sinh_pos_iff.mp (by rw [hsinh]; positivity)
  have hcosh : 0 < Real.cosh σ := Real.cosh_pos σ
  have hR : 0 < z0 * Real.cosh σ := by positivity
  have hlog : 2 * Real.log (z0 * Real.cosh σ) - 2 * Real.log (Real.cosh σ) = s := by
    rw [Real.log_mul hz0pos.ne' hcosh.ne', hz0, Real.log_exp]; ring
  have ha2 : (2 * σ) / 2 = σ := by ring
  refine ⟨2 * σ, z0 * Real.cosh σ, by positivity, hR, ?_, ?_, ?_, ?_, ?_⟩
  · unfold scF
    rw [ha2]
    field_simp
    rw [hsinh]
    field_simp
    norm_num
  · unfold scH
    rw [ha2]; exact hlog
  · unfold scH
    rw [show -(2 * σ) / 2 = -σ by ring, Real.cosh_neg]; exact hlog
  · intro τ hτ
    have hab : |τ / 2| ≤ |σ| := by
      rw [abs_of_pos hσpos, abs_le]
      constructor <;> linarith [hτ.1, hτ.2]
    have hc : Real.cosh (τ / 2) ≤ Real.cosh σ := Real.cosh_le_cosh.mpr hab
    have hlg : Real.log (Real.cosh (τ / 2)) ≤ Real.log (Real.cosh σ) :=
      Real.log_le_log (Real.cosh_pos _) hc
    unfold scH
    linarith
  · have h1 : 1 < Real.cosh σ := Real.one_lt_cosh.mpr hσpos.ne'
    have h2 : 0 < Real.log (Real.cosh σ) := Real.log_pos h1
    unfold scH
    simp only [zero_div, Real.cosh_zero, Real.log_one]
    rw [Real.log_mul hz0pos.ne' hcosh.ne', hz0, Real.log_exp] at *
    nlinarith

end GC.LongTime.CuspP1
