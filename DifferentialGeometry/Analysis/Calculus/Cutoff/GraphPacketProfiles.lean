import DifferentialGeometry.Analysis.Calculus.Cutoff.EdgeNetworkProfiles
import DifferentialGeometry.Analysis.Calculus.ScaledCutoffBlock
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Shared profiles and model blocks of the three graph packets (chapter 14, CGP01/SGP04)

Blueprint 207B, CGP01 (`prop:fibration-source-profile-binding`, B:3879): the global cutoffs are
built from the fixed profiles `f = 1 - χ_{8,9}(|·|)`, `g = 1 - χ_{8,9}`, `h`, `χ_{1/2,1}` already
defined in `EdgeNetworkProfiles` (`edgeCoordinateProfile`, `edgeHeightProfile`,
`jointHeightProfile`, `edgeSumProfile`). The two-component circle cutoff `1 - χ_{8,9}(|η|)` is the
radial profile `circleCutoffProfile`; it is smooth because the profile is constant near zero.

SGP04/EGP06/TCP05 (B:4602, B:5088, B:5518) use, for a listed block with affine input `λ(a)`, the
model block `(λ f(λ/(sℓ)), s f(λ/(sℓ)))`. This is FC05's `scaledCutoffBlock s` applied to the
profile `z ↦ f(z/ℓ)`; it is `graphPacketModelBlock ℓ s` below, with the early first and second
derivative bound `50 (P + 1)` (`P = edgeProfileDerivativeBound`) for `ℓ ≥ 1`, `s ≥ 99/100`, and the
per-block `C¹` composition error `200 (P + 1) θ` used in SGP04 and EGP06.
-/

set_option autoImplicit false
open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis

section Radial

variable {E : Type*} [NormedAddCommGroup E]

/-- A smooth profile that is constant on `(-∞, c]`, `c > 0`, composed with the norm of an inner
product space is smooth (the norm is smooth away from zero, and the composition is locally
constant near zero). -/
theorem contDiff_comp_norm_of_eq_const_near_zero [InnerProductSpace ℝ E] {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {c : ℝ}
    (hc : 0 < c) (hconst : ∀ t ≤ c, φ t = φ 0) : ContDiff ℝ ∞ (fun x : E => φ ‖x‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    refine (contDiffAt_const (c := φ 0)).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : E) hc] with y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact hconst _ hy.le
  · exact hφ.contDiffAt.comp x (contDiffAt_norm ℝ hx)

/-- CGP01's circle cutoff `1 - χ_{8,9}(|x|)` on a (two-dimensional) coordinate space. -/
noncomputable def circleCutoffProfile (x : E) : ℝ := edgeHeightProfile ‖x‖

theorem contDiff_circleCutoffProfile [InnerProductSpace ℝ E] : ContDiff ℝ ∞ (circleCutoffProfile (E := E)) := by
  have hconst : ∀ t ≤ (8 : ℝ), edgeHeightProfile t = edgeHeightProfile 0 := by
    intro t ht
    rw [edgeHeightProfile, descendingIntervalProfile_one (by norm_num) ht,
      descendingIntervalProfile_one (by norm_num) (by norm_num)]
  exact contDiff_comp_norm_of_eq_const_near_zero edgeProfiles_contDiff.2.1 (by norm_num) hconst

theorem circleCutoffProfile_mem_Icc (x : E) : circleCutoffProfile x ∈ Icc 0 1 :=
  (edgeProfiles_mem_Icc ‖x‖).2.1

theorem circleCutoffProfile_one {x : E} (hx : ‖x‖ ≤ 8) : circleCutoffProfile x = 1 :=
  descendingIntervalProfile_one (by norm_num) hx

theorem circleCutoffProfile_zero {x : E} (hx : 9 ≤ ‖x‖) : circleCutoffProfile x = 0 :=
  descendingIntervalProfile_zero (by norm_num) hx

theorem tsupport_circleCutoffProfile_subset :
    tsupport (circleCutoffProfile (E := E)) ⊆ Metric.closedBall 0 9 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  exact hx (circleCutoffProfile_zero (le_of_lt (lt_of_not_ge h)))

end Radial

section Identities

/-- CGP01/CFS23: on the tangential plateau `|η| < 8Δ` the edge cutoff equals its height factor. -/
theorem edgeCutoff_eq_height_of_lt {Δ η t : ℝ} (hΔ : 0 < Δ) (hη : |η| < 8 * Δ) :
    edgeCoordinateProfile (η / Δ) * edgeHeightProfile (t / Δ) = edgeHeightProfile (t / Δ) := by
  have h : η / Δ ∈ Icc (-8) 8 := by
    rw [abs_lt] at hη
    constructor
    · rw [le_div_iff₀ hΔ]; linarith
    · rw [div_le_iff₀ hΔ]; linarith
  rw [edgeProfiles_plateaus.1 h, one_mul]

/-- CGP01: a point of the closed support of the `E'` block `h(t/Δ) Z₀` has
`t/Δ ∈ [1/5, 9]` and edge sum at least `1/2`. -/
theorem jointBlock_support {Δ t Z : ℝ} (hΔ : 0 < Δ)
    (h : jointHeightProfile (t / Δ) * edgeSumProfile Z ≠ 0) :
    Δ / 5 < t ∧ t < 9 * Δ ∧ 1 / 2 < Z := by
  have hh : jointHeightProfile (t / Δ) ≠ 0 := left_ne_zero_of_mul h
  have hz : edgeSumProfile Z ≠ 0 := right_ne_zero_of_mul h
  refine ⟨?_, ?_, ?_⟩
  · by_contra hc
    exact hh (intervalPlateauProfile_zero_left (by norm_num)
      ((div_le_iff₀ hΔ).mpr (by linarith [le_of_not_gt hc])))
  · by_contra hc
    exact hh (intervalPlateauProfile_zero_right (by norm_num)
      ((le_div_iff₀ hΔ).mpr (by linarith [le_of_not_gt hc])))
  · by_contra hc
    exact hz (edgeSumProfile_zero (le_of_not_gt hc))

end Identities

section ModelBlock

/-- The tangential profile `z ↦ f(z/ℓ)` of a slim or edge block at scale `ℓ`. -/
noncomputable def scaledEdgeCoordinateProfile (ℓ : ℝ) (z : ℝ) : ℝ := edgeCoordinateProfile (z / ℓ)

/-- The model block `(λ f(λ/(sℓ)), s f(λ/(sℓ)))` of SGP04/EGP06, as a function of `λ`. -/
noncomputable def graphPacketModelBlock (ℓ s : ℝ) : ℝ → WithLp 2 (ℝ × ℝ) :=
  scaledCutoffBlock s (scaledEdgeCoordinateProfile ℓ)

theorem graphPacketModelBlock_apply (ℓ s x : ℝ) :
    graphPacketModelBlock ℓ s x =
      WithLp.toLp 2 (edgeCoordinateProfile (x / (s * ℓ)) * x,
        s * edgeCoordinateProfile (x / (s * ℓ))) := by
  have h : x / (s * ℓ) = s⁻¹ * x / ℓ := by ring
  rw [h]
  rfl

theorem scaledEdgeCoordinateProfile_eq_comp (ℓ : ℝ) :
    scaledEdgeCoordinateProfile ℓ =
      edgeCoordinateProfile ∘ (ℓ⁻¹ • ContinuousLinearMap.id ℝ ℝ) := by
  funext z
  simp [scaledEdgeCoordinateProfile, div_eq_inv_mul]

theorem contDiff_scaledEdgeCoordinateProfile (ℓ : ℝ) :
    ContDiff ℝ ∞ (scaledEdgeCoordinateProfile ℓ) := by
  rw [scaledEdgeCoordinateProfile_eq_comp]
  exact edgeProfiles_contDiff.1.comp (ContinuousLinearMap.contDiff _)

theorem scaledEdgeCoordinateProfile_bounds {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∀ x, scaledEdgeCoordinateProfile ℓ x ∈ Icc 0 1) ∧
    tsupport (scaledEdgeCoordinateProfile ℓ) ⊆ Metric.closedBall 0 (9 * ℓ) ∧
    (∀ x, ‖fderiv ℝ (scaledEdgeCoordinateProfile ℓ) x‖ ≤ edgeProfileDerivativeBound * ℓ⁻¹) ∧
    ∀ x, ‖fderiv ℝ (fderiv ℝ (scaledEdgeCoordinateProfile ℓ)) x‖ ≤
      edgeProfileDerivativeBound * ℓ⁻¹ ^ 2 := by
  have hP := edgeProfileDerivativeBound_ge_one
  have hf := edgeProfiles_derivative_le (f := edgeCoordinateProfile) (by simp)
  have hL : ‖(ℓ⁻¹ • ContinuousLinearMap.id ℝ ℝ : ℝ →L[ℝ] ℝ)‖ ≤ ℓ⁻¹ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
      (inv_nonneg.mpr hℓ.le)).trans_eq (mul_one _)
  have hd (x : ℝ) := linear_precomp_derivative_bounds (ℓ⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    (edgeProfiles_contDiff.1.of_le (by simp)) (inv_nonneg.mpr hℓ.le) (by linarith)
    (by linarith) hL hf.1 hf.2 x
  refine ⟨fun x => (edgeProfiles_mem_Icc _).1, ?_, ?_, ?_⟩
  · apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    by_contra h
    apply hx
    have hx' : 9 < |x / ℓ| := by
      rw [abs_div, abs_of_pos hℓ, lt_div_iff₀ hℓ]
      exact lt_of_not_ge h
    rcases lt_abs.mp hx' with h1 | h1
    · exact intervalPlateauProfile_zero_right (by norm_num) h1.le
    · exact intervalPlateauProfile_zero_left (by norm_num) (by linarith)
  · intro x
    rw [scaledEdgeCoordinateProfile_eq_comp]
    exact (hd x).1
  · intro x
    rw [scaledEdgeCoordinateProfile_eq_comp]
    exact (hd x).2

theorem contDiff_graphPacketModelBlock (ℓ s : ℝ) : ContDiff ℝ ∞ (graphPacketModelBlock ℓ s) :=
  contDiff_scaledCutoffBlock (contDiff_scaledEdgeCoordinateProfile ℓ) s

/-- SGP04/EGP06: the model block has first and second derivatives bounded by `50 (P + 1)` for
`ℓ ≥ 1` and `s ≥ 99/100`, with `P` the early fixed profile bound. -/
theorem graphPacketModelBlock_derivative_bounds {ℓ s : ℝ} (hℓ : 1 ≤ ℓ) (hs : 99 / 100 ≤ s)
    (x : ℝ) :
    ‖fderiv ℝ (graphPacketModelBlock ℓ s) x‖ ≤ 50 * (edgeProfileDerivativeBound + 1) ∧
      ‖fderiv ℝ (fderiv ℝ (graphPacketModelBlock ℓ s)) x‖ ≤
        50 * (edgeProfileDerivativeBound + 1) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hs0 : 0 < s := by linarith
  have hP := edgeProfileDerivativeBound_ge_one
  set P := edgeProfileDerivativeBound
  obtain ⟨hval, hsupp, hfirst, hsecond⟩ := scaledEdgeCoordinateProfile_bounds hℓ0
  have hinv : ℓ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hℓ
  have hinv0 : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr hℓ0.le
  have h := scaledCutoffBlock_derivative_bounds
    ((contDiff_scaledEdgeCoordinateProfile ℓ).of_le (by simp)) hs0 (by positivity)
    (by positivity) (by positivity) hval hsupp hfirst hsecond x
  have hmul : ℓ * ℓ⁻¹ = 1 := mul_inv_cancel₀ hℓ0.ne'
  constructor
  · refine h.1.trans ?_
    have : (9 * ℓ + 1) * (P * ℓ⁻¹) = 9 * P + P * ℓ⁻¹ := by
      rw [add_mul, mul_comm P, ← mul_assoc, mul_assoc 9, hmul]; ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hinv (by linarith : (0 : ℝ) ≤ P)]
  · refine h.2.trans ?_
    rw [div_le_iff₀ hs0]
    have : 2 * (P * ℓ⁻¹) + (9 * ℓ + 1) * (P * ℓ⁻¹ ^ 2) = 11 * P * ℓ⁻¹ + P * ℓ⁻¹ ^ 2 := by
      have : ℓ * ℓ⁻¹ ^ 2 = ℓ⁻¹ := by rw [sq, ← mul_assoc, hmul, one_mul]
      calc 2 * (P * ℓ⁻¹) + (9 * ℓ + 1) * (P * ℓ⁻¹ ^ 2)
          = 2 * (P * ℓ⁻¹) + 9 * P * (ℓ * ℓ⁻¹ ^ 2) + P * ℓ⁻¹ ^ 2 := by ring
        _ = 11 * P * ℓ⁻¹ + P * ℓ⁻¹ ^ 2 := by rw [this]; ring
    rw [this]
    have h1 : P * ℓ⁻¹ ≤ P := by nlinarith
    have h2 : P * ℓ⁻¹ ^ 2 ≤ P := by nlinarith [mul_le_mul hinv hinv hinv0 (by norm_num : (0:ℝ) ≤ 1)]
    nlinarith

/-- SGP04/EGP06: per-block `C¹` composition error. If the actual and affine inputs are
`θ`-close in `C¹` at `x` and the affine input has derivative at most two, the model blocks differ
by at most `200 (P + 1) θ` in value and derivative. -/
theorem graphPacketModelBlock_c1_comp_sub_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ℓ s : ℝ} (hℓ : 1 ≤ ℓ) (hs : 99 / 100 ≤ s) {U V : X → ℝ} {x : X}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x) {θ : ℝ} (hθ : 0 ≤ θ)
    (hclose : ‖U x - V x‖ ≤ θ) (hDclose : ‖fderiv ℝ U x - fderiv ℝ V x‖ ≤ θ)
    (hDV : ‖fderiv ℝ V x‖ ≤ 2) :
    max ‖graphPacketModelBlock ℓ s (U x) - graphPacketModelBlock ℓ s (V x)‖
      ‖fderiv ℝ (graphPacketModelBlock ℓ s ∘ U) x - fderiv ℝ (graphPacketModelBlock ℓ s ∘ V) x‖ ≤
      200 * (edgeProfileDerivativeBound + 1) * θ := by
  have hP := edgeProfileDerivativeBound_ge_one
  have hW := contDiff_graphPacketModelBlock ℓ s
  have hDW : Differentiable ℝ (fderiv ℝ (graphPacketModelBlock ℓ s)) :=
    ((contDiff_succ_iff_fderiv (n := 1)).mp (hW.of_le (by simp))).2.2.differentiable
      (by norm_num)
  have hb (y : ℝ) := graphPacketModelBlock_derivative_bounds hℓ hs y
  refine (c1_comp_sub_le_of_derivative_bounds (hW.differentiable (by simp))
    hDW hU hV (by linarith) (by linarith) (by norm_num) hθ
    (fun y => (hb y).1) (fun y => (hb y).2) hclose hDclose hDV).trans ?_
  nlinarith

end ModelBlock

end DifferentialGeometry.Analysis
