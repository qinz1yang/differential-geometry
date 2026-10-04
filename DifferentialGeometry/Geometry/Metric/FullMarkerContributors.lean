import DifferentialGeometry.Geometry.Metric.RetainedMarkerLocality
import DifferentialGeometry.Geometry.Metric.MarkerRecovery
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-! GAF04 (master207B, B:5896): actual full-marker control at every contributor.
(FD) every contributing centre is within `R_i/50` of the core centre (CFS07 + CFS26 inputs);
(FV) marker division at the model preimage; the affine model cutoff argument; and the plane part
of (FM): a locally constant scalar marker kills the tangent plane of the model. -/

set_option autoImplicit false
open Metric Filter Topology

namespace GC.MetricGeometry

/-- (FD): with `Σ ≤ ε/10000` and `b = ε⁻¹`, every selected centre whose closed `80 b r` support
meets the core ball `B(x, 8 b r_x)` of a full-`i`-marker centre is within `R_i/50` of it. -/
theorem contributor_dist_lt_fiftieth_of_full_marker {P X A : Type*} [PseudoMetricSpace X]
    (f : P → X) (ρ : P → ℝ) (marker : A → X → ℝ) (R : A → ℝ)
    (hR : ∀ i, 0 < R i) (hmarker : ∀ i, LipschitzWith 1 (marker i))
    (hfull : ∀ p, ∃ i, marker i (f p) = R i)
    (hsupport : ∀ i p, 0 < marker i (f p) → 3 * R i / 4 ≤ ρ p ∧ ρ p ≤ 5 * R i / 4)
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 ≤ σ) (hσε : σ ≤ ε / 10000)
    (pₓ pᵤ : P) (i : A) (hfullx : marker i (f pₓ) = R i)
    (hmeet : (closedBall (f pᵤ) (80 * ε⁻¹ * (σ * ρ pᵤ)) ∩
      ball (f pₓ) (8 * ε⁻¹ * (σ * ρ pₓ))).Nonempty) :
    dist (f pᵤ) (f pₓ) < R i / 50 := by
  obtain ⟨y, hyu, hyx⟩ := hmeet
  have hyu' : dist y (f pᵤ) ≤ 80 * ε⁻¹ * (σ * ρ pᵤ) := hyu
  have hyx' : dist y (f pₓ) < 8 * ε⁻¹ * (σ * ρ pₓ) := hyx
  have hx := hsupport i pₓ (by rw [hfullx]; exact hR i)
  obtain ⟨j, hj⟩ := hfull pᵤ
  have hu := hsupport j pᵤ (by rw [hj]; exact hR j)
  have hρu : 0 ≤ ρ pᵤ := by linarith [hR j]
  have hρx : 0 ≤ ρ pₓ := by linarith [hR i]
  have hb : 0 ≤ ε⁻¹ := inv_nonneg.mpr hε.le
  have ht : ε⁻¹ * σ ≤ 1 / 10000 := by
    calc ε⁻¹ * σ ≤ ε⁻¹ * (ε / 10000) := mul_le_mul_of_nonneg_left hσε hb
      _ = 1 / 10000 := by field_simp
  have ht0 : 0 ≤ ε⁻¹ * σ := mul_nonneg hb hσ
  have hd : dist (f pᵤ) (f pₓ) < 80 * ε⁻¹ * (σ * ρ pᵤ) + 8 * ε⁻¹ * (σ * ρ pₓ) := by
    have := dist_triangle (f pᵤ) y (f pₓ)
    rw [dist_comm (f pᵤ) y] at this
    linarith
  have hmax : 80 * ε⁻¹ * (σ * ρ pᵤ) + 8 * ε⁻¹ * (σ * ρ pₓ) ≤
      (128 * ε⁻¹) * max (σ * ρ pₓ) (σ * ρ pᵤ) := by
    have h1 : σ * ρ pᵤ ≤ max (σ * ρ pₓ) (σ * ρ pᵤ) := le_max_right _ _
    have h2 : σ * ρ pₓ ≤ max (σ * ρ pₓ) (σ * ρ pᵤ) := le_max_left _ _
    have h3 : 0 ≤ σ * ρ pₓ := mul_nonneg hσ hρx
    nlinarith
  have hsmall : (128 * ε⁻¹) * σ ≤ 1 / 5 := by nlinarith
  have hcmp := nearby_scale_comparison_of_retained_markers f ρ marker R hR hmarker hfull
    hsupport hσ (by positivity) hsmall pₓ pᵤ (by rw [dist_comm]; linarith)
  have hρu' : ρ pᵤ ≤ 5 / 3 * ρ pₓ := hcmp.2
  have hbound : 80 * ε⁻¹ * (σ * ρ pᵤ) + 8 * ε⁻¹ * (σ * ρ pₓ) ≤
      (424 / 3) * (ε⁻¹ * σ) * ρ pₓ := by
    have := mul_le_mul_of_nonneg_left hρu' (by positivity : (0 : ℝ) ≤ 80 * (ε⁻¹ * σ))
    nlinarith
  have hfin : (424 / 3) * (ε⁻¹ * σ) * ρ pₓ ≤ (424 / 3) * (1 / 10000) * (5 * R i / 4) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left ht (by norm_num)) hx.2 hρx (by positivity)
  have hRi := hR i
  linarith

/-- (FV): marker division at a model preimage whose normalized block is within `1/50` of the
full-marker block `(u, 1)` with `|u| ≤ 7ℓ`. -/
theorem norm_coordinate_lt_of_block_near_full_marker {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {u v : E} {ζ ℓ : ℝ} (hℓ : 1 ≤ ℓ) (hu : ‖u‖ ≤ 7 * ℓ)
    (hblock : dist (WithLp.toLp 2 (ζ • v, ζ)) (WithLp.toLp 2 (u, (1 : ℝ))) < 1 / 50) :
    49 / 50 < ζ ∧ ‖v‖ < 351 / 49 * ℓ := by
  obtain ⟨hζ, hv⟩ := norm_coordinate_sub_lt_of_block_dist (by norm_num) (by norm_num) hu hblock
  refine ⟨by linarith, ?_⟩
  have htri : ‖v‖ ≤ ‖u‖ + ‖v - u‖ := by
    have := norm_add_le u (v - u)
    rwa [add_sub_cancel] at this
  have hv' : ‖v - u‖ < (1 + 7 * ℓ) / 49 := by
    have : (1 + 7 * ℓ) * (1 / 50) / (1 - 1 / 50) = (1 + 7 * ℓ) / 49 := by ring
    linarith
  linarith

/-- The affine model comparison at tolerance `1/100` with ratio `s > .99` gives tolerance `1/50`
after division by `s`. -/
theorem norm_inv_smul_sub_lt_of_comparison {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l η : E} {s : ℝ} (hs : 99 / 100 < s) (hcmp : ‖l - s • η‖ < 1 / 100) :
    ‖s⁻¹ • l - η‖ < 1 / 50 := by
  have hs0 : 0 < s := by linarith
  have heq : s⁻¹ • l - η = s⁻¹ • (l - s • η) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hs0.ne', one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0)]
  have hinv : s⁻¹ < 100 / 99 := by
    rw [inv_lt_comm₀ hs0 (by norm_num)]
    linarith
  have h0 := norm_nonneg (l - s • η)
  calc s⁻¹ * ‖l - s • η‖ ≤ 100 / 99 * ‖l - s • η‖ :=
        mul_le_mul_of_nonneg_right hinv.le h0
    _ < 100 / 99 * (1 / 100) := by linarith
    _ < 1 / 50 := by norm_num

/-- The model cutoff argument has norm below `7.22 ℓ < 8 ℓ`. -/
theorem norm_lt_of_affine_comparison {E : Type*} [NormedAddCommGroup E]
    {a η : E} {ℓ : ℝ} (hℓ : 1 ≤ ℓ) (hη : ‖η‖ < 351 / 49 * ℓ) (hcmp : ‖a - η‖ < 1 / 50) :
    ‖a‖ < 361 / 50 * ℓ ∧ ‖a‖ < 8 * ℓ := by
  have htri : ‖a‖ ≤ ‖η‖ + ‖a - η‖ := by
    have := norm_add_le η (a - η)
    rwa [add_sub_cancel] at this
  constructor <;> linarith

/-- Plane part of (FM): a scalar (or block) marker that is locally constant along the model map
annihilates the image of its derivative, hence the tangent plane chosen from that model. -/
theorem range_fderiv_le_ker_of_eventually_const {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Φ : E → F) (v : F →L[ℝ] G) {a : E} {s : G} (hΦ : DifferentiableAt ℝ Φ a)
    (hconst : ∀ᶠ z in 𝓝 a, v (Φ z) = s) :
    LinearMap.range (fderiv ℝ Φ a : E →ₗ[ℝ] F) ≤ LinearMap.ker (v : F →ₗ[ℝ] G) := by
  have h1 : HasFDerivAt (fun z => v (Φ z)) (v.comp (fderiv ℝ Φ a)) a :=
    v.hasFDerivAt.comp a hΦ.hasFDerivAt
  have h2 : HasFDerivAt (fun z => v (Φ z)) (0 : E →L[ℝ] G) a :=
    (hasFDerivAt_const s a).congr_of_eventuallyEq hconst
  have h := h1.unique h2
  rintro y ⟨t, rfl⟩
  rw [LinearMap.mem_ker]
  have := congrArg (fun T : E →L[ℝ] G => T t) h
  simpa using this

end GC.MetricGeometry
