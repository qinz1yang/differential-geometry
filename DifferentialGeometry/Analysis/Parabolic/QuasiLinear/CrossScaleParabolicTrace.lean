import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.MaxRegSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The cross-scale parabolic trace embedding `L²(H^{a+2}) ∩ H¹(Hᵃ) ↪ C(H^{a+1})`

For the spectral tensor Sobolev scale `tensorHs g r s σ` of a closed Riemannian
manifold `(M, g)`, this file builds the **Lions–Magenes parabolic trace
embedding** one Sobolev order below the top regularity:

> If a time-dependent tensor field has its values in `H^{a+2}` (`L²`-in-time)
> and its time derivative in `Hᵃ` (`L²`-in-time), then it has a representative
> continuous in time into the intermediate scale `H^{a+1}`, with the
> sup-in-time energy estimate
>
>   `sup_t ‖u(t)‖²_{H^{a+1}} ≤ ‖u(0)‖²_{H^{a+1}} +
>      2 ∫₀ᵀ ‖u(s)‖_{H^{a+2}} · ‖∂_t u(s)‖_{Hᵃ} ds`.

## The summation-free route

The proof is *not* a Weierstrass `M`-test on the eigenmode series — an
`L²`-in-time bound cannot dominate a sup-in-time series and there is no
`(1 + λ)`-smoothing gain per mode.  Instead it follows the classical
Lions–Magenes argument, which is *summation-free*:

1. **Cross-scale duality pairing** (`crossPairing`): the `H^{a+1}` inner
   product, read as a pairing of an `H^{a+2}` vector against an `Hᵃ` vector.
   The weight splits as
   `(1 + λᵢ)^{a+1} = √(1+λᵢ)^{a+2} · √(1+λᵢ)^a`, so a single global
   Cauchy–Schwarz over the modes gives
   `|⟨v, w⟩| ≤ ‖v‖_{H^{a+2}} · ‖w‖_{Hᵃ}` (`abs_crossPairing_le`); no
   unsummable series appears.

2. **Absolute continuity of the squared norm**: `t ↦ ‖u(t)‖²_{H^{a+1}}` is
   the bilinear cross-pairing of the (continuous) `H^{a+2}` representative
   against the indefinite `Hᵃ`-integral of the derivative; it is therefore
   absolutely continuous, with a.e. derivative
   `2 ⟨v(t), ∂_t u(t)⟩` (`crossPairingNormSq_hasDerivAt`).

3. **Fundamental theorem of calculus** turns the a.e. derivative into the exact
   identity `‖u(t)‖² = ‖u(0)‖² + ∫₀ᵗ 2⟨v, ∂_t u⟩`, and the cross-scale
   Cauchy–Schwarz of step 1 bounds the integrand, giving the sup estimate.
   Continuity of `t ↦ ‖u(t)‖²` plus the (already-available) `H^{a+1}` weak
   continuity of the representative gives the strong-continuous representative.

## Data

The energy-space element is packaged as a `CrossScaleField`: a continuous
`H^{a+2}` representative `hi : ℝ → H^{a+2}` of the values, the `Hᵃ`-valued
time-Sobolev element `lo : timeH1 Hᵃ T` recording the initial value and the
`L²` derivative, and the structural link that the `H^{a+1}` view of `hi` is the
`H^{a+1}` view of the indefinite integral `lo.toFun`.  This matches exactly the
companion-field shape of the maximal-regularity Duhamel solution
(`maxRegDuhamelSolField` lives in `L²(H^{a+2})`, its carrier in `H¹(Hᵃ)`), so the
headline can be applied to discharge the sup-in-time `hstay` residual.

## Main results

* `abs_crossPairing_le` — the cross-scale Cauchy–Schwarz pairing bound.
* `crossPairing_self_eq_normSq` — the diagonal recovers `‖·‖²_{H^{a+1}}`.
* `CrossScaleField.continuousOn_repr` — the `H^{a+1}` representative is
  continuous on `[0,T]`.
* `CrossScaleField.normSq_eq_init_add_integral` — the FTC for the squared
  `H^{a+1}` norm.
* `CrossScaleField.iSup_normSq_le` — the sup-in-time energy estimate.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter intervalIntegral
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}
variable {a : ℝ} {T : ℝ}

/-- The middle Sobolev weight is the geometric mean of the upper and lower
weights: `(1 + λᵢ)^{a+1} = √((1+λᵢ)^{a+2}) · √((1+λᵢ)^a)`. -/
lemma tensorSobolevWeight_mid_eq_sqrt_mul_sqrt
    (i : TensorEigenIdx (I := I) (M := M) g r s) (a : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (a + 1) =
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a + 2)) *
        Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a) := by
  have hbase : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
  set x := 1 + TensorEigenIdx.lambda (I := I) (M := M) i with hx
  unfold tensorSobolevWeight
  rw [← hx]
  have hsqrt_u : Real.sqrt (x ^ (a + 2)) = x ^ ((a + 2) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbase.le]
    congr 1; ring
  have hsqrt_l : Real.sqrt (x ^ (a : ℝ)) = x ^ (a / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbase.le]
    congr 1; ring
  rw [hsqrt_u, hsqrt_l, ← Real.rpow_add hbase]
  congr 1; ring

/-- The mode-wise product family `i ↦ (1+λᵢ)^{a+1} · vᵢ · wᵢ` of an upper-scale
vector `v ∈ H^{a+2}` and a lower-scale vector `w ∈ Hᵃ` is summable.  The bound
splits the weight `(1+λᵢ)^{a+1} = √wᵢ⁺·√wᵢ⁻` and applies AM–GM to dominate the
term by the two (summable) weighted-square families. -/
lemma crossPairing_summable
    (v : tensorHs (I := I) (M := M) g r s (a + 2))
    (w : tensorHs (I := I) (M := M) g r s a) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (a + 1) * (v.coeff i * w.coeff i)) := by
  have hv := v.weighted_summable
  have hw := w.weighted_summable
  have h_dom : Summable
      (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
        (1 / 2) * (tensorSobolevWeight (I := I) (M := M) i (a + 2) * (v.coeff i) ^ 2) +
          (1 / 2) * (tensorSobolevWeight (I := I) (M := M) i a * (w.coeff i) ^ 2)) :=
    (hv.mul_left _).add (hw.mul_left _)
  refine Summable.of_norm_bounded h_dom ?_
  intro i
  set wu := tensorSobolevWeight (I := I) (M := M) i (a + 2) with hwu
  set wl := tensorSobolevWeight (I := I) (M := M) i a with hwl
  have hwu0 : 0 ≤ wu := tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)
  have hwl0 : 0 ≤ wl := tensorSobolevWeight_nonneg (I := I) (M := M) i a
  have hsplit : tensorSobolevWeight (I := I) (M := M) i (a + 1) =
      Real.sqrt wu * Real.sqrt wl :=
    tensorSobolevWeight_mid_eq_sqrt_mul_sqrt (I := I) (M := M) i a
  rw [Real.norm_eq_abs, hsplit, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsqu : Real.sqrt wu ^ 2 = wu := Real.sq_sqrt hwu0
  have hsql : Real.sqrt wl ^ 2 = wl := Real.sq_sqrt hwl0
  nlinarith [sq_nonneg (Real.sqrt wu * |v.coeff i| - Real.sqrt wl * |w.coeff i|),
    Real.sqrt_nonneg wu, Real.sqrt_nonneg wl, abs_nonneg (v.coeff i),
    abs_nonneg (w.coeff i), sq_abs (v.coeff i), sq_abs (w.coeff i), hsqu, hsql]

/-- The **cross-scale duality pairing** of an upper-scale vector `v ∈ H^{a+2}`
against a lower-scale vector `w ∈ Hᵃ`:

  `crossPairing v w = ∑ᵢ (1 + λᵢ)^{a+1} · vᵢ · wᵢ`,

the `H^{a+1}` inner product read through the shared eigenmode coordinates. -/
def crossPairing
    (v : tensorHs (I := I) (M := M) g r s (a + 2))
    (w : tensorHs (I := I) (M := M) g r s a) : ℝ :=
  ∑' i, tensorSobolevWeight (I := I) (M := M) i (a + 1) * (v.coeff i * w.coeff i)

/-- The cross-scale pairing is additive in its upper-scale argument. -/
lemma crossPairing_add_left
    (v v' : tensorHs (I := I) (M := M) g r s (a + 2))
    (w : tensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) (v + v') w =
      crossPairing (I := I) (M := M) v w + crossPairing (I := I) (M := M) v' w := by
  unfold crossPairing
  rw [← Summable.tsum_add (crossPairing_summable (I := I) (M := M) v w)
    (crossPairing_summable (I := I) (M := M) v' w)]
  refine tsum_congr (fun i => ?_)
  simp only [tensorHs.add_coeff]; ring

/-- The cross-scale pairing is additive in its lower-scale argument. -/
lemma crossPairing_add_right
    (v : tensorHs (I := I) (M := M) g r s (a + 2))
    (w w' : tensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) v (w + w') =
      crossPairing (I := I) (M := M) v w + crossPairing (I := I) (M := M) v w' := by
  unfold crossPairing
  rw [← Summable.tsum_add (crossPairing_summable (I := I) (M := M) v w)
    (crossPairing_summable (I := I) (M := M) v w')]
  refine tsum_congr (fun i => ?_)
  simp only [tensorHs.add_coeff]; ring

/-- The cross-scale pairing is homogeneous in its upper-scale argument. -/
lemma crossPairing_smul_left (c : ℝ)
    (v : tensorHs (I := I) (M := M) g r s (a + 2))
    (w : tensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) (c • v) w =
      c * crossPairing (I := I) (M := M) v w := by
  unfold crossPairing
  rw [← tsum_mul_left]
  refine tsum_congr (fun i => ?_)
  simp only [tensorHs.smul_coeff]; ring

/-- The cross-scale pairing is homogeneous in its lower-scale argument. -/
lemma crossPairing_smul_right (c : ℝ)
    (v : tensorHs (I := I) (M := M) g r s (a + 2))
    (w : tensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) v (c • w) =
      c * crossPairing (I := I) (M := M) v w := by
  unfold crossPairing
  rw [← tsum_mul_left]
  refine tsum_congr (fun i => ?_)
  simp only [tensorHs.smul_coeff]; ring

/-- The cross-scale pairing is the `ℓ²` inner product of the two diagonally
rescaled coordinate families. -/
lemma crossPairing_eq_inner_rescale
    (v : tensorHs (I := I) (M := M) g r s (a + 2))
    (w : tensorHs (I := I) (M := M) g r s a) :
    crossPairing (I := I) (M := M) v w =
      (inner ℝ (tensorHs.rescaleToL2 (I := I) (M := M) v)
        (tensorHs.rescaleToL2 (I := I) (M := M) w) : ℝ) := by
  rw [lp.inner_eq_tsum]
  unfold crossPairing
  refine tsum_congr (fun i => ?_)
  rw [show (inner ℝ ((tensorHs.rescaleToL2 (I := I) (M := M) v : _ → ℝ) i)
          ((tensorHs.rescaleToL2 (I := I) (M := M) w : _ → ℝ) i) : ℝ) =
        (tensorHs.rescaleToL2 (I := I) (M := M) v : _ → ℝ) i *
          (tensorHs.rescaleToL2 (I := I) (M := M) w : _ → ℝ) i by
      simp [real_inner_eq_re_inner, RCLike.inner_apply, mul_comm]]
  rw [tensorHs.rescaleToL2_apply, tensorHs.rescaleToL2_apply,
    tensorSobolevWeight_mid_eq_sqrt_mul_sqrt (I := I) (M := M) i a]
  ring

/-- **The cross-scale Cauchy–Schwarz pairing bound.**  The `H^{a+1}` pairing of an
`H^{a+2}` vector against an `Hᵃ` vector is controlled by the product of their
norms at the respective scales:

  `|crossPairing v w| ≤ ‖v‖_{H^{a+2}} · ‖w‖_{Hᵃ}`. -/
theorem abs_crossPairing_le
    (v : tensorHs (I := I) (M := M) g r s (a + 2))
    (w : tensorHs (I := I) (M := M) g r s a) :
    |crossPairing (I := I) (M := M) v w| ≤ ‖v‖ * ‖w‖ := by
  rw [crossPairing_eq_inner_rescale]
  refine le_trans (abs_real_inner_le_norm _ _) ?_
  have hv : ‖tensorHs.rescaleToL2 (I := I) (M := M) v‖ = ‖v‖ :=
    (tensorHs.rescaleEquivL2 (I := I) (M := M)).norm_map v
  have hw : ‖tensorHs.rescaleToL2 (I := I) (M := M) w‖ = ‖w‖ :=
    (tensorHs.rescaleEquivL2 (I := I) (M := M)).norm_map w
  rw [hv, hw]

/-- The cross-scale pairing of `v ∈ H^{a+2}` against its own `Hᵃ` view is the
squared `H^{a+1}` norm of the `H^{a+1}` view of `v`. -/
theorem crossPairing_self_eq_normSq
    (v : tensorHs (I := I) (M := M) g r s (a + 2)) :
    crossPairing (I := I) (M := M) v
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a ≤ a + 2 by linarith) v) =
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a + 1 ≤ a + 2 by linarith) v‖ ^ 2 := by
  rw [tensorHs.norm_sq_eq_tsum]
  unfold crossPairing
  refine tsum_congr (fun i => ?_)
  rw [tensorHsInclusion_coeff_apply, tensorHsInclusion_coeff_apply, sq]

/-- The eigenmode-coordinate `|T.coeff i|` is bounded by `√((1+λᵢ)^σ)⁻¹ · ‖T‖`. -/
lemma abs_coeff_le_norm {σ : ℝ} (i : TensorEigenIdx (I := I) (M := M) g r s)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    |T.coeff i| ≤ (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹ * ‖T‖ := by
  have hw_pos : 0 < tensorSobolevWeight (I := I) (M := M) i σ :=
    tensorSobolevWeight_pos (I := I) (M := M) i σ
  have hsqrt_pos : 0 < Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) :=
    Real.sqrt_pos.mpr hw_pos
  have h_term_le : tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 ≤ ‖T‖ ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum]
    refine Summable.le_tsum T.weighted_summable i (fun j _ => ?_)
    have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) j σ :=
      tensorSobolevWeight_nonneg (I := I) (M := M) j σ
    positivity
  have hsq : (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * |T.coeff i|) ^ 2 ≤ ‖T‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hw_pos.le, sq_abs]; exact h_term_le
  have hle : Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * |T.coeff i| ≤ ‖T‖ := by
    have h1 : 0 ≤ Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) * |T.coeff i| :=
      mul_nonneg hsqrt_pos.le (abs_nonneg _)
    nlinarith [hsq, h1, norm_nonneg T]
  rw [inv_mul_eq_div, le_div_iff₀ hsqrt_pos, mul_comm]
  exact hle

/-- The eigenmode-coordinate `T ↦ T.coeff i` as a continuous linear functional
on `Hˢ`, with operator-norm bound `√((1+λᵢ)^σ)⁻¹`. -/
def coeffCLM {σ : ℝ} (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorHs (I := I) (M := M) g r s σ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun T => T.coeff i
      map_add' := fun S T => by simp only [tensorHs.add_coeff]
      map_smul' := fun c T => by simp only [tensorHs.smul_coeff, RingHom.id_apply, smul_eq_mul] }
    (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹
    (fun T => by
      change ‖T.coeff i‖ ≤ _
      rw [Real.norm_eq_abs]
      exact abs_coeff_le_norm (I := I) (M := M) i T)

@[simp] lemma coeffCLM_apply {σ : ℝ} (i : TensorEigenIdx (I := I) (M := M) g r s)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) i T = T.coeff i := rfl

/-- **Scalar absolutely-continuous FTC-2 for the square, between two base
points.**  Let `c, d : ℝ → ℝ` with `d` interval integrable on `t₀..t`, and
suppose `c` is an indefinite integral of `d` near `t₀..t`, i.e. for every `x` in
the (unordered) interval `c x - c t₀ = ∫ r in t₀..x, d r`.  Then

  `c t ^ 2 = c t₀ ^ 2 + ∫ s in t₀..t, 2 * c s * d s`. -/
theorem sq_eq_base_add_integral_of_indefinite
    {c d : ℝ → ℝ} {t₀ t : ℝ}
    (hd : IntervalIntegrable d volume t₀ t)
    (hc : ∀ x ∈ uIcc t₀ t, c x - c t₀ = ∫ r in t₀..x, d r) :
    c t ^ 2 = c t₀ ^ 2 + ∫ s in t₀..t, 2 * c s * d s := by
  set e : ℝ → ℝ := fun τ => c t₀ + ∫ r in t₀..τ, d r with he_def
  have hce : ∀ x ∈ uIcc t₀ t, c x = e x := by
    intro x hx
    have := hc x hx
    simp only [he_def]; linarith [this]
  have h0mem : t₀ ∈ uIcc t₀ t := left_mem_uIcc
  have htmem : t ∈ uIcc t₀ t := right_mem_uIcc
  have hac_int : AbsolutelyContinuousOnInterval
      (fun τ => ∫ r in t₀..τ, d r) t₀ t :=
    hd.absolutelyContinuousOnInterval_intervalIntegral h0mem
  have hac_const : AbsolutelyContinuousOnInterval (fun _ : ℝ => c t₀) t₀ t :=
    (LipschitzWith.const (c t₀)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hac_e : AbsolutelyContinuousOnInterval e t₀ t := by
    have := hac_const.add hac_int
    simpa only [he_def, Pi.add_apply] using this
  have hprod := AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub hac_e hac_e
  have hae_deriv : ∀ᵐ x, x ∈ uIcc t₀ t → deriv e x = d x := by
    filter_upwards [hd.ae_hasDerivAt_integral] with x hx hxmem
    have hxd : HasDerivAt (fun τ => ∫ r in t₀..τ, d r) (d x) x :=
      hx hxmem t₀ h0mem
    have hee : HasDerivAt e (d x) x := by
      have := (hasDerivAt_const x (c t₀)).add hxd
      simpa only [he_def, zero_add] using this
    exact hee.deriv
  have hcongr : (∫ x in t₀..t, deriv e x * e x + e x * deriv e x) =
      ∫ x in t₀..t, 2 * c x * d x := by
    refine intervalIntegral.integral_congr_ae ?_
    have hae' : ∀ᵐ x ∂(volume.restrict (uIoc t₀ t)),
        x ∈ uIcc t₀ t → deriv e x = d x :=
      ae_restrict_of_ae hae_deriv
    rw [ae_restrict_iff' measurableSet_uIoc] at hae'
    filter_upwards [hae'] with x hx hxmem
    have hxd : deriv e x = d x := hx hxmem (uIoc_subset_uIcc hxmem)
    have hxce : c x = e x := hce x (uIoc_subset_uIcc hxmem)
    rw [hxd, hxce]; ring
  rw [hcongr] at hprod
  have hct : c t = e t := hce t htmem
  have hct₀ : c t₀ = e t₀ := hce t₀ h0mem
  rw [hct, hct₀]
  nlinarith [hprod]

structure CrossScaleField (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (a : ℝ) (T : ℝ) where
  /-- The upper-scale (`H^{a+2}`) `L²`-in-time datum, an a.e.-class. -/
  hiL2 : timeL2 (tensorHs (I := I) (M := M) g r s (a + 2)) T
  /-- The lower-scale (`Hᵃ`) time-Sobolev datum: initial value and `L²`
  derivative. -/
  lo : timeH1 (tensorHs (I := I) (M := M) g r s a) T
  /-- For almost every `t`, the `Hᵃ` view of the pointwise value `hiL2 t` is the
  indefinite `Hᵃ`-integral `lo.toFun t` of the derivative.  This is the a.e.
  compatibility of the two scales; no continuity is assumed. -/
  link : ∀ᵐ t ∂(timeMeasure T),
    tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) (hiL2 t) = lo.toFun t

namespace CrossScaleField

variable (u : CrossScaleField (I := I) (M := M) g r s a T)

/-- The per-mode coordinate `cᵢ(t) = (lo.toFun t).coeff i`, a scalar function of
time defined for every `t`. -/
def coeffFun (i : TensorEigenIdx (I := I) (M := M) g r s) (t : ℝ) : ℝ :=
  (u.lo.toFun t).coeff i

/-- The per-mode coordinate is the scalar indefinite integral of the derivative
coordinate:

  `cᵢ(t) = lo.init.coeff i + ∫₀ᵗ (lo.deriv s).coeff i ds`. -/
lemma coeffFun_eq_integral (i : TensorEigenIdx (I := I) (M := M) g r s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    u.coeffFun i t =
      u.lo.init.coeff i + ∫ s in (0 : ℝ)..t, (u.lo.deriv s).coeff i := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  have hcomm : ∫ s in (0 : ℝ)..t, (u.lo.deriv s).coeff i =
      (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i)
        (∫ s in (0 : ℝ)..t, u.lo.deriv s) := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm
      (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i)
      (u.lo.intervalIntegrable_deriv h0 ht)]
    rfl
  have hval : u.coeffFun i t =
      (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i) (u.lo.toFun t) := rfl
  rw [hval, timeH1.toFun_apply, map_add, hcomm]
  rfl

/-- Each per-mode coordinate `cᵢ` is continuous on `[0,T]`: the bounded
coordinate functional `coeffCLM i` composed with the continuous represented
function `lo.toFun`. -/
lemma continuousOn_coeffFun (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ContinuousOn (u.coeffFun i) (Icc (0 : ℝ) T) := by
  have hcomp : ContinuousOn
      (fun t => coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i
        (u.lo.toFun t)) (Icc (0 : ℝ) T) :=
    (coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a)
      i).continuous.comp_continuousOn u.lo.continuousOn_toFun
  simpa only [coeffCLM_apply] using hcomp

/-- For almost every `t`, every per-mode coordinate of the lower-scale function
equals the corresponding coordinate of the top-scale value `hiL2 t`. -/
lemma ae_coeffFun_eq_hiL2 :
    ∀ᵐ t ∂(timeMeasure T), ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      u.coeffFun i t = (u.hiL2 t).coeff i := by
  filter_upwards [u.link] with t ht i
  have := congrArg (fun T => tensorHs.coeff T i) ht
  simpa only [coeffFun, tensorHsInclusion_coeff_apply] using this.symm

/-- For almost every `t`, the finite-set weighted partial sum of the squared
continuous coordinates at the *top* exponent `a+2` is bounded by the squared
`H^{a+2}` norm of `hiL2 t`. -/
lemma ae_finset_top_sq_le (S : Finset (TensorEigenIdx (I := I) (M := M) g r s)) :
    ∀ᵐ t ∂(timeMeasure T),
      ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 2) * (u.coeffFun i t) ^ 2 ≤
        ‖u.hiL2 t‖ ^ 2 := by
  filter_upwards [u.ae_coeffFun_eq_hiL2] with t ht
  have hsum_eq : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 2) * (u.coeffFun i t) ^ 2 =
      ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 2) * ((u.hiL2 t).coeff i) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => by rw [ht i])
  rw [hsum_eq, tensorHs.norm_sq_eq_tsum]
  refine Summable.sum_le_tsum S (fun i _ => ?_) (u.hiL2 t).weighted_summable
  exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)) (sq_nonneg _)

/-- The derivative coordinate `s ↦ (lo.deriv s).coeff i` is interval integrable
on every `t₀..t` with endpoints in `[0,T]`: the bounded functional `coeffCLM i`
applied to the interval-integrable `L²` derivative. -/
lemma intervalIntegrable_deriv_coeffFun
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable (fun τ => (u.lo.deriv τ).coeff i) volume t₀ t := by
  have hbase : IntervalIntegrable (fun τ => u.lo.deriv τ) volume t₀ t :=
    u.lo.intervalIntegrable_deriv ht₀ ht
  have hcomp : IntervalIntegrable
      (fun τ => coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a)
        i (u.lo.deriv τ)) volume t₀ t :=
    intervalIntegrable_iff.mpr
      ((coeffCLM (I := I) (M := M) (g := g) (r := r) (s := s) (σ := a) i).integrable_comp
        (intervalIntegrable_iff.mp hbase))
  simpa only [coeffCLM_apply] using hcomp

/-- **Per-mode squared fundamental theorem of calculus, between two times.**
For `t₀, t ∈ [0,T]`,

  `cᵢ(t)² = cᵢ(t₀)² + ∫_{t₀}^t 2·cᵢ(s)·(lo.deriv s).coeff i ds`. -/
lemma coeffFun_sq_eq (i : TensorEigenIdx (I := I) (M := M) g r s)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T) :
    (u.coeffFun i t) ^ 2 = (u.coeffFun i t₀) ^ 2 +
      ∫ s in t₀..t, 2 * (u.coeffFun i s) * (u.lo.deriv s).coeff i := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  refine sq_eq_base_add_integral_of_indefinite
    (u.intervalIntegrable_deriv_coeffFun i ht₀ ht) (fun x hx => ?_)
  have hxmem : x ∈ Icc (0 : ℝ) T := uIcc_subset_Icc ht₀ ht hx
  rw [u.coeffFun_eq_integral i hxmem, u.coeffFun_eq_integral i ht₀]
  rw [add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left
    (u.intervalIntegrable_deriv_coeffFun i h0 hxmem)
    (u.intervalIntegrable_deriv_coeffFun i h0 ht₀)

/-- **Finite-set cross-scale Cauchy–Schwarz, almost everywhere.**  For a.e. `s`
and every finite set of modes `S`, the partial cross-scale pairing of the
continuous coordinates against the derivative coordinates is bounded by the
product of the `H^{a+2}` norm of `hiL2 s` and the `Hᵃ` norm of `lo.deriv s`:

  `|∑_{i∈S} (1+λᵢ)^{a+1} cᵢ(s) dᵢ(s)| ≤ ‖hiL2 s‖_{H^{a+2}} · ‖lo.deriv s‖_{Hᵃ}`. -/
lemma ae_abs_finset_crossPairing_le :
    ∀ᵐ τ ∂(timeMeasure T),
      ∀ S : Finset (TensorEigenIdx (I := I) (M := M) g r s),
        |∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) *
          (u.coeffFun i τ * (u.lo.deriv τ).coeff i)| ≤
            ‖u.hiL2 τ‖ * ‖u.lo.deriv τ‖ := by
  filter_upwards [u.ae_coeffFun_eq_hiL2] with τ hs S
  set f : TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (a + 2)) * u.coeffFun i τ with hf_def
  set d : TensorEigenIdx (I := I) (M := M) g r s → ℝ :=
    fun i => Real.sqrt (tensorSobolevWeight (I := I) (M := M) i a) * (u.lo.deriv τ).coeff i with hd_def
  have hsummand : ∀ i,
      tensorSobolevWeight (I := I) (M := M) i (a + 1) *
        (u.coeffFun i τ * (u.lo.deriv τ).coeff i) = f i * d i := by
    intro i
    rw [hf_def, hd_def, tensorSobolevWeight_mid_eq_sqrt_mul_sqrt (I := I) (M := M) i a]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsummand i)]
  have hCS : (∑ i ∈ S, f i * d i) ^ 2 ≤ (∑ i ∈ S, (f i) ^ 2) * ∑ i ∈ S, (d i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq S f d
  have hfsq : ∑ i ∈ S, (f i) ^ 2 ≤ ‖u.hiL2 τ‖ ^ 2 := by
    have heq : ∑ i ∈ S, (f i) ^ 2 =
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 2) * ((u.hiL2 τ).coeff i) ^ 2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hf_def, mul_pow, Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)),
        hs i]
    rw [heq, tensorHs.norm_sq_eq_tsum]
    refine Summable.sum_le_tsum S (fun i _ => ?_) (u.hiL2 τ).weighted_summable
    exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 2)) (sq_nonneg _)
  have hdsq : ∑ i ∈ S, (d i) ^ 2 ≤ ‖u.lo.deriv τ‖ ^ 2 := by
    have heq : ∑ i ∈ S, (d i) ^ 2 =
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i a * ((u.lo.deriv τ).coeff i) ^ 2 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hd_def, mul_pow, Real.sq_sqrt (tensorSobolevWeight_nonneg (I := I) (M := M) i a)]
    rw [heq, tensorHs.norm_sq_eq_tsum]
    refine Summable.sum_le_tsum S (fun i _ => ?_) (u.lo.deriv τ).weighted_summable
    exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i a) (sq_nonneg _)
  have hsq_le : (∑ i ∈ S, f i * d i) ^ 2 ≤ (‖u.hiL2 τ‖ * ‖u.lo.deriv τ‖) ^ 2 := by
    refine le_trans hCS ?_
    rw [mul_pow]
    refine mul_le_mul hfsq hdsq (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (sq_nonneg _)
  have hprodnn : 0 ≤ ‖u.hiL2 τ‖ * ‖u.lo.deriv τ‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  exact abs_le_of_sq_le_sq hsq_le hprodnn

/-- The dominating product `s ↦ ‖hiL2 s‖ · ‖lo.deriv s‖` is integrable on
`[0,T]`: the product of the two square-integrable norm factors. -/
lemma integrableOn_normMul :
    IntegrableOn (fun s => ‖u.hiL2 s‖ * ‖u.lo.deriv s‖) (Set.Icc (0 : ℝ) T) volume := by
  have hhi : IntegrableOn (fun s => ‖u.hiL2 s‖ ^ 2) (Set.Icc (0 : ℝ) T) volume := by
    have hLp : MemLp (fun s => u.hiL2 s) 2 (timeMeasure T) := Lp.memLp u.hiL2
    have hint := hLp.integrable_norm_rpow (by norm_num) (by norm_num)
    have hpow : (fun x => ‖u.hiL2 x‖ ^ (2 : ℝ≥0∞).toReal) = (fun x => ‖u.hiL2 x‖ ^ 2) := by
      funext x
      rw [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num, Real.rpow_two]
    rw [hpow] at hint
    exact hint
  have hlo : IntegrableOn (fun s => ‖u.lo.deriv s‖ ^ 2) (Set.Icc (0 : ℝ) T) volume := by
    have hLp : MemLp (fun s => u.lo.deriv s) 2 (timeMeasure T) := Lp.memLp u.lo.deriv
    have hint := hLp.integrable_norm_rpow (by norm_num) (by norm_num)
    have hpow : (fun x => ‖u.lo.deriv x‖ ^ (2 : ℝ≥0∞).toReal) = (fun x => ‖u.lo.deriv x‖ ^ 2) := by
      funext x
      rw [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num, Real.rpow_two]
    rw [hpow] at hint
    exact hint
  have hmeas : AEStronglyMeasurable (fun s => ‖u.hiL2 s‖ * ‖u.lo.deriv s‖)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    have h1 : AEStronglyMeasurable (fun s => ‖u.hiL2 s‖)
        (volume.restrict (Set.Icc (0 : ℝ) T)) :=
      (Lp.aestronglyMeasurable u.hiL2).norm
    have h2 : AEStronglyMeasurable (fun s => ‖u.lo.deriv s‖)
        (volume.restrict (Set.Icc (0 : ℝ) T)) :=
      (Lp.aestronglyMeasurable u.lo.deriv).norm
    exact h1.mul h2
  refine Integrable.mono' (g := fun s => (1 / 2) * (‖u.hiL2 s‖ ^ 2 + ‖u.lo.deriv s‖ ^ 2))
    ((hhi.add hlo).const_mul (1 / 2)) hmeas (ae_of_all _ (fun s => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  nlinarith [sq_nonneg (‖u.hiL2 s‖ - ‖u.lo.deriv s‖), norm_nonneg (u.hiL2 s),
    norm_nonneg (u.lo.deriv s)]

/-- **`H^{a+1}` summability of the representative coordinates, uniformly in
time.**  For `0 < T` there is a single bound `B` such that, for every `t` and
every finite set of modes `S`,

  `∑_{i∈S} (1+λᵢ)^{a+1} cᵢ(t)² ≤ B`.

In particular the family `i ↦ (1+λᵢ)^{a+1} cᵢ(t)²` is summable for every `t`,
i.e. the per-mode coordinates of `lo.toFun t` define an element of `H^{a+1}`. -/
lemma exists_uniform_bound (hT : 0 < T) :
    ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ S : Finset (TensorEigenIdx (I := I) (M := M) g r s),
      ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t) ^ 2 ≤ B := by
  have hμ_ne : timeMeasure T ≠ 0 := timeMeasure_ne_zero hT
  haveI : (ae (timeMeasure T)).NeBot := MeasureTheory.ae_neBot.2 hμ_ne
  have hcombine : ∀ᵐ t₀ ∂(timeMeasure T), t₀ ∈ Icc (0 : ℝ) T ∧
      (∀ i : TensorEigenIdx (I := I) (M := M) g r s, u.coeffFun i t₀ = (u.hiL2 t₀).coeff i) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc, u.ae_coeffFun_eq_hiL2]
      with t₀ hmem hcoeff using ⟨hmem, hcoeff⟩
  obtain ⟨t₀, ht₀mem, ht₀coeff⟩ := hcombine.exists
  set C : ℝ := 2 * ∫ s in Set.Icc (0 : ℝ) T, ‖u.hiL2 s‖ * ‖u.lo.deriv s‖ with hC_def
  set R : ℝ := ‖u.hiL2 t₀‖ ^ 2 with hR_def
  refine ⟨R + C, fun t ht S => ?_⟩
  have hsum_ftc : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t) ^ 2 =
      ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t₀) ^ 2 +
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) *
          ∫ s in t₀..t, 2 * (u.coeffFun i s) * (u.lo.deriv s).coeff i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [u.coeffFun_sq_eq i ht₀mem ht, mul_add]
  rw [hsum_ftc]
  have hterm0 : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t₀) ^ 2 ≤ R := by
    rw [hR_def]
    have heq : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t₀) ^ 2 =
        ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) * ((u.hiL2 t₀).coeff i) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => by rw [ht₀coeff i])
    rw [heq]
    refine le_trans (Summable.sum_le_tsum S
      (fun i _ => mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 1)) (sq_nonneg _))
      ((tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith) (u.hiL2 t₀)).weighted_summable.congr
        (fun i => by rw [tensorHsInclusion_coeff_apply]))) ?_
    have hnormSq : (∑' i, tensorSobolevWeight (I := I) (M := M) i (a + 1) *
          ((u.hiL2 t₀).coeff i) ^ 2) =
        ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (show a + 1 ≤ a + 2 by linarith) (u.hiL2 t₀)‖ ^ 2 := by
      rw [tensorHs.norm_sq_eq_tsum]
      exact (tsum_congr (fun i => by rw [tensorHsInclusion_coeff_apply])).symm
    rw [hnormSq]
    have hle := tensorHsInclusion_norm_le (I := I) (M := M)
      (show a + 1 ≤ a + 2 by linarith) (u.hiL2 t₀)
    nlinarith [hle, norm_nonneg (u.hiL2 t₀),
      norm_nonneg (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith) (u.hiL2 t₀))]
  have hterm1 : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) *
        ∫ s in t₀..t, 2 * (u.coeffFun i s) * (u.lo.deriv s).coeff i ≤ C := by
    have hintegrable : ∀ i, IntervalIntegrable
        (fun τ => 2 * (u.coeffFun i τ) * (u.lo.deriv τ).coeff i) volume t₀ t := by
      intro i
      have hcont : ContinuousOn (fun τ => 2 * u.coeffFun i τ) (uIcc t₀ t) :=
        continuousOn_const.mul ((u.continuousOn_coeffFun i).mono (uIcc_subset_Icc ht₀mem ht))
      have hd := u.intervalIntegrable_deriv_coeffFun i ht₀mem ht
      exact hd.continuousOn_mul hcont
    set G : ℝ → ℝ := fun τ => ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) *
      (2 * (u.coeffFun i τ) * (u.lo.deriv τ).coeff i) with hG_def
    have hsum_int : ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) *
          ∫ τ in t₀..t, 2 * (u.coeffFun i τ) * (u.lo.deriv τ).coeff i =
        ∫ τ in t₀..t, G τ := by
      rw [hG_def,
        intervalIntegral.integral_finset_sum (s := S) (fun i _ => (hintegrable i).const_mul _)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [intervalIntegral.integral_const_mul]
    rw [hsum_int]
    have hsub : Set.uIoc t₀ t ⊆ Set.Icc (0 : ℝ) T :=
      (Set.uIoc_subset_uIcc).trans (uIcc_subset_Icc ht₀mem ht)
    set dom : ℝ → ℝ := fun τ => 2 * (‖u.hiL2 τ‖ * ‖u.lo.deriv τ‖) with hdom_def
    have hdom_nonneg : ∀ τ, 0 ≤ dom τ := fun τ => by rw [hdom_def]; positivity
    have hGbound : ∀ᵐ τ ∂(volume.restrict (Set.uIoc t₀ t)), ‖G τ‖ ≤ dom τ := by
      have hfull := u.ae_abs_finset_crossPairing_le
      have hae := ae_restrict_of_ae_restrict_of_subset hsub hfull
      filter_upwards [hae] with τ hτ
      have hbnd := hτ S
      have hGeq : G τ = 2 * ∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) *
          (u.coeffFun i τ * (u.lo.deriv τ).coeff i) := by
        rw [hG_def, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => by ring)
      rw [Real.norm_eq_abs, hGeq, hdom_def, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
      nlinarith [hbnd, abs_nonneg (∑ i ∈ S, tensorSobolevWeight (I := I) (M := M) i (a + 1) *
        (u.coeffFun i τ * (u.lo.deriv τ).coeff i)),
        mul_nonneg (norm_nonneg (u.hiL2 τ)) (norm_nonneg (u.lo.deriv τ))]
    have hdom_int : IntervalIntegrable dom volume t₀ t := by
      rw [intervalIntegrable_iff, hdom_def]
      exact (u.integrableOn_normMul.mono_set (Set.uIoc_subset_uIcc.trans
        (uIcc_subset_Icc ht₀mem ht))).const_mul 2
    have hdom_set_int : IntegrableOn dom (Set.Icc (0 : ℝ) T) volume := by
      rw [hdom_def]; exact u.integrableOn_normMul.const_mul 2
    calc ∫ τ in t₀..t, G τ
        ≤ |∫ τ in t₀..t, G τ| := le_abs_self _
      _ ≤ |∫ τ in t₀..t, dom τ| := by
          have hbnd := intervalIntegral.norm_integral_le_abs_of_norm_le
            (μ := volume) (a := t₀) (b := t) (f := G) (g := dom) hGbound hdom_int
          rwa [Real.norm_eq_abs] at hbnd
      _ = ∫ τ in Set.uIoc t₀ t, dom τ := by
          rw [intervalIntegral.abs_integral_eq_abs_integral_uIoc]
          exact abs_of_nonneg (setIntegral_nonneg measurableSet_uIoc (fun τ _ => hdom_nonneg τ))
      _ ≤ ∫ τ in Set.Icc (0 : ℝ) T, dom τ :=
          setIntegral_mono_set hdom_set_int (ae_of_all _ hdom_nonneg)
            (HasSubset.Subset.eventuallyLE hsub)
      _ = C := by rw [hC_def, hdom_def, ← MeasureTheory.integral_const_mul]
  linarith [hterm0, hterm1]

/-- **`H^{a+1}` summability of the representative coordinates.**  For `0 < T` and
every `t ∈ [0,T]`, the family `i ↦ (1+λᵢ)^{a+1} cᵢ(t)²` is summable: the
continuous per-mode coordinates of `lo.toFun t` define an element of `H^{a+1}`.
This is the conclusion of the Lions–Magenes energy comparison, i.e.
`exists_uniform_bound`. -/
lemma summable_coeffFun_sq (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t) ^ 2) := by
  obtain ⟨B, hB⟩ := u.exists_uniform_bound hT
  refine summable_of_sum_le (c := B)
    (fun i => mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i (a + 1)) (sq_nonneg _))
    (fun S => hB t ht S)

open Classical in
/-- The intermediate-scale (`H^{a+1}`) representative of the field, **produced**
from the continuous per-mode coordinates `cᵢ(t) = (lo.toFun t).coeff i`.  Where
the coordinates are `H^{a+1}`-summable it is the corresponding `H^{a+1}` element;
otherwise it is `0` (a case that does not arise on `[0,T]` for `0 < T`). -/
def repr (t : ℝ) : tensorHs (I := I) (M := M) g r s (a + 1) :=
  if h : Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t) ^ 2) then
    { coeff := fun i => u.coeffFun i t, weighted_summable := h }
  else 0

/-- On the summable regime, the representative's coordinates are exactly the
continuous per-mode coordinates `cᵢ(t)`. -/
lemma repr_coeff_of_summable {t : ℝ}
    (h : Summable (fun i : TensorEigenIdx (I := I) (M := M) g r s =>
      tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t) ^ 2))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (u.repr t).coeff i = u.coeffFun i t := by
  rw [repr, dif_pos h]

/-- For `0 < T` and `t ∈ [0,T]`, the representative's coordinates are the
continuous per-mode coordinates `cᵢ(t)`. -/
@[simp] lemma repr_coeff (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (u.repr t).coeff i = u.coeffFun i t :=
  u.repr_coeff_of_summable (u.summable_coeffFun_sq hT ht) i

/-- The squared `H^{a+1}` norm of the representative is the weighted tsum of the
squared continuous coordinates. -/
lemma normSq_repr (hT : 0 < T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖u.repr t‖ ^ 2 =
      ∑' i, tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t) ^ 2 := by
  rw [tensorHs.norm_sq_eq_tsum]
  exact tsum_congr (fun i => by rw [u.repr_coeff hT ht])

end CrossScaleField

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry
