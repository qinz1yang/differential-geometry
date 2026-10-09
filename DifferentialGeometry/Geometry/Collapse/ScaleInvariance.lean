import DifferentialGeometry.Geometry.Collapse.CurvatureScaleBalls
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormBridge
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling

/-!
# Scale invariance of the static collapse predicates

For a metric `g` and `c > 0`, the rescaled metric `c g` has distances `√c d_g`
(`riemannianBallOf_scaleMetric`), volume `(√c)^n vol_g` (`volume_scale_apply`), curvature scale
`√c R_p` (`curvatureRadius_scaleMetric`, A1 T4) and derivative norms `|∇^k Rm|_g / (c (√c)^k)`
(`curvatureDerivativeNorm_scaleMetric_div`, A4 T2). Consequently, in dimension three:

* T3 `ballVolume_scaleMetric`: `vol_{c g} B_{c g}(p, √c r) = (√c)^3 vol_g B_g(p, r)`;
* T3 `volumeCollapsedAtCurvatureScale_scaleMetric_iff`: the collapsing predicate at the curvature
  scale is scale invariant;
* T3 `curvatureDerivativesControlled_scaleMetric_iff`: the derivative-control predicate is scale
  invariant (each radius `r` of `c g` is `√c t` for a radius `t` of `g`).

Not scale invariant, hence excluded: `NearlyCuspidalBoundary` (it compares with a fixed hyperbolic
cusp metric and a fixed `δ`) and `boundaryVolumeCollapsed` (its buffer `boundaryBufferDistance = 10`
is a fixed distance, which becomes `10 / √c` for `g`), both in `Geometry/Collapse/CuspBoundary.lean`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open Set
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [CompleteSpace E] in
/-- Volume of rescaled balls in any dimension. -/
theorem ballVolume_scaleMetric_finrank (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I M)
    (p : M) (r : ℝ) :
    ballVolume (scaleMetric c hc g) p (Real.sqrt c * r) =
      ENNReal.ofReal (Real.sqrt c) ^ Module.finrank ℝ E * ballVolume g p r := by
  unfold ballVolume
  rw [riemannianBallOf_scaleMetric, Integral.Measure.volume_scale_apply]

omit [CompleteSpace E] in
/-- **T3.** Volume of rescaled balls in dimension three. -/
theorem ballVolume_scaleMetric (hdim : Module.finrank ℝ E = 3) (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M) (p : M) (r : ℝ) :
    ballVolume (scaleMetric c hc g) p (Real.sqrt c * r) =
      ENNReal.ofReal (Real.sqrt c) ^ 3 * ballVolume g p r := by
  rw [ballVolume_scaleMetric_finrank, hdim]


/-! ### Scaling conversions for one radius -/

omit [SigmaCompactSpace M] in
/-- `√c t` is below the curvature scale of `c g` iff `t` is below that of `g`. -/
theorem ofReal_mul_lt_curvatureRadius_scaleMetric_iff (c : ℝ) (hc : 0 < c)
    {g : SmoothRiemannianMetric I M} {p : M} {t : ℝ} :
    ENNReal.ofReal (Real.sqrt c * t) < curvatureRadius (scaleMetric c hc g) p ↔
      ENNReal.ofReal t < curvatureRadius g p := by
  rw [curvatureRadius_scaleMetric, ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
  exact ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hc)).ne'
    ENNReal.ofReal_ne_top

omit [SigmaCompactSpace M] in
/-- The curvature scale of `c g` is `√c t` iff that of `g` is `t`. -/
theorem curvatureRadius_scaleMetric_eq_ofReal_mul_iff (c : ℝ) (hc : 0 < c)
    {g : SmoothRiemannianMetric I M} {p : M} {t : ℝ} :
    curvatureRadius (scaleMetric c hc g) p = ENNReal.ofReal (Real.sqrt c * t) ↔
      curvatureRadius g p = ENNReal.ofReal t := by
  rw [curvatureRadius_scaleMetric, ENNReal.ofReal_mul (Real.sqrt_nonneg c)]
  exact ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hc)).ne'
    ENNReal.ofReal_ne_top

private theorem ofReal_mul_sqrt_mul_pow_three (c : ℝ) (hc : 0 < c) (w t : ℝ) :
    ENNReal.ofReal (w * (Real.sqrt c * t) ^ 3) =
      ENNReal.ofReal (Real.sqrt c) ^ 3 * ENNReal.ofReal (w * t ^ 3) := by
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg c), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

omit [CompleteSpace E] in
/-- The upper volume bound `w r³` transforms with the radius. -/
theorem ballVolume_scaleMetric_le_iff (hdim : Module.finrank ℝ E = 3) (c : ℝ) (hc : 0 < c)
    {g : SmoothRiemannianMetric I M} {p : M} {w t : ℝ} :
    ballVolume (scaleMetric c hc g) p (Real.sqrt c * t) ≤
        ENNReal.ofReal (w * (Real.sqrt c * t) ^ 3) ↔
      ballVolume g p t ≤ ENNReal.ofReal (w * t ^ 3) := by
  rw [ballVolume_scaleMetric hdim, ofReal_mul_sqrt_mul_pow_three c hc]
  exact ENNReal.mul_le_mul_iff_right
    (pow_ne_zero 3 (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hc)).ne')
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

omit [CompleteSpace E] in
/-- The lower volume bound `w r³` transforms with the radius. -/
theorem le_ballVolume_scaleMetric_iff (hdim : Module.finrank ℝ E = 3) (c : ℝ) (hc : 0 < c)
    {g : SmoothRiemannianMetric I M} {p : M} {w t : ℝ} :
    ENNReal.ofReal (w * (Real.sqrt c * t) ^ 3) ≤
        ballVolume (scaleMetric c hc g) p (Real.sqrt c * t) ↔
      ENNReal.ofReal (w * t ^ 3) ≤ ballVolume g p t := by
  rw [ballVolume_scaleMetric hdim, ofReal_mul_sqrt_mul_pow_three c hc]
  exact ENNReal.mul_le_mul_iff_right
    (pow_ne_zero 3 (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hc)).ne')
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

omit [SigmaCompactSpace M] in
/-- The derivative bound `B r^{-(k+2)}` transforms with the radius. -/
theorem curvatureDerivativeNorm_scaleMetric_le_iff (c : ℝ) (hc : 0 < c)
    {g : SmoothRiemannianMetric I M} {k : ℕ} {x : M} {B t : ℝ} :
    curvatureDerivativeNorm (scaleMetric c hc g) k x ≤ B * ((Real.sqrt c * t) ^ (k + 2))⁻¹ ↔
      curvatureDerivativeNorm g k x ≤ B * (t ^ (k + 2))⁻¹ := by
  have hpos : 0 < c * Real.sqrt c ^ k := mul_pos hc (pow_pos (Real.sqrt_pos.mpr hc) k)
  have hrhs : B * ((Real.sqrt c * t) ^ (k + 2))⁻¹ = B * (t ^ (k + 2))⁻¹ / (c * Real.sqrt c ^ k) := by
    rw [mul_pow, pow_add, Real.sq_sqrt hc.le]
    field_simp
  rw [curvatureDerivativeNorm_scaleMetric_div, hrhs]
  exact div_le_div_iff_of_pos_right hpos

/-- Reparametrising positive radii by a positive factor. -/
private theorem forall_pos_iff_of_mul {s : ℝ} (hs : 0 < s) {P Q : ℝ → Prop}
    (h : ∀ t : ℝ, 0 < t → (P (s * t) ↔ Q t)) :
    (∀ r : ℝ, 0 < r → P r) ↔ ∀ t : ℝ, 0 < t → Q t := by
  constructor
  · intro hP t ht
    exact (h t ht).mp (hP (s * t) (mul_pos hs ht))
  · intro hQ r hr
    have ht : 0 < r / s := div_pos hr hs
    have hr' : s * (r / s) = r := by field_simp
    rw [← hr']
    exact (h (r / s) ht).mpr (hQ (r / s) ht)

/-! ### T3: scale invariance of the static predicates -/

/-- **T3.** Collapsing at the curvature scale is scale invariant. -/
theorem volumeCollapsedAtCurvatureScale_scaleMetric_iff (hdim : Module.finrank ℝ E = 3) (c : ℝ)
    (hc : 0 < c) {g : SmoothRiemannianMetric I M} {w : ℝ} {p : M} :
    volumeCollapsedAtCurvatureScale (scaleMetric c hc g) w p ↔
      volumeCollapsedAtCurvatureScale g w p := by
  unfold volumeCollapsedAtCurvatureScale
  refine forall_pos_iff_of_mul (Real.sqrt_pos.mpr hc) fun t _ => ?_
  rw [curvatureRadius_scaleMetric_eq_ofReal_mul_iff, ballVolume_scaleMetric_le_iff hdim]

/-- **T3.** Derivative control at the curvature scale is scale invariant. -/
theorem curvatureDerivativesControlled_scaleMetric_iff (hdim : Module.finrank ℝ E = 3) (c : ℝ)
    (hc : 0 < c) {g : SmoothRiemannianMetric I M} {K : ℕ} {A : ℝ → ℝ} {w₀ : ℝ} :
    curvatureDerivativesControlled (scaleMetric c hc g) K A w₀ ↔
      curvatureDerivativesControlled g K A w₀ := by
  unfold curvatureDerivativesControlled
  refine forall_congr' fun p => forall_congr' fun w => ?_
  have key : (∀ r : ℝ, 0 < r → w₀ ≤ w → w < euclideanThreeUnitBallVolume →
      ENNReal.ofReal r < curvatureRadius (scaleMetric c hc g) p →
      ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (scaleMetric c hc g) p r →
      ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf (scaleMetric c hc g) p r,
        curvatureDerivativeNorm (scaleMetric c hc g) k q ≤ A w * (r ^ (k + 2))⁻¹) ↔
      (∀ t : ℝ, 0 < t → w₀ ≤ w → w < euclideanThreeUnitBallVolume →
      ENNReal.ofReal t < curvatureRadius g p →
      ENNReal.ofReal (w * t ^ 3) ≤ ballVolume g p t →
      ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf g p t,
        curvatureDerivativeNorm g k q ≤ A w * (t ^ (k + 2))⁻¹) := by
    refine forall_pos_iff_of_mul (Real.sqrt_pos.mpr hc) fun t _ => ?_
    rw [ofReal_mul_lt_curvatureRadius_scaleMetric_iff, le_ballVolume_scaleMetric_iff hdim,
      riemannianBallOf_scaleMetric]
    simp only [curvatureDerivativeNorm_scaleMetric_le_iff]
  constructor
  · intro h t hw₀ hw ht
    exact key.mp (fun r hr hw₀' hw' => h r hw₀' hw' hr) t ht hw₀ hw
  · intro h r hw₀ hw hr
    exact key.mpr (fun t ht hw₀' hw' => h t hw₀' hw' ht) r hr hw₀ hw

end DifferentialGeometry.Geometry.Collapse
