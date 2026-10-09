import DifferentialGeometry.Geometry.Collapse.CuspBoundary
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Curvature.Riemann.Tensor

/-!
# Order-zero metric error of a cusp embedding (F-a, binding at order 0)

For a cusp embedding `e : CuspEmbedding W g K δ X` (`Geometry/Collapse/CuspBoundary.lean`) the field
`metric_error` bounds the `H`-norms of `∇_H^k (e*g - H)` by `δ`, `H = dz² + e^{-z} q` the model
cusp metric. Its order-zero part alone gives, at EVERY point of `cuspDomain` (boundary included):

* `CuspEmbedding.abs_pullback_inner_sub_le`: `|g(De v, De w) - H(v, w)| ≤ δ |v|_H |w|_H`;
* `CuspEmbedding.abs_height_deriv_le`: `|dz(v)| ≤ (1 - δ)^{-1/2} |De v|_g`,
  i.e. `|dz|_g ≤ (1-δ)^{-1/2}`;
* `CuspEmbedding.pullback_inner_vertical_le`: a vertical vector (`v.1 = 0`) has
  `|De v|_g² ≤ (1 + δ) dz(v)²`, i.e. `|dz|_g ≥ (1+δ)^{-1/2}`;
* the BSA01 numbers (blueprint 207B, B:7591): for `δ ≤ 1/100`, `|dz(v)| ≤ 1.01 |De v|_g` and
  `|De v|_g ≤ 1.01 |dz(v)|` on vertical vectors (`…_le_of_le_hundredth`).

The curvature (order-two) part of the binding needs a finite-order transfer through the `C^{K+1}`
map `e.toFun`; it is not attempted here (lane B-1 sheet, item F-a.C).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle
open GC.Endpoint Bundle
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Collapse
universe u

/-- The cusp metric error evaluated on a pair of vectors is the difference of the pulled-back
inner product and the model inner product. -/
theorem cuspMetricError_apply_vec2 {W : CompactCarrier.{u}}
    (g : SmoothRiemannianMetric W.model W.Carrier) (H : HyperbolicCusp)
    (f : CuspHalfSpace → W.Carrier) (p : CuspHalfSpace)
    (v w : TangentSpace halfCollarModel p) :
    cuspMetricError g H f p (vec2 v w) =
      g.inner (f p) (mfderiv halfCollarModel W.model f p v)
        (mfderiv halfCollarModel W.model f p w) - H.metric.inner p v w := by
  rw [← localPullInner_apply (I := halfCollarModel) (J := W.model) g f p v w]
  rfl

/-- The model cusp metric dominates the square of the height derivative. -/
theorem sq_height_le_cusp_inner (H : HyperbolicCusp) (p : CuspHalfSpace)
    (v : TangentSpace halfCollarModel p) :
    (v.2 0) ^ 2 ≤ H.metric.inner p v v := by
  rw [H.metric_formula]
  have hq : 0 ≤ H.torusMetric.inner p.1 v.1 v.1 := metric_inner_self_nonneg _ _ _
  nlinarith [Real.exp_pos (-p.2.val 0)]

/-- On vertical vectors the model cusp metric is the square of the height derivative. -/
theorem cusp_inner_vertical (H : HyperbolicCusp) (p : CuspHalfSpace)
    (v : TangentSpace halfCollarModel p) (hv : v.1 = 0) :
    H.metric.inner p v v = (v.2 0) ^ 2 := by
  have hq : H.torusMetric.inner p.1 v.1 v.1 = 0 := by
    have h1 : H.torusMetric.inner p.1 v.1 = 0 := by
      rw [hv]
      exact (H.torusMetric.inner p.1).map_zero
    rw [h1]
    rfl
  rw [H.metric_formula, hq, mul_zero, add_zero, sq]

/-- Order-zero binding of the metric error of a cusp embedding: at every point of the cusp
domain the pulled-back inner product is `δ`-close to the model one, relative to the model norms. -/
theorem CuspEmbedding.abs_pullback_inner_sub_le {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (v w : TangentSpace halfCollarModel p) :
    |g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p w) - e.cusp.metric.inner p v w| ≤
      δ * Real.sqrt (e.cusp.metric.inner p v v) * Real.sqrt (e.cusp.metric.inner p w w) := by
  have h0 := e.metric_error 0 (Nat.zero_le _) p hp
  change tensor0SFiberNorm e.cusp.metric p 2 (cuspMetricError g e.cusp e.toFun p) ≤ δ at h0
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := halfCollarModel) e.cusp.metric p
  have hb := abs_apply_le_sqrt_normSq0S (I := halfCollarModel) e.cusp.metric p 2 basis hON
    (cuspMetricError g e.cusp e.toFun p) (vec2 v w)
  rw [cuspMetricError_apply_vec2, Fin.prod_univ_two] at hb
  simp only [vec2, Fin.isValue, ↓reduceIte, one_ne_zero] at hb
  refine hb.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right h0 (by positivity)

/-- The pulled-back metric dominates `(1 - δ)` times the model metric on the cusp domain. -/
theorem CuspEmbedding.one_sub_mul_le_pullback_inner {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (v : TangentSpace halfCollarModel p) :
    (1 - δ) * e.cusp.metric.inner p v v ≤
      g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p v) := by
  have h := e.abs_pullback_inner_sub_le hp v v
  rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg _ _ _)] at h
  linarith [(abs_le.mp h).1]

/-- The pulled-back metric is at most `(1 + δ)` times the model metric on the cusp domain. -/
theorem CuspEmbedding.pullback_inner_le_one_add_mul {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (v : TangentSpace halfCollarModel p) :
    g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p v) ≤
      (1 + δ) * e.cusp.metric.inner p v v := by
  have h := e.abs_pullback_inner_sub_le hp v v
  rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg _ _ _)] at h
  linarith [(abs_le.mp h).2]

/-- Upper bound of the height derivative (`|dz|_g ≤ (1-δ)^{-1/2}`) on the cusp domain. -/
theorem CuspEmbedding.abs_height_deriv_le {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) (hδ : δ < 1) {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (v : TangentSpace halfCollarModel p) :
    |v.2 0| ≤ (Real.sqrt (1 - δ))⁻¹ * Real.sqrt (g.inner (e.toFun p)
      (mfderiv halfCollarModel W.model e.toFun p v)
      (mfderiv halfCollarModel W.model e.toFun p v)) := by
  have h1 := e.one_sub_mul_le_pullback_inner hp v
  have h2 := sq_height_le_cusp_inner e.cusp p v
  have hpos : 0 < 1 - δ := by linarith
  have hsq : (v.2 0) ^ 2 ≤ (1 - δ)⁻¹ * g.inner (e.toFun p)
      (mfderiv halfCollarModel W.model e.toFun p v)
      (mfderiv halfCollarModel W.model e.toFun p v) := by
    rw [inv_mul_eq_div, le_div_iff₀ hpos]
    nlinarith
  calc |v.2 0| = Real.sqrt ((v.2 0) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((1 - δ)⁻¹ * g.inner (e.toFun p)
      (mfderiv halfCollarModel W.model e.toFun p v)
      (mfderiv halfCollarModel W.model e.toFun p v)) := Real.sqrt_le_sqrt hsq
    _ = _ := by rw [Real.sqrt_mul (inv_nonneg.mpr hpos.le), Real.sqrt_inv]

/-- On vertical vectors the pulled-back length is controlled by the height derivative
(`|dz|_g ≥ (1+δ)^{-1/2}`). -/
theorem CuspEmbedding.pullback_inner_vertical_le {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (v : TangentSpace halfCollarModel p) (hv : v.1 = 0) :
    g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p v) ≤ (1 + δ) * (v.2 0) ^ 2 := by
  have h := e.pullback_inner_le_one_add_mul hp v
  rwa [cusp_inner_vertical e.cusp p v hv] at h

/-- BSA01's `|dz| ≤ 1.01` on the collar, at the level of the embedding: for `δ ≤ 1/100`. -/
theorem CuspEmbedding.abs_height_deriv_le_of_le_hundredth {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) (hδ : δ ≤ 1 / 100) {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (v : TangentSpace halfCollarModel p) :
    |v.2 0| ≤ 1.01 * Real.sqrt (g.inner (e.toFun p)
      (mfderiv halfCollarModel W.model e.toFun p v)
      (mfderiv halfCollarModel W.model e.toFun p v)) := by
  refine (e.abs_height_deriv_le (by linarith) hp v).trans
    (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  have hs : (1 / 1.01 : ℝ) ≤ Real.sqrt (1 - δ) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  rw [inv_le_comm₀ (Real.sqrt_pos.mpr (by linarith)) (by norm_num)]
  simpa [one_div] using hs

/-- BSA01's `|dz| ≥ 1/1.01` on the collar, at the level of the embedding: for `δ ≤ 1/100`, a
vertical vector has `|De v|_g ≤ 1.01 |dz(v)|`. -/
theorem CuspEmbedding.sqrt_pullback_inner_vertical_le_of_le_hundredth {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ} {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) (hδ : δ ≤ 1 / 100) {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (v : TangentSpace halfCollarModel p) (hv : v.1 = 0) :
    Real.sqrt (g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
        (mfderiv halfCollarModel W.model e.toFun p v)) ≤ 1.01 * |v.2 0| := by
  have h := e.pullback_inner_vertical_le hp v hv
  have h' : g.inner (e.toFun p) (mfderiv halfCollarModel W.model e.toFun p v)
      (mfderiv halfCollarModel W.model e.toFun p v) ≤ (1.01 * |v.2 0|) ^ 2 := by
    rw [mul_pow, sq_abs]
    have hz := sq_nonneg (v.2 0)
    nlinarith
  calc _ ≤ Real.sqrt ((1.01 * |v.2 0|) ^ 2) := Real.sqrt_le_sqrt h'
    _ = 1.01 * |v.2 0| := Real.sqrt_sq (by positivity)

end DifferentialGeometry.Geometry.Collapse
