import DifferentialGeometry.Geometry.Comparison.FiniteMetric.RiemannianHinge
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EndpointBand

/-!
# LFR23 (H1): the endpoint band kernels on actual minimizing directions of a finite metric

Binding of W4-F7c's LFR23 kernels (`EndpointBand.lean`) to a complete finite-regularity metric
`g : C^{r+1}` (`1 ≤ r`) with `sec_g ≥ 0`, through CM5.b (`comparisonAngle_le_arccos_inner_finite`).
A unit vector `v ∈ T_xM` is a minimizing direction from `x` toward `n` when
`exp_x (d(n, x) v) = n` (the finite form of `inwardMinimizingDirections`, cf. CM-H's
`mem_inwardMinimizingDirections_iff_expMap`).

* `inner_le_cos_metricComparisonAngle_finite`, `inner_le_comparisonCosine_finite`: (H1) of the
  W4-F7c addendum, `cos ∠(v, w) ≤ comparisonCosine(d(x,z₀), d(x,x⁺), d(z₀,x⁺))`;
* `one_add_inner_lt_of_endpoint_finite`: (LFR23.1) on actual directions, `1 + g_x(v, w) < 300 δ`;
* `sqrt_inner_sub_lt_of_endpoint_finite`, `inner_neg_lt_of_endpoint_finite`: the direction
  diameter `|v - v'|_{g_x} < 2√(600δ)` and `g_x(-v, v') < -7/8` (`δ ≤ 1/9600`), from the kernels
  `norm_sub_lt_of_one_add_inner_lt`, `inner_neg_lt_of_one_add_inner_lt` on `(T_xM, g_x)`.
Lane CM-A2, 2026-10-04.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Comparison.Toponogov

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {n : ℕ∞ω} (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))

/-- The direction-diameter kernel on `(T_xM, g_x)`. -/
theorem sqrt_inner_sub_lt_of_one_add_inner_lt_finite (x : M) {v v' w : TangentSpace I x} {c : ℝ}
    (hv : g.inner x v v = 1) (hv' : g.inner x v' v' = 1) (hw : g.inner x w w = 1)
    (h : 1 + g.inner x v w < c) (h' : 1 + g.inner x v' w < c) :
    Real.sqrt (g.inner x (v - v') (v - v')) < 2 * Real.sqrt (2 * c) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hn (z : TangentSpace I x) (hz : g.inner x z z = 1) : ‖z‖ = 1 := by
    rw [norm_eq_sqrt_real_inner]
    exact (congrArg Real.sqrt hz).trans Real.sqrt_one
  have hk := norm_sub_lt_of_one_add_inner_lt (hn v hv) (hn v' hv') (hn w hw) h h'
  rwa [norm_eq_sqrt_real_inner] at hk

/-- The negated-direction kernel on `(T_xM, g_x)`. -/
theorem inner_neg_lt_of_one_add_inner_lt_finite (x : M) {v v' w : TangentSpace I x} {c : ℝ}
    (hc : c ≤ 1 / 32) (hv : g.inner x v v = 1) (hv' : g.inner x v' v' = 1)
    (hw : g.inner x w w = 1) (h : 1 + g.inner x v w < c) (h' : 1 + g.inner x v' w < c) :
    g.inner x (-v) v' < -(7 / 8) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hn (z : TangentSpace I x) (hz : g.inner x z z = 1) : ‖z‖ = 1 := by
    rw [norm_eq_sqrt_real_inner]
    exact (congrArg Real.sqrt hz).trans Real.sqrt_one
  exact inner_neg_lt_of_one_add_inner_lt hc (hn v hv) (hn v' hv') (hn w hw) h h'

end Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]
  {r : ℕ∞} (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

/-- **LFR23 (H1)**, cosine form: for unit minimizing directions `v` (from `x` toward `z₀`) and `w`
(from `x` toward `x⁺`), `g_x(v, w) ≤ cos ∠̃_x(z₀, x⁺)`. -/
theorem inner_le_cos_metricComparisonAngle_finite (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {x z₀ x' : M} (hz₀ : z₀ ≠ x) (hx' : x' ≠ x) {v w : E}
    (hv : g.inner x v v = 1) (hw : g.inner x w w = 1)
    (hvz : g.expMap (⟨x, dist z₀ x • v⟩ : TangentBundle I M) = z₀)
    (hwx : g.expMap (⟨x, dist x' x • w⟩ : TangentBundle I M) = x') :
    g.inner x v w ≤ Real.cos (metricComparisonAngle z₀ x x') := by
  have ha : 0 < dist z₀ x := dist_pos.mpr hz₀
  have hb : 0 < dist x' x := dist_pos.mpr hx'
  have hminA : dist x (g.expMap (⟨x, dist z₀ x • v⟩ : TangentBundle I M)) = dist z₀ x := by
    rw [hvz, dist_comm]
  have hminB : dist x (g.expMap (⟨x, dist x' x • w⟩ : TangentBundle I M)) = dist x' x := by
    rw [hwx, dist_comm]
  have h := DifferentialGeometry.Geometry.FiniteComparison.comparisonAngle_le_arccos_inner_finite
    g hr hnorm x v w ha hb hv hw hminA hminB hsec
  rw [hvz, hwx] at h
  have hcs := abs_finite_inner_le g x v w
  rw [hv, hw, Real.sqrt_one, one_mul] at hcs
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (comparisonAngle_mem_Icc _ _ _).1
    (Real.arccos_le_pi _) h
  rw [Real.cos_arccos (abs_le.mp hcs).1 (abs_le.mp hcs).2] at hcos
  rwa [metricComparisonAngle, dist_comm x z₀, dist_comm x x']

/-- **LFR23 (H1)**, the addendum's form: `cos ∠(v, w) ≤ comparisonCosine(d(x,z₀), d(x,x⁺), d(z₀,x⁺))`. -/
theorem inner_le_comparisonCosine_finite (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {x z₀ x' : M} (hz₀ : z₀ ≠ x) (hx' : x' ≠ x) {v w : E}
    (hv : g.inner x v v = 1) (hw : g.inner x w w = 1)
    (hvz : g.expMap (⟨x, dist z₀ x • v⟩ : TangentBundle I M) = z₀)
    (hwx : g.expMap (⟨x, dist x' x • w⟩ : TangentBundle I M) = x') :
    g.inner x v w ≤ comparisonCosine (dist x z₀) (dist x x') (dist z₀ x') := by
  have h := inner_le_cos_metricComparisonAngle_finite g hr hnorm hsec hz₀ hx' hv hw hvz hwx
  have ha : 0 < dist x z₀ := dist_pos.mpr hz₀.symm
  have hb : 0 < dist x x' := dist_pos.mpr hx'.symm
  have hlow : |dist x z₀ - dist x x'| ≤ dist z₀ x' := by
    rw [abs_le]
    constructor
    · linarith [dist_triangle x z₀ x', dist_comm z₀ x]
    · linarith [dist_triangle z₀ x' x, dist_comm x' x, dist_comm z₀ x]
  have hup : dist z₀ x' ≤ dist x z₀ + dist x x' := by
    linarith [dist_triangle z₀ x x', dist_comm z₀ x]
  rwa [metricComparisonAngle, cos_comparisonAngle ha hb hlow hup] at h

/-- **(LFR23.1) on actual directions.** Under the LFR23 distortion data, a unit minimizing
direction `v` toward `z₀` and `w` toward `x⁺` at a point of `1/2 ≤ r ≤ 37/4` satisfy
`1 + g_x(v, w) < 300 δ`. -/
theorem one_add_inner_lt_of_endpoint_finite (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {z₀ x x' : M} {q : M → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 1000) (hq0 : q z₀ = 0)
    (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hx' : dist z₀ x' = 19 / 2) (hx₁ : 1 / 2 ≤ dist z₀ x) (hx₂ : dist z₀ x ≤ 37 / 4) {v w : E}
    (hv : g.inner x v v = 1) (hw : g.inner x w w = 1)
    (hvz : g.expMap (⟨x, dist z₀ x • v⟩ : TangentBundle I M) = z₀)
    (hwx : g.expMap (⟨x, dist x' x • w⟩ : TangentBundle I M) = x') :
    1 + g.inner x v w < 300 * δ := by
  have hz₀ : z₀ ≠ x := fun h => by rw [h, dist_self] at hx₁; norm_num at hx₁
  have hxx' : x' ≠ x := fun h => by rw [h] at hx'; linarith
  have h := inner_le_cos_metricComparisonAngle_finite g hr hnorm hsec hz₀ hxx' hv hw hvz hwx
  have hk := one_add_cos_metricComparisonAngle_lt hδ hδ' hq0 hqnn hdist hx' hx₁ hx₂
  linarith

/-- **LFR23, direction diameter on actual directions**: two unit minimizing directions toward `z₀`
at `x` are within `2√(600δ)` for `g_x`. -/
theorem sqrt_inner_sub_lt_of_endpoint_finite (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {z₀ x x' : M} {q : M → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 1000) (hq0 : q z₀ = 0)
    (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hx' : dist z₀ x' = 19 / 2) (hx₁ : 1 / 2 ≤ dist z₀ x) (hx₂ : dist z₀ x ≤ 37 / 4) {v v' w : E}
    (hv : g.inner x v v = 1) (hv' : g.inner x v' v' = 1) (hw : g.inner x w w = 1)
    (hvz : g.expMap (⟨x, dist z₀ x • v⟩ : TangentBundle I M) = z₀)
    (hv'z : g.expMap (⟨x, dist z₀ x • v'⟩ : TangentBundle I M) = z₀)
    (hwx : g.expMap (⟨x, dist x' x • w⟩ : TangentBundle I M) = x') :
    Real.sqrt (g.inner x (v - v') (v - v')) < 2 * Real.sqrt (600 * δ) := by
  have h := one_add_inner_lt_of_endpoint_finite g hr hnorm hsec hδ hδ' hq0 hqnn hdist hx' hx₁ hx₂
    hv hw hvz hwx
  have h' := one_add_inner_lt_of_endpoint_finite g hr hnorm hsec hδ hδ' hq0 hqnn hdist hx' hx₁ hx₂
    hv' hw hv'z hwx
  have hk := sqrt_inner_sub_lt_of_one_add_inner_lt_finite g x hv hv' hw h h'
  rwa [← mul_assoc, show (2 : ℝ) * 300 = 600 by norm_num] at hk

/-- **LFR23, the negated direction on actual directions** (`δ ≤ 1/9600`). -/
theorem inner_neg_lt_of_endpoint_finite (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {z₀ x x' : M} {q : M → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 9600) (hq0 : q z₀ = 0)
    (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hx' : dist z₀ x' = 19 / 2) (hx₁ : 1 / 2 ≤ dist z₀ x) (hx₂ : dist z₀ x ≤ 37 / 4) {v v' w : E}
    (hv : g.inner x v v = 1) (hv' : g.inner x v' v' = 1) (hw : g.inner x w w = 1)
    (hvz : g.expMap (⟨x, dist z₀ x • v⟩ : TangentBundle I M) = z₀)
    (hv'z : g.expMap (⟨x, dist z₀ x • v'⟩ : TangentBundle I M) = z₀)
    (hwx : g.expMap (⟨x, dist x' x • w⟩ : TangentBundle I M) = x') :
    g.inner x (-v) v' < -(7 / 8) := by
  have hδ1 : δ < 1 / 1000 := by linarith
  have h := one_add_inner_lt_of_endpoint_finite g hr hnorm hsec hδ hδ1 hq0 hqnn hdist hx' hx₁ hx₂
    hv hw hvz hwx
  have h' := one_add_inner_lt_of_endpoint_finite g hr hnorm hsec hδ hδ1 hq0 hqnn hdist hx' hx₁ hx₂
    hv' hw hv'z hwx
  exact inner_neg_lt_of_one_add_inner_lt_finite g x (by linarith) hv hv' hw h h'

end DifferentialGeometry.Geometry.Collapse
