import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OuterTransferLocal_S35
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- **(S2)** C⁰ comparison from `buffer_error` (k = 0): on `B(x_i, 2n)`,
`|ḡ(dφ v, dφ v) - h(v, v)| ≤ δ · h(v, v)`. -/
theorem bufferedMap_metric_abs_le_S40 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (i : Fin B.count) (t : ℝ) (ht : B.start ≤ t) (p : (B.model i).Carrier)
    (hp : p ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint
      (2 * (B.accuracy t)⁻¹))
    (v : TangentSpace (𝓡 3) p) :
    |(scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht)) (postMetric F.observation t)).inner
        (B.map i t ht p) (mfderiv (𝓡 3) (𝓡 3) (B.map i t ht) p v)
        (mfderiv (𝓡 3) (𝓡 3) (B.map i t ht) p v) - (B.model i).metric.inner p v v| ≤
      B.accuracy t * (B.model i).metric.inner p v v := by
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (B.model i).metric p
  have herr := B.buffer_error i t ht 0 (Nat.zero_le _) p hp
  set E : Tensor0SSpace 2 (𝓡 3) p :=
    ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
          ((t⁻¹ : ℝ) • localPullInner (postMetric F.observation t) (B.map i t ht) p -
            (B.model i).metric.inner p)).uncurryLeft with hE
  change Real.sqrt (normSq0S (B.model i).metric p 2 E) < _ at herr
  have hbound := abs_apply_le_sqrt_normSq0S (B.model i).metric p 2 basis hON E (fun _ => v)
  have heval : E (fun _ => v) =
      (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht)) (postMetric F.observation t)).inner
        (B.map i t ht p) (mfderiv (𝓡 3) (𝓡 3) (B.map i t ht) p v)
        (mfderiv (𝓡 3) (𝓡 3) (B.map i t ht) p v) - (B.model i).metric.inner p v v := rfl
  have hprod : (∏ _a : Fin 2, Real.sqrt ((B.model i).metric.inner p v v)) =
      (B.model i).metric.inner p v v := by
    rw [Fin.prod_univ_two, Real.mul_self_sqrt (metric_inner_self_nonneg _ _ _)]
  rw [heval, hprod] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right herr.le (metric_inner_self_nonneg _ _ _))

theorem bufferedMap_metric_lower_S40 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (i : Fin B.count) (t : ℝ) (ht : B.start ≤ t) (p : (B.model i).Carrier)
    (hp : p ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint
      (2 * (B.accuracy t)⁻¹))
    (v : TangentSpace (𝓡 3) p) :
    (1 - B.accuracy t) * (B.model i).metric.inner p v v ≤
      (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht)) (postMetric F.observation t)).inner
        (B.map i t ht p) (mfderiv (𝓡 3) (𝓡 3) (B.map i t ht) p v)
        (mfderiv (𝓡 3) (𝓡 3) (B.map i t ht) p v) := by
  have h := (abs_le.mp (bufferedMap_metric_abs_le_S40 B i t ht p hp v)).1
  linarith

theorem bufferedMap_metric_upper_S40 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (i : Fin B.count) (t : ℝ) (ht : B.start ≤ t) (p : (B.model i).Carrier)
    (hp : p ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint
      (2 * (B.accuracy t)⁻¹))
    (v : TangentSpace (𝓡 3) p) :
    (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht)) (postMetric F.observation t)).inner
        (B.map i t ht p) (mfderiv (𝓡 3) (𝓡 3) (B.map i t ht) p v)
        (mfderiv (𝓡 3) (𝓡 3) (B.map i t ht) p v) ≤
      (1 + B.accuracy t) * (B.model i).metric.inner p v v := by
  have h := (abs_le.mp (bufferedMap_metric_abs_le_S40 B i t ht p hp v)).2
  linarith

/-- The closed `h`-ball of radius `R ≤ n` around `y ∈ B(x_i, n)` lies in `B(x_i, 2n)`. -/
theorem closedBall_subset_buffer_S40 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (i : Fin B.count) (t : ℝ) (ht : B.start ≤ t) (y : (B.model i).Carrier)
    (hy : y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹)
    {R : ℝ} (hRn : R ≤ (B.accuracy t)⁻¹) :
    riemannianClosedBallOf (B.model i).metric y R ⊆
      riemannianBallOf (B.model i).metric (B.model i).basepoint (2 * (B.accuracy t)⁻¹) := by
  intro x hx
  have hnpos : 0 < (B.accuracy t)⁻¹ := inv_pos.mpr (B.accuracy_pos t ht)
  have h1 : riemannianEDistOf (B.model i).metric (B.model i).basepoint y <
      ENNReal.ofReal (B.accuracy t)⁻¹ := hy
  have h2 : riemannianEDistOf (B.model i).metric y x ≤ ENNReal.ofReal R := hx
  have h3 := (riemannianEDistOf_triangle (B.model i).metric (B.model i).basepoint y x).trans_lt
    (ENNReal.add_lt_add_of_lt_of_le (h2.trans_lt ENNReal.ofReal_lt_top).ne h1 (h2.trans (ENNReal.ofReal_le_ofReal hRn)))
  rw [← ENNReal.ofReal_add hnpos.le hnpos.le] at h3
  have : (B.accuracy t)⁻¹ + (B.accuracy t)⁻¹ = 2 * (B.accuracy t)⁻¹ := by ring
  rwa [this] at h3

/-- **(S2 + S3)** First exit without a `hlower` hypothesis. -/
theorem bufferedMap_ball_subset_image_S40 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K)
    (i : Fin B.count) (t : ℝ) (ht : B.start ≤ t) (y : (B.model i).Carrier)
    (hy : y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹)
    {R : ℝ} (hR : 0 < R) (hRn : R ≤ (B.accuracy t)⁻¹) (hδ : B.accuracy t < 1) :
    riemannianBallOf
        (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht)) (postMetric F.observation t))
        (B.map i t ht y) (R * Real.sqrt (1 - B.accuracy t)) ⊆
      B.map i t ht '' riemannianClosedBallOf (B.model i).metric y R := by
  have hsub := closedBall_subset_buffer_S40 B i t ht y hy hRn
  have hpos : 0 < 1 - B.accuracy t := sub_pos.mpr hδ
  have hsq : 0 < Real.sqrt (1 - B.accuracy t) := Real.sqrt_pos.mpr hpos
  have hnpos : 0 < (B.accuracy t)⁻¹ := inv_pos.mpr (B.accuracy_pos t ht)
  have hy2 : y ∈ riemannianBallOf (B.model i).metric (B.model i).basepoint
      (2 * (B.accuracy t)⁻¹) := by
    refine riemannianBallOf_mono _ _ ?_ hy
    linarith
  have hcap := ambient_ball_subset_image_S35 B i t ht
    (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht)) (postMetric F.observation t)) y
    (B.buffer_domain i t ht hy2) hR (inv_pos.mpr hsq : 0 < (Real.sqrt (1 - B.accuracy t))⁻¹)
    (fun x hx => B.buffer_domain i t ht (hsub hx))
    (fun x hx v => by
      have hlow := bufferedMap_metric_lower_S40 B i t ht x (hsub hx) v
      have hnn := metric_inner_self_nonneg (B.model i).metric x v
      have hL : ((Real.sqrt (1 - B.accuracy t))⁻¹) ^ 2 = (1 - B.accuracy t)⁻¹ := by
        rw [inv_pow, Real.sq_sqrt hpos.le]
      rw [hL]
      rw [inv_mul_eq_div, le_div_iff₀ hpos]
      linarith)
  have hRL : R / (Real.sqrt (1 - B.accuracy t))⁻¹ = R * Real.sqrt (1 - B.accuracy t) := by
    rw [div_inv_eq_mul]
  rwa [hRL] at hcap

end GC.LongTime.Ch12
