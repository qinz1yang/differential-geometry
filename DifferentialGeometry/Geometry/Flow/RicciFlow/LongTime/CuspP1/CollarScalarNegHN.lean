import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspCurvatureCV.ConnectionErrorBall
import DifferentialGeometry.Geometry.Curvature.FiniteNumeratorTransfer
import DifferentialGeometry.Geometry.Curvature.ScalarPerturbation
import DifferentialGeometry.Geometry.Curvature.Metric.ConstantRicci
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Thurston.ConstantCurvatureAtlas

/-!
# ⑧ 的 `hneg`：cusp collar 上 `R_post < 0`（O-W-HNEG G1，后缀 `_HN`）

`cores.map i s '' riemannianBallOf h basepoint (accuracy s)⁻¹`（cusp collar）上
`metricScalarAt (postMetric F.observation s) p < 0`，前提 `cores.accuracy s ≤ 1/2000`。

路线（全部在开子流形 `↥ball = cores.ballOpen_BD i s` 上，难点 A 由 BOUNDARY/CURV 的 `_BD`/`_CV` 解决）：
* 双曲模型的截面曲率是 `−1/4`（`FiniteVolumeHyperbolicModel.curvature`），所以 `Ric♯ = −½ id`、
  `R_h = −3/2`（`ricci_of_op` + `riemannOp_eq_smul_of_hasConstantSectionalCurvature`，经
  `ricciSharp_restrictOpen` 搬到 `h_B = refMetric_BD`）；
* `metric_error`（k ≤ 2，`accuracy < 1` ⇒ `2 ≤ ⌈acc⁻¹⌉₊`）经 `ballError_eq_CV` + restrict 引理 +
  `finiteMetricDifference_norm_eq` ⇒ `metricDerivNorm k ĝ_s h_B h_B x ≤ acc`（难点 B）；
* `abs_scalar_curvature_sub_le_of_small_metric_derivatives`（d = 3，K = 1/2）：
  `|R(ĝ_s) + 3/2| ≤ 3·(720.5·acc)/(1 − acc) < 3/2`（`acc ≤ 1/2000`）⇒ `R(ĝ_s) < 0`；
* `ĝ_s = scaleMetric s⁻¹ (localPullMetric g(s) f_s|ball)` ⇒ `R(ĝ_s)(x) = s · R_{g(s)}(f_s x)`
  （`metricScalarAt_scaleMetric` + `metricScalarAt_localPull`），`s > 0` 保号。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff
namespace GC.LongTime
universe u

section ConstantCurvature

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]

/-- 3 维、截面曲率 `κ` 常数 ⇒ `Ric♯ v = 2κ · v`。 -/
theorem ricciSharp_eq_of_constSec_HN {g : SmoothRiemannianMetric (𝓡 3) M} {κ : ℝ}
    (hg : GC.Geometry.HasConstantSectionalCurvature g κ) (x : M) (v : TangentSpace (𝓡 3) x) :
    ricciSharp g x v = (2 * κ) • v := by
  apply SmoothRiemannianMetric.eq_of_inner_eq g
  intro w
  rw [inner_ricciSharp, ricci_of_op g x κ
    (GC.Geometry.riemannOp_eq_smul_of_hasConstantSectionalCurvature hg x) v w,
    map_smul, smul_apply, smul_eq_mul, finrank_euclideanSpace_fin]
  norm_num

/-- 限制到开子流形 `U` 后仍有 `Ric♯ v = 2κ · v`。 -/
theorem ricciSharp_restrictOpen_eq_of_constSec_HN {g : SmoothRiemannianMetric (𝓡 3) M} {κ : ℝ}
    (hg : GC.Geometry.HasConstantSectionalCurvature g κ) (U : TopologicalSpace.Opens M) (x : U)
    (v : TangentSpace (𝓡 3) x) :
    ricciSharp (g.restrictOpen U) x v = (2 * κ) • v := by
  have h := ricciSharp_restrictOpen g U x v
  rw [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply] at h
  exact h.trans (ricciSharp_eq_of_constSec_HN hg (x : M) v)

/-- 限制度量的标量曲率 `= 6κ`（`Ric♯` 的迹）。 -/
theorem metricScalarAt_restrictOpen_of_constSec_HN {g : SmoothRiemannianMetric (𝓡 3) M} {κ : ℝ}
    (hg : GC.Geometry.HasConstantSectionalCurvature g κ) (U : TopologicalSpace.Opens M)
    (x : U) : metricScalarAt (g.restrictOpen U) x = 6 * κ := by
  have hlin : (ricciSharp (g.restrictOpen U) x).toLinearMap =
      (2 * κ) • (LinearMap.id : TangentSpace (𝓡 3) x →ₗ[ℝ] TangentSpace (𝓡 3) x) := by
    ext v
    exact ricciSharp_restrictOpen_eq_of_constSec_HN hg U x v
  rw [metricScalar_eq_trace_ricciSharp, hlin, map_smul, LinearMap.trace_id]
  change 2 * κ * (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) = 6 * κ
  rw [finrank_euclideanSpace_fin]
  ring

/-- 限制度量的 Ricci 算子范数：`|Ric♯ v| = |2κ| |v| `。 -/
theorem sqrt_ricciSharp_restrictOpen_le_of_constSec_HN {g : SmoothRiemannianMetric (𝓡 3) M}
    {κ : ℝ} (hg : GC.Geometry.HasConstantSectionalCurvature g κ) (U : TopologicalSpace.Opens M)
    (x : U) (v : TangentSpace (𝓡 3) x) :
    Real.sqrt ((g.restrictOpen U).inner x (ricciSharp (g.restrictOpen U) x v)
        (ricciSharp (g.restrictOpen U) x v)) ≤
      |2 * κ| * Real.sqrt ((g.restrictOpen U).inner x v v) := by
  have hq : (g.restrictOpen U).inner x ((2 * κ) • v) ((2 * κ) • v) =
      (2 * κ) * (2 * κ) * (g.restrictOpen U).inner x v v := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  rw [ricciSharp_restrictOpen_eq_of_constSec_HN hg U x v, hq,
    Real.sqrt_mul' _ (metric_inner_self_nonneg _ _ _), Real.sqrt_mul_self_eq_abs]

end ConstantCurvature

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}

/-- 难点 B：`metric_error`（k ≤ 2，`acc < 1`）⇒ `↥ball` 上 `metricDerivNorm k ĝ_t h_B h_B x ≤ acc`。 -/
theorem PersistentHyperbolicCores.metricDerivNorm_ball_le_HN
    (cores : PersistentHyperbolicCores F K) (i : Fin cores.count) (t : ℝ) (ht : cores.start ≤ t)
    (hacc : cores.accuracy t < 1) (x : ↥(cores.ballOpen_BD i t)) (k : ℕ) (hk : k ≤ 2) :
    metricDerivNorm k (cores.pulledMetric_BD i t ht hacc) (cores.refMetric_BD i t)
      (cores.refMetric_BD i t) x ≤ cores.accuracy t := by
  have hpos : 0 < cores.accuracy t := cores.accuracy_pos t ht
  have h2 : 2 ≤ ⌈(cores.accuracy t)⁻¹⌉₊ := by
    have h1 : ((1 : ℕ) : ℝ) < (cores.accuracy t)⁻¹ := by
      rw [Nat.cast_one]
      exact one_lt_inv₀ hpos |>.mpr hacc
    exact Nat.lt_ceil.mpr h1
  have hme := cores.metric_error i t ht k (le_max_of_le_right (hk.trans h2)) x.1 x.2
  have hrestr := tensor0SFiberNorm_iteratedMetricCovariantDerivative_restrictOpen
    (cores.model i).metric (cores.ballOpen_BD i t) (s := 2)
    (fun p : (cores.model i).Carrier =>
      ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
        ((t⁻¹ : ℝ) • localPullInner (I := 𝓡 3) (J := 𝓡 3) (postMetric F.observation t)
          (cores.map i t ht) p - (cores.model i).metric.inner p)).uncurryLeft) k x
  rw [← hrestr] at hme
  have hdiff : finiteMetricDifference (cores.pulledMetric_BD i t ht hacc)
      (cores.refMetric_BD i t) = fun z : ↥(cores.ballOpen_BD i t) =>
        Tensor0SSpace.ofModel (I := 𝓡 3) (x := z)
          (Tensor0SSpace.toModel
            (((continuousMultilinearCurryFin1 ℝ
              (TangentSpace (𝓡 3) (z : (cores.model i).Carrier)) ℝ).symm.toContinuousLinearMap.comp
                ((t⁻¹ : ℝ) • localPullInner (postMetric F.observation t)
                  (cores.map i t ht) (z : (cores.model i).Carrier) -
                (cores.model i).metric.inner (z : (cores.model i).Carrier))).uncurryLeft)) :=
    cores.ballError_eq_CV i t ht hacc
  rw [← finiteMetricDifference_norm_eq, hdiff]
  exact hme.le

/-- scale/pullback 不变性：`R(ĝ_t)(x) = t · R_{g(t)}(f_t x)`。 -/
theorem PersistentHyperbolicCores.metricScalarAt_pulled_HN
    (cores : PersistentHyperbolicCores F K) (i : Fin cores.count) (t : ℝ) (ht : cores.start ≤ t)
    (hacc : cores.accuracy t < 1) (x : ↥(cores.ballOpen_BD i t)) :
    metricScalarAt (cores.pulledMetric_BD i t ht hacc) x =
      t * metricScalarAt (postMetric F.observation t) (cores.map i t ht x.1) := by
  unfold PersistentHyperbolicCores.pulledMetric_BD
  rw [metricScalarAt_scaleMetric, metricScalarAt_localPull, inv_inv]
  rfl

/-- 数值：`a ≤ 1/2000` ⇒ `3·((240·3·a + a·½)/(1 − a)) < 3/2`。 -/
theorem scalar_perturbation_constant_lt_HN {a : ℝ} (ha : a ≤ 1 / 2000) :
    3 * ((240 * 3 * a + a * (1 / 2)) / (1 - a)) < 3 / 2 := by
  have hden : 0 < 1 - a := by linarith
  have h : (240 * 3 * a + a * (1 / 2)) / (1 - a) < 1 / 2 := by
    rw [div_lt_iff₀ hden]
    linarith
  linarith

/-- `↥ball` 上：`acc t ≤ 1/2000` ⇒ `R(ĝ_t) < 0`（与 `R(h_B) = −3/2` 的距离 `< 3/2`）。 -/
theorem PersistentHyperbolicCores.scalar_pulled_neg_HN
    (cores : PersistentHyperbolicCores F K) (i : Fin cores.count) (t : ℝ) (ht : cores.start ≤ t)
    (hacc : cores.accuracy t < 1) (h2000 : cores.accuracy t ≤ 1 / 2000)
    (x : ↥(cores.ballOpen_BD i t)) :
    metricScalarAt (cores.pulledMetric_BD i t ht hacc) x < 0 := by
  have hpos : 0 < cores.accuracy t := cores.accuracy_pos t ht
  have hsec : GC.Geometry.HasConstantSectionalCurvature (cores.model i).metric (-(1 / 4 : ℝ)) :=
    (cores.model i).curvature
  have hbound := abs_scalar_curvature_sub_le_of_small_metric_derivatives
    (cores.pulledMetric_BD i t ht hacc) (cores.refMetric_BD i t) x (cores.accuracy t)
    (by linarith) (cores.metricDerivNorm_ball_le_HN i t ht hacc x) (1 / 2)
    (fun v => by
      have h := sqrt_ricciSharp_restrictOpen_le_of_constSec_HN hsec (cores.ballOpen_BD i t) x v
      norm_num at h ⊢
      exact h)
  have href : metricScalarAt (cores.refMetric_BD i t) x = -(3 / 2) := by
    rw [metricScalarAt_restrictOpen_of_constSec_HN hsec]
    norm_num
  rw [href, finrank_euclideanSpace_fin] at hbound
  have hc := scalar_perturbation_constant_lt_HN h2000
  push_cast at hbound
  linarith [(abs_le.mp hbound).2]

/-- **G1 `scalar_neg_on_collar_of_accuracy_HN`**：`acc s ≤ 1/2000` ⇒ cusp collar
`f_s '' ball` 上 `R_{g(s)} < 0`（形状 = IMS06 G7/G10/G14 的 `hneg`，`i`、`hs` 任意）。 -/
theorem PersistentHyperbolicCores.scalar_neg_on_collar_of_accuracy_HN
    (cores : PersistentHyperbolicCores F K) (i : Fin cores.count) {s : ℝ}
    (hs : cores.start ≤ s) (hacc : cores.accuracy s ≤ 1 / 2000) :
    ∀ p ∈ cores.map i s hs '' riemannianBallOf (cores.model i).metric (cores.model i).basepoint
      (cores.accuracy s)⁻¹, metricScalarAt (postMetric F.observation s) p < 0 := by
  rintro p ⟨x, hx, rfl⟩
  have hacc1 : cores.accuracy s < 1 := by linarith
  have h := cores.scalar_pulled_neg_HN i s hs hacc1 hacc ⟨x, hx⟩
  rw [cores.metricScalarAt_pulled_HN i s hs hacc1] at h
  exact neg_of_mul_neg_right h (cores.start_pos.trans_le hs).le

end GC.LongTime
