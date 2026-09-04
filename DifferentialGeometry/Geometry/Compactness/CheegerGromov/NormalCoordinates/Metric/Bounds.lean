import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.Basic
import DifferentialGeometry.Geometry.Metric.TensorInner.MetricKoszul

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff Topology Bundle

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]

section RawNormalCoordinates

variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

private local instance : NormedAddCommGroup (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance : NormedSpace Real (E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

private local instance : NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance : NormedSpace Real (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

private local instance : NormedAddCommGroup (E →L[Real] E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance : NormedSpace Real (E →L[Real] E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

def NormalCoordMetricEquivOn
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) (U : Set E) :
    Prop :=
  forall z : E, z ∈ U -> forall v : E,
    (1 / 2 : Real) * ‖v‖ ^ 2 <= normalCoordMetric (I := I) Y x z v v ∧
      normalCoordMetric (I := I) Y x z v v <= 2 * ‖v‖ ^ 2

namespace NormalCoordMetricEquivOn

omit [NeZero (Module.finrank ℝ E)] in
theorem coercive
    {Y : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x : Y.M}
    {U : Set E} (h : NormalCoordMetricEquivOn (I := I) Y x U)
    {z : E} (hz : z ∈ U) :
    IsCoercive (normalCoordMetric (I := I) Y x z) := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro v
  simpa [pow_two, mul_assoc] using (h z hz v).1

omit [NeZero (Module.finrank ℝ E)] in
theorem sharp_norm_le
    {Y : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x : Y.M}
    {U : Set E} (h : NormalCoordMetricEquivOn (I := I) Y x U)
    {z : E} (hz : z ∈ U) (eta : E →L[Real] Real) :
    ‖(h.coercive hz).sharp eta‖ <= 2 * ‖eta‖ := by
  have hbound := IsCoercive.sharp_norm_le (h.coercive hz)
    (c := (1 / 2 : Real)) (by norm_num)
    (fun v => by simpa [pow_two, mul_assoc] using (h z hz v).1) eta
  norm_num at hbound ⊢
  exact hbound

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem abs_apply_le
    {Y : PointedRiemannianManifold.{u, uE, uH} (I := I)} {x : Y.M}
    {U : Set E} (h : NormalCoordMetricEquivOn (I := I) Y x U)
    {z : E} (hz : z ∈ U) (v w : E) :
    |normalCoordMetric (I := I) Y x z v w| ≤ 2 * ‖v‖ * ‖w‖ := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : RiemannianBundle (fun y : Y.M ↦ TangentSpace I y) :=
    ⟨Y.metric.toRiemannianMetric⟩
  let dExp := mfderiv 𝓘(Real, E) I
    (fun u ↦ expMapDiffeo (I := I) Y.metric x u) z
  have hcs :
      |normalCoordMetric (I := I) Y x z v w| ≤
        ‖dExp v‖ * ‖dExp w‖ := by
    rw [normal_coord_metric_apply (I := I)]
    exact abs_real_inner_le_norm (dExp v) (dExp w)
  have hvSq : ‖dExp v‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    convert (h z hz v).2 using 1
    rw [normal_coord_metric_apply (I := I)]
    rfl
  have hwSq : ‖dExp w‖ ^ 2 ≤ 2 * ‖w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    convert (h z hz w).2 using 1
    rw [normal_coord_metric_apply (I := I)]
    rfl
  have hprodSq :
      (‖dExp v‖ * ‖dExp w‖) ^ 2 ≤ (2 * ‖v‖ * ‖w‖) ^ 2 := by
    have hmul := mul_le_mul hvSq hwSq (sq_nonneg ‖dExp w‖)
      (mul_nonneg (by norm_num) (sq_nonneg ‖v‖))
    nlinarith [sq_nonneg ‖v‖, sq_nonneg ‖w‖]
  exact hcs.trans <| le_of_sq_le_sq hprodSq
    (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg v)) (norm_nonneg w))

end NormalCoordMetricEquivOn

def NormalCoordMetricDerivBound
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M)
    (U : Set E) (p : Nat) (C : Real) : Prop :=
  forall z : E, z ∈ U ->
    ‖iteratedFDeriv Real p (normalCoordMetric (I := I) Y x) z‖ <= C

structure NormalCoordMetricBounds
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  metricC : Nat -> Real
  metricC_nonneg : forall p : Nat, 0 <= metricC p
  radius : forall k : Nat, (X.obj k).M -> Real
  radius_pos : forall (k : Nat) (x : (X.obj k).M), 0 < radius k x

  metric_equiv :
    forall (k : Nat) (x : (X.obj k).M),
      NormalCoordMetricEquivOn (I := I) (X.obj k) x
        (Metric.ball (0 : E) (radius k x))

  metric_deriv :
    forall (k p : Nat) (x : (X.obj k).M),
      NormalCoordMetricDerivBound (I := I) (X.obj k) x
        (Metric.ball (0 : E) (radius k x)) p (metricC p)

namespace NormalCoordMetricBounds

theorem half_le_metricCoerciveConst
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X)
    (k : Nat) (x : (X.obj k).M) :
    letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
    letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
    letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    letI : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    (1 / 2 : Real) ≤ metricCoerciveConst (I := I) (X.obj k).metric x := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (TangentBundle I (X.obj k).M) :=
    (X.obj k).t2TangentBundle
  have h0 : (0 : E) ∈ Metric.ball 0 (h.radius k x) := by
    rw [Metric.mem_ball, dist_self]
    exact h.radius_pos k x
  apply le_metricCoerciveConst (I := I)
  intro v
  rw [← normal_coord_metric_zero (I := I) (X.obj k) x]
  exact (h.metric_equiv k x 0 h0 v).1

omit [NeZero (Module.finrank ℝ E)] in
theorem fderiv_apply_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X)
    (k : Nat) (x : (X.obj k).M) {z : E}
    (hz : z ∈ Metric.ball (0 : E) (h.radius k x)) (u v w : E) :
    ‖fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z u v w‖ ≤
      h.metricC 1 * ‖u‖ * ‖v‖ * ‖w‖ := by
  let D := fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z
  let T := iteratedFDeriv Real 1 (normalCoordMetric (I := I) (X.obj k) x) z
  have hT : ‖T‖ ≤ h.metricC 1 := h.metric_deriv k 1 x z hz
  have hDu : ‖D u‖ ≤ h.metricC 1 * ‖u‖ := by
    calc
      ‖D u‖ = ‖T (fun _ : Fin 1 ↦ u)‖ := by
        simp only [D, T, iteratedFDeriv_one_apply]
      _ ≤ ‖T‖ * ∏ _ : Fin 1, ‖u‖ := ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖T‖ * ‖u‖ := by simp
      _ ≤ h.metricC 1 * ‖u‖ :=
        mul_le_mul_of_nonneg_right hT (norm_nonneg u)
  calc
    ‖D u v w‖ ≤ ‖D u‖ * ‖v‖ * ‖w‖ :=
      ContinuousLinearMap.le_opNorm₂ (D u) v w
    _ ≤ (h.metricC 1 * ‖u‖) * ‖v‖ * ‖w‖ := by
      gcongr
    _ = h.metricC 1 * ‖u‖ * ‖v‖ * ‖w‖ := rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem koszul_vec_norm_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X)
    (k : Nat) (x : (X.obj k).M) {z : E}
    (hz : z ∈ Metric.ball (0 : E) (h.radius k x)) (v w : E) :
    ‖MetricKoszul.koszulVec ((h.metric_equiv k x).coercive hz)
        (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z) v w‖ ≤
      3 * h.metricC 1 * ‖v‖ * ‖w‖ := by
  have hraw := MetricKoszul.koszul_vec_norm_le
    ((h.metric_equiv k x).coercive hz)
    (c := (1 / 2 : Real)) (by norm_num)
    (fun u ↦ by simpa [pow_two, mul_assoc] using (h.metric_equiv k x z hz u).1)
    (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z)
    (C := h.metricC 1) (h.metricC_nonneg 1)
    (h.fderiv_apply_le k x hz) v w
  norm_num at hraw ⊢
  ring_nf at hraw ⊢
  exact hraw

omit [NeZero (Module.finrank ℝ E)] in
theorem koszul_vec_pair_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X)
    (k : Nat) (x : (X.obj k).M) {z y : E}
    (hz : z ∈ Metric.ball (0 : E) (h.radius k x))
    (hy : y ∈ Metric.ball (0 : E) (h.radius k x))
    (hmetric :
      ‖normalCoordMetric (I := I) (X.obj k) x y -
          normalCoordMetric (I := I) (X.obj k) x z‖ ≤
        h.metricC 1 * ‖z - y‖)
    (hjet : ∀ u v w : E,
      ‖(fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z -
          fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y) u v w‖ ≤
        (h.metricC 2 * ‖z - y‖) * ‖u‖ * ‖v‖ * ‖w‖)
    (v w : E) :
    ‖MetricKoszul.koszulVec ((h.metric_equiv k x).coercive hz)
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z) v w -
        MetricKoszul.koszulVec ((h.metric_equiv k x).coercive hy)
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y) v w‖ ≤
      (6 * (h.metricC 1) ^ 2 + 3 * h.metricC 2) *
        ‖z - y‖ * ‖v‖ * ‖w‖ := by
  have hraw := MetricKoszul.koszul_vec_sub_le
    ((h.metric_equiv k x).coercive hz)
    ((h.metric_equiv k x).coercive hy)
    (cB := (1 / 2 : Real)) (cC := (1 / 2 : Real))
    (by norm_num) (by norm_num)
    (fun u ↦ by simpa [pow_two, mul_assoc] using (h.metric_equiv k x z hz u).1)
    (fun u ↦ by simpa [pow_two, mul_assoc] using (h.metric_equiv k x y hy u).1)
    (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z)
    (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y)
    (Csub := h.metricC 2 * ‖z - y‖) (CF := h.metricC 1)
    (mul_nonneg (h.metricC_nonneg 2) (norm_nonneg _))
    (h.metricC_nonneg 1) hjet (h.fderiv_apply_le k x hy) v w
  norm_num at hraw
  have hC1 : 0 ≤ h.metricC 1 := h.metricC_nonneg 1
  calc
    ‖MetricKoszul.koszulVec ((h.metric_equiv k x).coercive hz)
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z) v w -
        MetricKoszul.koszulVec ((h.metric_equiv k x).coercive hy)
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y) v w‖
        ≤ 2 * ((3 / 2 : Real) * (h.metricC 2 * ‖z - y‖) * ‖v‖ * ‖w‖) +
          2 * (‖normalCoordMetric (I := I) (X.obj k) x y -
              normalCoordMetric (I := I) (X.obj k) x z‖ *
            (2 * ((3 / 2 : Real) * h.metricC 1 * ‖v‖ * ‖w‖))) := hraw
    _ ≤ 2 * ((3 / 2 : Real) * (h.metricC 2 * ‖z - y‖) * ‖v‖ * ‖w‖) +
          2 * ((h.metricC 1 * ‖z - y‖) *
            (2 * ((3 / 2 : Real) * h.metricC 1 * ‖v‖ * ‖w‖))) := by
      gcongr
    _ = (6 * (h.metricC 1) ^ 2 + 3 * h.metricC 2) *
          ‖z - y‖ * ‖v‖ * ‖w‖ := by
      ring

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
private theorem fderiv_eval3
    {G : E → E →L[Real] E →L[Real] Real} {q : E}
    (hG : DifferentiableAt Real (fderiv Real G) q)
    (d u v w : E) :
    fderiv Real (fun p ↦ fderiv Real G p u v w) q d =
      fderiv Real (fderiv Real G) q d u v w := by
  have hu : HasFDerivAt (fun _ : E ↦ u) 0 q :=
    hasFDerivAt_const (𝕜 := Real) (x := q) u
  have hv : HasFDerivAt (fun _ : E ↦ v) 0 q :=
    hasFDerivAt_const (𝕜 := Real) (x := q) v
  have hw : HasFDerivAt (fun _ : E ↦ w) 0 q :=
    hasFDerivAt_const (𝕜 := Real) (x := q) w
  have hfirst := hG.hasFDerivAt.clm_apply hu
  have hsecond := hfirst.clm_apply hv
  have hthird := hsecond.clm_apply hw
  have happ := DFunLike.congr_fun hthird.fderiv d
  simpa using happ

omit [NeZero (Module.finrank Real E)] in
theorem koszul_vec_lip_on
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X)
    (k : Nat) (x : (X.obj k).M) {r : Real}
    (hrMetric : Metric.ball (0 : E) r ⊆
      Metric.ball (0 : E) (h.radius k x))
    (hrExp :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Metric.ball (0 : E) r ⊆
        Metric.ball (0 : E)
          (expMapC2Radius (I := I) (X.obj k).metric x))
    {z y : E}
    (hz : z ∈ Metric.ball (0 : E) r)
    (hy : y ∈ Metric.ball (0 : E) r)
    (v w : E) :
    ‖MetricKoszul.koszulVec ((h.metric_equiv k x).coercive (hrMetric hz))
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z) v w -
        MetricKoszul.koszulVec ((h.metric_equiv k x).coercive (hrMetric hy))
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y) v w‖ ≤
      (6 * (h.metricC 1) ^ 2 + 3 * h.metricC 2) *
        ‖z - y‖ * ‖v‖ * ‖w‖ := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  let G := normalCoordMetric (I := I) (X.obj k) x
  let U := Metric.ball (0 : E) r
  have hsm : ContDiffOn Real (⊤ : ℕ∞) G U :=
    (normal_coord_metric_cont_diff_on_exp_ball (I := I) (X.obj k) x).mono hrExp
  have hdiff : ∀ q ∈ U, DifferentiableAt Real G q := by
    intro q hq
    exact (hsm q hq).contDiffAt (Metric.isOpen_ball.mem_nhds hq) |>.differentiableAt (by simp)
  have hmetric : ‖G y - G z‖ ≤ h.metricC 1 * ‖z - y‖ := by
    have hmean := (convex_ball (0 : E) r).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := Real) (C := h.metricC 1) hdiff (fun q hq ↦ by
        rw [← norm_iteratedFDeriv_one (f := G)]
        exact h.metric_deriv k 1 x q (hrMetric hq)) hz hy
    calc
      ‖G y - G z‖ ≤ h.metricC 1 * ‖y - z‖ := hmean
      _ = h.metricC 1 * ‖z - y‖ := by rw [norm_sub_rev]
  have hdiffD : ∀ q ∈ U, DifferentiableAt Real (fderiv Real G) q := by
    intro q hq
    have hqsm := (hsm q hq).contDiffAt (Metric.isOpen_ball.mem_nhds hq)
    have hfdsm : ContDiffAt Real 1 (fderiv Real G) q :=
      hqsm.fderiv_right (m := 1) (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
    exact hfdsm.differentiableAt_one
  have hjet : ∀ u a b : E,
      ‖(fderiv Real G z - fderiv Real G y) u a b‖ ≤
        (h.metricC 2 * ‖z - y‖) * ‖u‖ * ‖a‖ * ‖b‖ := by
    intro u a b
    let F : E → Real := fun q ↦ fderiv Real G q u a b
    let C : Real := h.metricC 2 * ‖u‖ * ‖a‖ * ‖b‖
    have hC : 0 ≤ C := by
      dsimp only [C]
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (h.metricC_nonneg 2) (norm_nonneg u)) (norm_nonneg a))
        (norm_nonneg b)
    have hFdiff : ∀ q ∈ U, DifferentiableAt Real F q := by
      intro q hq
      have hu : HasFDerivAt (fun _ : E ↦ u) 0 q :=
        hasFDerivAt_const (𝕜 := Real) (x := q) u
      have ha : HasFDerivAt (fun _ : E ↦ a) 0 q :=
        hasFDerivAt_const (𝕜 := Real) (x := q) a
      have hb : HasFDerivAt (fun _ : E ↦ b) 0 q :=
        hasFDerivAt_const (𝕜 := Real) (x := q) b
      exact ((((hdiffD q hq).hasFDerivAt.clm_apply hu).clm_apply ha).clm_apply hb).differentiableAt
    have hFbound : ∀ q ∈ U, ‖fderiv Real F q‖ ≤ C := by
      intro q hq
      refine ContinuousLinearMap.opNorm_le_bound _ hC fun d ↦ ?_
      rw [fderiv_eval3 (hdiffD q hq) d u a b]
      have hdu :
          iteratedFDeriv Real 2 G q (![d, u] : Fin 2 → E) =
            fderiv Real (fderiv Real G) q d u := by
        rw [iteratedFDeriv_two_apply]
        simp [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← hdu]
      calc
        ‖iteratedFDeriv Real 2 G q (![d, u] : Fin 2 → E) a b‖ ≤
            ‖iteratedFDeriv Real 2 G q (![d, u] : Fin 2 → E)‖ * ‖a‖ * ‖b‖ :=
          ContinuousLinearMap.le_opNorm₂ _ a b
        _ ≤ (‖iteratedFDeriv Real 2 G q‖ *
              ∏ i : Fin 2, ‖(![d, u] : Fin 2 → E) i‖) * ‖a‖ * ‖b‖ := by
          gcongr
          exact (iteratedFDeriv Real 2 G q).le_opNorm _
        _ = (‖iteratedFDeriv Real 2 G q‖ * (‖d‖ * ‖u‖)) * ‖a‖ * ‖b‖ := by
          rw [Fin.prod_univ_two]
          simp [Matrix.cons_val_zero, Matrix.cons_val_one]
        _ ≤ (h.metricC 2 * (‖d‖ * ‖u‖)) * ‖a‖ * ‖b‖ := by
          gcongr
          exact h.metric_deriv k 2 x q (hrMetric hq)
        _ = C * ‖d‖ := by
          dsimp only [C]
          ring
    have hmean := (convex_ball (0 : E) r).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := Real) (C := C) hFdiff hFbound hz hy
    calc
      ‖(fderiv Real G z - fderiv Real G y) u a b‖ = ‖F z - F y‖ := by
        simp only [F, sub_apply]
      _ = ‖F y - F z‖ := norm_sub_rev _ _
      _ ≤ C * ‖y - z‖ := hmean
      _ = (h.metricC 2 * ‖z - y‖) * ‖u‖ * ‖a‖ * ‖b‖ := by
        dsimp only [C]
        rw [norm_sub_rev y z]
        ring
  exact h.koszul_vec_pair_le k x (hrMetric hz) (hrMetric hy)
    (by simpa only [G] using hmetric)
    (by simpa only [G] using hjet) v w

omit [NeZero (Module.finrank Real E)] in
theorem koszul_vec_lip_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X)
    (k : Nat) (x : (X.obj k).M)
    (hsub :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Metric.ball (0 : E) (h.radius k x) ⊆
        Metric.ball (0 : E)
          (expMapC2Radius (I := I) (X.obj k).metric x))
    {z y : E}
    (hz : z ∈ Metric.ball (0 : E) (h.radius k x))
    (hy : y ∈ Metric.ball (0 : E) (h.radius k x))
    (v w : E) :
    ‖MetricKoszul.koszulVec ((h.metric_equiv k x).coercive hz)
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z) v w -
        MetricKoszul.koszulVec ((h.metric_equiv k x).coercive hy)
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y) v w‖ ≤
      (6 * (h.metricC 1) ^ 2 + 3 * h.metricC 2) *
        ‖z - y‖ * ‖v‖ * ‖w‖ := by
  simpa using h.koszul_vec_lip_on k x (fun _ hz' ↦ hz') hsub hz hy v w

omit [NeZero (Module.finrank Real E)] in
theorem koszul_accel_lip_on
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X)
    (k : Nat) (x : (X.obj k).M) {r : Real}
    (hrMetric : Metric.ball (0 : E) r ⊆
      Metric.ball (0 : E) (h.radius k x))
    (hrExp :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Metric.ball (0 : E) r ⊆
        Metric.ball (0 : E)
          (expMapC2Radius (I := I) (X.obj k).metric x))
    {z y : E × E} {R : Real} (hR : 0 ≤ R)
    (hz : z.1 ∈ Metric.ball (0 : E) r)
    (hy : y.1 ∈ Metric.ball (0 : E) r)
    (hzv : ‖z.2‖ ≤ R) (hyv : ‖y.2‖ ≤ R) :
    ‖MetricKoszul.koszulVec ((h.metric_equiv k x).coercive (hrMetric hz))
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z.1) z.2 z.2 -
        MetricKoszul.koszulVec ((h.metric_equiv k x).coercive (hrMetric hy))
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y.1) y.2 y.2‖ ≤
      ((6 * (h.metricC 1) ^ 2 + 3 * h.metricC 2) * R ^ 2 +
          6 * h.metricC 1 * R) * ‖z - y‖ := by
  let : TopologicalSpace (X.obj k).M := (X.obj k).topology
  let : ChartedSpace H (X.obj k).M := (X.obj k).charted
  let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
  let : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
  let Kz := MetricKoszul.koszulVec ((h.metric_equiv k x).coercive (hrMetric hz))
    (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z.1)
  let Ky := MetricKoszul.koszulVec ((h.metric_equiv k x).coercive (hrMetric hy))
    (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y.1)
  let A : Real := 6 * (h.metricC 1) ^ 2 + 3 * h.metricC 2
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact add_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg (h.metricC 1)))
      (mul_nonneg (by norm_num) (h.metricC_nonneg 2))
  have hC1 : 0 ≤ h.metricC 1 := h.metricC_nonneg 1
  have hposNorm : ‖z.1 - y.1‖ ≤ ‖z - y‖ := by
    simpa only [Prod.fst_sub] using norm_fst_le (z - y)
  have hvelNorm : ‖z.2 - y.2‖ ≤ ‖z - y‖ := by
    simpa only [Prod.snd_sub] using norm_snd_le (z - y)
  have hpos : ‖Kz z.2 z.2 - Ky z.2 z.2‖ ≤
      A * R ^ 2 * ‖z - y‖ := by
    have hraw := h.koszul_vec_lip_on k x hrMetric hrExp hz hy z.2 z.2
    calc
      ‖Kz z.2 z.2 - Ky z.2 z.2‖ ≤
          A * ‖z.1 - y.1‖ * ‖z.2‖ * ‖z.2‖ := by
        simpa only [Kz, Ky, A] using hraw
      _ ≤ A * ‖z - y‖ * R * R := by gcongr
      _ = A * R ^ 2 * ‖z - y‖ := by ring
  have hvel : ‖Ky z.2 z.2 - Ky y.2 y.2‖ ≤
      6 * h.metricC 1 * R * ‖z - y‖ := by
    have hraw := MetricKoszul.koszul_vec_diag_le
      ((h.metric_equiv k x).coercive (hrMetric hy))
      (c := (1 / 2 : Real)) (by norm_num)
      (fun u ↦ by
        simpa [pow_two, mul_assoc] using (h.metric_equiv k x y.1 (hrMetric hy) u).1)
      (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y.1)
      (C := h.metricC 1) hC1 (h.fderiv_apply_le k x (hrMetric hy)) z.2 y.2
    norm_num at hraw
    calc
      ‖Ky z.2 z.2 - Ky y.2 y.2‖ ≤
          2 * ((3 / 2 : Real) * h.metricC 1 *
            (‖z.2‖ + ‖y.2‖) * ‖z.2 - y.2‖) := by
        simpa only [Ky] using hraw
      _ = 3 * h.metricC 1 * (‖z.2‖ + ‖y.2‖) * ‖z.2 - y.2‖ := by ring
      _ ≤ 3 * h.metricC 1 * (R + R) * ‖z - y‖ := by gcongr
      _ = 6 * h.metricC 1 * R * ‖z - y‖ := by ring
  have hsplit : Kz z.2 z.2 - Ky y.2 y.2 =
      (Kz z.2 z.2 - Ky z.2 z.2) + (Ky z.2 z.2 - Ky y.2 y.2) := by
    abel
  rw [hsplit]
  calc
    ‖(Kz z.2 z.2 - Ky z.2 z.2) + (Ky z.2 z.2 - Ky y.2 y.2)‖ ≤
        ‖Kz z.2 z.2 - Ky z.2 z.2‖ + ‖Ky z.2 z.2 - Ky y.2 y.2‖ :=
      norm_add_le _ _
    _ ≤ A * R ^ 2 * ‖z - y‖ + 6 * h.metricC 1 * R * ‖z - y‖ :=
      add_le_add hpos hvel
    _ = (A * R ^ 2 + 6 * h.metricC 1 * R) * ‖z - y‖ := by ring
    _ = ((6 * (h.metricC 1) ^ 2 + 3 * h.metricC 2) * R ^ 2 +
          6 * h.metricC 1 * R) * ‖z - y‖ := by rfl

omit [NeZero (Module.finrank Real E)] in
theorem koszul_accel_lip_le
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X)
    (k : Nat) (x : (X.obj k).M)
    (hsub :
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      Metric.ball (0 : E) (h.radius k x) ⊆
        Metric.ball (0 : E)
          (expMapC2Radius (I := I) (X.obj k).metric x))
    {z y : E × E} {R : Real} (hR : 0 ≤ R)
    (hz : z.1 ∈ Metric.ball (0 : E) (h.radius k x))
    (hy : y.1 ∈ Metric.ball (0 : E) (h.radius k x))
    (hzv : ‖z.2‖ ≤ R) (hyv : ‖y.2‖ ≤ R) :
    ‖MetricKoszul.koszulVec ((h.metric_equiv k x).coercive hz)
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) z.1) z.2 z.2 -
        MetricKoszul.koszulVec ((h.metric_equiv k x).coercive hy)
          (fderiv Real (normalCoordMetric (I := I) (X.obj k) x) y.1) y.2 y.2‖ ≤
      ((6 * (h.metricC 1) ^ 2 + 3 * h.metricC 2) * R ^ 2 +
          6 * h.metricC 1 * R) * ‖z - y‖ := by
  simpa using h.koszul_accel_lip_on k x (fun _ hz' ↦ hz') hsub hR hz hy hzv hyv

def subseq {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (h : NormalCoordMetricBounds (I := I) X) (f : Nat -> Nat) :
    NormalCoordMetricBounds (I := I) (X.subseq f) where
  metricC := h.metricC
  metricC_nonneg := h.metricC_nonneg
  radius := fun k x => h.radius (f k) x
  radius_pos := by
    intro k x
    exact h.radius_pos (f k) x
  metric_equiv := by
    intro k x
    simpa [PointedRiemannianSeq.subseq] using h.metric_equiv (f k) x
  metric_deriv := by
    intro k p x
    simpa [PointedRiemannianSeq.subseq] using h.metric_deriv (f k) p x

end NormalCoordMetricBounds

end RawNormalCoordinates

end HCGCompactness
end DifferentialGeometry
